"""
verifiers/python/gate_a0_lb.py — Standalone Certified Evaluation of GH26 Appendix D (N_a = 1000).

Computes outward-rounded 60-digit interval enclosures (mpmath.iv) with exact dyadic _mpi_
conversion to Fraction (handling both Python int and gmpy2.mpz mantissas cleanly) and strictly
outward-rounded decimal formatting for the published 3,000-item finite menu in
Giannakopoulos & Hahn (arXiv:2609.35711v3, Appendix D).
Refuses Python -O and uses zero assert-based checks.
"""
import time
from fractions import Fraction
import mpmath as mp

if not __debug__:
    raise RuntimeError("Refusing to run under Python -O (optimized mode).")

mp.mp.dps = 60
mp.iv.dps = 60


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"VERIFICATION FAILURE: {msg}")


def dyadic_tuple_to_frac(t) -> Fraction:
    """Convert finite mpmath _mpf_ 4-tuple (sign, man, exp, bc) to exact Fraction; strictly trap +/-inf and NaN."""
    require(isinstance(t, tuple) and len(t) == 4, f"Malformed mpmath tuple: {t!r}")
    sgn_bit, man, exp, bc = t
    if type(man).__name__ == "mpz":
        man = int(man)
    require(type(sgn_bit) is int and type(man) is int and type(exp) is int and type(bc) is int, f"Non-int tuple fields: {t!r}")
    require(bc >= 0, f"Non-finite mpmath special value encountered (inf/nan): {t!r}")
    require(mp.isfinite(mp.mpf(t)), f"mpmath.isfinite rejected endpoint: {t!r}")
    if man == 0:
        require(t == (0, 0, 0, 0), f"Non-canonical zero / special tuple rejected: {t!r}")
        return Fraction(0)
    require(sgn_bit in (0, 1) and man > 0, f"Invalid sign/mantissa: {t!r}")
    sgn = -1 if sgn_bit else 1
    if exp >= 0:
        return Fraction(sgn * (man << exp), 1)
    return Fraction(sgn * man, 1 << (-exp))


def fmt_frac_down(q: Fraction, digits: int = 16) -> str:
    require(q >= 0, "Expected nonnegative fraction")
    scale = 10 ** digits
    scaled = (q.numerator * scale) // q.denominator
    require(Fraction(scaled, scale) <= q, "Downward check failed")
    return f"{scaled // scale}.{scaled % scale:0{digits}d}"


def fmt_frac_up(q: Fraction, digits: int = 16) -> str:
    require(q >= 0, "Expected nonnegative fraction")
    scale = 10 ** digits
    num = q.numerator * scale
    den = q.denominator
    scaled = (num + den - 1) // den
    require(Fraction(scaled, scale) >= q, "Upward check failed")
    return f"{scaled // scale}.{scaled % scale:0{digits}d}"


def frac_to_iv_checked(q: Fraction):
    iv = mp.iv.mpf(q.numerator) / mp.iv.mpf(q.denominator)
    lo_f = dyadic_tuple_to_frac(iv._mpi_[0])
    hi_f = dyadic_tuple_to_frac(iv._mpi_[1])
    require(lo_f <= q <= hi_f, f"Enclosure failed for {q}")
    return iv


def poly_mul_trunc(a, b, deg: int):
    z0 = mp.iv.mpf(0)
    out = [z0] * (deg + 1)
    la = min(len(a), deg + 1)
    lb = min(len(b), deg + 1)
    for i in range(la):
        ai = a[i]
        if ai == 0:
            continue
        lim = min(lb, deg + 1 - i)
        for j in range(lim):
            bj = b[j]
            if bj != 0:
                out[i + j] += ai * bj
    return out


def poly_pow_trunc(base, exp: int, deg: int):
    res = [mp.iv.mpf(0)] * (deg + 1)
    res[0] = mp.iv.mpf(1)
    cur = list(base[: deg + 1])
    if len(cur) < deg + 1:
        cur.extend([mp.iv.mpf(0)] * (deg + 1 - len(cur)))
    e = exp
    while e > 0:
        if e & 1:
            res = poly_mul_trunc(res, cur, deg)
        e >>= 1
        if e > 0:
            cur = poly_mul_trunc(cur, cur, deg)
    return res


def eval_gh26_menu(label: str, F_ticks: int, p1_tick: int, uncond_pay_frac: Fraction) -> None:
    t0 = time.time()
    Na = 1000
    D = 40
    deg = F_ticks - 1
    specs = [
        ("A1", 5, 280, Fraction(3, 10), p1_tick),
        ("A2", 40, 320, Fraction(19, 20), 40),
        ("A3", 600, 880, Fraction(27, 8), 600),
    ]
    S_A = sum(s[3] for s in specs)
    require(S_A == Fraction(37, 8), "Unexpected S_A")

    P_single, Q_single = [], []
    for name, kmin, kmax, rev, p_tick in specs:
        pmf_k = {}
        for k in range(kmin, kmax + 1):
            s_cur = Fraction(D, Na * k) * rev
            s_nxt = Fraction(D, Na * (k + 1)) * rev if k < kmax else Fraction(0)
            pr = s_cur - s_nxt
            require(pr > 0, f"Non-positive PMF in {name}")
            pmf_k[k] = pr
        p0 = Fraction(1) - sum(pmf_k.values())
        require(p0 > 0, f"Non-positive p0 in {name}")
        surv = Fraction(0)
        for k in range(kmax, kmin - 1, -1):
            surv += pmf_k[k]
            require(Fraction(k, D) * surv == rev / Na, f"SRev mismatch in {name}")

        P = [mp.iv.mpf(0)] * (deg + 1)
        Q = [mp.iv.mpf(0)] * (deg + 1)
        P[0] += frac_to_iv_checked(p0)
        p_val_iv = frac_to_iv_checked(Fraction(p_tick, D))
        for k, pr in pmf_k.items():
            u = k - p_tick
            require(u >= 0, "Negative surplus tick")
            if u <= deg:
                pr_iv = frac_to_iv_checked(pr)
                P[u] += pr_iv
                if p_tick > 0:
                    Q[u] += pr_iv * p_val_iv
        P_single.append(P)
        Q_single.append(Q)

    P_pow = [poly_pow_trunc(P, Na, deg) for P in P_single]
    P_pow_m1 = [poly_pow_trunc(P, Na - 1, deg) for P in P_single]

    P_12 = poly_mul_trunc(P_pow[0], P_pow[1], deg)
    P_tot = poly_mul_trunc(P_12, P_pow[2], deg)
    p_non_enter = sum(P_tot, mp.iv.mpf(0))
    p_enter = mp.iv.mpf(1) - p_non_enter

    P_23 = poly_mul_trunc(P_pow[1], P_pow[2], deg)
    P_13 = poly_mul_trunc(P_pow[0], P_pow[2], deg)
    loss_A1 = mp.iv.mpf(Na) * sum(poly_mul_trunc(poly_mul_trunc(Q_single[0], P_pow_m1[0], deg), P_23, deg), mp.iv.mpf(0)) if p1_tick > 0 else mp.iv.mpf(0)
    loss_A2 = mp.iv.mpf(Na) * sum(poly_mul_trunc(poly_mul_trunc(Q_single[1], P_pow_m1[1], deg), P_13, deg), mp.iv.mpf(0))
    loss_A3 = mp.iv.mpf(Na) * sum(poly_mul_trunc(poly_mul_trunc(Q_single[2], P_pow_m1[2], deg), P_12, deg), mp.iv.mpf(0))
    loss_tot = loss_A1 + loss_A2 + loss_A3

    SA_iv = frac_to_iv_checked(S_A)
    F_iv = frac_to_iv_checked(Fraction(F_ticks, D))
    uncond_pay = frac_to_iv_checked(uncond_pay_frac)
    E_A = uncond_pay + F_iv * p_enter - loss_tot
    ratio = (E_A + SA_iv) / SA_iv

    pne_lo, pne_hi = dyadic_tuple_to_frac(p_non_enter._mpi_[0]), dyadic_tuple_to_frac(p_non_enter._mpi_[1])
    loss_lo, loss_hi = dyadic_tuple_to_frac(loss_tot._mpi_[0]), dyadic_tuple_to_frac(loss_tot._mpi_[1])
    rat_lo, rat_hi = dyadic_tuple_to_frac(ratio._mpi_[0]), dyadic_tuple_to_frac(ratio._mpi_[1])

    print("=" * 76)
    print(f"{label} (N_a = 1000, dps = 60, mpmath backend = {mp.libmp.BACKEND})")
    print("  (All printed decimals strictly outward-rounded)")
    print("=" * 76)
    print(f"  Pr[U_A < F]            in [{fmt_frac_down(pne_lo, 14)}, {fmt_frac_up(pne_hi, 14)}]")
    print(f"  E[Pay_A * 1{{U_A < F}}] in [{fmt_frac_down(loss_lo, 14)}, {fmt_frac_up(loss_hi, 14)}]")
    print(f"  (E_A + S_A) / S_A      in [{fmt_frac_down(rat_lo, 14)}, {fmt_frac_up(rat_hi, 14)}]")
    print(f"  Elapsed: {time.time() - t0:.2f}s")


def main():
    eval_gh26_menu("EXACT UNROUNDED EVALUATION OF GH26 APPENDIX D (p_1 = 0, F = 7)", 280, 0, Fraction(37, 8) - Fraction(3, 10))
    eval_gh26_menu("RE-PRICED 3-GROUP CONTROL ON GH26 ITEMS (p_1 = 1/8, F = 55/8)", 275, 5, Fraction(37, 8))


if __name__ == "__main__":
    main()
