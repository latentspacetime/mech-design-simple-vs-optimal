"""
verifiers/python/verify_lb_independent.py — Standalone Verifier 2
(Exact Python arbitrary-precision Fraction + 140-bit outward-rounded integer Kronecker
interval polynomial arithmetic + mpmath.iv dps=50 Chernoff tail bound).

Independently certifies cert_lb_2195.json:
  REV(X) > (439/200) * max(SREV(X), BREV(X)) = 2.195 * max(SREV(X), BREV(X)).

Verification discipline:
  - Refuses Python -O (__debug__ check); ZERO assert-based checks (explicit RuntimeError traps).
  - Resolves certificate via optional argv[1] or sibling/certificates cert_lb_2195.json (zero hardcoded paths)
    and logs exact path and SHA-256 digest.
  - Exact rational arithmetic (fractions.Fraction) pins ALL certificate fields (target, D, F, Na,
    P_0, t, deg_Z, S_A, and all 8 group specifications including k_max = k_min + 700), verifies strict
    point-mass positivity (including p_0 = 1 - sum > 0) alongside exact rational support checks,
    and verifies single-item SRev == r_g / Na at every support point.
  - Exact outward-rounded fixed-point integer interval arithmetic at scale 2^{-140} (~42 decimal digits)
    with ZERO subtraction and dynamically sized non-overlapping Kronecker bit-stride W > bit_length(max_coeff).
  - Outward-rounded mpmath.iv (dps=50) with exact dyadic _mpi_ containment self-checks on all rational-to-interval
    conversions (handling both Python int and gmpy2.mpz mantissas cleanly) for the Chernoff MGF infinite-tail
    bound covering ALL p in [55, inf).
  - ALL printed decimal lower/upper bounds are strictly outward-rounded via exact integer floor/ceil!
"""
import hashlib
import json
import sys
import time
from fractions import Fraction
from pathlib import Path
import mpmath as mp

if not __debug__:
    raise RuntimeError("Refusing to run under Python -O (optimized mode).")

DPS = 50
mp.mp.dps = DPS
mp.iv.dps = DPS

# Fixed-point integer interval scale: 2^{-S}, S = 140 bits (~42.1 decimal digits)
SCALE_BITS = 140
SCALE_ONE = 1 << SCALE_BITS
SCALE_MASK = SCALE_ONE - 1

# Complete exact pinned theorem constants (matching Table 1 & cert_lb_2195.json)
PINNED_TARGET = Fraction(439, 200)
PINNED_GRID_DEN = 100
PINNED_F_TICKS = 700
PINNED_NA = 5000
PINNED_P0_TICKS = 5500
PINNED_CHERNOFF_T = Fraction(1, 10)
PINNED_DEG_Z = 5013
PINNED_SA = Fraction(1949, 400)
PINNED_GROUPS = [
    ("A1", 227, 2000, 7, 707, 7),
    ("A2", 207, 2000, 11, 711, 11),
    ("A3", 9, 250, 16, 716, 16),
    ("A4", 547, 2000, 46, 746, 46),
    ("A5", 179, 1000, 82, 782, 82),
    ("A6", 199, 1000, 118, 818, 118),
    ("A7", 817, 2000, 166, 866, 166),
    ("A8", 7119, 2000, 1545, 2245, 1545),
]


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"VERIFICATION FAILURE: {msg}")


def require_exact_int(val, name: str) -> int:
    """Require exact JSON integer (rejects floats, bools, and strings)."""
    require(type(val) is int, f"Field '{name}' must be an exact JSON integer, got {type(val).__name__}: {val!r}")
    return val


def fmt_frac_down(q: Fraction, digits: int = 24) -> str:
    """Strictly downward-rounded decimal string: exact decimal value <= q."""
    require(q >= 0, f"Expected nonnegative fraction in fmt_frac_down, got {q}")
    scale = 10 ** digits
    scaled = (q.numerator * scale) // q.denominator
    require(Fraction(scaled, scale) <= q, "Downward decimal rounding check failed")
    return f"{scaled // scale}.{scaled % scale:0{digits}d}"


def fmt_frac_up(q: Fraction, digits: int = 24) -> str:
    """Strictly upward-rounded decimal string: exact decimal value >= q."""
    require(q >= 0, f"Expected nonnegative fraction in fmt_frac_up, got {q}")
    scale = 10 ** digits
    num = q.numerator * scale
    den = q.denominator
    scaled = (num + den - 1) // den
    require(Fraction(scaled, scale) >= q, "Upward decimal rounding check failed")
    return f"{scaled // scale}.{scaled % scale:0{digits}d}"


def fmt_width_up(q: Fraction) -> str:
    """Strictly upward-rounded scientific bound on a positive rational width q."""
    require(q > 0, "Expected positive width")
    # Find smallest integer e such that q < 10^e, then ceil(q * 10^(3 - e)) * 10^(e - 3)
    exp = 0
    val = q
    while val >= 10:
        val /= 10
        exp += 1
    while val < 1:
        val *= 10
        exp -= 1
    # Now 1 <= q * 10^(-exp) < 10; round up to 3 decimal digits of mantissa
    scale = Fraction(1000, 1) * (Fraction(10, 1) ** (-exp))
    scaled_num = (q * scale).numerator
    scaled_den = (q * scale).denominator
    m_up = (scaled_num + scaled_den - 1) // scaled_den
    bound = Fraction(m_up, 1000) * (Fraction(10, 1) ** exp)
    require(bound >= q, "Width upward bound failed")
    return f"{m_up / 1000:.3f}e{exp:+d}"


def dyadic_tuple_to_frac(t) -> Fraction:
    """Convert finite mpmath _mpf_ 4-tuple (sign, man, exp, bc) to exact Fraction; strictly trap +/-inf and NaN."""
    require(isinstance(t, tuple) and len(t) == 4, f"Malformed mpmath tuple: {t!r}")
    sgn_bit, man, exp, bc = t
    if type(man).__name__ == "mpz":
        man = int(man)
    # In mpmath, +/-inf and NaN have man == 0 with negative bc (-1, -2, -3) and nonzero sentinel exp!
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


def frac_to_fx(q: Fraction) -> tuple[int, int]:
    """Convert exact nonnegative Fraction q >= 0 to outward-rounded (lo, hi) with lo/2^S <= q <= hi/2^S."""
    require(q >= 0, f"Expected nonnegative fraction for fx conversion, got {q}")
    num = q.numerator << SCALE_BITS
    den = q.denominator
    lo = num // den
    hi = (num + den - 1) // den
    require(Fraction(lo, SCALE_ONE) <= q <= Fraction(hi, SCALE_ONE), f"fx enclosure failed for {q}")
    return lo, hi


def poly_mul_kronecker_trunc(
    a_lo: list[int], a_hi: list[int], b_lo: list[int], b_hi: list[int], deg: int
) -> tuple[list[int], list[int]]:
    """
    Exact outward-rounded truncated multiplication of nonnegative fixed-point polynomials
    via dynamically sized Kronecker substitution (guaranteed zero carry overlap!).
    """
    la = min(len(a_lo), deg + 1)
    lb = min(len(b_lo), deg + 1)
    if la == 0 or lb == 0:
        return [], []
    out_len = min(la + lb - 1, deg + 1)

    max_a = max(a_hi[:la])
    max_b = max(b_hi[:lb])
    if max_a == 0 or max_b == 0:
        return [0] * out_len, [0] * out_len

    max_coeff = min(la, lb) * max_a * max_b
    W = max_coeff.bit_length() + 4
    require(max_coeff < (1 << W), "Kronecker stride invariant violated")

    def pack(arr: list[int], length: int) -> int:
        def rec(l: int, r: int) -> int:
            if r - l == 1:
                return arr[l]
            m = (l + r) // 2
            return rec(l, m) | (rec(m, r) << ((m - l) * W))
        return rec(0, length)

    def unpack(val: int, length: int) -> list[int]:
        out = [0] * length
        def rec(v: int, l: int, r: int) -> None:
            if r - l == 1:
                out[l] = v
                return
            m = (l + r) // 2
            shift = (m - l) * W
            lo_part = v & ((1 << shift) - 1)
            hi_part = v >> shift
            rec(lo_part, l, m)
            rec(hi_part, m, r)
        val_trunc = val & ((1 << (length * W)) - 1)
        rec(val_trunc, 0, length)
        return out

    pa_lo = pack(a_lo, la)
    pb_lo = pack(b_lo, lb)
    pa_hi = pack(a_hi, la)
    pb_hi = pack(b_hi, lb)

    prod_lo_raw = unpack(pa_lo * pb_lo, out_len)
    prod_hi_raw = unpack(pa_hi * pb_hi, out_len)

    c_lo = [v >> SCALE_BITS for v in prod_lo_raw]
    c_hi = [(v + SCALE_MASK) >> SCALE_BITS for v in prod_hi_raw]
    for i in range(out_len):
        require(0 <= c_lo[i] <= c_hi[i], f"Invalid interval at coeff {i}")
    return c_lo, c_hi


def poly_pow_trunc(base_lo: list[int], base_hi: list[int], exp: int, deg: int) -> tuple[list[int], list[int]]:
    """Binary exponentiation modulo z^{deg+1} in exact outward-rounded Kronecker fixed-point intervals."""
    res_lo = [SCALE_ONE]
    res_hi = [SCALE_ONE]
    cur_lo = list(base_lo[: deg + 1])
    cur_hi = list(base_hi[: deg + 1])
    e = exp
    while e > 0:
        if e & 1:
            res_lo, res_hi = poly_mul_kronecker_trunc(res_lo, res_hi, cur_lo, cur_hi, deg)
        e >>= 1
        if e > 0:
            cur_lo, cur_hi = poly_mul_kronecker_trunc(cur_lo, cur_hi, cur_lo, cur_hi, deg)
    if len(res_lo) < deg + 1:
        pad = deg + 1 - len(res_lo)
        res_lo.extend([0] * pad)
        res_hi.extend([0] * pad)
    return res_lo, res_hi


def frac_to_iv_checked(q: Fraction):
    """Convert exact Fraction to mpmath.iv with explicit exact dyadic _mpi_ containment self-check."""
    iv = mp.iv.mpf(q.numerator) / mp.iv.mpf(q.denominator)
    a_t, b_t = iv._mpi_
    lo_f = dyadic_tuple_to_frac(a_t)
    hi_f = dyadic_tuple_to_frac(b_t)
    require(lo_f <= q <= hi_f, f"mpmath.iv enclosure check failed for {q}: [{lo_f}, {hi_f}]")
    return iv


def resolve_cert_path() -> Path:
    if len(sys.argv) > 1:
        return Path(sys.argv[1]).resolve()
    p = Path(__file__).resolve().parent.parent.parent / "certificates" / "cert_lb_2195.json"
    require(p.exists(), f"Certificate not found at {p}; pass explicit path as argv[1].")
    return p


def main():
    t0 = time.time()
    cert_path = resolve_cert_path()
    raw_bytes = cert_path.read_bytes()
    cert_sha = hashlib.sha256(raw_bytes).hexdigest()
    data = json.loads(raw_bytes.decode("utf-8"))

    target_num = require_exact_int(data["target_num"], "target_num")
    target_den = require_exact_int(data["target_den"], "target_den")
    D = require_exact_int(data["grid_den"], "grid_den")
    F_ticks = require_exact_int(data["entry_fee_ticks"], "entry_fee_ticks")
    Na = require_exact_int(data["Na"], "Na")
    P0_ticks = require_exact_int(data["chernoff_P0_ticks"], "chernoff_P0_ticks")
    t_num = require_exact_int(data["chernoff_t_num"], "chernoff_t_num")
    t_den = require_exact_int(data["chernoff_t_den"], "chernoff_t_den")

    # Pin ALL raw integer and rational scalar certificate parameters
    require(target_num == 439 and target_den == 200, f"Raw target mismatch: {target_num}/{target_den}")
    target = Fraction(target_num, target_den)
    require(target == PINNED_TARGET, f"Target mismatch: {target} != {PINNED_TARGET}")
    require(D == PINNED_GRID_DEN, f"Grid den mismatch: {D} != {PINNED_GRID_DEN}")
    require(F_ticks == PINNED_F_TICKS, f"F_ticks mismatch: {F_ticks} != {PINNED_F_TICKS}")
    require(Na == PINNED_NA, f"Na mismatch: {Na} != {PINNED_NA}")
    require(P0_ticks == PINNED_P0_TICKS, f"P0_ticks mismatch: {P0_ticks} != {PINNED_P0_TICKS}")
    require(t_num == 1 and t_den == 10, f"Raw Chernoff t mismatch: {t_num}/{t_den}")
    t_ch = Fraction(t_num, t_den)
    require(t_ch == PINNED_CHERNOFF_T, f"Chernoff t mismatch: {t_ch} != {PINNED_CHERNOFF_T}")
    require(t_ch > 0 and Fraction(P0_ticks, D) >= Fraction(1, 1) / t_ch, "Chernoff monotonicity requires P0 >= 1/t")

    F_frac = Fraction(F_ticks, D)
    P0_frac = Fraction(P0_ticks, D)
    groups_raw = data["groups"]
    require(isinstance(groups_raw, list) and len(groups_raw) == len(PINNED_GROUPS), f"Expected {len(PINNED_GROUPS)} groups")

    # 1. Pin ALL 8 raw & rational group specifications + exact rational PMF & single-item SRev verification
    groups = []
    S_A = Fraction(0)
    for idx, g in enumerate(groups_raw):
        exp_name, exp_rn, exp_rd, exp_kmin, exp_kmax, exp_pt = PINNED_GROUPS[idx]
        r_num = require_exact_int(g["r_num"], f"groups[{idx}].r_num")
        r_den = require_exact_int(g["r_den"], f"groups[{idx}].r_den")
        k_min = require_exact_int(g["k_min"], f"groups[{idx}].k_min")
        k_max = require_exact_int(g["k_max"], f"groups[{idx}].k_max")
        p_tick = require_exact_int(g["p_tick"], f"groups[{idx}].p_tick")
        require(g["name"] == exp_name, f"Group name mismatch at {idx}")
        require(r_num == exp_rn and r_den == exp_rd, f"Raw r_g mismatch in {exp_name}: {r_num}/{r_den} != {exp_rn}/{exp_rd}")
        r_g = Fraction(r_num, r_den)
        require(k_min == exp_kmin and k_max == exp_kmax and p_tick == exp_pt, f"Tick mismatch in {exp_name}")
        require(k_max == k_min + F_ticks, f"Span mismatch in {exp_name}")
        require(r_g > 0 and 1 <= k_min <= k_max and p_tick == k_min, f"Invalid group spec {g}")
        S_A += r_g

        pmf_k = {}
        for k in range(k_min, k_max + 1):
            s_cur = Fraction(D, Na * k) * r_g
            s_nxt = Fraction(D, Na * (k + 1)) * r_g if k < k_max else Fraction(0)
            pr = s_cur - s_nxt
            require(pr > 0, f"Non-positive PMF at k={k} in {g['name']}")
            pmf_k[k] = pr
        sum_pos = sum(pmf_k.values())
        p0 = Fraction(1) - sum_pos
        require(p0 > 0, f"Non-positive p0 in {g['name']}")

        surv = Fraction(0)
        for k in range(k_max, k_min - 1, -1):
            surv += pmf_k[k]
            rev_k = Fraction(k, D) * surv
            require(rev_k == r_g / Na, f"Single-item SRev mismatch at k={k} in {g['name']}")

        uncond_one = Fraction(p_tick, D) * surv
        require(uncond_one == r_g / Na, f"Unconditional payment mismatch in {g['name']}")

        groups.append({
            "name": g["name"],
            "r_g": r_g,
            "k_min": k_min,
            "k_max": k_max,
            "p_tick": p_tick,
            "p0": p0,
            "pmf_k": pmf_k,
        })

    require(S_A == PINNED_SA, f"Unexpected S_A={S_A} != {PINNED_SA}")
    print("=" * 76)
    print("VERIFIER 2 (Python Exact Fraction + 140-bit Kronecker Int-IV + mpmath.iv)")
    print(f"  Input certificate: {cert_path}")
    print(f"  Certificate SHA-256: {cert_sha}")
    print("=" * 76)
    print(f"  [PASS] All 8 groups & parameters pinned; exact PMFs & single-item SRev verified (S_A = {S_A}).")

    # 2. Entry-Fee Revenue on A (deg_U = 699) via 140-bit exact Kronecker integer intervals
    t_u0 = time.time()
    deg_U = F_ticks - 1
    K = len(groups)
    P_U_lo, P_U_hi = [], []
    Q_U_lo, Q_U_hi = [], []
    for g in groups:
        plo = [0] * (deg_U + 1)
        phi = [0] * (deg_U + 1)
        qlo = [0] * (deg_U + 1)
        qhi = [0] * (deg_U + 1)
        p0_l, p0_h = frac_to_fx(g["p0"])
        plo[0] += p0_l
        phi[0] += p0_h
        p_tick = g["p_tick"]
        p_val_frac = Fraction(p_tick, D)
        for k, pr in g["pmf_k"].items():
            u = k - p_tick
            require(u >= 0, "Negative surplus tick")
            if u <= deg_U:
                pr_l, pr_h = frac_to_fx(pr)
                plo[u] += pr_l
                phi[u] += pr_h
                qp_l, qp_h = frac_to_fx(pr * p_val_frac)
                qlo[u] += qp_l
                qhi[u] += qp_h
        P_U_lo.append(plo)
        P_U_hi.append(phi)
        Q_U_lo.append(qlo)
        Q_U_hi.append(qhi)

    P_U_pow = [poly_pow_trunc(P_U_lo[i], P_U_hi[i], Na, deg_U) for i in range(K)]
    P_U_pow_m1 = [poly_pow_trunc(P_U_lo[i], P_U_hi[i], Na - 1, deg_U) for i in range(K)]

    pref = [([SCALE_ONE], [SCALE_ONE])]
    for i in range(K):
        pref.append(poly_mul_kronecker_trunc(pref[-1][0], pref[-1][1], P_U_pow[i][0], P_U_pow[i][1], deg_U))
    suff = [None] * (K + 1)
    suff[K] = ([SCALE_ONE], [SCALE_ONE])
    for i in range(K - 1, -1, -1):
        suff[i] = poly_mul_kronecker_trunc(P_U_pow[i][0], P_U_pow[i][1], suff[i + 1][0], suff[i + 1][1], deg_U)

    p_ne_lo = Fraction(sum(pref[K][0]), SCALE_ONE)
    p_ne_hi = Fraction(sum(pref[K][1]), SCALE_ONE)
    require(Fraction(0) <= p_ne_lo <= p_ne_hi <= Fraction(1), "Invalid p_non_enter interval")

    loss_lo = Fraction(0)
    loss_hi = Fraction(0)
    for i in range(K):
        oth_lo, oth_hi = poly_mul_kronecker_trunc(pref[i][0], pref[i][1], suff[i + 1][0], suff[i + 1][1], deg_U)
        qp_lo, qp_hi = poly_mul_kronecker_trunc(Q_U_lo[i], Q_U_hi[i], P_U_pow_m1[i][0], P_U_pow_m1[i][1], deg_U)
        fl_lo, fl_hi = poly_mul_kronecker_trunc(qp_lo, qp_hi, oth_lo, oth_hi, deg_U)
        loss_lo += Fraction(Na * sum(fl_lo), SCALE_ONE)
        loss_hi += Fraction(Na * sum(fl_hi), SCALE_ONE)

    E_A_lo = S_A + F_frac * (Fraction(1) - p_ne_hi) - loss_hi
    E_A_hi = S_A + F_frac * (Fraction(1) - p_ne_lo) - loss_lo
    ratio_lo = (E_A_lo + S_A) / S_A
    ratio_hi = (E_A_hi + S_A) / S_A
    require(ratio_lo <= ratio_hi, "Inverted ratio interval")
    require(ratio_lo > target, f"Ratio lower bound <= target {target}")
    r_width = ratio_hi - ratio_lo

    print(f"  [PASS] Entry-fee PGF (deg={deg_U}) computed in {time.time() - t_u0:.3f}s (all decimals strictly outward-rounded):")
    print(f"         Pr[U_A < 7]              in [{fmt_frac_down(p_ne_lo, 24)}, {fmt_frac_up(p_ne_hi, 24)}]")
    print(f"         E[Pay_A * 1{{U_A < 7}}]   in [{fmt_frac_down(loss_lo, 24)}, {fmt_frac_up(loss_hi, 24)}]")
    print(f"         (E_A + S_A) / S_A        in [{fmt_frac_down(ratio_lo, 24)}, {fmt_frac_up(ratio_hi, 24)}]")
    print(f"         Exact internal width     <= {fmt_width_up(r_width)}")
    print(f"  [PASS] Certified strict exact-rational inequality: (E_A + S_A)/S_A >= {fmt_frac_down(ratio_lo, 21)} > {target}")

    # 3a. Exact Finite-Grid BRev Certification for ALL k = 1..deg_Z (exact integer ceiling!)
    t_z0 = time.time()
    diff_ticks = (P0_frac - S_A) * D
    require(diff_ticks > 0, "P0 must exceed S_A")
    deg_Z = (diff_ticks.numerator + diff_ticks.denominator - 1) // diff_ticks.denominator
    require(deg_Z == PINNED_DEG_Z, f"Pinned deg_Z mismatch: {deg_Z} != {PINNED_DEG_Z}")
    require(S_A + Fraction(deg_Z, D) >= P0_frac, "deg_Z fails to reach P0")

    tot_lo, tot_hi = [SCALE_ONE], [SCALE_ONE]
    for g in groups:
        blo = [0] * (deg_Z + 1)
        bhi = [0] * (deg_Z + 1)
        p0_l, p0_h = frac_to_fx(g["p0"])
        blo[0] = p0_l
        bhi[0] = p0_h
        for k, pr in g["pmf_k"].items():
            if k <= deg_Z:
                pr_l, pr_h = frac_to_fx(pr)
                blo[k] += pr_l
                bhi[k] += pr_h
        pw_lo, pw_hi = poly_pow_trunc(blo, bhi, Na, deg_Z)
        tot_lo, tot_hi = poly_mul_kronecker_trunc(tot_lo, tot_hi, pw_lo, pw_hi, deg_Z)

    cdf_lo_int = 0
    cdf_hi_int = 0
    max_rev_hi = Fraction(0)
    max_rev_k = 0
    max_w_z = Fraction(0)
    for k in range(1, deg_Z + 1):
        cdf_lo_int += tot_lo[k - 1]
        cdf_hi_int += tot_hi[k - 1]
        surv_hi = Fraction(SCALE_ONE - cdf_lo_int, SCALE_ONE)
        surv_lo = Fraction(SCALE_ONE - cdf_hi_int, SCALE_ONE)
        pk = S_A + Fraction(k, D)
        rev_hi = pk * surv_hi
        rev_lo = pk * surv_lo
        w = rev_hi - rev_lo
        if w > max_w_z:
            max_w_z = w
        if rev_hi > max_rev_hi:
            max_rev_hi = rev_hi
            max_rev_k = k
        require(rev_hi <= S_A, f"BRev violation at k={k}")

    slack_z = S_A - max_rev_hi
    print(f"  [PASS] Finite-grid BRev verified for ALL k = 1..{deg_Z} in {time.time() - t_z0:.3f}s:")
    print(f"         max_{{1<=k<={deg_Z}}} (S_A + k/{D})*Pr[Z_A >= k/{D}] <= {fmt_frac_up(max_rev_hi, 18)} < S_A = 4.8725")
    print(f"         Worst grid point k = {max_rev_k} (slack >= {fmt_frac_down(slack_z, 12)}, max internal width <= {fmt_width_up(max_w_z)})")

    # 3b. Infinite-Tail Chernoff MGF Bound for ALL p >= P_0 = 55 via mpmath.iv (dps=50)!
    t_iv = frac_to_iv_checked(t_ch)
    P0_iv = frac_to_iv_checked(P0_frac)
    SA_iv = frac_to_iv_checked(S_A)
    M_tot = mp.iv.mpf(1)
    for g in groups:
        mgf_one = frac_to_iv_checked(g["p0"])
        for k, pr in g["pmf_k"].items():
            x_iv = frac_to_iv_checked(Fraction(k, D))
            mgf_one += frac_to_iv_checked(pr) * mp.iv.exp(t_iv * x_iv)
        M_tot *= mgf_one ** Na
    chernoff_iv = P0_iv * mp.iv.exp(-t_iv * (P0_iv - SA_iv)) * M_tot
    chernoff_hi_frac = dyadic_tuple_to_frac(chernoff_iv._mpi_[1])
    require(chernoff_hi_frac < S_A, f"Chernoff tail bound failed: {chernoff_hi_frac} >= {S_A}")
    print(f"  [PASS] Infinite-tail mpmath.iv Chernoff bound (ALL p >= {P0_frac}, t={t_ch}):")
    print(f"         sup_{{p >= {P0_frac}}} p*Pr[S_A + Z_A >= p] <= {fmt_frac_up(chernoff_hi_frac, 18)} < S_A = 4.8725")

    print("\n" + "=" * 76)
    print(f"VERIFIER 2 FINAL VERDICT: PASS (0 failures, elapsed {time.time() - t0:.3f}s)")
    print(f"  CERTIFIED: REV(X) > ({target}) * max(SREV(X), BREV(X)) = 2.195 * max(SREV, BREV)")
    print(f"  Certified outward-rounded lower endpoint: {fmt_frac_down(ratio_lo, 21)}")
    print("=" * 76)


if __name__ == "__main__":
    main()
