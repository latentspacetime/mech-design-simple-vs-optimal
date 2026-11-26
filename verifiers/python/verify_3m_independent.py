"""
verify_3m_independent.py — Gate-4-Hardened Independent Python mpmath.iv Verifier (dps=35)
for Theorem 1: REV(X) <= (62/25) * max(SREV(X), BREV(X)) = 2.48 * max(SREV(X), BREV(X)).

Methodologically distinct from verify_3m_rust.rs:
  - Arithmetic backend: Python arbitrary-precision mpmath.iv at 35 decimal digits (dps=35)
  - Exact rational tree verification, halfspace construction, and upper-corner tightening via fractions.Fraction
  - Explicit _mpi_ dyadic enclosure self-check on every Fraction -> iv.mpf conversion
  - L(lam) upper bound via midpoint-convex Jensen lower bound on J(lam) = int_0^inf e^{-lam*t}/(1+t)^2 dt
  - Multi-resolution concentrated exact rational t-grids (up to 3,803 panels on [1e-7, 15000])
  - Exact pinned scales ls == (3/50, 7/20, 9/5) and hard theorem ceiling target <= 62/25
  - Zero assert-based checks (all invariants enforced via require() -> SystemExit); refuses Python -O.
"""
import argparse
import json
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from mpmath import iv

if sys.flags.optimize:
    raise SystemExit("REJECT: refusing to run under Python -O / PYTHONOPTIMIZE.")

iv.dps = 35
THEOREM_LS = [Fraction(3, 50), Fraction(7, 20), Fraction(9, 5)]
THEOREM_CEILING = Fraction(62, 25)


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise SystemExit(f"REJECT: {msg}")


def mpf_tup_to_frac(tup) -> Fraction:
    sign, man, exp, bc = tup
    if type(man).__name__ == "mpz":
        man = int(man)
    if man == 0 and exp == 0 and bc == 0:
        return Fraction(0)  # accepts both +0.0 and -0.0
    require(type(man) is int and man > 0 and bc > 0, f"Non-finite or invalid mpmath endpoint: {tup}")
    val = Fraction(man) * (Fraction(2) ** exp if exp >= 0 else Fraction(1, 2 ** (-exp)))
    return -val if sign else val


def f2iv(fr: Fraction):
    r = iv.mpf(fr.numerator) / iv.mpf(fr.denominator)
    require(mpf_tup_to_frac(r._mpi_[0]) <= fr <= mpf_tup_to_frac(r._mpi_[1]), "Enclosure failure")
    return r


def parse_frac(x) -> Fraction:
    require(isinstance(x, (int, float, str)) and not isinstance(x, bool), f"Bad JSON numeric: {x!r}")
    s = str(x).strip()
    require(0 < len(s) <= 64, f"Numeric token length out of bounds: {s!r}")
    require(s.lower() not in ("nan", "inf", "-inf", "infinity", "-infinity"), f"Non-finite JSON: {x!r}")
    if "e" in s.lower():
        parts = s.lower().split("e")
        require(len(parts) == 2 and -30 <= int(parts[1]) <= 30, f"Exponent out of bounds: {s!r}")
    return Fraction(s)


def ceil_dec(fr: Fraction, places: int = 8) -> str:
    scale = 10 ** places
    q, r = divmod(fr.numerator * scale, fr.denominator)
    if r > 0:
        q += 1
    neg = q < 0
    aq = -q if neg else q
    w, f = divmod(aq, scale)
    return f"{'-' if neg else ''}{w}.{f:0{places}d}"


_L_CACHE = {}


def L_upper_midpoint_convex(lam_fr: Fraction, lam_iv):
    """Rigorous upper bound on L(lam) via midpoint-convex lower bound on J(lam)."""
    if lam_fr in _L_CACHE:
        return _L_CACHE[lam_fr]
    require(lam_fr > 0, "lam must be > 0")
    scale = min(Fraction(1), Fraction(1) / lam_fr)
    knots = [Fraction(0)]
    for i in range(1, 201):
        knots.append(Fraction(2 * i, 200) * scale)
    t_start = float(knots[-1])
    t_end = max(600.0, 600.0 / float(lam_fr))
    for i in range(1, 501):
        fr = Fraction(f"{t_start * (t_end / t_start) ** (i / 500):.7g}")
        if fr > knots[-1]:
            knots.append(fr)
    J_lo = iv.mpf(0)
    for i in range(len(knots) - 1):
        dt = f2iv(knots[i + 1] - knots[i])
        mid = f2iv((knots[i] + knots[i + 1]) / 2)
        J_lo += dt * iv.exp(-lam_iv * mid) / ((iv.mpf(1) + mid) ** 2)
    require(J_lo.a > 0, "Non-positive J_lo")
    ans = lam_iv - iv.log(J_lo)
    _L_CACHE[lam_fr] = ans
    return ans


def build_halfspaces_exact(ls, box):
    l1, l2, l3 = ls
    g1a, g1b, g2a, g2b, g3a, g3b = box
    g1m, g2m, g3m = (g1a + g1b) / 2, (g2a + g2b) / 2, (g3a + g3b) / 2
    A = l1 * (l3 - l2) / (l2 * (l3 - l1))
    B = l3 * (l2 - l1) / (l2 * (l3 - l1))
    th = (l2 - l1) / (l3 - l1)

    def tangent(g0, dl):
        d = 1 + dl * g0
        return Fraction(1) / (d * d), (g0 / d) - g0 / (d * d)

    m12, r12 = tangent(g1m, l2 - l1)
    m23, r23 = tangent(g2m, l3 - l2)
    m13, r13 = tangent(g1m, l3 - l1)
    p = max(g3m, Fraction(1, 1000000))
    q = max(g1m, Fraction(1, 1000000))
    hd = ((1 - th) * p + th * q) ** 2
    h1, h3 = (1 - th) * p * p / hd, th * q * q / hd
    Z, O = Fraction(0), Fraction(1)
    D = [
        [O, Z, Z], [-O, Z, Z], [Z, O, Z], [Z, -O, Z], [Z, Z, O], [Z, Z, -O],
        [l1 / l2, -O, Z], [Z, l2 / l3, -O], [A, -O, B], [-(1 - th), O, -th],
        [-m12, O, Z], [Z, -m23, O], [-m13, Z, O], [-h1, O, -h3],
    ]
    d = [g1b, -g1a, g2b, -g2a, g3b, -g3a, Z, Z, Z, Z, r12, r23, r13, Z]
    return D, d


def ubar_upper(ls_fr, ls_iv, g_iv, t_fr, t_iv):
    # All ls_fr are included as exact grid knots, so each panel [t_j, t_{j+1}] lies
    # cleanly on one side of every l_i; Corollary 4 guarantees continuity and monotonicity.
    best = (iv.mpf(1) / t_iv).b
    for i in range(3):
        if t_fr <= ls_fr[i]:
            v = g_iv[i] * ls_iv[i] / t_iv
            if v.b < best: best = v.b
        if t_fr >= ls_fr[i]:
            den = iv.mpf(1) / g_iv[i] - ls_iv[i] + t_iv
            if den.a > 0:
                v = iv.mpf(1) / den
                if v.b < best: best = v.b
    for i in range(2):
        if ls_fr[i] <= t_fr <= ls_fr[i + 1]:
            th = f2iv((t_fr - ls_fr[i]) / (ls_fr[i + 1] - ls_fr[i]))
            den = (iv.mpf(1) - th) / g_iv[i] + th / g_iv[i + 1]
            if den.a > 0:
                v = iv.mpf(1) / den
                if v.b < best: best = v.b
    return iv.mpf(best)


def h_upper(u_iv):
    uh = iv.mpf(u_iv.b)
    if uh.b <= 0: return iv.mpf(0)
    if uh.b < iv.mpf("1e-4").a: return uh / iv.mpf(2)
    return iv.mpf(1) - (iv.mpf(1) - iv.exp(-uh)) / uh


def make_t_lvl(ls_fr, n_lo, n_mid, n_hi, t0, T):
    a, b = 1e-4, 50.0
    p1 = [Fraction(f"{t0 * (a / t0) ** (i / n_lo):.6g}") for i in range(n_lo + 1)]
    p2 = [Fraction(f"{a * (b / a) ** (i / n_mid):.6g}") for i in range(n_mid + 1)]
    p3 = [Fraction(f"{b * (T / b) ** (i / n_hi):.6g}") for i in range(n_hi + 1)]
    frs = sorted(set(p1 + p2 + p3 + list(ls_fr)))
    require(frs[0] > 0, "t-grid must be > 0")
    return frs, [f2iv(t) for t in frs], [f2iv((frs[j + 1] - frs[j]) / 2) for j in range(len(frs) - 1)]


_WS = {}


def _init_w(ls_fr, target_fr):
    iv.dps = 35
    c_raw = [Fraction(0)] + [Fraction(f"{5e-6 * (6000.0 / 5e-6) ** (i / 90):.6g}") for i in range(91)]
    c_frs = sorted(set(c_raw))
    _WS["ls_fr"] = ls_fr
    _WS["ls_iv"] = [f2iv(x) for x in ls_fr]
    _WS["target_fr"] = target_fr
    _WS["target_iv"] = f2iv(target_fr)
    _WS["c_frs"] = c_frs
    _WS["t_levels"] = [
        make_t_lvl(ls_fr, 30, 250, 30, 5e-7, 6000.0),
        make_t_lvl(ls_fr, 70, 820, 70, 3e-7, 10000.0),
        make_t_lvl(ls_fr, 140, 1950, 140, 1e-7, 15000.0),
        make_t_lvl(ls_fr, 150, 3500, 150, 1e-7, 15000.0),
    ]


def _verify_one(task):
    idx, box, a_fr, lam_fr, eta0_fr, y_fr = task
    ls_fr = _WS["ls_fr"]; ls_iv = _WS["ls_iv"]
    target_fr = _WS["target_fr"]; target_iv = _WS["target_iv"]
    c_frs = _WS["c_frs"]; t_levels = _WS["t_levels"]
    l1, l2, l3 = ls_fr
    th = (l2 - l1) / (l3 - l1)
    g1a, g1b, g2a, g2b, g3a, g3b = box

    require(len(a_fr) > 0 and len(a_fr) == len(lam_fr) and sum(a_fr) == 1 and all(a >= 0 for a in a_fr) and all(l > 0 for l in lam_fr), "Bad w")
    D, d = build_halfspaces_exact(ls_fr, box)
    require(len(y_fr) == len(d) and all(y >= 0 for y in y_fr), "Bad y")
    eta_fr = [sum(D[r][c] * y_fr[r] for r in range(len(d))) for c in range(3)]
    s_fr = sum(d[r] * y_fr[r] for r in range(len(d)))

    gh1 = min(g1b, Fraction(1) / l1)
    gh2 = min(g2b, Fraction(1) / l2)
    gh3 = min(g3b, Fraction(1) / l3)
    for _ in range(3):
        gh2 = min(gh2, gh1 / (1 + (l2 - l1) * gh1))
        gh3 = min(gh3, gh2 / (1 + (l3 - l2) * gh2), gh1 / (1 + (l3 - l1) * gh1))
        if gh1 > 0 and gh3 > 0:
            gh2 = min(gh2, Fraction(1) / ((1 - th) / gh1 + th / gh3))
    gh2 = min(gh2, gh1 / (1 + (l2 - l1) * gh1))
    gh3 = min(gh3, gh2 / (1 + (l3 - l2) * gh2))
    require(gh1 >= gh2 >= gh3 > 0, "Bad g_hi order")
    g_iv = [f2iv(gh1), f2iv(gh2), f2iv(gh3)]
    active = [(a, l, f2iv(a), f2iv(l)) for a, l in zip(a_fr, lam_fr) if a > 0]
    eta0_iv = f2iv(eta0_fr)
    eta_iv = [f2iv(x) for x in eta_fr]

    L_hi = iv.mpf(0); lbar = iv.mpf(0)
    for _, lf, av, lv in active:
        L_hi += (av / lv) * L_upper_midpoint_convex(lf, lv)
        lbar += av * lv
    base = iv.mpf(1) + L_hi + eta0_iv + f2iv(s_fr)
    allow = (target_iv - base).a

    exp_t_c = _WS.setdefault("exp_t_c", {})
    def get_et(lf, lv, lvl):
        k = (lf, lvl)
        if k not in exp_t_c:
            _, tivs, _ = t_levels[lvl]
            exp_t_c[k] = [iv.exp(-lv * tivs[j + 1]) for j in range(len(tivs) - 1)]
        return exp_t_c[k]

    pou_c = {}
    def get_lvl(lvl):
        if lvl not in pou_c:
            frs, tivs, dtivs = t_levels[lvl]
            nt = len(frs) - 1
            pou = [h_upper(ubar_upper(ls_fr, ls_iv, g_iv, frs[j], tivs[j])) for j in range(nt)]
            ets = [get_et(lf, lv, lvl) for _, lf, _, lv in active]
            pou_c[lvl] = (tivs, dtivs, nt, pou, tivs[0] * lbar, iv.mpf(1) / (iv.mpf(2) * tivs[-1]), ets)
        return pou_c[lvl]

    def eval_c(ca_fr, cb_fr, lvl):
        tivs, hdtivs, nt, pou, head, tail, ets = get_lvl(lvl)
        ca, cb = f2iv(ca_fr), f2iv(cb_fr)
        cc = [av * iv.exp(-lv * cb) for _, _, av, lv in active]
        ka = len(cc)
        Ih = head + tail
        one = iv.mpf(1)
        inv_p = one / (ca + tivs[0])
        for j in range(nt):
            inv_n = one / (ca + tivs[j + 1])
            wv = cc[0] * ets[0][j]
            for ki in range(1, ka):
                wv += cc[ki] * ets[ki][j]
            df = pou[j] - wv
            if df.b > 0: Ih += iv.mpf(df.b) * hdtivs[j] * (inv_p + inv_n)
            inv_p = inv_n
        aw = iv.mpf(0)
        for _, _, av, lv in active:
            z = lv * cb
            if cb_fr == 0: aw += av
            elif z.b < iv.mpf("1e-4").a: aw += av * (iv.mpf(1) - z / iv.mpf(2))
            else: aw += av * (iv.mpf(1) - iv.exp(-z)) / z
        lin = eta0_iv
        for i in range(3):
            ta = eta_iv[i] * f2iv(Fraction(1) / (ca_fr + ls_fr[i]))
            tb = eta_iv[i] * f2iv(Fraction(1) / (cb_fr + ls_fr[i]))
            lin = lin + iv.mpf(ta.a if ta.a <= tb.a else tb.a)
        return ((Ih - aw) - lin).b

    d_hi = iv.mpf(-100)
    q = [(c_frs[i], c_frs[i + 1], 0, 0) for i in range(len(c_frs) - 1)]
    while q:
        ca_fr, cb_fr, dep, tlvl = q.pop(0)
        vb = eval_c(ca_fr, cb_fr, tlvl)
        if vb > allow:
            if tlvl == 0: q.append((ca_fr, cb_fr, dep, 1))
            elif dep < 4:
                cm = (ca_fr + cb_fr) / 2
                q.append((ca_fr, cm, dep + 1, tlvl)); q.append((cm, cb_fr, dep + 1, tlvl))
            elif tlvl == 1: q.append((ca_fr, cb_fr, dep, 2))
            elif tlvl == 2: q.append((ca_fr, cb_fr, dep, 3))
            elif dep < 6:
                cm = (ca_fr + cb_fr) / 2
                q.append((ca_fr, cm, dep + 1, 3)); q.append((cm, cb_fr, dep + 1, 3))
            elif vb > d_hi.b: d_hi = iv.mpf(vb)
        elif vb > d_hi.b:
            d_hi = iv.mpf(vb)

    Cm_fr = c_frs[-1]; Cm = f2iv(Cm_fr)
    Itc = iv.log(iv.mpf(1) + iv.mpf(1) / (iv.mpf(2) * Cm)) + iv.log(iv.mpf(1) + iv.mpf(2) * Cm) / (iv.mpf(2) * Cm)
    lt = eta0_iv
    for i in range(3):
        ti = eta_iv[i] * f2iv(Fraction(1) / (Cm_fr + ls_fr[i]))
        lt = lt + iv.mpf(ti.a if ti.a < 0 else 0)
    tv = (Itc - lt).b
    if tv > d_hi.b: d_hi = iv.mpf(tv)
    tot = base + (iv.mpf(d_hi.b) if d_hi.b > 0 else iv.mpf(0))
    ub_fr = mpf_tup_to_frac(tot._mpi_[1])
    ok = bool(tot.b <= target_iv.a and ub_fr <= target_fr)
    return idx, ok, ub_fr


def reject_const(s):
    raise SystemExit(f"REJECT: illegal JSON constant {s!r}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cert_path")
    ap.add_argument("--expected-ls", type=str, default="3/50,7/20,9/5")
    ap.add_argument("--expected-target", type=str, default="62/25")
    ap.add_argument("--workers", type=int, default=min(8, os.cpu_count() or 4))
    args = ap.parse_args()
    t0 = time.time()
    with open(args.cert_path) as f:
        data = json.load(f, parse_float=str, parse_constant=reject_const)
    require(isinstance(data, dict), "Certificate root must be a JSON object")
    require(isinstance(data.get("ls"), list), "ls must be a JSON list")
    ls_fr = [parse_frac(x) for x in data["ls"]]
    exp_ls = [parse_frac(x) for x in args.expected_ls.split(",")]
    require(ls_fr == exp_ls and ls_fr == THEOREM_LS, f"ls mismatch: got {ls_fr}, expected_ls={exp_ls}, theorem_ls={THEOREM_LS}")
    require(len(ls_fr) == 3 and 0 < ls_fr[0] < ls_fr[1] < ls_fr[2], f"Bad ls: {ls_fr}")

    target_fr = parse_frac(data["target"])
    exp_fr = parse_frac(args.expected_target)
    require(0 < exp_fr <= THEOREM_CEILING, f"expected target {exp_fr} exceeds theorem ceiling {THEOREM_CEILING}")
    require(0 < target_fr <= THEOREM_CEILING, f"certificate target {target_fr} exceeds theorem ceiling {THEOREM_CEILING}")
    require(target_fr == exp_fr, f"certificate target {target_fr} != expected target {exp_fr} (refusing silent target mismatch)")

    tree = data["tree"]
    require(isinstance(tree, dict) and isinstance(tree.get("box"), list), "Root node/box malformed")
    rbox = [parse_frac(x) for x in tree["box"]]
    require(len(rbox) == 6, "Root box must have 6 coords")
    for i in range(3):
        require(rbox[2 * i] <= 0 and rbox[2 * i + 1] >= Fraction(1) / ls_fr[i], "Root box coverage fail")

    l1, l2, l3 = ls_fr
    A = l1 * (l3 - l2) / (l2 * (l3 - l1))
    B = l3 * (l2 - l1) / (l2 * (l3 - l1))
    th = (l2 - l1) / (l3 - l1)
    leaf_tasks = []
    n_disjoint = 0

    stack = [tree]
    while stack:
        node = stack.pop()
        require(isinstance(node, dict) and isinstance(node.get("box"), list), "Malformed tree node")
        box = [parse_frac(x) for x in node["box"]]
        require(len(box) == 6, "Box len != 6")
        g1a, g1b, g2a, g2b, g3a, g3b = box
        require(0 <= g1a < g1b and 0 <= g2a < g2b and 0 <= g3a < g3b, f"Bad box {box}")
        ntype = node.get("type")
        if ntype == "disjoint":
            # Non-strict closed-form exclusion of int(cl(L)) proved sound by proof.tex Section 6
            # topological closure theorem (cl(L) = cl(int(cl(L)))).
            ok = (
                g2b <= (l1 / l2) * g1a
                or g3b <= (l2 / l3) * g2a
                or g2a * (1 + (l2 - l1) * g1b) >= g1b
                or g3a * (1 + (l3 - l2) * g2b) >= g2b
                or g3a * (1 + (l3 - l1) * g1b) >= g1b
                or g2b <= A * g1a + B * g3a
                or (g1b > 0 and g3b > 0 and g2a * ((1 - th) * g3b + th * g1b) >= g1b * g3b)
            )
            if not ok and "farkas_y" in node:
                require(isinstance(node["farkas_y"], list), "farkas_y must be list")
                D, d = build_halfspaces_exact(ls_fr, box)
                fy = [parse_frac(v) for v in node["farkas_y"]]
                require(len(fy) == len(d) and all(v >= 0 for v in fy), "Bad farkas_y")
                DTy = [sum(D[r][c] * fy[r] for r in range(len(d))) for c in range(3)]
                lhs_min = sum(min(DTy[c] * box[2 * c], DTy[c] * box[2 * c + 1]) for c in range(3))
                ok = sum(d[r] * fy[r] for r in range(len(d))) < lhs_min
            require(ok, f"Invalid disjoint box {box}")
            n_disjoint += 1
        elif ntype == "split":
            ax = node.get("axis")
            ch = node.get("children")
            require(ax in (0, 1, 2) and isinstance(ch, list) and len(ch) == 2, "Invalid split")
            require(isinstance(ch[0], dict) and isinstance(ch[1], dict), "Malformed children")
            require(isinstance(ch[0].get("box"), list) and isinstance(ch[1].get("box"), list), "Malformed child boxes")
            c1 = [parse_frac(x) for x in ch[0]["box"]]
            c2 = [parse_frac(x) for x in ch[1]["box"]]
            require(len(c1) == 6 and len(c2) == 6, "Child box len != 6")
            for j in range(3):
                if j == ax:
                    require(c1[2 * j] == box[2 * j] and c1[2 * j + 1] == c2[2 * j] and c2[2 * j + 1] == box[2 * j + 1], "Split gap")
                else:
                    require(c1[2 * j] == box[2 * j] and c1[2 * j + 1] == box[2 * j + 1], "Off-axis mismatch 0")
                    require(c2[2 * j] == box[2 * j] and c2[2 * j + 1] == box[2 * j + 1], "Off-axis mismatch 1")
            stack.append(ch[1]); stack.append(ch[0])
        elif ntype == "leaf":
            require(
                isinstance(node.get("a"), list)
                and isinstance(node.get("lam"), list)
                and isinstance(node.get("y"), list),
                "Leaf arrays must be JSON lists",
            )
            leaf_tasks.append((
                len(leaf_tasks) + 1, box,
                [parse_frac(x) for x in node["a"]],
                [parse_frac(x) for x in node["lam"]],
                parse_frac(node["eta0"]),
                [parse_frac(x) for x in node["y"]],
            ))
        else:
            raise SystemExit(f"REJECT: unknown node type {ntype!r}")

    require(len(leaf_tasks) >= 1, "Vacuous certificate with 0 leaves")
    failed = 0
    done = 0
    max_ub_fr = Fraction(0)
    with ProcessPoolExecutor(max_workers=args.workers, initializer=_init_w, initargs=(ls_fr, target_fr)) as ex:
        for idx, ok, ub_fr in ex.map(_verify_one, leaf_tasks, chunksize=1):
            done += 1
            if ub_fr > max_ub_fr: max_ub_fr = ub_fr
            if not ok:
                failed += 1
                print(f"  [INDEP FAIL] leaf #{idx} ub<={ceil_dec(ub_fr)}", flush=True)
            elif done % 60 == 0 or done == len(leaf_tasks):
                print(f"  [INDEP PASS] {done}/{len(leaf_tasks)} leaves (max_ub<={ceil_dec(max_ub_fr)}, {time.time()-t0:.1f}s)", flush=True)

    verdict = "PASS" if failed == 0 else "FAIL"
    ls_str = ",".join(str(x) for x in ls_fr)
    print(f"INDEPENDENT VERIFIER (dps=35, midpoint-convex L) {verdict}: ls=({ls_str}), leaves={len(leaf_tasks)}, disjoint={n_disjoint}, failed={failed}, max_ub<={ceil_dec(max_ub_fr)} (target={target_fr}, {time.time()-t0:.1f}s)")
    sys.exit(0 if failed == 0 else 1)


if __name__ == "__main__":
    main()
