//! Gate-4-Hardened Independent Rust IEEE-754 Outward-Rounded Interval-Arithmetic Verifier
//! for the 3-Moment Reciprocal-Concavity Theorem (proof.tex, Theorem 1: REV <= 62/25 * max(SREV, BREV)).
//!
//! ZERO TRUST IN `libm::exp` OR `libm::ln`:
//!   - Every `Iv` constructor enforces `lo.is_finite() && hi.is_finite() && lo <= hi` (NaN/Inf fail-closed).
//!   - Basic ops (+, -, *, /) widen every IEEE-754 result by 1 full ULP outward (`next_down` / `next_up`).
//!   - `Iv::exp` is computed purely from IEEE-754 (+, -, *, /) via exact power-of-2 range reduction
//!     x = 2^m * r (|r| <= 0.25), degree-14 Taylor polynomial with proven remainder |R_15| <= 2*(0.25)^15/15! < 1e-21,
//!     and m interval squarings.
//!   - `Iv::ln` is computed purely from IEEE-754 (+, -, *, /) via exact exponent split y = 2^k * m (m in [0.75, 1.5]),
//!     atanh series 2 * sum_{n=0}^{14} z^{2n+1}/(2n+1) (|z| <= 1/5, |R| < 1e-21), and a startup-self-certified
//!     enclosure of ln(2) verified by `exp(ln2_lo) < 2 < exp(ln2_hi)`.
//!   - Scales ls = (3/50, 7/20, 9/5) and weights sum(a) == 1 are verified in exact decimal i128 arithmetic
//!     with checked_mul/checked_add (zero integer overflow possible).
//!   - Branch decisions in `ubar_hi` use ONLY interval endpoints (never raw floats).
//!   - Disjointness certifies R intersect int(cl(L)) = empty (covered by the topological closure theorem in
//!     proof.tex Section 6: cl(L) = cl(int(cl(L))), finitely many closed certified leaves cover cl(L)).

use rayon::prelude::*;
use serde::Deserialize;
use std::fs;
use std::time::Instant;

#[derive(Clone, Copy, Debug)]
struct Iv {
    lo: f64,
    hi: f64,
}

impl Iv {
    #[inline]
    fn new(lo: f64, hi: f64) -> Self {
        assert!(lo.is_finite() && hi.is_finite() && lo <= hi, "Invalid interval [{}, {}]", lo, hi);
        Self { lo, hi }
    }
    #[inline]
    fn exact(x: f64) -> Self {
        Self::new(x, x)
    }
    #[inline]
    fn from_ratio_i128(num: i128, den: i128) -> Self {
        assert!(den > 0, "Non-positive rational denominator");
        // Exact enclosure of num/den using IEEE-754 division widened 2 ULPs (exact for |num|,|den| < 2^53,
        // and we assert num, den fit exactly in f64 with zero loss!).
        let nf = num as f64;
        let df = den as f64;
        assert!((nf as i128) == num && (df as i128) == den, "i128 exceeds exact f64 range: {}/{}", num, den);
        Self::exact(nf).div(Self::exact(df))
    }
    #[inline]
    fn neg(self) -> Self {
        Self::new(-self.hi, -self.lo)
    }
    #[inline]
    fn add(self, o: Self) -> Self {
        Self::new((self.lo + o.lo).next_down(), (self.hi + o.hi).next_up())
    }
    #[inline]
    fn sub(self, o: Self) -> Self {
        Self::new((self.lo - o.hi).next_down(), (self.hi - o.lo).next_up())
    }
    #[inline]
    fn mul(self, o: Self) -> Self {
        let p1 = self.lo * o.lo;
        let p2 = self.lo * o.hi;
        let p3 = self.hi * o.lo;
        let p4 = self.hi * o.hi;
        assert!(p1.is_finite() && p2.is_finite() && p3.is_finite() && p4.is_finite(), "Overflow in Iv::mul");
        let mn = p1.min(p2).min(p3).min(p4);
        let mx = p1.max(p2).max(p3).max(p4);
        Self::new(mn.next_down(), mx.next_up())
    }
    #[inline]
    fn div(self, o: Self) -> Self {
        assert!(o.lo > 0.0 || o.hi < 0.0, "Interval division containing zero: [{}, {}]", o.lo, o.hi);
        let p1 = self.lo / o.lo;
        let p2 = self.lo / o.hi;
        let p3 = self.hi / o.lo;
        let p4 = self.hi / o.hi;
        assert!(p1.is_finite() && p2.is_finite() && p3.is_finite() && p4.is_finite(), "Overflow in Iv::div");
        let mn = p1.min(p2).min(p3).min(p4);
        let mx = p1.max(p2).max(p3).max(p4);
        Self::new(mn.next_down(), mx.next_up())
    }
    /// Self-certified exp(x) for scalar x using ONLY IEEE-754 (+, -, *, /) + proven Taylor remainder.
    fn exp_scalar(x: f64) -> Self {
        assert!(x.is_finite(), "Non-finite exp input");
        if x < -740.0 {
            // 0 < exp(x) < exp(-740) < 1e-300 (strictly valid for all x < -740!)
            return Self::new(0.0, 1e-300);
        }
        assert!(x <= 700.0, "exp overflow guard");
        // Halve x by exact powers of 2 until |r| <= 0.25
        let mut r = x;
        let mut m = 0u32;
        while r.abs() > 0.25 {
            r *= 0.5;
            m += 1;
        }
        // Degree-14 Taylor: sum_{k=0}^{14} r^k / k! with proven remainder |R_15| <= e^{0.25}*(0.25)^15 / 15! < 1e-20
        let rv = Self::exact(r);
        let mut sum = Self::exact(1.0);
        let mut term = Self::exact(1.0);
        for k in 1..=14u32 {
            term = term.mul(rv).div(Self::exact(k as f64));
            sum = sum.add(term);
        }
        let rem = Self::new(-1e-20, 1e-20);
        let mut res = sum.add(rem);
        if res.lo < 0.0 {
            res = Self::new(0.0, res.hi);
        }
        for _ in 0..m {
            res = res.mul(res);
        }
        res
    }
    #[inline]
    fn exp(self) -> Self {
        let a = Self::exp_scalar(self.lo);
        let b = Self::exp_scalar(self.hi);
        Self::new(a.lo.max(0.0), b.hi)
    }
    /// Self-certified ln(y) for scalar y > 0 using ONLY IEEE-754 (+, -, *, /) + atanh series + certified ln(2).
    fn ln_scalar(y: f64, ln2: Self) -> Self {
        assert!(y.is_finite() && y > 0.0, "Invalid ln input: {}", y);
        // Scale y by exact powers of 2 into [0.75, 1.5]
        let mut m = y;
        let mut k = 0i32;
        while m > 1.5 {
            m *= 0.5;
            k += 1;
        }
        while m < 0.75 {
            m *= 2.0;
            k -= 1;
        }
        // z = (m - 1)/(m + 1) satisfies |z| <= 1/5 = 0.2.
        // ln(m) = 2 * sum_{n=0}^{14} z^{2n+1}/(2n+1) + R, |R| <= 2*(0.2)^31 / (31*(1-0.04)) < 1e-22.
        let one = Self::exact(1.0);
        let mv = Self::exact(m);
        let z = mv.sub(one).div(mv.add(one));
        let z2 = z.mul(z);
        let mut zp = z;
        let mut s = Self::exact(0.0);
        for n in 0..=14u32 {
            s = s.add(zp.div(Self::exact((2 * n + 1) as f64)));
            zp = zp.mul(z2);
        }
        let ln_m = Self::exact(2.0).mul(s).add(Self::new(-1e-21, 1e-21));
        ln_m.add(Self::exact(k as f64).mul(ln2))
    }
    #[inline]
    fn ln(self, ln2: Self) -> Self {
        let a = Self::ln_scalar(self.lo, ln2);
        let b = Self::ln_scalar(self.hi, ln2);
        Self::new(a.lo, b.hi)
    }
}

/// Self-certify an interval enclosure for ln(2) directly from our proven `Iv::exp`!
fn certified_ln2() -> Iv {
    let lo = 0.6931471805599f64;
    let hi = 0.6931471805600f64;
    assert!(Iv::exp_scalar(lo).hi < 2.0, "ln2 lower bound failed self-certification: {:?}", Iv::exp_scalar(lo));
    assert!(Iv::exp_scalar(hi).lo > 2.0, "ln2 upper bound failed self-certification: {:?}", Iv::exp_scalar(hi));
    Iv::new(lo, hi)
}

/// Parse a JSON number/string strictly from its exact raw decimal lexeme (requires serde_json
/// `arbitrary_precision` feature for raw JSON number tokens), returning reduced `(num, den, Iv)`
/// with checked i128 arithmetic (zero wrapping/overflow and zero f64 text parsing).
fn parse_json_decimal_exact(v: &serde_json::Value) -> (i128, i128, Iv) {
    let s = match v {
        serde_json::Value::Number(n) => n.to_string(),
        serde_json::Value::String(st) => st.clone(),
        _ => panic!("Expected JSON number/string, got {:?}", v),
    };
    let s = s.trim();
    let (mant_s, exp10): (&str, i32) = match s.find(['e', 'E']) {
        Some(pos) => (&s[..pos], s[pos + 1..].parse().expect("bad exponent")),
        None => (s, 0),
    };
    assert!((-18..=18).contains(&exp10), "Exponent out of [-18, 18]: {}", s);
    let (neg, body) = if let Some(rest) = mant_s.strip_prefix('-') {
        (true, rest)
    } else if let Some(rest) = mant_s.strip_prefix('+') {
        (false, rest)
    } else {
        (false, mant_s)
    };
    let (int_s, frac_s) = match body.split_once('.') {
        Some((a, b)) => (a, b),
        None => (body, ""),
    };
    assert!(
        !int_s.is_empty() || !frac_s.is_empty(),
        "Empty decimal mantissa: {}",
        s
    );
    assert!(
        int_s.bytes().all(|b| b.is_ascii_digit()) && frac_s.bytes().all(|b| b.is_ascii_digit()),
        "Non-digit characters in mantissa: {}",
        s
    );
    assert!(frac_s.len() <= 20 && int_s.len() + frac_s.len() <= 30, "Too many decimal digits: {}", s);
    let mut digits = String::with_capacity(int_s.len() + frac_s.len());
    digits.push_str(int_s);
    digits.push_str(frac_s);
    let mut num: i128 = digits.parse().expect("bad mantissa");
    if neg {
        num = num.checked_neg().expect("num neg overflow");
    }
    let shift = exp10.checked_sub(frac_s.len() as i32).expect("shift overflow");
    let mut den: i128 = 1;
    if shift >= 0 {
        for _ in 0..shift {
            num = num.checked_mul(10).expect("num overflow");
        }
    } else {
        let neg_shift = shift.checked_neg().expect("neg_shift overflow");
        for _ in 0..neg_shift {
            den = den.checked_mul(10).expect("den overflow");
        }
    }
    let mut a = num.checked_abs().expect("abs overflow");
    let mut b = den;
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    let g = a.max(1);
    let rn = num / g;
    let rd = den / g;
    let rn_abs = rn.checked_abs().expect("rn abs overflow");
    let iv_val = if rn_abs < (1i128 << 52) && rd < (1i128 << 52) {
        Iv::from_ratio_i128(rn, rd)
    } else {
        let nf = rn as f64;
        let df = rd as f64;
        assert!(nf.is_finite() && df.is_finite() && df > 0.0, "i128 to f64 overflow");
        Iv::new(nf.next_down(), nf.next_up()).div(Iv::new(df.next_down(), df.next_up()))
    };
    (rn, rd, iv_val)
}

fn parse_dyadic_box_coord(v: &serde_json::Value) -> (i128, Iv) {
    // Parse exact raw JSON decimal into dyadic integer k = val * 2^30 (checked!) AND bit-exact Iv!
    let (rn, rd, _) = parse_json_decimal_exact(v);
    let hi_bound = 100i128.checked_mul(rd).expect("box bound overflow");
    assert!(rn >= 0 && rn <= hi_bound, "Box coordinate out of [0, 100]: {:?}", v);
    let scaled_num = rn.checked_mul(1i128 << 30).expect("dyadic scale overflow");
    assert!(scaled_num % rd == 0, "Box coordinate is not exact 2^-30 dyadic: {:?}", v);
    let k = scaled_num / rd;
    let scale = (1u64 << 30) as f64;
    let kf = k as f64;
    assert!((kf as i128) == k, "Dyadic integer exceeds exact f64 range: {}", k);
    let f = kf / scale;
    assert!(f.is_finite() && (f * scale) as i128 == k, "Dyadic exact f64 round-trip failed: {:?}", v);
    (k, Iv::exact(f))
}

#[derive(Deserialize)]
struct CertRaw {
    ls: Vec<serde_json::Value>,
    target: serde_json::Value,
    tree: serde_json::Value,
}

struct LeafTask {
    idx: usize,
    b_iv: [Iv; 6],
    a_iv: Vec<Iv>,
    lam_iv: Vec<Iv>,
    eta0_iv: Iv,
    y_iv: Vec<Iv>,
    ub_est: f64,
}

fn halfspaces_iv(ls: [Iv; 3], b: [Iv; 6]) -> ([[Iv; 3]; 14], [Iv; 14]) {
    let [l1, l2, l3] = ls;
    let [g1a, g1b, g2a, g2b, g3a, g3b] = b;
    let two = Iv::exact(2.0);
    let one = Iv::exact(1.0);
    let zero = Iv::exact(0.0);
    let neg1 = Iv::exact(-1.0);

    let g1m = g1a.add(g1b).div(two);
    let g2m = g2a.add(g2b).div(two);
    let g3m = g3a.add(g3b).div(two);

    let d21 = l2.sub(l1);
    let d32 = l3.sub(l2);
    let d31 = l3.sub(l1);
    let a_sec = l1.mul(d32).div(l2.mul(d31));
    let b_sec = l3.mul(d21).div(l2.mul(d31));
    let th13 = d21.div(d31);
    let om_th = one.sub(th13);

    let tan_c = |g0: Iv, dl: Iv| -> (Iv, Iv) {
        let den = one.add(dl.mul(g0));
        let y0 = g0.div(den);
        let m0 = one.div(den.mul(den));
        (m0, y0.sub(m0.mul(g0)))
    };
    let (m12, r12) = tan_c(g1m, d21);
    let (m23, r23) = tan_c(g2m, d32);
    let (m13, r13) = tan_c(g1m, d31);

    // Fixed strictly positive tangent point (p_pt, q_pt) > 0: valid for ANY positive scalars!
    let p_pt = Iv::exact((0.5 * (g3m.lo + g3m.hi)).max(1e-6));
    let q_pt = Iv::exact((0.5 * (g1m.lo + g1m.hi)).max(1e-6));
    assert!(p_pt.lo > 0.0 && q_pt.lo > 0.0);
    let hd = om_th.mul(p_pt).add(th13.mul(q_pt));
    let hd2 = hd.mul(hd);
    let h1 = om_th.mul(p_pt).mul(p_pt).div(hd2);
    let h3 = th13.mul(q_pt).mul(q_pt).div(hd2);

    let d_mat = [
        [one, zero, zero], [neg1, zero, zero],
        [zero, one, zero], [zero, neg1, zero],
        [zero, zero, one], [zero, zero, neg1],
        [l1.div(l2), neg1, zero],
        [zero, l2.div(l3), neg1],
        [a_sec, neg1, b_sec],
        [om_th.neg(), one, th13.neg()],
        [m12.neg(), one, zero],
        [zero, m23.neg(), one],
        [m13.neg(), zero, one],
        [h1.neg(), one, h3.neg()],
    ];
    let d_vec = [
        g1b, g1a.neg(), g2b, g2a.neg(), g3b, g3a.neg(),
        zero, zero, zero, zero,
        r12, r23, r13, zero,
    ];
    (d_mat, d_vec)
}

fn l_upper_midpoint(lam: Iv, ln2: Iv) -> Iv {
    let s = (1.0 / lam.hi).min(1.0);
    let mut knots = Vec::with_capacity(1400);
    knots.push(0.0f64);
    for i in 1..=300 {
        knots.push(2.0 * (i as f64) * s / 300.0);
    }
    let t0 = *knots.last().unwrap();
    let tend = (800.0 / lam.lo).max(800.0);
    for i in 1..=1000 {
        let v = t0 * (tend / t0).powf((i as f64) / 1000.0);
        if v > *knots.last().unwrap() {
            knots.push(v);
        }
    }
    let one = Iv::exact(1.0);
    let two = Iv::exact(2.0);
    let neg_lam = lam.neg();
    let mut j_lo = Iv::exact(0.0);
    for w in knots.windows(2) {
        let a = Iv::exact(w[0]);
        let b = Iv::exact(w[1]);
        let dt = b.sub(a);
        let mid = a.add(b).div(two);
        let denom = one.add(mid);
        let term = dt.mul(neg_lam.mul(mid).exp()).div(denom.mul(denom));
        j_lo = j_lo.add(term);
    }
    assert!(j_lo.lo > 0.0, "Non-positive J_lo");
    lam.sub(j_lo.ln(ln2))
}

/// Strictly interval-endpoint-guarded Ubar upper bound (zero raw-float branch comparisons!).
fn ubar_hi(ls: [Iv; 3], g_hi: [Iv; 3], t: Iv) -> Iv {
    let one = Iv::exact(1.0);
    let mut best = one.div(t).hi;
    for i in 0..3 {
        // Branch t <= l_i valid iff t.hi <= l_i.lo
        if t.hi <= ls[i].lo {
            let v = g_hi[i].mul(ls[i]).div(t).hi;
            if v < best { best = v; }
        }
        // Branch t >= l_i valid iff t.lo >= l_i.hi
        if t.lo >= ls[i].hi {
            let den = one.div(g_hi[i]).sub(ls[i]).add(t);
            if den.lo > 0.0 {
                let v = one.div(den).hi;
                if v < best { best = v; }
            }
        }
        // Crossing knot: if t overlaps ls[i], since U_1 is nonincreasing and U_1(l_i) <= g_hi[i],
        // for any s in [t_lo, t_hi] with s >= l_i we have U_1(s) <= g_hi[i], and for s <= l_i
        // we have U_1(s) <= g_hi[i]*l_i/s <= g_hi[i]*l_i/t_lo!
        if t.lo <= ls[i].hi && t.hi >= ls[i].lo {
            let v = g_hi[i].mul(ls[i]).div(t).hi.max(g_hi[i].hi);
            if v < best { best = v; }
        }
    }
    for i in 0..2 {
        if t.lo >= ls[i].hi && t.hi <= ls[i + 1].lo {
            let th = t.sub(ls[i]).div(ls[i + 1].sub(ls[i]));
            let om_th = one.sub(th);
            if th.lo >= 0.0 && om_th.lo >= 0.0 {
                let den = om_th.div(g_hi[i]).add(th.div(g_hi[i + 1]));
                if den.lo > 0.0 {
                    let v = one.div(den).hi;
                    if v < best { best = v; }
                }
            }
        }
    }
    Iv::exact(best)
}

fn h_upper(u: Iv) -> Iv {
    let uh = Iv::exact(u.hi);
    if uh.hi <= 0.0 { return Iv::exact(0.0); }
    if uh.hi < 1e-4 { return uh.div(Iv::exact(2.0)); }
    let one = Iv::exact(1.0);
    one.sub(one.sub(uh.neg().exp()).div(uh))
}

fn build_t_grid(n_lo: usize, n_mid: usize, n_hi: usize, t0: f64, t_end: f64) -> Vec<f64> {
    let a = 1e-4f64;
    let b = 50.0f64;
    let mut pts = Vec::with_capacity(n_lo + n_mid + n_hi + 16);
    for i in 0..=n_lo { pts.push(t0 * (a / t0).powf(i as f64 / n_lo as f64)); }
    for i in 0..=n_mid { pts.push(a * (b / a).powf(i as f64 / n_mid as f64)); }
    for i in 0..=n_hi { pts.push(b * (t_end / b).powf(i as f64 / n_hi as f64)); }
    // Bracket the three exact rational scales 3/50, 7/20, 9/5 with exact floats
    for &x in &[0.06f64, 0.35f64, 1.80f64] {
        pts.push(x.next_down());
        pts.push(x.next_up());
    }
    pts.sort_by(|x, y| x.partial_cmp(y).unwrap());
    pts.dedup_by(|a, b| (*a - *b).abs() <= 1e-15 * a.abs().max(1.0));
    assert!(pts[0] > 0.0 && pts.windows(2).all(|w| w[0] < w[1]));
    pts
}

fn main() {
    let t0 = Instant::now();
    let ln2 = certified_ln2();

    let args: Vec<String> = std::env::args().collect();
    let cert_path = args.get(1).map(|s| s.as_str()).unwrap_or("../../../certificates/tree_cert_3m_2480_tight.json");
    let expected_target_str = args.get(2).map(|s| s.as_str()).unwrap_or("2.48");

    let txt = fs::read_to_string(cert_path).expect("read cert");
    let cert: CertRaw = serde_json::from_str(&txt).expect("parse json");

    // Pin exact theorem scales ls == (3/50, 7/20, 9/5) via exact rational parsing!
    assert!(cert.ls.len() == 3, "ls must have length 3");
    let (n1, d1, l1_iv) = parse_json_decimal_exact(&cert.ls[0]);
    let (n2, d2, l2_iv) = parse_json_decimal_exact(&cert.ls[1]);
    let (n3, d3, l3_iv) = parse_json_decimal_exact(&cert.ls[2]);
    assert!(
        (n1, d1) == (3, 50) && (n2, d2) == (7, 20) && (n3, d3) == (9, 5),
        "ls must equal exact rationals (3/50, 7/20, 9/5), got ({}/{}, {}/{}, {}/{})",
        n1, d1, n2, d2, n3, d3
    );
    let ls_iv = [l1_iv, l2_iv, l3_iv];

    // Pin target <= expected_target <= exact theorem constant 62/25 in checked i128 rational arithmetic!
    let (tn, td, _) = parse_json_decimal_exact(&cert.target);
    let (en, ed, target_iv) = parse_json_decimal_exact(&serde_json::Value::String(expected_target_str.to_string()));
    assert!(
        en > 0 && en.checked_mul(25).unwrap() <= 62i128.checked_mul(ed).unwrap(),
        "Expected target {} exceeds theorem constant 62/25",
        expected_target_str
    );
    assert!(
        tn > 0 && tn.checked_mul(ed).unwrap() == en.checked_mul(td).unwrap(),
        "Certificate target {}/{} != expected target {} (refusing silent target mismatch)",
        tn, td, expected_target_str
    );

    let one = Iv::exact(1.0);
    let d21 = ls_iv[1].sub(ls_iv[0]);
    let d32 = ls_iv[2].sub(ls_iv[1]);
    let d31 = ls_iv[2].sub(ls_iv[0]);
    let a_sec = ls_iv[0].mul(d32).div(ls_iv[1].mul(d31));
    let b_sec = ls_iv[2].mul(d21).div(ls_iv[1].mul(d31));
    let th13 = d21.div(d31);
    let om_th = one.sub(th13);

    // Verify root covers [0, 1/l_i]
    let parse_box = |nd: &serde_json::Value| -> ([i128; 6], [Iv; 6]) {
        let arr = nd["box"].as_array().expect("box must be array");
        assert!(arr.len() == 6);
        let mut ks = [0i128; 6];
        let mut ivs = [Iv::exact(0.0); 6];
        for i in 0..6 {
            let (k, ivv) = parse_dyadic_box_coord(&arr[i]);
            ks[i] = k; ivs[i] = ivv;
        }
        for j in 0..3 { assert!(ks[2 * j] >= 0 && ks[2 * j] < ks[2 * j + 1], "Degenerate box"); }
        (ks, ivs)
    };

    let (_, rbox_iv) = parse_box(&cert.tree);
    for i in 0..3 {
        assert!(rbox_iv[2 * i].hi <= 0.0 && rbox_iv[2 * i + 1].lo >= one.div(ls_iv[i]).hi,
                "Root box fails to cover [0, 1/l_{}]", i + 1);
    }

    let mut leaves: Vec<LeafTask> = Vec::new();
    let mut n_disjoint = 0usize;
    let mut stack: Vec<&serde_json::Value> = vec![&cert.tree];

    while let Some(nd) = stack.pop() {
        let (bk, bi) = parse_box(nd);
        match nd["type"].as_str().expect("missing type") {
            "split" => {
                let ax = nd["axis"].as_u64().expect("axis") as usize;
                assert!(ax < 3);
                let ch = nd["children"].as_array().expect("children");
                assert!(ch.len() == 2);
                let (c1, _) = parse_box(&ch[0]);
                let (c2, _) = parse_box(&ch[1]);
                for j in 0..3 {
                    if j == ax {
                        assert!(c1[2 * j] == bk[2 * j] && c1[2 * j + 1] == c2[2 * j] && c2[2 * j + 1] == bk[2 * j + 1]);
                    } else {
                        assert!(c1[2 * j] == bk[2 * j] && c1[2 * j + 1] == bk[2 * j + 1]);
                        assert!(c2[2 * j] == bk[2 * j] && c2[2 * j + 1] == bk[2 * j + 1]);
                    }
                }
                stack.push(&ch[1]);
                stack.push(&ch[0]);
            }
            "disjoint" => {
                let [g1a, g1b, g2a, g2b, g3a, g3b] = bi;
                // Exact checked i128 check for c6: ls is strictly pinned to (3/50, 7/20, 9/5) => A=1/7, B=6/7!
                // Disjoint from int(cl(L)) if 7*g2_hi <= g1_lo + 6*g3_lo (checked_mul/add, zero overflow!).
                let lhs_c6 = 7i128.checked_mul(bk[3]).expect("c6 overflow");
                let rhs_c6 = bk[0].checked_add(6i128.checked_mul(bk[4]).expect("c6 overflow")).expect("c6 overflow");
                let ok_closed =
                    lhs_c6 <= rhs_c6
                    || g2b.hi <= ls_iv[0].div(ls_iv[1]).mul(g1a).lo
                    || g3b.hi <= ls_iv[1].div(ls_iv[2]).mul(g2a).lo
                    || g2a.mul(one.add(d21.mul(g1b))).lo >= g1b.hi
                    || g3a.mul(one.add(d32.mul(g2b))).lo >= g2b.hi
                    || g3a.mul(one.add(d31.mul(g1b))).lo >= g1b.hi
                    || g2b.hi <= a_sec.mul(g1a).add(b_sec.mul(g3a)).lo
                    || (g1b.lo > 0.0 && g3b.lo > 0.0 && g2a.mul(om_th.mul(g3b).add(th13.mul(g1b))).lo >= g1b.mul(g3b).hi);
                let ok = if ok_closed {
                    true
                } else if let Some(arr) = nd.get("farkas_y").and_then(|v| v.as_array()) {
                    assert!(arr.len() == 14);
                    let (d_mat, d_vec) = halfspaces_iv(ls_iv, bi);
                    let fy_iv: Vec<Iv> = arr.iter().map(|v| {
                        let (yn, _, yiv) = parse_json_decimal_exact(v);
                        assert!(yn >= 0, "Negative Farkas ray");
                        yiv
                    }).collect();
                    let mut dty = [Iv::exact(0.0); 3];
                    for r in 0..14 {
                        for c in 0..3 { dty[c] = dty[c].add(d_mat[r][c].mul(fy_iv[r])); }
                    }
                    let mut lhs_min = Iv::exact(0.0);
                    for c in 0..3 {
                        let p1 = dty[c].mul(bi[2 * c]);
                        let p2 = dty[c].mul(bi[2 * c + 1]);
                        lhs_min = lhs_min.add(Iv::exact(p1.lo.min(p2.lo)));
                    }
                    let mut rhs_max = Iv::exact(0.0);
                    for r in 0..14 { rhs_max = rhs_max.add(d_vec[r].mul(fy_iv[r])); }
                    rhs_max.hi < lhs_min.lo
                } else {
                    false
                };
                assert!(ok, "Disjoint check failed on box {:?}", bk);
                n_disjoint += 1;
            }
            "leaf" => {
                let a_arr = nd["a"].as_array().expect("a must be array");
                let l_arr = nd["lam"].as_array().expect("lam must be array");
                let y_arr = nd["y"].as_array().expect("y must be array");
                assert!(!a_arr.is_empty() && a_arr.len() == l_arr.len() && y_arr.len() == 14);

                // EXACT rational check that sum(a_k) == 1 (checked i128 cross-multiplication!)
                let mut sum_n: i128 = 0;
                let mut sum_d: i128 = 1;
                let mut a_iv = Vec::with_capacity(a_arr.len());
                for av in a_arr {
                    let (an, ad, aiv) = parse_json_decimal_exact(av);
                    assert!(an >= 0, "Negative weight a_k");
                    let nn = sum_n.checked_mul(ad).unwrap().checked_add(an.checked_mul(sum_d).unwrap()).unwrap();
                    let nd_den = sum_d.checked_mul(ad).unwrap();
                    let (mut x, mut y) = (nn.abs(), nd_den);
                    while y != 0 { let t = x % y; x = y; y = t; }
                    sum_n = nn / x.max(1);
                    sum_d = nd_den / x.max(1);
                    a_iv.push(aiv);
                }
                assert!(sum_n == sum_d, "Weights a_k do not sum EXACTLY to 1: {}/{}", sum_n, sum_d);

                let mut lam_iv = Vec::with_capacity(l_arr.len());
                for lv in l_arr {
                    let (ln_num, _, liv) = parse_json_decimal_exact(lv);
                    assert!(ln_num > 0, "Non-positive lambda");
                    lam_iv.push(liv);
                }
                let (_, _, eta0_iv) = parse_json_decimal_exact(&nd["eta0"]);
                let mut y_iv = Vec::with_capacity(14);
                for yv in y_arr {
                    let (yn, _, yiv) = parse_json_decimal_exact(yv);
                    assert!(yn >= 0, "Negative Farkas multiplier y");
                    y_iv.push(yiv);
                }
                leaves.push(LeafTask {
                    idx: leaves.len() + 1,
                    b_iv: bi,
                    a_iv,
                    lam_iv,
                    eta0_iv,
                    y_iv,
                    ub_est: nd.get("ub_est").and_then(|v| v.as_f64()).unwrap_or(0.0),
                });
            }
            other => panic!("Unknown node type: {}", other),
        }
    }
    assert!(!leaves.is_empty(), "Vacuous certificate with 0 leaves");

    let t_pts = build_t_grid(150, 3500, 150, 1e-7, 15000.0);
    let t_ivs: Vec<Iv> = t_pts.iter().map(|&x| Iv::exact(x)).collect();
    let hdt_ivs: Vec<Iv> = t_ivs.windows(2).map(|w| w[1].sub(w[0]).div(Iv::exact(2.0))).collect();
    let n_t = hdt_ivs.len();

    let mut c_pts = vec![0.0f64];
    for i in 0..=400 {
        c_pts.push(1e-5 * (6000.0 / 1e-5f64).powf(i as f64 / 400.0));
    }
    let c_ivs: Vec<Iv> = c_pts.iter().map(|&x| Iv::exact(x)).collect();

    println!("==========================================================================");
    println!("GATE-4-HARDENED RUST SELF-CERTIFIED INTERVAL VERIFIER (ZERO libm exp/ln TRUST)");
    println!("  ls=(3/50, 7/20, 9/5), TARGET<={} (n_t={}, n_c={}), leaves={}, disjoint={}",
             expected_target_str, n_t, c_ivs.len() - 1, leaves.len(), n_disjoint);
    println!("==========================================================================");

    let results: Vec<(usize, bool, f64, f64)> = leaves
        .par_iter()
        .map(|leaf| {
            let bi = leaf.b_iv;
            let (d_mat, d_vec) = halfspaces_iv(ls_iv, bi);
            let eta0_iv = leaf.eta0_iv;

            let mut eta_iv = [Iv::exact(0.0); 3];
            let mut s_max = Iv::exact(0.0);
            for r in 0..14 {
                s_max = s_max.add(d_vec[r].mul(leaf.y_iv[r]));
                for c in 0..3 { eta_iv[c] = eta_iv[c].add(d_mat[r][c].mul(leaf.y_iv[r])); }
            }

            let mut gh = [
                Iv::exact(bi[1].hi.min(one.div(ls_iv[0]).hi)),
                Iv::exact(bi[3].hi.min(one.div(ls_iv[1]).hi)),
                Iv::exact(bi[5].hi.min(one.div(ls_iv[2]).hi)),
            ];
            for _ in 0..3 {
                let b12 = gh[0].div(one.add(d21.mul(gh[0]))).hi;
                gh[1] = Iv::exact(gh[1].hi.min(b12));
                let b23 = gh[1].div(one.add(d32.mul(gh[1]))).hi;
                let b13 = gh[0].div(one.add(d31.mul(gh[0]))).hi;
                gh[2] = Iv::exact(gh[2].hi.min(b23).min(b13));
                let bh = one.div(om_th.div(gh[0]).add(th13.div(gh[2]))).hi;
                gh[1] = Iv::exact(gh[1].hi.min(bh));
            }
            let b12 = gh[0].div(one.add(d21.mul(gh[0]))).hi;
            gh[1] = Iv::exact(gh[1].hi.min(b12));
            let b23 = gh[1].div(one.add(d32.mul(gh[1]))).hi;
            gh[2] = Iv::exact(gh[2].hi.min(b23));
            assert!(gh[0].hi >= gh[1].hi && gh[1].hi >= gh[2].hi && gh[2].lo > 0.0);

            let active: Vec<(Iv, Iv)> = leaf.a_iv.iter().copied().zip(leaf.lam_iv.iter().copied()).filter(|(a, _)| a.hi > 0.0).collect();
            assert!(!active.is_empty());
            let mut l_term = Iv::exact(0.0);
            let mut lbar = Iv::exact(0.0);
            for &(av, lv) in &active {
                l_term = l_term.add(av.div(lv).mul(l_upper_midpoint(lv, ln2)));
                lbar = lbar.add(av.mul(lv));
            }

            let pou: Vec<Iv> = (0..n_t).map(|j| h_upper(ubar_hi(ls_iv, gh, t_ivs[j]))).collect();
            let ets: Vec<Vec<Iv>> = active
                .iter()
                .map(|&(_, lv)| {
                    let nlv = lv.neg();
                    (0..n_t).map(|j| nlv.mul(t_ivs[j + 1]).exp()).collect()
                })
                .collect();

            let head = t_ivs[0].mul(lbar);
            let tail = one.div(Iv::exact(2.0).mul(*t_ivs.last().unwrap()));
            let base = one.add(l_term).add(eta0_iv).add(s_max);
            let allow = target_iv.sub(base).lo;

            let eval_c = |ca: Iv, cb: Iv| -> f64 {
                let cc: Vec<Iv> = active.iter().map(|&(av, lv)| av.mul(lv.neg().mul(cb).exp())).collect();
                let mut i_hi = head.add(tail);
                let mut inv_p = one.div(ca.add(t_ivs[0]));
                let ka = cc.len();
                for j in 0..n_t {
                    let inv_n = one.div(ca.add(t_ivs[j + 1]));
                    let mut wv = cc[0].mul(ets[0][j]);
                    for ki in 1..ka { wv = wv.add(cc[ki].mul(ets[ki][j])); }
                    let df = pou[j].sub(wv);
                    if df.hi > 0.0 {
                        i_hi = i_hi.add(Iv::exact(df.hi).mul(hdt_ivs[j]).mul(inv_p.add(inv_n)));
                    }
                    inv_p = inv_n;
                }
                let mut aw = Iv::exact(0.0);
                for &(av, lv) in &active {
                    let z = lv.mul(cb);
                    if cb.hi == 0.0 {
                        aw = aw.add(av);
                    } else if z.hi < 1e-4 {
                        aw = aw.add(av.mul(one.sub(z.div(Iv::exact(2.0)))));
                    } else {
                        aw = aw.add(av.mul(one.sub(z.neg().exp()).div(z)));
                    }
                }
                let mut lin = eta0_iv;
                for i in 0..3 {
                    let ta = eta_iv[i].mul(one.div(ca.add(ls_iv[i])));
                    let tb = eta_iv[i].mul(one.div(cb.add(ls_iv[i])));
                    lin = lin.add(Iv::exact(ta.lo.min(tb.lo)));
                }
                let res = i_hi.sub(aw).sub(lin).hi;
                assert!(res.is_finite());
                res
            };

            let mut d_hi = -100.0f64;
            let mut q: Vec<(Iv, Iv, u8)> = (0..(c_ivs.len() - 1)).map(|i| (c_ivs[i], c_ivs[i + 1], 0)).collect();
            while let Some((ca, cb, dep)) = q.pop() {
                let vb = eval_c(ca, cb);
                if vb > allow && dep < 4 {
                    let mid = Iv::exact(0.5 * (ca.lo + cb.hi));
                    q.push((ca, mid, dep + 1));
                    q.push((mid, cb, dep + 1));
                } else if vb > d_hi {
                    d_hi = vb;
                }
            }

            let cm = *c_ivs.last().unwrap();
            let two_cm = Iv::exact(2.0).mul(cm);
            let itc = one.add(one.div(two_cm)).ln(ln2).add(one.add(two_cm).ln(ln2).div(two_cm));
            let mut lt = eta0_iv;
            for i in 0..3 {
                let ti = eta_iv[i].mul(one.div(cm.add(ls_iv[i])));
                lt = lt.add(Iv::exact(ti.lo.min(0.0)));
            }
            let tv = itc.sub(lt).hi;
            assert!(tv.is_finite());
            if tv > d_hi { d_hi = tv; }

            let tot = base.add(Iv::exact(d_hi.max(0.0)));
            (leaf.idx, tot.hi <= target_iv.lo, tot.hi, leaf.ub_est)
        })
        .collect();

    let fmt_ceil_8 = |x: f64| -> String {
        let scaled_hi = Iv::exact(x).mul(Iv::exact(100_000_000.0)).hi;
        let n = scaled_hi.ceil() as u128;
        format!("{}.{:08}", n / 100_000_000, n % 100_000_000)
    };
    let mut failed = 0usize;
    let mut max_ub = 0.0f64;
    let mut worst_id = 0usize;
    for &(idx, ok, ub, est) in &results {
        if ub > max_ub { max_ub = ub; worst_id = idx; }
        if !ok {
            failed += 1;
            if failed <= 15 {
                println!("  [RUST FAIL] leaf #{} est={:.6} ub<={} > {}", idx, est, fmt_ceil_8(ub), expected_target_str);
            }
        }
    }
    let cmp_sym = if failed == 0 { "<=" } else { ">" };
    println!("==========================================================================");
    println!("RUST SELF-CERTIFIED VERIFIER {} in {:.2}s: ls=(3/50,7/20,9/5), leaves={}, disjoint={}, failed={}, max_ub<={} {} {} (worst leaf #{})",
             if failed == 0 { "PASS" } else { "FAIL" },
             t0.elapsed().as_secs_f64(), results.len(), n_disjoint, failed, fmt_ceil_8(max_ub), cmp_sym, expected_target_str, worst_id);
    println!("==========================================================================");
    if failed > 0 { std::process::exit(1); }
}
