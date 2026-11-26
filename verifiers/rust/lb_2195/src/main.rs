//! Standalone Verifier 1 (Rust, IEEE-754 outward-rounded interval arithmetic + exact i128 rationals)
//! for cert_lb_2195.json: REV(X) > (439/200) * max(SREV(X), BREV(X)) = 2.195 * max(SREV(X), BREV(X)).
//!
//! Security & soundness invariants:
//!   - Compiled with overflow-checks = true and serde_json arbitrary_precision (rustc 1.96.0 pinned).
//!   - Core interval exp arithmetic avoids libm::exp/libm::ln: custom power-of-two range-reduced degree-14
//!     Taylor exp on |r| <= 0.35 with explicit remainder bound |R_15| <= e^{0.35} * 0.35^15 / 15! < 1.6e-19 < 1e-18
//!     and startup-verified ln(2) enclosure (round() selects only an integer shift m verified by |r| <= 0.35;
//!     display helper fmt_up_sci uses log10/powi with parsed re-verification of outward rounding).
//!   - Basic +, -, *, / widened outward by 1 full ULP via next_down/next_up with finite/non-NaN traps.
//!   - Exact checked-i128 rational arithmetic pins ALL certificate fields (target, D, F, Na, P0, t,
//!     deg_Z, S_A, and all 8 group specs including k_max = k_min + 700), verifies strict point-mass
//!     positivity (including p_0 = 1 - sum > 0) alongside exact rational support checks,
//!     and verifies single-item SRev == r_g / Na at every support point.
//!   - Zero-subtraction schoolbook truncated interval polynomial multiplication (and exact binomial
//!     expansion for sparse high-offset groups such as A8) certifies (1) entry-fee revenue E_A,
//!     (2) BRev <= S_A at every tick k = 1..5013, and (3) infinite-tail Chernoff MGF bound for p >= 55.
//!   - All printed decimal lower/upper endpoints are strictly outward-rounded and verified.

use serde::Deserialize;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

// ---------------------------------------------------------------------------
// Exact checked i128 rational arithmetic
// ---------------------------------------------------------------------------
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Rat {
    num: i128,
    den: i128,
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

impl Rat {
    fn new(mut num: i128, mut den: i128) -> Self {
        if den == 0 {
            panic!("Zero denominator in Rat::new");
        }
        if den < 0 {
            num = num.checked_neg().expect("i128 neg overflow");
            den = den.checked_neg().expect("i128 neg overflow");
        }
        if num == 0 {
            return Rat { num: 0, den: 1 };
        }
        let g = gcd_u128(num.unsigned_abs(), den.unsigned_abs()) as i128;
        Rat {
            num: num / g,
            den: den / g,
        }
    }

    fn add(self, o: Self) -> Self {
        let n1 = self.num.checked_mul(o.den).expect("Rat add mul overflow");
        let n2 = o.num.checked_mul(self.den).expect("Rat add mul overflow");
        let n = n1.checked_add(n2).expect("Rat add overflow");
        let d = self.den.checked_mul(o.den).expect("Rat add den overflow");
        Rat::new(n, d)
    }

    fn sub(self, o: Self) -> Self {
        let neg = Rat {
            num: o.num.checked_neg().expect("Rat sub neg overflow"),
            den: o.den,
        };
        self.add(neg)
    }

    fn mul(self, o: Self) -> Self {
        let g1 = gcd_u128(self.num.unsigned_abs(), o.den.unsigned_abs()) as i128;
        let g2 = gcd_u128(o.num.unsigned_abs(), self.den.unsigned_abs()) as i128;
        let n = (self.num / g1)
            .checked_mul(o.num / g2)
            .expect("Rat mul num overflow");
        let d = (self.den / g2)
            .checked_mul(o.den / g1)
            .expect("Rat mul den overflow");
        Rat::new(n, d)
    }

    fn div(self, o: Self) -> Self {
        if o.num == 0 {
            panic!("Division by zero in Rat::div");
        }
        self.mul(Rat::new(o.den, o.num))
    }

    fn to_iv(self) -> Iv {
        Iv::from_i128(self.num).div(Iv::from_i128(self.den))
    }
}

// ---------------------------------------------------------------------------
// Outward-rounded IEEE-754 interval arithmetic (ZERO libm trust!)
// ---------------------------------------------------------------------------
#[derive(Clone, Copy, Debug)]
struct Iv {
    lo: f64,
    hi: f64,
}

#[inline]
fn next_down(x: f64) -> f64 {
    if !x.is_finite() {
        panic!("Non-finite float in next_down: {}", x);
    }
    if x == 0.0 {
        return -f64::from_bits(1);
    }
    let bits = x.to_bits();
    let res = if x > 0.0 {
        f64::from_bits(bits - 1)
    } else {
        f64::from_bits(bits + 1)
    };
    if !res.is_finite() {
        panic!("Overflow to non-finite in next_down");
    }
    res
}

#[inline]
fn next_up(x: f64) -> f64 {
    if !x.is_finite() {
        panic!("Non-finite float in next_up: {}", x);
    }
    if x == 0.0 {
        return f64::from_bits(1);
    }
    let bits = x.to_bits();
    let res = if x > 0.0 {
        f64::from_bits(bits + 1)
    } else {
        f64::from_bits(bits - 1)
    };
    if !res.is_finite() {
        panic!("Overflow to non-finite in next_up");
    }
    res
}

/// Strictly outward-rounded decimal formatting for finite non-negative f64 values:
/// fmt_down_12(x) produces a 12-decimal string whose exact decimal value is <= x;
/// fmt_up_12(x) produces a 12-decimal string whose exact decimal value is >= x.
fn fmt_down_12(x: f64) -> String {
    assert!(x.is_finite() && x >= 0.0 && x < 1e6, "fmt_down_12 range");
    let scale = 1_000_000_000_000_i128; // 10^12
    let mut scaled = (x * (scale as f64)).floor() as i128;
    loop {
        let s = format!("{}.{:012}", scaled / scale, scaled % scale);
        // Verify exact decimal string parses to <= x (with 1-ULP margin via next_up):
        let parsed: f64 = s.parse().expect("parse decimal");
        if next_up(parsed) <= x || (parsed == x && scaled == 0) {
            return s;
        }
        assert!(scaled > 0, "fmt_down_12 underflow");
        scaled -= 1;
    }
}

fn fmt_up_12(x: f64) -> String {
    assert!(x.is_finite() && x >= 0.0 && x < 1e6, "fmt_up_12 range");
    let scale = 1_000_000_000_000_i128; // 10^12
    let mut scaled = (x * (scale as f64)).ceil() as i128;
    loop {
        let s = format!("{}.{:012}", scaled / scale, scaled % scale);
        let parsed: f64 = s.parse().expect("parse decimal");
        if next_down(parsed) >= x {
            return s;
        }
        scaled += 1;
    }
}

/// Strictly upward-rounded scientific bound for positive finite widths.
fn fmt_up_sci(x: f64) -> String {
    assert!(x.is_finite() && x > 0.0, "fmt_up_sci range");
    let exp = x.log10().floor() as i32;
    let base = 10.0_f64.powi(exp);
    let mut m = ((x / base) * 100.0).ceil() as i64;
    loop {
        let s = format!("{:.2}e{:+}", (m as f64) / 100.0, exp);
        let parsed: f64 = s.parse().expect("parse sci");
        if next_down(parsed) >= x {
            return s;
        }
        m += 1;
    }
}

impl Iv {
    #[inline]
    fn new(lo: f64, hi: f64) -> Self {
        if !lo.is_finite() || !hi.is_finite() || lo > hi {
            panic!("Invalid interval [{}, {}]", lo, hi);
        }
        Iv { lo, hi }
    }

    #[inline]
    fn zero() -> Self {
        Iv { lo: 0.0, hi: 0.0 }
    }

    #[inline]
    fn one() -> Self {
        Iv { lo: 1.0, hi: 1.0 }
    }

    #[inline]
    fn is_zero(self) -> bool {
        self.lo == 0.0 && self.hi == 0.0
    }

    fn from_i128(n: i128) -> Self {
        let f = n as f64;
        if !f.is_finite() {
            panic!("i128 too large for f64: {}", n);
        }
        if n.unsigned_abs() <= (1u128 << 53) {
            Iv::new(f, f)
        } else {
            Iv::new(next_down(f), next_up(f))
        }
    }

    #[inline]
    fn add(self, o: Self) -> Self {
        if self.is_zero() {
            return o;
        }
        if o.is_zero() {
            return self;
        }
        Iv::new(next_down(self.lo + o.lo), next_up(self.hi + o.hi))
    }

    #[inline]
    fn sub(self, o: Self) -> Self {
        if o.is_zero() {
            return self;
        }
        Iv::new(next_down(self.lo - o.hi), next_up(self.hi - o.lo))
    }

    #[inline]
    fn neg(self) -> Self {
        Iv::new(-self.hi, -self.lo)
    }

    #[inline]
    fn mul(self, o: Self) -> Self {
        if self.is_zero() || o.is_zero() {
            return Iv::zero();
        }
        let p1 = self.lo * o.lo;
        let p2 = self.lo * o.hi;
        let p3 = self.hi * o.lo;
        let p4 = self.hi * o.hi;
        let mn = p1.min(p2).min(p3).min(p4);
        let mx = p1.max(p2).max(p3).max(p4);
        Iv::new(next_down(mn), next_up(mx))
    }

    #[inline]
    fn div(self, o: Self) -> Self {
        if o.lo <= 0.0 && o.hi >= 0.0 {
            panic!("Interval division by interval containing zero: [{}, {}]", o.lo, o.hi);
        }
        let p1 = self.lo / o.lo;
        let p2 = self.lo / o.hi;
        let p3 = self.hi / o.lo;
        let p4 = self.hi / o.hi;
        let mn = p1.min(p2).min(p3).min(p4);
        let mx = p1.max(p2).max(p3).max(p4);
        Iv::new(next_down(mn), next_up(mx))
    }

    fn pow_u64(mut self, mut e: u64) -> Self {
        let mut res = Iv::one();
        while e > 0 {
            if (e & 1) == 1 {
                res = res.mul(self);
            }
            e >>= 1;
            if e > 0 {
                self = self.mul(self);
            }
        }
        res
    }
}

/// Self-certified zero-libm Taylor exp(r) on |r| <= 0.35:
///   sum_{k=0}^{14} r^k / k! +/- 1e-18.
/// Remainder bound: |R_15| <= e^{0.35} * 0.35^15 / 15! < 1.58e-19 < 1e-18.
fn exp_small_point(r: f64) -> Iv {
    if r.abs() > 0.35 {
        panic!("exp_small_point out of range: {}", r);
    }
    let riv = Iv::new(r, r);
    let mut term = Iv::one();
    let mut sum = Iv::one();
    for k in 1..=14 {
        term = term.mul(riv).div(Iv::from_i128(k));
        sum = sum.add(term);
    }
    sum.add(Iv::new(-1e-18, 1e-18))
}

/// Startup-verified ln(2) enclosure via exp(lo/4)^4 < 2 < exp(hi/4)^4 (division by 4 is binary-exact).
fn certified_ln2() -> Iv {
    let lo = 0.6931471805599_f64;
    let hi = 0.6931471805600_f64;
    let e_lo = exp_small_point(lo / 4.0).pow_u64(4);
    let e_hi = exp_small_point(hi / 4.0).pow_u64(4);
    if !(e_lo.hi < 2.0 && e_hi.lo > 2.0) {
        panic!("Startup ln(2) certification failed!");
    }
    Iv::new(lo, hi)
}

/// Zero-libm range-reduced exp(x) for point x: write x = m * ln(2) + r with |r| <= 0.35,
/// compute exp(r) * 2^m.
fn exp_point(x: f64, ln2: Iv) -> Iv {
    let m = (x / 0.6931471805599453_f64).round() as i64;
    let r = Iv::new(x, x).sub(Iv::from_i128(m as i128).mul(ln2));
    let er_lo = exp_small_point(r.lo);
    let er_hi = exp_small_point(r.hi);
    let mut res = Iv::new(er_lo.lo, er_hi.hi);
    if m >= 0 {
        let scale = Iv::from_i128(2).pow_u64(m as u64);
        res = res.mul(scale);
    } else {
        let scale = Iv::one().div(Iv::from_i128(2).pow_u64((-m) as u64));
        res = res.mul(scale);
    }
    res
}

fn exp_iv(x: Iv, ln2: Iv) -> Iv {
    let lo_e = exp_point(x.lo, ln2);
    let hi_e = exp_point(x.hi, ln2);
    Iv::new(lo_e.lo, hi_e.hi)
}

// ---------------------------------------------------------------------------
// Zero-subtraction schoolbook truncated interval polynomial arithmetic
// (All PGF coefficients are nonnegative, avoiding catastrophic cancellation.)
// ---------------------------------------------------------------------------
fn poly_mul_trunc(a: &[Iv], b: &[Iv], deg: usize) -> Vec<Iv> {
    let la = a.len().min(deg + 1);
    let lb = b.len().min(deg + 1);
    if la == 0 || lb == 0 {
        return Vec::new();
    }
    let out_len = (la + lb - 1).min(deg + 1);
    let mut out = vec![Iv::zero(); out_len];
    for i in 0..la {
        let ai = a[i];
        if ai.is_zero() {
            continue;
        }
        let lim = lb.min(out_len - i);
        for j in 0..lim {
            let bj = b[j];
            if !bj.is_zero() {
                out[i + j] = out[i + j].add(ai.mul(bj));
            }
        }
    }
    out
}

fn comb_i128(n: u64, k: u64) -> i128 {
    let mut res: i128 = 1;
    for i in 1..=k {
        res = res
            .checked_mul((n - k + i) as i128)
            .expect("comb mul overflow")
            / (i as i128);
    }
    res
}

fn poly_pow_trunc(base: &[Iv], exp: u64, deg: usize) -> Vec<Iv> {
    let mut k_first: Option<usize> = None;
    for i in 1..base.len().min(deg + 1) {
        if !base[i].is_zero() {
            k_first = Some(i);
            break;
        }
    }
    let kf = match k_first {
        None => {
            let mut r = vec![Iv::zero(); deg + 1];
            r[0] = base[0].pow_u64(exp);
            return r;
        }
        Some(k) => k,
    };
    let max_j = deg / kf;
    if max_j <= 6 {
        let p0 = base[0];
        let q = &base[kf..base.len().min(deg + 1)];
        let mut res = vec![Iv::zero(); deg + 1];
        let mut q_pow = vec![Iv::one()];
        for j in 0..=max_j {
            let shift = j * kf;
            let rem = deg - shift;
            let coeff = Iv::from_i128(comb_i128(exp, j as u64)).mul(p0.pow_u64(exp - j as u64));
            for idx in 0..q_pow.len().min(rem + 1) {
                res[shift + idx] = res[shift + idx].add(coeff.mul(q_pow[idx]));
            }
            if j < max_j {
                let next_rem = deg - (j + 1) * kf;
                q_pow = poly_mul_trunc(&q_pow, q, next_rem);
            }
        }
        return res;
    }

    let mut res = vec![Iv::one()];
    let mut cur = base[..base.len().min(deg + 1)].to_vec();
    let mut e = exp;
    while e > 0 {
        if (e & 1) == 1 {
            res = poly_mul_trunc(&res, &cur, deg);
        }
        e >>= 1;
        if e > 0 {
            cur = poly_mul_trunc(&cur, &cur, deg);
        }
    }
    if res.len() < deg + 1 {
        res.resize(deg + 1, Iv::zero());
    }
    res
}

// ---------------------------------------------------------------------------
// JSON certificate schema (exact integer tokens parsed directly)
// ---------------------------------------------------------------------------
#[derive(Deserialize)]
struct GroupSpec {
    name: String,
    r_num: i128,
    r_den: i128,
    k_min: usize,
    k_max: usize,
    p_tick: usize,
}

#[derive(Deserialize)]
struct CertSpec {
    target_num: i128,
    target_den: i128,
    grid_den: i128,
    entry_fee_ticks: usize,
    #[serde(rename = "Na")]
    na: u64,
    #[serde(rename = "chernoff_P0_ticks")]
    chernoff_p0_ticks: i128,
    chernoff_t_num: i128,
    chernoff_t_den: i128,
    groups: Vec<GroupSpec>,
}

const PINNED_GROUPS: [(&str, i128, i128, usize, usize, usize); 8] = [
    ("A1", 227, 2000, 7, 707, 7),
    ("A2", 207, 2000, 11, 711, 11),
    ("A3", 9, 250, 16, 716, 16),
    ("A4", 547, 2000, 46, 746, 46),
    ("A5", 179, 1000, 82, 782, 82),
    ("A6", 199, 1000, 118, 818, 118),
    ("A7", 817, 2000, 166, 866, 166),
    ("A8", 7119, 2000, 1545, 2245, 1545),
];

fn resolve_cert_path() -> PathBuf {
    if let Some(arg) = env::args().nth(1) {
        return PathBuf::from(arg);
    }
    let candidates = [
        Path::new("cert_lb_2195.json").to_path_buf(),
        Path::new("../cert_lb_2195.json").to_path_buf(),
        Path::new("../../cert_lb_2195.json").to_path_buf(),
    ];
    for c in &candidates {
        if c.exists() {
            return c.clone();
        }
    }
    if let Ok(exe) = env::current_exe() {
        let mut dir = exe.parent();
        for _ in 0..4 {
            if let Some(d) = dir {
                let p = d.join("cert_lb_2195.json");
                if p.exists() {
                    return p;
                }
                dir = d.parent();
            }
        }
    }
    panic!("Could not locate cert_lb_2195.json; pass explicit path as argv[1].");
}

fn main() {
    let t0 = Instant::now();
    let ln2 = certified_ln2();

    let cert_path = resolve_cert_path();
    let raw = fs::read_to_string(&cert_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", cert_path.display(), e));
    let cert: CertSpec = serde_json::from_str(&raw).expect("Failed to parse JSON");

    // Exact pinned theorem constants (both raw integer tokens and rational values pinned!)
    assert_eq!((cert.target_num, cert.target_den), (439, 200), "Raw target mismatch");
    let target = Rat::new(cert.target_num, cert.target_den);
    assert_eq!(target, Rat::new(439, 200), "Target mismatch");
    assert_eq!(cert.grid_den, 100, "Grid den mismatch");
    assert_eq!(cert.entry_fee_ticks, 700, "Entry fee ticks mismatch");
    assert_eq!(cert.na, 5000, "Na mismatch");
    assert_eq!(cert.chernoff_p0_ticks, 5500, "Chernoff P0 ticks mismatch");
    assert_eq!((cert.chernoff_t_num, cert.chernoff_t_den), (1, 10), "Raw Chernoff t mismatch");
    let t_ch_rat = Rat::new(cert.chernoff_t_num, cert.chernoff_t_den);
    assert_eq!(t_ch_rat, Rat::new(1, 10), "Chernoff t mismatch");
    assert_eq!(cert.groups.len(), PINNED_GROUPS.len(), "Group count mismatch");

    let d_rat = Rat::new(cert.grid_den, 1);
    let na_rat = Rat::new(i128::from(cert.na), 1);
    let f_rat = Rat::new(i128::try_from(cert.entry_fee_ticks).expect("F ticks"), cert.grid_den);
    let p0_rat = Rat::new(cert.chernoff_p0_ticks, cert.grid_den);
    assert_eq!(p0_rat, Rat::new(55, 1), "P0 mismatch");
    assert!(t_ch_rat.num > 0, "Chernoff t must be positive");
    let p0_t = p0_rat.mul(t_ch_rat);
    assert!(p0_t.num >= p0_t.den, "Chernoff monotonicity requires P0 >= 1/t");

    // 1. Exact rational PMFs & single-item SRev verification + full group pinning
    let mut s_a = Rat::new(0, 1);
    struct GroupData {
        p0: Rat,
        pmf: Vec<(usize, Rat)>,
        p_tick: usize,
    }
    let mut groups_data: Vec<GroupData> = Vec::new();

    for (idx, g) in cert.groups.iter().enumerate() {
        let (exp_name, exp_rn, exp_rd, exp_kmin, exp_kmax, exp_pt) = PINNED_GROUPS[idx];
        assert_eq!(g.name, exp_name, "Group name mismatch at index {}", idx);
        assert_eq!((g.r_num, g.r_den), (exp_rn, exp_rd), "Raw r_g mismatch in {}", g.name);
        let r_g = Rat::new(g.r_num, g.r_den);
        assert_eq!(r_g, Rat::new(exp_rn, exp_rd), "Group r_g mismatch in {}", g.name);
        assert_eq!(g.k_min, exp_kmin, "k_min mismatch in {}", g.name);
        assert_eq!(g.k_max, exp_kmax, "k_max mismatch in {}", g.name);
        assert_eq!(g.p_tick, exp_pt, "p_tick mismatch in {}", g.name);
        assert_eq!(g.k_max, g.k_min + cert.entry_fee_ticks, "Span mismatch in {}", g.name);
        assert!(r_g.num > 0 && g.k_min >= 1 && g.k_min <= g.k_max && g.p_tick == g.k_min);
        s_a = s_a.add(r_g);

        let mut pmf = Vec::with_capacity(g.k_max - g.k_min + 1);
        let mut sum_pos = Rat::new(0, 1);
        for k in g.k_min..=g.k_max {
            let k_i = i128::try_from(k).expect("k i128");
            let s_cur = d_rat.mul(r_g).div(na_rat.mul(Rat::new(k_i, 1)));
            let s_nxt = if k < g.k_max {
                d_rat.mul(r_g).div(na_rat.mul(Rat::new(k_i + 1, 1)))
            } else {
                Rat::new(0, 1)
            };
            let pr = s_cur.sub(s_nxt);
            assert!(pr.num > 0, "Non-positive PMF in {}", g.name);
            sum_pos = sum_pos.add(pr);
            pmf.push((k, pr));
        }
        let p0 = Rat::new(1, 1).sub(sum_pos);
        assert!(p0.num > 0, "Non-positive p0 in {}", g.name);

        let expected_rev = r_g.div(na_rat);
        let mut surv = Rat::new(0, 1);
        for &(k, pr) in pmf.iter().rev() {
            surv = surv.add(pr);
            let rev_k = Rat::new(i128::try_from(k).expect("k"), cert.grid_den).mul(surv);
            assert_eq!(rev_k, expected_rev, "Single-item SRev mismatch at k={} in {}", k, g.name);
        }
        let uncond_one = Rat::new(i128::try_from(g.p_tick).expect("pt"), cert.grid_den).mul(surv);
        assert_eq!(uncond_one, expected_rev, "Unconditional payment mismatch in {}", g.name);

        groups_data.push(GroupData {
            p0,
            pmf,
            p_tick: g.p_tick,
        });
    }
    assert_eq!(s_a, Rat::new(1949, 400), "Unexpected S_A");

    println!("============================================================================");
    println!("VERIFIER 1 (Rust zero-libm IEEE-754 + exact i128 Rat)");
    println!("  Input certificate: {} ({} bytes)", cert_path.display(), raw.len());
    println!("============================================================================");
    println!("  [PASS] All 8 groups & parameters pinned; exact i128 PMFs & single-item SRev verified (S_A = {}/{}).", s_a.num, s_a.den);

    // 2. Entry-fee revenue E_A (deg_U = 699)
    let t_u0 = Instant::now();
    let deg_u = cert.entry_fee_ticks - 1;
    let k_cnt = groups_data.len();
    let mut p_u: Vec<Vec<Iv>> = Vec::with_capacity(k_cnt);
    let mut q_u: Vec<Vec<Iv>> = Vec::with_capacity(k_cnt);
    for gd in &groups_data {
        let mut p = vec![Iv::zero(); deg_u + 1];
        let mut q = vec![Iv::zero(); deg_u + 1];
        p[0] = p[0].add(gd.p0.to_iv());
        let p_val_iv = Rat::new(i128::try_from(gd.p_tick).expect("pt"), cert.grid_den).to_iv();
        for &(k, pr) in &gd.pmf {
            let u = k - gd.p_tick;
            if u <= deg_u {
                let pr_iv = pr.to_iv();
                p[u] = p[u].add(pr_iv);
                q[u] = q[u].add(pr_iv.mul(p_val_iv));
            }
        }
        p_u.push(p);
        q_u.push(q);
    }

    let p_u_pow: Vec<Vec<Iv>> = p_u.iter().map(|p| poly_pow_trunc(p, cert.na, deg_u)).collect();
    let p_u_pow_m1: Vec<Vec<Iv>> = p_u.iter().map(|p| poly_pow_trunc(p, cert.na - 1, deg_u)).collect();

    let mut pref: Vec<Vec<Iv>> = vec![Vec::new(); k_cnt + 1];
    let mut suff: Vec<Vec<Iv>> = vec![Vec::new(); k_cnt + 1];
    pref[0] = vec![Iv::one()];
    for i in 0..k_cnt {
        pref[i + 1] = poly_mul_trunc(&pref[i], &p_u_pow[i], deg_u);
    }
    suff[k_cnt] = vec![Iv::one()];
    for i in (0..k_cnt).rev() {
        suff[i] = poly_mul_trunc(&p_u_pow[i], &suff[i + 1], deg_u);
    }

    let mut p_non_enter = Iv::zero();
    for &c in &pref[k_cnt] {
        p_non_enter = p_non_enter.add(c);
    }
    let p_enter = Iv::one().sub(p_non_enter);

    let mut loss_tot = Iv::zero();
    let na_iv = Iv::from_i128(i128::from(cert.na));
    for i in 0..k_cnt {
        let other = poly_mul_trunc(&pref[i], &suff[i + 1], deg_u);
        let q_prod = poly_mul_trunc(&q_u[i], &p_u_pow_m1[i], deg_u);
        let full = poly_mul_trunc(&q_prod, &other, deg_u);
        let mut s = Iv::zero();
        for &c in &full {
            s = s.add(c);
        }
        loss_tot = loss_tot.add(na_iv.mul(s));
    }

    let sa_iv = s_a.to_iv();
    let f_iv = f_rat.to_iv();
    let e_a = sa_iv.add(f_iv.mul(p_enter)).sub(loss_tot);
    let ratio_iv = e_a.add(sa_iv).div(sa_iv);
    let target_iv = target.to_iv();

    println!("  [PASS] Entry-fee PGF (deg={}) computed in {:.3}s (all decimals strictly outward-rounded):", deg_u, t_u0.elapsed().as_secs_f64());
    println!("         Pr[U_A < 7]              in [{}, {}]", fmt_down_12(p_non_enter.lo), fmt_up_12(p_non_enter.hi));
    println!("         E[Pay_A * 1{{U_A < 7}}]   in [{}, {}]", fmt_down_12(loss_tot.lo), fmt_up_12(loss_tot.hi));
    println!("         (E_A + S_A) / S_A        in [{}, {}] (internal width <= {})", fmt_down_12(ratio_iv.lo), fmt_up_12(ratio_iv.hi), fmt_up_sci(next_up(ratio_iv.hi - ratio_iv.lo)));
    assert!(ratio_iv.lo > target_iv.hi, "Ratio lower endpoint <= target");
    println!("  [PASS] Certified strict inequality: (E_A + S_A)/S_A >= {} > {}/{}", fmt_down_12(ratio_iv.lo), target.num, target.den);

    // 3. Exact BRev verification over [0, inf)
    let t_z0 = Instant::now();
    let diff_ticks = p0_rat.sub(s_a).mul(d_rat);
    assert!(diff_ticks.num > 0 && diff_ticks.den > 0, "P0 must exceed S_A");
    let deg_z_i128 = (diff_ticks.num + diff_ticks.den - 1) / diff_ticks.den;
    let deg_z = usize::try_from(deg_z_i128).expect("deg_z usize");
    assert_eq!(deg_z, 5013, "Pinned deg_z mismatch");
    let check_reach = s_a.add(Rat::new(deg_z_i128, cert.grid_den)).sub(p0_rat);
    assert!(check_reach.num >= 0, "deg_Z fails to reach P0");

    let mut p_z_tot = vec![Iv::one()];
    for gd in &groups_data {
        let mut base = vec![Iv::zero(); deg_z + 1];
        base[0] = gd.p0.to_iv();
        for &(k, pr) in &gd.pmf {
            if k <= deg_z {
                base[k] = base[k].add(pr.to_iv());
            }
        }
        let pw = poly_pow_trunc(&base, cert.na, deg_z);
        p_z_tot = poly_mul_trunc(&p_z_tot, &pw, deg_z);
    }

    let mut cdf_lt = Iv::zero();
    let mut max_rev_hi = 0.0_f64;
    let mut max_rev_k = 0usize;
    let mut max_w = 0.0_f64;
    for k in 1..=deg_z {
        cdf_lt = cdf_lt.add(p_z_tot[k - 1]);
        let surv_k = Iv::one().sub(cdf_lt);
        let pk_iv = s_a.add(Rat::new(i128::try_from(k).expect("k"), cert.grid_den)).to_iv();
        let rev_k = pk_iv.mul(surv_k);
        let w = next_up(rev_k.hi - rev_k.lo);
        if w > max_w {
            max_w = w;
        }
        if rev_k.hi > max_rev_hi {
            max_rev_hi = rev_k.hi;
            max_rev_k = k;
        }
        assert!(rev_k.hi <= sa_iv.lo, "BRev violation at k={}", k);
    }
    println!("  [PASS] Finite-grid BRev verified for ALL k = 1..{} in {:.3}s:", deg_z, t_z0.elapsed().as_secs_f64());
    println!("         max_{{1<=k<={}}} (S_A + k/100)*Pr[Z_A >= k/100] <= {} < S_A = 4.8725", deg_z, fmt_up_12(max_rev_hi));
    println!("         Worst grid point k = {} (slack >= {}, max internal width <= {})", max_rev_k, fmt_down_12(next_down(sa_iv.lo - max_rev_hi)), fmt_up_sci(max_w));

    // 3b. Zero-libm Chernoff MGF tail bound for ALL p >= P_0 = 55!
    let t_iv = t_ch_rat.to_iv();
    let p0_iv = p0_rat.to_iv();
    let mut m_tot = Iv::one();
    for gd in &groups_data {
        let mut mgf_one = gd.p0.to_iv();
        for &(k, pr) in &gd.pmf {
            let x_iv = Rat::new(i128::try_from(k).expect("k"), cert.grid_den).to_iv();
            let ex = exp_iv(t_iv.mul(x_iv), ln2);
            mgf_one = mgf_one.add(pr.to_iv().mul(ex));
        }
        m_tot = m_tot.mul(mgf_one.pow_u64(cert.na));
    }
    let chernoff_iv = p0_iv.mul(exp_iv(t_iv.mul(p0_iv.sub(sa_iv)).neg(), ln2)).mul(m_tot);
    assert!(chernoff_iv.hi < sa_iv.lo, "Chernoff bound failed");
    println!("  [PASS] Infinite-tail zero-libm Chernoff bound (ALL p >= {}/{}, t={}/{}):", p0_rat.num, p0_rat.den, t_ch_rat.num, t_ch_rat.den);
    println!("         sup_{{p >= 55}} p*Pr[S_A + Z_A >= p] <= {} < S_A = 4.8725", fmt_up_12(chernoff_iv.hi));

    println!("\n============================================================================");
    println!("VERIFIER 1 FINAL VERDICT: PASS (0 failures, elapsed {:.3}s)", t0.elapsed().as_secs_f64());
    println!("  CERTIFIED: REV(X) > ({}/{}) * max(SREV(X), BREV(X)) = 2.195 * max(SREV, BREV)", target.num, target.den);
    println!("  Certified outward-rounded lower endpoint: {}", fmt_down_12(ratio_iv.lo));
    println!("============================================================================");
}
