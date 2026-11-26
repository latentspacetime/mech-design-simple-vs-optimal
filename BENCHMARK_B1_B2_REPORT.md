# Full-Workload Lean 4 Kernel Micro-Benchmark Report (`B1` and `B2`)

- **Date:** 2026-11-25
- **Host:** Apple M3 Pro (macOS, 18 GiB unified RAM)
- **Toolchain:** `leanprover/lean4:v4.14.0` (`lake env lean`, pure kernel `by decide`, zero `native_decide`)
- **Pre-Declared Go/No-Go Thresholds:** Extrapolated build wall-clock `<= 30 min` (`1,800 s`) AND peak RSS `<= 12 GiB` (`12,884,901,888` bytes).
- **Benchmark Sources:** `<release-root>/scratch_bench/`

---

## Executive Decision Summary

| Benchmark | Workload | Extrapolated Wall-Clock | Extrapolated Peak RSS | Threshold (`<= 30 min`, `<= 12 GiB`) | Decision |
| --- | --- | --- | --- | --- | --- |
| **B1 (`2.195` LB Poly + Grid)** | Schoolbook `List Nat` (`deg=699` + `deg=5013`, 8 groups, `N_a=5000`) | `~2.9 hr` (`deg=699`) + `~147 hr` (`deg=5013`) | `> 12 GiB` (even single `deg=699` times out >60s) | FAIL (both) | **NO-GO** |
| **B1 (`2.195` LB Poly + Grid)** | Kronecker-packed `Nat` (GMP-backed `Nat.mul`, `deg=699` + `deg=5013`) | `~12.5 min` (`deg=699` only), **SIGABRT (`EXIT=134`)** at `deg=5013` | `> 12 GiB` (accumulating `~248.7 MiB/mult` WHNF cache across ~600 mults; crashes at `deg=5013`) | FAIL (`deg=5013` crashes; RSS > 12 GiB) | **NO-GO** |
| **B2 (`2.48` UB Quadrature)** | 14-term Taylor `exp` + `h(u)` + trapezoid sum (`722` leaves × `3,803` `t`-panels × `401` `c`-panels × `2x` margin) | `~4.5 × 10^8 s` (`~14.3 CPU-years`; `~86.7 hr` for 1 single leaf) | `~3.05 GiB` at `200` panels (`> 12 GiB` by `~800` panels) | FAIL (by `~250,000x` time) | **NO-GO** |

**Consequence per Stage 1 Plan:** Do **NOT** implement `LowerBoundPoly.lean` or `UpperBoundQuadrature.lean` in Lean 4's kernel. Keep all analytic, structural, moment-polytope, Farkas-decoupling, exact-rational binary tree coverage/disjointness (`CertTreeData248.lean`), 8-group PMF/REV/SREV (`LowerBoundPmf.lean`), concentrating-bundle Chebyshev + exact conservative finite witness `N_b = 2^46800` (`LowerBoundChebyshevAndWitness.lean`), Time-Varying Jensen + non-vacuity (`UpperBoundJensenAndDomain.lean`), and DSIC/IR tie-breaking (`LowerBoundDSIC.lean`) kernel-proved in `MathForgeMechDesign`, while recording the exact external computational verifier backends (`verify_3m_rust` + `verify_3m_independent.py` for the 722-leaf quadrature; `verify_lb_rust` + `verify_lb_independent.py` for the `deg=699` / `deg=5013` / `5013`-grid / Chernoff arithmetic) explicitly in `FORMALIZATION_COVERAGE_LEDGER.md`.

---

## Raw `/usr/bin/time -l lake env lean <File.lean>` Measurements

All probes used a strict `60s` per-probe timeout and pure structural recursion evaluated by `by decide` (zero `native_decide`).

### Benchmark B1: `2.195` LB Truncated Fixed-Point Polynomial Multiplication (`2^{-140}` scale)

#### B1a. Structurally-Recursive Schoolbook `List Nat` Multiplication

| Probe File | Degree | Mults | Exit | Real (s) | User (s) | Sys (s) | Max RSS (bytes / GiB) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `BenchB1_Schoolbook_100.lean` | `100` | `1` | `0` | `3.17` | `1.61` | `0.44` | `390,742,016` (`0.364 GiB`) |
| `BenchB1_Schoolbook_200.lean` | `200` | `1` | `0` | `6.29` | `5.75` | `0.49` | `1,010,335,744` (`0.941 GiB`) |
| `BenchB1_Schoolbook_699.lean` | `699` | `1` | `TIMEOUT` | `> 60.0` | — | — | — |

**Extrapolation (Schoolbook):**
- Empirical quadratic `O(d^2)` scaling from `d = 200` (`6.29s`, `0.941 GiB`) to `d = 699` (`(700/201)^2 = 12.13x`): `~76.3 s` per single mult (consistent with timing out at `> 60s`).
- Full `N_a = 5,000` (`17` mults per group × `8` groups = `136` mults, even counting only one endpoint before doubling for lo/hi and `Q_U` loss products):
  - At `deg = 699`: `136 × 76.3 s ≈ 10,377 s` (`2.88 hr`, `5.8x` over the 30-min cap; `> 20 hr` including lo/hi + `P_U^(Na-1)` + `Q_U` terms).
  - At `deg = 5,013`: `(5014/201)^2 = 622.3x` ⇒ `~3,914 s` (`65.2 min`) per single mult ⇒ `136 × 3,914 s ≈ 532,300 s` (`147.9 hr`, `295x` over the 30-min cap).

#### B1b. Structurally-Recursive Kronecker-Packed `Nat` Multiplication (GMP-Backed, `set_option exponentiation.threshold 2000000`)

| Probe File | Degree | Mults | Exit | Real (s) | User (s) | Sys (s) | Max RSS (bytes / GiB) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `BenchB1_Kronecker_699_one.lean` | `699` | `1` | `0` | `3.59` | `2.37` | `0.45` | `506,937,344` (`0.472 GiB`) |
| `BenchB1_Kronecker_699_pow8.lean` | `699` | `3` (`N=8`) | `0` | `6.08` | `5.60` | `0.42` | `1,028,636,672` (`0.958 GiB`) |
| `BenchB1_Kronecker_5013_one.lean` | `5013` | `1` | `134` (`SIGABRT`) | `0.76` | `0.48` | `0.27` | `315,359,232` (`0.294 GiB`) |

**Extrapolation (Kronecker):**
- Marginal cost at `deg = 699` (from `1` mult → `3` mults): `(6.08 - 3.59) / 2 = 1.245 s/mult` and `(1028.6 - 506.9) / 2 = 260.8 MB/mult` RSS growth.
- Across full `deg = 699` workload (`8` groups × (`17` mults `P^Na` + `17` mults `P^(Na-1)` + prefix/suffix/loss mults) × `2` endpoints ≈ `600` mults): `~750 s` wall-clock if split into many modules, **but** inside Lean's WHNF reducer a single `by decide` would require `> 12 GiB` RSS unless manually chunked into dozens of intermediate certificate files.
- Crucially, **`deg = 5,013` crashes immediately with `EXIT=134` (`SIGABRT`)** in Lean `v4.14.0`'s kernel when constructing/packing a `5,014`-coefficient list (`1.5M`-bit packed `Nat`). Even ignoring the stack crash, `5,013` grid point checks plus `8 × 17 × 2 = 272` degree-`5013` multiplications far exceeds the `12 GiB` RSS and `30 min` bounds.

---

### Benchmark B2: `2.48` UB Interval Quadrature (14-Term Taylor `exp` + `h(u)` + Trapezoid Sum, `2^{-64}` scale)

| Probe File | Panels | Exit | Real (s) | User (s) | Sys (s) | Max RSS (bytes / GiB) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `BenchB2_Quad_200.lean` (default threshold) | `200` | `0` | `52.58` | `41.48` | `6.11` | `2,642,952,192` (`2.461 GiB`) |
| `BenchB2_Quad_200.lean` (`exponentiation.threshold 2000000`) | `200` | `0` | `40.87` | `38.64` | `1.64` | `3,270,819,840` (`3.046 GiB`) |
| `BenchB2_Quad_500.lean` (`exponentiation.threshold 2000000`) | `500` | `TIMEOUT` | `> 60.0` | — | — | — |

**Extrapolation (Quadrature):**
- Measured per-panel cost (optimized `exponentiation.threshold`): **`0.2044 s / panel`** and **`~15.6 MiB / panel`** RSS (explaining why `500` panels exceeds `60s` and `~800` panels would exceed `12 GiB` RSS).
- Full adaptive workload per leaf: `3,803` `t`-panels × `401` initial `c`-panels = `1,525,003` `(c, t)` panel evaluations + `1,300` `L(λ)` panels = `1,526,303` panels/leaf.
  - Single leaf wall-clock: `1,526,303 × 0.2044 s ≈ 311,976 s ≈ 86.7 hours`.
  - Full `722` leaves × `2x` safety margin (`2.204 × 10^9` panel evaluations): **`~4.50 × 10^8 s ≈ 14.28 CPU-years`**.
- **Verdict:** Overwhelming **NO-GO** (`~250,000x` above the `30 min` threshold and orders of magnitude above the `12 GiB` RSS cap).
