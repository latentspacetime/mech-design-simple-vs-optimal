# Mechanism Design `[2.195, 2.48]` Negative Trap and Mutation Matrix

**Overall Result:** `ALL TRAPS REJECTED WITH EXPECTED DIAGNOSTICS + CLEAN CONTROLS & ORACLES PASSED`

| Case | Suite | Trap Class | Mutation / Check | rc | Diagnostic | Verdict |
| --- | --- | --- | --- | ---: | --- | --- |
| `CTRL_UB_rust` | 2.48 UB | Clean Control | Unmodified 2.48 certificate (Rust) | `0` | `RUST SELF-CERTIFIED VERIFIER PASS in 21.00s: ls=(3/50,7/20,9/5), leaves=722, disjoint=32, ` | **PASS** |
| `CTRL_LB_rust` | 2.195 LB | Clean Control | Unmodified 2.195 certificate (Rust) | `0` | `VERIFIER 1 FINAL VERDICT: PASS (0 failures, elapsed 7.072s)` | **PASS** |
| `U_CB1_target249_py` | 2.48 UB | Claim-Binding/Schema | JSON target=2.49 rejected vs pinned 62/25 (Python) | `1` | `REJECT: certificate target 249/100 exceeds theorem ceiling 62/25` | **REJECTED (OK)** |
| `U_CB1_target249_rs` | 2.48 UB | Claim-Binding/Schema | JSON target=2.49 rejected vs pinned 62/25 (Rust) | `101` | `Certificate target 249/100 != expected target 2.48 (refusing silent target mismatch)` | **REJECTED (OK)** |
| `U_CB2_target_below_py` | 2.48 UB | Claim-Binding/Schema | JSON target=2.47 < --expected-target 62/25 raises mismatch without silent overwrite (Py) | `1` | `REJECT: certificate target 247/100 != expected target 62/25 (refusing silent target mismat` | **REJECTED (OK)** |
| `U_CB2_target_below_rs` | 2.48 UB | Claim-Binding/Schema | JSON target=2.47 < expected 2.48 raises mismatch without silent overwrite (Rust) | `101` | `Certificate target 247/100 != expected target 2.48 (refusing silent target mismatch)` | **REJECTED (OK)** |
| `U_CB3_shifted_ls_py` | 2.48 UB | Claim-Binding/Schema | Shifted ls[0]=0.07 rejected against pinned (3/50,7/20,9/5) (Py) | `1` | `REJECT: ls mismatch: got [Fraction(7, 100), Fraction(7, 20), Fraction(9, 5)], expected_ls=` | **REJECTED (OK)** |
| `U_CB3_shifted_ls_rs` | 2.48 UB | Claim-Binding/Schema | Shifted ls[0]=0.07 rejected against pinned (3/50,7/20,9/5) (Rust) | `101` | `ls must equal exact rationals (3/50, 7/20, 9/5), got (7/100, 7/20, 9/5)` | **REJECTED (OK)** |
| `U_CB4_python_dash_O` | 2.48 UB | Runtime-Guard | verify_3m_independent.py refuses Python -O | `1` | `REJECT: refusing to run under Python -O / PYTHONOPTIMIZE.` | **REJECTED (OK)** |
| `U_CB5_binary64_round_py` | 2.48 UB | Claim-Binding/Schema | JSON target=2.4800000000000001 rejected without binary64 rounding (Py) | `1` | `REJECT: certificate target 24800000000000001/10000000000000000 exceeds theorem ceiling 62/` | **REJECTED (OK)** |
| `U_AS1_target247_rs` | 2.48 UB | Arithmetic-Soundness | Drive target=2.47 through JSON+CLI -> leaf numerical failure (Rust) | `1` | `RUST SELF-CERTIFIED VERIFIER FAIL in 136.70s: ls=(3/50,7/20,9/5), leaves=722, disjoint=32,` | **REJECTED (OK)** |
| `U_AS2_corrupt_dual_rs` | 2.48 UB | Arithmetic-Soundness | Corrupt leaf #1 Farkas dual eta0=1.0 -> ub > 2.48 (Rust) | `1` | `RUST SELF-CERTIFIED VERIFIER FAIL in 20.33s: ls=(3/50,7/20,9/5), leaves=722, disjoint=32, ` | **REJECTED (OK)** |
| `U_AS2_corrupt_dual_py` | 2.48 UB | Arithmetic-Soundness | Corrupt leaf #1 Farkas dual eta0=1.0 -> Python _verify_one returns False (Py) | `1` | `PY_LEAF1 ok=False ub<=3.39005424` | **REJECTED (OK)** |
| `U_AS3_drop_coverage_py` | 2.48 UB | Arithmetic-Soundness | Shrink child box -> tree split coverage gap (Py) | `1` | `REJECT: Split gap` | **REJECTED (OK)** |
| `U_AS3_drop_coverage_rs` | 2.48 UB | Arithmetic-Soundness | Shrink child box -> tree split coverage gap (Rust) | `101` | `assertion failed: c1[2 * j] == bk[2 * j] && c1[2 * j + 1] == c2[2 * j] &&` | **REJECTED (OK)** |
| `U_AS4_disjoint_interior_py` | 2.48 UB | Arithmetic-Soundness | Mark feasible-interior box [0,1]x[0,3]x[0,5/8] as disjoint (Py) | `1` | `REJECT: Invalid disjoint box [Fraction(0, 1), Fraction(1, 1), Fraction(0, 1), Fraction(3, ` | **REJECTED (OK)** |
| `U_AS4_disjoint_interior_rs` | 2.48 UB | Arithmetic-Soundness | Mark feasible-interior box [0,1]x[0,3]x[0,5/8] as disjoint (Rust) | `101` | `Disjoint check failed on box [0, 1073741824, 0, 3221225472, 0, 671088640]` | **REJECTED (OK)** |
| `U_AS5_oracle_rounding` | 2.48 UB | Arithmetic-Soundness | Boundary oracle: outward f2iv enclosure & non-finite trap | `0` | `ORACLE_UB_OK` | **PASS** |
| `U_AS6_lean_tighten_247` | 2.48 UB | Claim-Binding/Constant-Pin | Lean Mathlib rejects tightened UB certTarget (62/25) -> 247/100 | `1` | `<stdin>:3:53: error: unsolved goals` | **REJECTED (OK)** |
| `U_AS7_lean_disjoint_trap` | 2.48 UB | Arithmetic-Soundness | Lean kernel `by decide` rejects feasible-interior box marked disjoint | `1` | `<stdin>:3:110: error: tactic 'decide' proved that the proposition` | **REJECTED (OK)** |
| `L_CB1_perturb_rg_py` | 2.195 LB | Claim-Binding/Schema | Perturb A1 r_num 227->228 rejected (Py) | `1` | `RuntimeError: VERIFICATION FAILURE: Raw r_g mismatch in A1: 228/2000 != 227/2000` | **REJECTED (OK)** |
| `L_CB1_perturb_rg_rs` | 2.195 LB | Claim-Binding/Schema | Perturb A1 r_num 227->228 rejected (Rust) | `101` | `assertion `left == right` failed: Raw r_g mismatch in A1` | **REJECTED (OK)** |
| `L_CB2_python_dash_O` | 2.195 LB | Runtime-Guard | verify_lb_independent.py refuses Python -O | `1` | `RuntimeError: Refusing to run under Python -O (optimized mode).` | **REJECTED (OK)** |
| `L_CB3_mutate_degZ_src` | 2.195 LB | Claim-Binding/Schema | Source-mutate PINNED_DEG_Z 5013->5000 fails K_cut check (Py) | `1` | `RuntimeError: VERIFICATION FAILURE: Pinned deg_Z mismatch: 5013 != 5000` | **REJECTED (OK)** |
| `L_CB4_target2196_pin_py` | 2.195 LB | Claim-Binding/Schema | JSON target=2196/1000 rejected by raw pin guard (Py) | `1` | `RuntimeError: VERIFICATION FAILURE: Raw target mismatch: 2196/1000` | **REJECTED (OK)** |
| `L_CB5_bad_chernoff_pin_py` | 2.195 LB | Claim-Binding/Schema | JSON chernoff_t=1/100 rejected by raw pin guard (Py) | `1` | `RuntimeError: VERIFICATION FAILURE: Raw Chernoff t mismatch: 1/100` | **REJECTED (OK)** |
| `L_CB5_bad_chernoff_pin_rs` | 2.195 LB | Claim-Binding/Schema | JSON chernoff_t=1/100 rejected by raw pin guard (Rust) | `101` | `assertion `left == right` failed: Raw Chernoff t mismatch` | **REJECTED (OK)** |
| `L_AS1_target2196_arith_py` | 2.195 LB | Arithmetic-Soundness | Bypass pins & drive target=2.196 (> 2.195136...) -> ratio failure (Py) | `1` | `RuntimeError: VERIFICATION FAILURE: Ratio lower bound <= target 549/250` | **REJECTED (OK)** |
| `L_AS2a_chernoff_mono_py` | 2.195 LB | Arithmetic-Soundness | Bypass pins & set t=1/100 -> fails monotonicity P0 >= 1/t (Py) | `1` | `RuntimeError: VERIFICATION FAILURE: Chernoff monotonicity requires P0 >= 1/t` | **REJECTED (OK)** |
| `L_AS2b_chernoff_tail_py` | 2.195 LB | Arithmetic-Soundness | Bypass pins & set t=1/2 -> fails mpmath.iv MGF tail bound (Py) | `1` | `RuntimeError: VERIFICATION FAILURE: Chernoff tail bound failed: 72347071120281455947500857` | **REJECTED (OK)** |
| `L_AS3_oracle_rounding` | 2.195 LB | Arithmetic-Soundness | Boundary oracle: 140-bit frac_to_fx & inf/nan trap | `0` | `ORACLE_LB_OK` | **PASS** |
| `L_AS4_lean_tighten_2196` | 2.195 LB | Arithmetic-Soundness | Lean Mathlib rejects tightened LB 439/200 -> 2196/1000 | `1` | `<stdin>:3:54: error: unsolved goals` | **REJECTED (OK)** |
| `L_AS5_lean_pmf_mut` | 2.195 LB | Arithmetic-Soundness | Lean Mathlib rejects perturbed A1 r_num=228 vs S_A=1949/400 | `1` | `<stdin>:3:122: error: unsolved goals` | **REJECTED (OK)** |
