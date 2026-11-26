# Statement Fidelity Ledger — Mechanism Design `[2.195, 2.48]` Bundle

**Generated:** 2026-11-25 16:18 PST  
**Purpose:** Side-by-side comparison of exported Lean 4 theorem signatures and core definitions in `lean_mathlib/` (`MathForgeMechDesign`) against exact manuscript equations and quantifiers in `paper/proof_body.tex`. Mandatory audit item for Gate 4.

## 1. Core Definitions Alignment

| Mathematical Concept | Manuscript Location (`paper/proof_body.tex`) | Lean 4 Definition | Exact Fidelity Notes |
| --- | --- | --- | --- |
| Stieltjes transform `U_1(t)` and reciprocal `F(t)` | Part I, Sec. 3–4 (`lem:recip-conc`) | `U1 (μ : Measure ℝ) (t : ℝ) := ∫ c, (c + t)⁻¹ ∂μ`, `F μ t := (U1 μ t)⁻¹` | Exact match for probability measure `μ` (`IsProbabilityMeasure μ`, `∀ᵐ c ∂μ, 0 < c`). |
| Discrete cap probability measure `μ = ∑ (r_j/S) δ_{c_j}` | Part I, Sec. 3 (`eq:norm`) | `capMeasure r c := ∑ j, ENNReal.ofReal (r j / ∑ i, r i) • Measure.dirac (c j)` | Exact match; `S > 0`, `IsProbabilityMeasure`, and `∀ᵐ x, 0 < x` explicitly discharged. |
| Harmonic-secant envelope `Ubar(t; γ_bar)` | Part I, Cor. 4 (`cor:ubar`) | `Ubar l₁ l₂ l₃ g₁ g₂ g₃ t` | Exact piecewise minimum over `1/t`, `u_i(t)`, and `s_i(t)` on `[l_i, l_{i+1}]`. |
| 14-inequality 3-moment polytope `D γ ≤ d` | Part I, Sec. 5 (`lem:lens`, `lem:farkas`) | `polytope14 l₁ l₂ l₃ g₁a g₁b g₂a g₂b g₃a g₃b` | Exact 6 box + 4 global + 3 concave tangent + 1 harmonic tangent inequalities. |
| Typed GH26 base inequalities (`eqs. 27–29`) | Part I, Sec. 2 (`eq:gh27`–`eq:gh29`) | `structure GH26BaseInequalities` in `UpperBoundJensenAndDomain.lean` | Encodes normalized `m ≥ 1`, `r_j > 0`, `c_j > 0`, `S, B ∈ (0, 1]`, tail bound `Fbar_j(c_j+t) ≤ r_j/(c_j+t)`, `L` increasing, and GH26 eqs. (27) & (29). **Non-vacuity:** concrete `m = 1` witness `gh26_nonvacuous_m1` proved. **Universal applicability:** external premise cited from GH26 Lemmas 4.4–4.5 on normalized finite grids `I_K^m`. |
| 8-group all-paid PMF and `SREV(A)` | Part II, Table 2, `eq:item-dist`, Lemma 7 | `groupSpec (g : Fin 8)`, `pmfPos`, `p0`, `survReal`, `singleItemRev`, `S_A := 1949/400` | Exact rational match with `certificates/cert_lb_2195.json` verified by `scripts/check_json_lean_eq_mech.py`. |
| Concentrating bundle `B` and `BREV` comparison | Part II, Lemma 8 (`lem:b-bundle`) | `H (Nb : ℕ)`, `expY`, `expY2`, `varZB_lt`, `shifted_bundle_price_le_max`, `brev_le_srev_of_var_bound` | Exact match for every `N_b ≥ 2`. |
| Posted-menu `M_0` and perturbed `M_δ` DSIC/IR | Part II, Sec. 10, Lemma 11 (`lem:tiebreak`) | `menuPrice`, `buyerUtility`, `posted_menu_dsic_ir`, `perturbed_menu_payment_ge` | Exact match for any tie-breaking utility-maximizing buyer rule; payment drop bounded by `ε_1 + |A| ε_2 + ε_3`. |

## 2. Exported Theorem Side-by-Side Comparison

| Manuscript Claim | Manuscript Quantifiers | Exported Lean 4 Theorem Signature | Fidelity Verdict |
| --- | --- | --- | --- |
| Reciprocal-Concavity Lemma (`lem:recip-conc`) | Probability measure `μ` on `(0, ∞)`, `t > 0` | `F_ge_self`, `F_deriv_ge_one`, `F_deriv2_le_zero`, `F_concaveOn` | **Exact match.** |
| Cap measure normalization | `m ≥ 1`, `r_j > 0`, `c_j > 0` | `capMeasure_isProbabilityMeasure`, `capMeasure_ae_pos` | **Exact match.** |
| 3D Moment Lens (`lem:lens`), Envelope (`cor:ubar`), Farkas (`lem:farkas`) | `γ ∈ ℒ`, `y ∈ ℝ_{\ge 0}^{14}`, `η = D^T y` | `lens_ineq_i`..`v`, `U1_le_Ubar_le_inv`, `polytope_valid`, `farkas_decoupling` | **Exact match.** |
| Binary tree cover & 32-box disjointness (`tree_cert_3m_2480_tight.json`) | Root `[0,17]×[0,3]×[0,5/8]`, 722 leaves, 32 disjoint boxes | `cert248_root_covers`, `cert248_leaf_count`, `cert248_disjoint_count`, `cert248_tree_valid`, `treeValid_covers_real`, `certTree248_covers_R0` | **Exact match** (`by decide` on exact-rational split/disjoint predicates + real-space coverage soundness `treeValid_covers_real`; linking `disjointCheck` to `L ∩ b = ∅` uses kernel-proved `lens_ineq_i..v`/`polytope_valid` plus paper-level `cl(L) = cl(int(cl(L)))`; JSON equality verified). |
| Time-Varying Jensen Alignment (`lem:jensen-mono`) | `inst : GH26BaseInequalities`, `a_k ≥ 0`, `∑ a_k = 1`, `λ_k > 0`, `U_1 ≤ Ubar ≤ 1/t` | `time_varying_jensen_alignment`, `gh26_nonvacuous` | **Exact match** (scoped explicitly to `GH26BaseInequalities`; domain extension from `[0,∞)^m` to `I_K^m` has shifted payment kernel-proved in `shifted_payment_ic_ir` and monotone convergence + GH26 Prop. 2.2 on paper). |
| 8-group PMF, `REV(X_g) = r_g/N_a`, `SREV(A) = 1949/400` (`lem:srev-a`) | `g ∈ {1..8}`, all posted prices `v > 0` | `pmfPos_pos`, `p0_pos`, `pmf_sum_eq_one`, `posted_price_rev_le`, `posted_price_rev_eq_on_grid`, `singleItemRev_eq`, `srev_A_eq` | **Exact match.** |
| Bundle `B` variance & `BREV ≤ SREV` (`lem:b-bundle`) | `N_b ≥ 2`, `sup_p p Pr[S_A + Z_A ≥ p] = S_A` | `varZB_lt`, `shifted_bundle_price_le_max`, `brev_le_srev_of_var_bound` | **Exact match.** |
| Exact conservative finite witness (`N_b = 2^46800`, `δ = S_A / 10^8`) | `r = 2.195136628895 ≤ (E_A + S_A)/S_A` ⇒ finite ratio `> 439/200` | `harmonic_two_pow_ge`, `finite_witness_margin`, `finite_witness_ratio_gt` | **Exact match** (dyadic bound `H_{2^46800} ≥ 23401`, slack `> 8.62e-8`). |
| DSIC/IR & tie-breaking perturbation (`lem:tiebreak`) | `0 < ε_1 < p_B`, `0 < ε_2 < 0.07`, `0 < ε_3 < 7`, every tie-breaking rule | `posted_menu_dsic_ir`, `perturbed_menu_payment_ge` | **Exact match.** |

## 3. Axiom Audit Summary (`MathForgeMechDesign`, 55 Exported Theorems)
- `cert248_leaf_count`, `cert248_disjoint_count`: **zero axioms** (`[]`).
- `cert248_root_covers`, `cert248_tree_valid`: `[propext]` only.
- Remaining `51` theorems: strictly subsets of `[propext, Classical.choice, Quot.sound]`.
- Zero `sorryAx`, zero `Lean.ofReduceBool`, zero `Lean.trustCompiler`, zero custom `axiom`/`opaque`.
