import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import MathForgeMechDesign.CertTreeData248

/-!
# Mechanism Design 2.48 Upper Bound: Reciprocal-Concavity, 3-Moment Lens, Farkas Decoupling, and Kernel Tree Cover (`L-MUST`)

Proves:
1. **Reciprocal-Concavity Lemma (`lem:recip-conc`)** strictly for a probability measure `μ` on `(0, ∞)`:
   - `U1 μ t = ∫ c, (c + t)⁻¹ ∂μ`, `F μ t = (U1 μ t)⁻¹`
   - `U1_pos`, `U1_le_inv`, `F_ge_self : ∀ t > 0, t ≤ F μ t`
   - Exact derivatives `hasDerivAt_U1`, `hasDerivAt_U1'` via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
   - `F_deriv_ge_one : ∀ t > 0, 1 ≤ deriv (F μ) t` via Cauchy-Schwarz
   - `F_deriv2_le_zero : ∀ t > 0, deriv (deriv (F μ)) t ≤ 0` via Cauchy-Schwarz
   - `F_concaveOn : ConcaveOn ℝ (Set.Ioi 0) (F μ)` via `concaveOn_of_deriv2_nonpos`
2. **Explicit discrete cap measure construction** `capMeasure r c := ∑ j, ENNReal.ofReal (r j / S) • Measure.dirac (c j)`
   discharging BOTH `IsProbabilityMeasure (capMeasure r c)` and `∀ᵐ x ∂(capMeasure r c), 0 < x`.
3. **3-Moment Lens (`lem:lens`)**, **Harmonic-Secant Upper Envelope (`cor:ubar`)**, and
   **14-inequality Polytope & Farkas Decoupling (`lem:farkas`)**.
4. **Kernel-verified exact binary tree coverage & 32-box disjointness** of `tree_cert_3m_2480_tight.json`
   via pure structural recursion and `by decide` (ZERO `native_decide`), plus real-space partition soundness.
-/

namespace MathForgeMechDesign.UpperBoundRecipAndTree

open scoped BigOperators Topology
open MeasureTheory Metric Set

section ReciprocalConcavity

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- First Stieltjes moment `U_1(t) = ∫ (c + t)⁻¹ dμ(c)`. -/
noncomputable def U1 (t : ℝ) : ℝ := ∫ c, (c + t)⁻¹ ∂μ

/-- Reciprocal scale function `F(t) = 1 / U_1(t)`. -/
noncomputable def F (t : ℝ) : ℝ := (U1 μ t)⁻¹

/-- First derivative formula `U_1'(t) = - ∫ (c + t)⁻² dμ(c)`. -/
noncomputable def U1Deriv (t : ℝ) : ℝ := - ∫ c, ((c + t)⁻¹) ^ 2 ∂μ

/-- Second derivative formula `U_1''(t) = 2 ∫ (c + t)⁻³ dμ(c)`. -/
noncomputable def U1Deriv2 (t : ℝ) : ℝ := 2 * ∫ c, ((c + t)⁻¹) ^ 3 ∂μ

lemma integrable_inv_pow (hsupp : ∀ᵐ c ∂μ, 0 < c) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Integrable (fun c : ℝ => ((c + t)⁻¹) ^ k) μ := by
  have hmeas : AEStronglyMeasurable (fun c : ℝ => ((c + t)⁻¹) ^ k) μ :=
    (((measurable_id.add measurable_const).inv).pow_const k).aestronglyMeasurable
  refine Integrable.mono' (integrable_const ((t⁻¹) ^ k)) hmeas ?_
  filter_upwards [hsupp] with c hc
  have hct : 0 < c + t := by linarith
  have hle : (c + t)⁻¹ ≤ t⁻¹ := inv_anti₀ ht (by linarith)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (by positivity) hle k

lemma U1_pos (hsupp : ∀ᵐ c ∂μ, 0 < c) {t : ℝ} (ht : 0 < t) :
    0 < U1 μ t := by
  unfold U1
  have hint : Integrable (fun c : ℝ => (c + t)⁻¹) μ := by
    simpa using integrable_inv_pow μ hsupp ht 1
  have hnn : 0 ≤ᵐ[μ] (fun c : ℝ => (c + t)⁻¹) := by
    filter_upwards [hsupp] with c hc
    have : 0 < c + t := by linarith
    positivity
  rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
  have hsup_eq : μ (Function.support (fun c : ℝ => (c + t)⁻¹)) = μ Set.univ := by
    apply measure_congr
    filter_upwards [hsupp] with c hc
    have hct : 0 < c + t := by linarith
    show (c ∈ Function.support (fun c : ℝ => (c + t)⁻¹)) = (c ∈ (Set.univ : Set ℝ))
    exact propext ⟨fun _ => Set.mem_univ c, fun _ => Function.mem_support.mpr (ne_of_gt (inv_pos.mpr hct))⟩
  rw [hsup_eq, measure_univ]
  exact zero_lt_one

lemma U1_le_inv (hsupp : ∀ᵐ c ∂μ, 0 < c) {t : ℝ} (ht : 0 < t) :
    U1 μ t ≤ t⁻¹ := by
  unfold U1
  have hint : Integrable (fun c : ℝ => (c + t)⁻¹) μ := by
    simpa using integrable_inv_pow μ hsupp ht 1
  have hle : ∫ c, (c + t)⁻¹ ∂μ ≤ ∫ _c, t⁻¹ ∂μ := by
    apply integral_mono_ae hint (integrable_const t⁻¹)
    filter_upwards [hsupp] with c hc
    exact inv_anti₀ ht (by linarith)
  simpa [integral_const, measure_univ] using hle

/-- Reciprocal-Concavity Lemma part (a): `F(t) ≥ t` for all `t > 0`. -/
theorem F_ge_self (hsupp : ∀ᵐ c ∂μ, 0 < c) {t : ℝ} (ht : 0 < t) :
    t ≤ F μ t := by
  unfold F
  have hpos : 0 < U1 μ t := U1_pos μ hsupp ht
  have hle : U1 μ t ≤ t⁻¹ := U1_le_inv μ hsupp ht
  calc
    t = (t⁻¹)⁻¹ := (inv_inv t).symm
    _ ≤ (U1 μ t)⁻¹ := inv_anti₀ hpos hle

/-- Exact first derivative of `U_1` on `(0, ∞)` via dominated differentiation under the integral sign. -/
theorem hasDerivAt_U1 (hsupp : ∀ᵐ c ∂μ, 0 < c) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (U1 μ) (U1Deriv μ t₀) t₀ := by
  have hε : 0 < t₀ / 2 := half_pos ht₀
  have hF_meas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (fun c : ℝ => (c + t)⁻¹) μ :=
    Filter.Eventually.of_forall fun t =>
      ((measurable_id.add measurable_const).inv).aestronglyMeasurable
  have hF_int : Integrable (fun c : ℝ => (c + t₀)⁻¹) μ := by
    simpa using integrable_inv_pow μ hsupp ht₀ 1
  have hF'_meas : AEStronglyMeasurable (fun c : ℝ => -((c + t₀)⁻¹) ^ 2) μ :=
    ((((measurable_id.add measurable_const).inv).pow_const 2).neg).aestronglyMeasurable
  have h_bound :
      ∀ᵐ c ∂μ, ∀ t ∈ ball t₀ (t₀ / 2), ‖-((c + t)⁻¹) ^ 2‖ ≤ ((t₀ / 2)⁻¹) ^ 2 := by
    filter_upwards [hsupp] with c hc t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have ht_lo : t₀ / 2 < t := by linarith [(abs_lt.mp ht).1]
    have hct : 0 < c + t := by linarith
    have hle : (c + t)⁻¹ ≤ (t₀ / 2)⁻¹ := inv_anti₀ hε (by linarith)
    rw [norm_neg, Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity) hle 2
  have h_diff :
      ∀ᵐ c ∂μ, ∀ t ∈ ball t₀ (t₀ / 2),
        HasDerivAt (fun x : ℝ => (c + x)⁻¹) (-((c + t)⁻¹) ^ 2) t := by
    filter_upwards [hsupp] with c hc t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have ht_lo : t₀ / 2 < t := by linarith [(abs_lt.mp ht).1]
    have hct : c + t ≠ 0 := by linarith
    have h1 : HasDerivAt (fun x : ℝ => c + x) 1 t := (hasDerivAt_id t).const_add c
    have h2 := h1.inv hct
    simpa [inv_pow, neg_div] using h2
  have hres :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (E := ℝ)
      hε hF_meas hF_int hF'_meas h_bound (integrable_const (((t₀ / 2)⁻¹) ^ 2)) h_diff
  have hneg : ∫ c, -((c + t₀)⁻¹) ^ 2 ∂μ = U1Deriv μ t₀ := by
    unfold U1Deriv
    exact integral_neg _
  rw [hneg] at hres
  exact hres.2

/-- Exact second derivative of `U_1` on `(0, ∞)` via dominated differentiation under the integral sign. -/
theorem hasDerivAt_U1Deriv (hsupp : ∀ᵐ c ∂μ, 0 < c) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (U1Deriv μ) (U1Deriv2 μ t₀) t₀ := by
  have hε : 0 < t₀ / 2 := half_pos ht₀
  have hF_meas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (fun c : ℝ => ((c + t)⁻¹) ^ 2) μ :=
    Filter.Eventually.of_forall fun t =>
      (((measurable_id.add measurable_const).inv).pow_const 2).aestronglyMeasurable
  have hF_int : Integrable (fun c : ℝ => ((c + t₀)⁻¹) ^ 2) μ :=
    integrable_inv_pow μ hsupp ht₀ 2
  have hF'_meas : AEStronglyMeasurable (fun c : ℝ => -(2 * ((c + t₀)⁻¹) ^ 3)) μ :=
    ((((((measurable_id.add measurable_const).inv).pow_const 3).const_mul 2)).neg).aestronglyMeasurable
  have h_bound :
      ∀ᵐ c ∂μ, ∀ t ∈ ball t₀ (t₀ / 2), ‖-(2 * ((c + t)⁻¹) ^ 3)‖ ≤ 2 * ((t₀ / 2)⁻¹) ^ 3 := by
    filter_upwards [hsupp] with c hc t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have ht_lo : t₀ / 2 < t := by linarith [(abs_lt.mp ht).1]
    have hct : 0 < c + t := by linarith
    have hle : (c + t)⁻¹ ≤ (t₀ / 2)⁻¹ := inv_anti₀ hε (by linarith)
    rw [norm_neg, Real.norm_of_nonneg (by positivity)]
    have hpow : ((c + t)⁻¹) ^ 3 ≤ ((t₀ / 2)⁻¹) ^ 3 := pow_le_pow_left₀ (by positivity) hle 3
    linarith
  have h_diff :
      ∀ᵐ c ∂μ, ∀ t ∈ ball t₀ (t₀ / 2),
        HasDerivAt (fun x : ℝ => ((c + x)⁻¹) ^ 2) (-(2 * ((c + t)⁻¹) ^ 3)) t := by
    filter_upwards [hsupp] with c hc t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have ht_lo : t₀ / 2 < t := by linarith [(abs_lt.mp ht).1]
    have hct : c + t ≠ 0 := by linarith
    have h1 : HasDerivAt (fun x : ℝ => (c + x)⁻¹) (-((c + t)⁻¹) ^ 2) t := by
      have := ((hasDerivAt_id t).const_add c).inv hct
      simpa [inv_pow, neg_div] using this
    have h2 := h1.pow 2
    convert h2 using 1
    ring
  have hres :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (E := ℝ)
      hε hF_meas hF_int hF'_meas h_bound (integrable_const (2 * ((t₀ / 2)⁻¹) ^ 3)) h_diff
  have hneg := hres.2.neg
  have hval : -(∫ c, -(2 * ((c + t₀)⁻¹) ^ 3) ∂μ) = U1Deriv2 μ t₀ := by
    unfold U1Deriv2
    rw [integral_neg, neg_neg, integral_mul_left]
  rw [hval] at hneg
  exact hneg

/-- Closed-form first derivative of `F(t) = 1 / U_1(t)`. -/
noncomputable def FDeriv (t : ℝ) : ℝ := -(U1Deriv μ t) / (U1 μ t) ^ 2

/-- Closed-form second derivative of `F(t) = 1 / U_1(t)`. -/
noncomputable def FDeriv2 (t : ℝ) : ℝ :=
  (2 * (U1Deriv μ t) ^ 2 - U1 μ t * U1Deriv2 μ t) / (U1 μ t) ^ 3

lemma hasDerivAt_F (hsupp : ∀ᵐ c ∂μ, 0 < c) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (F μ) (FDeriv μ t) t := by
  have hpos := (U1_pos μ hsupp ht).ne'
  have h1 := (hasDerivAt_U1 μ hsupp ht).inv hpos
  simpa [F, FDeriv] using h1

lemma hasDerivAt_FDeriv (hsupp : ∀ᵐ c ∂μ, 0 < c) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (FDeriv μ) (FDeriv2 μ t) t := by
  have hpos := (U1_pos μ hsupp ht).ne'
  have hU1 := hasDerivAt_U1 μ hsupp ht
  have hU1' := hasDerivAt_U1Deriv μ hsupp ht
  have hnum : HasDerivAt (fun x => -(U1Deriv μ x)) (-(U1Deriv2 μ t)) t := hU1'.neg
  have hden : HasDerivAt (fun x => (U1 μ x) ^ 2) (2 * U1 μ t * U1Deriv μ t) t := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hU1.pow 2
  have hq := hnum.div hden (pow_ne_zero 2 hpos)
  convert hq using 1
  unfold FDeriv2
  field_simp [hpos]
  ring

/-- Reciprocal-Concavity Lemma part (b): `F'(t) ≥ 1` for all `t > 0` (via Cauchy-Schwarz). -/
theorem F_deriv_ge_one (hsupp : ∀ᵐ c ∂μ, 0 < c) {t : ℝ} (ht : 0 < t) :
    1 ≤ deriv (F μ) t := by
  rw [(hasDerivAt_F μ hsupp ht).deriv]
  unfold FDeriv U1Deriv
  have hpos : 0 < U1 μ t := U1_pos μ hsupp ht
  rw [neg_neg, one_le_div (pow_pos hpos 2)]
  -- Cauchy-Schwarz: 0 ≤ ∫ ((c + t)⁻¹ - U1 μ t)^2 dμ = ∫ (c + t)⁻² dμ - (U1 μ t)^2
  set lam := U1 μ t
  have hi1 : Integrable (fun c : ℝ => (c + t)⁻¹) μ := by
    simpa using integrable_inv_pow μ hsupp ht 1
  have hi2 : Integrable (fun c : ℝ => ((c + t)⁻¹) ^ 2) μ :=
    integrable_inv_pow μ hsupp ht 2
  have hnn : 0 ≤ ∫ c, ((c + t)⁻¹ - lam) ^ 2 ∂μ :=
    integral_nonneg (fun c => sq_nonneg _)
  have hexp :
      (fun c : ℝ => ((c + t)⁻¹ - lam) ^ 2) =
      fun c => (((c + t)⁻¹) ^ 2 - (2 * lam) * (c + t)⁻¹) + lam ^ 2 := by
    ext c; ring
  rw [hexp] at hnn
  have hi_sub : Integrable (fun c : ℝ => ((c + t)⁻¹) ^ 2 - (2 * lam) * (c + t)⁻¹) μ :=
    hi2.sub (hi1.const_mul (2 * lam))
  rw [integral_add hi_sub (integrable_const (lam ^ 2)),
      integral_sub hi2 (hi1.const_mul (2 * lam)),
      integral_mul_left, integral_const, measure_univ] at hnn
  simp only [ENNReal.one_toReal, smul_eq_mul, one_mul] at hnn
  have hU1_eq : ∫ c, (c + t)⁻¹ ∂μ = lam := rfl
  rw [hU1_eq] at hnn
  linarith

/-- Reciprocal-Concavity Lemma part (c): `F''(t) ≤ 0` for all `t > 0` (via Cauchy-Schwarz). -/
theorem F_deriv2_le_zero (hsupp : ∀ᵐ c ∂μ, 0 < c) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (F μ)) t ≤ 0 := by
  have heq_on : Set.EqOn (deriv (F μ)) (FDeriv μ) (Set.Ioi 0) := fun x hx =>
    (hasDerivAt_F μ hsupp hx).deriv
  have heq_ev : deriv (F μ) =ᶠ[𝓝 t] FDeriv μ :=
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht) heq_on
  rw [Filter.EventuallyEq.deriv_eq heq_ev, (hasDerivAt_FDeriv μ hsupp ht).deriv]
  unfold FDeriv2 U1Deriv U1Deriv2
  have hU1_pos : 0 < U1 μ t := U1_pos μ hsupp ht
  refine div_nonpos_of_nonpos_of_nonneg ?_ (pow_nonneg hU1_pos.le 3)
  -- Need: (∫ a^2)^2 ≤ (∫ a) * (∫ a^3), proved from 0 ≤ ∫ a * (1 - lam * a)^2 dμ
  set I1 := ∫ c, (c + t)⁻¹ ∂μ
  set I2 := ∫ c, ((c + t)⁻¹) ^ 2 ∂μ
  set I3 := ∫ c, ((c + t)⁻¹) ^ 3 ∂μ
  have hi1 : Integrable (fun c : ℝ => (c + t)⁻¹) μ := by
    simpa using integrable_inv_pow μ hsupp ht 1
  have hi2 : Integrable (fun c : ℝ => ((c + t)⁻¹) ^ 2) μ :=
    integrable_inv_pow μ hsupp ht 2
  have hi3 : Integrable (fun c : ℝ => ((c + t)⁻¹) ^ 3) μ :=
    integrable_inv_pow μ hsupp ht 3
  have hI3_pos : 0 < I3 := by
    have hnn3 : 0 ≤ᵐ[μ] (fun c : ℝ => ((c + t)⁻¹) ^ 3) := by
      filter_upwards [hsupp] with c hc
      have : 0 < c + t := by linarith
      positivity
    rw [integral_pos_iff_support_of_nonneg_ae hnn3 hi3]
    have hsup : μ (Function.support (fun c : ℝ => ((c + t)⁻¹) ^ 3)) = μ Set.univ := by
      apply measure_congr
      filter_upwards [hsupp] with c hc
      have hct : 0 < c + t := by linarith
      show (c ∈ Function.support (fun c : ℝ => ((c + t)⁻¹) ^ 3)) = (c ∈ (Set.univ : Set ℝ))
      exact propext ⟨fun _ => Set.mem_univ c, fun _ => Function.mem_support.mpr (ne_of_gt (pow_pos (inv_pos.mpr hct) 3))⟩
    rw [hsup, measure_univ]
    exact zero_lt_one
  set lam := I2 / I3
  have hnn : 0 ≤ ∫ c, (c + t)⁻¹ * (1 - lam * (c + t)⁻¹) ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hsupp] with c hc
    have hct : 0 < c + t := by linarith
    positivity
  have hexp :
      (fun c : ℝ => (c + t)⁻¹ * (1 - lam * (c + t)⁻¹) ^ 2) =
      fun c => ((c + t)⁻¹ - (2 * lam) * ((c + t)⁻¹) ^ 2) + (lam ^ 2) * ((c + t)⁻¹) ^ 3 := by
    ext c; ring
  rw [hexp] at hnn
  have hi_sub : Integrable (fun c : ℝ => (c + t)⁻¹ - (2 * lam) * ((c + t)⁻¹) ^ 2) μ :=
    hi1.sub (hi2.const_mul (2 * lam))
  rw [integral_add hi_sub (hi3.const_mul (lam ^ 2)),
      integral_sub hi1 (hi2.const_mul (2 * lam)),
      integral_mul_left, integral_mul_left] at hnn
  have hcs : I2 ^ 2 ≤ I1 * I3 := by
    have hmul := mul_nonneg hnn hI3_pos.le
    have hid :
        (I1 - 2 * lam * I2 + lam ^ 2 * I3) * I3 = I1 * I3 - I2 ^ 2 := by
      dsimp [lam]
      field_simp [hI3_pos.ne']
      ring
    linarith
  have hU1_eq : U1 μ t = I1 := rfl
  rw [hU1_eq]
  nlinarith

/-- Reciprocal-Concavity Lemma: `F(t) = 1 / U_1(t)` is concave on `(0, ∞)`. -/
theorem F_concaveOn (hsupp : ∀ᵐ c ∂μ, 0 < c) :
    ConcaveOn ℝ (Set.Ioi 0) (F μ) := by
  have hf_diff : DifferentiableOn ℝ (F μ) (Set.Ioi 0) := fun t ht =>
    (hasDerivAt_F μ hsupp ht).differentiableAt.differentiableWithinAt
  have hf_cont : ContinuousOn (F μ) (Set.Ioi 0) := hf_diff.continuousOn
  have heq_on : Set.EqOn (deriv (F μ)) (FDeriv μ) (Set.Ioi 0) := fun x hx =>
    (hasDerivAt_F μ hsupp hx).deriv
  have hf'_diff : DifferentiableOn ℝ (deriv (F μ)) (Set.Ioi 0) := by
    rw [differentiableOn_congr heq_on]
    intro t ht
    exact (hasDerivAt_FDeriv μ hsupp ht).differentiableAt.differentiableWithinAt
  refine concaveOn_of_deriv2_nonpos (convex_Ioi 0) hf_cont ?_ ?_ ?_
  · rwa [interior_Ioi]
  · rwa [interior_Ioi]
  · intro t ht
    rw [interior_Ioi] at ht
    simpa [Function.iterate_succ, Function.iterate_zero] using F_deriv2_le_zero μ hsupp ht

end ReciprocalConcavity

section DiscreteCapMeasure

/-- Explicit discrete cap probability measure `μ = ∑_j (r_j / S) δ_{c_j}` for `m ≥ 1` items
    with strictly positive revenues `r_j > 0` and strictly positive caps `c_j > 0`. -/
noncomputable def capMeasure {m : ℕ} (r c : Fin m → ℝ) : Measure ℝ :=
  ∑ j : Fin m, ENNReal.ofReal (r j / ∑ i : Fin m, r i) • Measure.dirac (c j)

lemma capSum_pos {m : ℕ} (hm : 0 < m) (r : Fin m → ℝ) (hr : ∀ j, 0 < r j) :
    0 < ∑ i : Fin m, r i := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty

/-- `capMeasure r c` is a valid probability measure (`μ Set.univ = 1`). -/
theorem capMeasure_isProbabilityMeasure {m : ℕ} (hm : 0 < m)
    (r c : Fin m → ℝ) (hr : ∀ j, 0 < r j) :
    IsProbabilityMeasure (capMeasure r c) := by
  constructor
  have hS : 0 < ∑ i : Fin m, r i := capSum_pos hm r hr
  unfold capMeasure
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.coe_smul, Pi.smul_apply,
             smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ,
             Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => div_nonneg (hr j).le hS.le)]
  have hsum_one : ∑ j : Fin m, r j / ∑ i : Fin m, r i = 1 := by
    rw [← Finset.sum_div, div_self hS.ne']
  rw [hsum_one, ENNReal.ofReal_one]

/-- `capMeasure r c` is supported strictly on `(0, ∞)` (`∀ᵐ x ∂μ, 0 < x`). -/
theorem capMeasure_ae_pos {m : ℕ} (r c : Fin m → ℝ) (hc : ∀ j, 0 < c j) :
    ∀ᵐ x ∂(capMeasure r c), 0 < x := by
  rw [ae_iff]
  unfold capMeasure
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.coe_smul, Pi.smul_apply,
             smul_eq_mul]
  apply Finset.sum_eq_zero
  intro j _
  have hset : {x : ℝ | ¬ 0 < x} = Set.Iic 0 := by ext x; simp
  have hnot : c j ∉ Set.Iic (0 : ℝ) := by simp [hc j]
  have hdir : Measure.dirac (c j) {x : ℝ | ¬ 0 < x} = 0 := by
    rw [hset, Measure.dirac_apply' _ measurableSet_Iic]
    simp [hnot]
  rw [hdir, mul_zero]

end DiscreteCapMeasure

section MomentLensAndEnvelope

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- Concave hyperbola map `φ_{ij}(g) = g / (1 + (l_j - l_i) * g)`. -/
noncomputable def phiMap (dl g : ℝ) : ℝ := g / (1 + dl * g)

/-- Lemma 4(i): Monotonicity ratios `γ₂ ≥ (l₁/l₂) γ₁` and `γ₃ ≥ (l₂/l₃) γ₂`. -/
theorem lens_ineq_i (hsupp : ∀ᵐ c ∂μ, 0 < c) {l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₁₂ : l₁ < l₂) :
    (l₁ / l₂) * U1 μ l₁ ≤ U1 μ l₂ := by
  have hl₂ : 0 < l₂ := lt_trans hl₁ hl₁₂
  unfold U1
  rw [← integral_mul_left]
  have hi1_base : Integrable (fun c : ℝ => (c + l₁)⁻¹) μ := by
    simpa using integrable_inv_pow μ hsupp hl₁ 1
  have hi1 : Integrable (fun c : ℝ => (l₁ / l₂) * (c + l₁)⁻¹) μ := hi1_base.const_mul _
  have hi2 : Integrable (fun c : ℝ => (c + l₂)⁻¹) μ := by
    simpa using integrable_inv_pow μ hsupp hl₂ 1
  apply integral_mono_ae hi1 hi2
  filter_upwards [hsupp] with c hc
  have hc1 : 0 < c + l₁ := by linarith
  have hc2 : 0 < c + l₂ := by linarith
  have hL : (l₁ / l₂) * (c + l₁)⁻¹ = l₁ / (l₂ * (c + l₁)) := by
    field_simp [hl₂.ne', hc1.ne']
  have hR : (c + l₂)⁻¹ = 1 / (c + l₂) := (one_div _).symm
  rw [hL, hR, div_le_div_iff₀ (mul_pos hl₂ hc1) hc2]
  nlinarith

/-- Helper: `F(t₂) ≥ F(t₁) + (t₂ - t₁)` for `0 < t₁ ≤ t₂` (from `F'(t) ≥ 1`). -/
theorem F_sub_ge (hsupp : ∀ᵐ c ∂μ, 0 < c) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (hle : t₁ ≤ t₂) :
    F μ t₁ + (t₂ - t₁) ≤ F μ t₂ := by
  by_cases heq : t₁ = t₂
  · subst heq; linarith
  · have hlt : t₁ < t₂ := lt_of_le_of_ne hle heq
    -- Apply MVT to g(t) = F(t) - t on [t₁, t₂]
    let g : ℝ → ℝ := fun t => F μ t - t
    have hg_cont : ContinuousOn g (Set.Icc t₁ t₂) := by
      intro x hx
      have hx_pos : 0 < x := lt_of_lt_of_le ht₁ hx.1
      exact ((hasDerivAt_F μ hsupp hx_pos).sub (hasDerivAt_id x)).continuousAt.continuousWithinAt
    have hg_deriv : ∀ x ∈ Set.Ioo t₁ t₂, 0 ≤ deriv g x := by
      intro x hx
      have hx_pos : 0 < x := lt_trans ht₁ hx.1
      have hd : HasDerivAt g (FDeriv μ x - 1) x :=
        (hasDerivAt_F μ hsupp hx_pos).sub (hasDerivAt_id x)
      rw [hd.deriv]
      have h1 := F_deriv_ge_one μ hsupp hx_pos
      rw [(hasDerivAt_F μ hsupp hx_pos).deriv] at h1
      linarith
    have hg_diff : DifferentiableOn ℝ g (Set.Ioo t₁ t₂) := fun x hx =>
      ((hasDerivAt_F μ hsupp (lt_trans ht₁ hx.1)).sub (hasDerivAt_id x)).differentiableAt.differentiableWithinAt
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc t₁ t₂) hg_cont
      (by rwa [interior_Icc]) (by intro x hx; rw [interior_Icc] at hx; exact hg_deriv x hx)
    have hle' := hmono (Set.left_mem_Icc.mpr hle) (Set.right_mem_Icc.mpr hle) hle
    dsimp [g] at hle'
    linarith

/-- Lemma 4(ii): Nonlinear hyperbolic upper bound `γ_j ≤ γ_i / (1 + (l_j - l_i) γ_i)`. -/
theorem lens_ineq_ii (hsupp : ∀ᵐ c ∂μ, 0 < c) {l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hle : l₁ ≤ l₂) :
    U1 μ l₂ ≤ phiMap (l₂ - l₁) (U1 μ l₁) := by
  have hl₂ : 0 < l₂ := lt_of_lt_of_le hl₁ hle
  have h1 : 0 < U1 μ l₁ := U1_pos μ hsupp hl₁
  have h2 : 0 < U1 μ l₂ := U1_pos μ hsupp hl₂
  have hF := F_sub_ge μ hsupp hl₁ hle
  unfold F at hF
  unfold phiMap
  have hden : 0 < 1 + (l₂ - l₁) * U1 μ l₁ := by nlinarith
  rw [le_div_iff₀ hden]
  have hmul := mul_le_mul_of_nonneg_left hF (mul_pos h1 h2).le
  have hL : U1 μ l₁ * U1 μ l₂ * ((U1 μ l₁)⁻¹ + (l₂ - l₁)) =
      U1 μ l₂ * (1 + (l₂ - l₁) * U1 μ l₁) := by
    field_simp [h1.ne', h2.ne']
    ring
  have hR : U1 μ l₁ * U1 μ l₂ * (U1 μ l₂)⁻¹ = U1 μ l₁ := by
    field_simp [h2.ne']
  linarith

/-- Lemma 4(ii) tangent plane: for every `g₀ ≥ 0`, `dl ≥ 0`, `g ≥ 0`,
    `phiMap dl g ≤ g₀ / (1 + dl * g₀) + (g - g₀) / (1 + dl * g₀)^2`. -/
theorem phiMap_tangent_le {dl g₀ g : ℝ} (hdl : 0 ≤ dl) (hg₀ : 0 ≤ g₀) (hg : 0 ≤ g) :
    phiMap dl g ≤ g₀ / (1 + dl * g₀) + (g - g₀) / (1 + dl * g₀) ^ 2 := by
  unfold phiMap
  have d1 : 0 < 1 + dl * g := by nlinarith
  have d0 : 0 < 1 + dl * g₀ := by nlinarith
  have hdiff :
      g₀ / (1 + dl * g₀) + (g - g₀) / (1 + dl * g₀) ^ 2 - g / (1 + dl * g) =
      dl * (g - g₀) ^ 2 / ((1 + dl * g₀) ^ 2 * (1 + dl * g)) := by
    field_simp [d1.ne', d0.ne']
    ring
  have hnn : 0 ≤ dl * (g - g₀) ^ 2 / ((1 + dl * g₀) ^ 2 * (1 + dl * g)) := by positivity
  linarith

/-- Lemma 4(iii): Secant lower bound `A_sec * γ₁ + B_sec * γ₃ ≤ γ₂`. -/
theorem lens_ineq_iii (hsupp : ∀ᵐ c ∂μ, 0 < c) {l₁ l₂ l₃ : ℝ}
    (hl₁ : 0 < l₁) (hl₁₂ : l₁ < l₂) (hl₂₃ : l₂ < l₃) :
    let A := l₁ * (l₃ - l₂) / (l₂ * (l₃ - l₁))
    let B := l₃ * (l₂ - l₁) / (l₂ * (l₃ - l₁))
    A * U1 μ l₁ + B * U1 μ l₃ ≤ U1 μ l₂ := by
  intro A B
  have hl₂ : 0 < l₂ := lt_trans hl₁ hl₁₂
  have hl₃ : 0 < l₃ := lt_trans hl₂ hl₂₃
  have hl₁₃ : 0 < l₃ - l₁ := by linarith
  unfold U1
  have hi1 : Integrable (fun c : ℝ => (c + l₁)⁻¹) μ := by simpa using integrable_inv_pow μ hsupp hl₁ 1
  have hi2 : Integrable (fun c : ℝ => (c + l₂)⁻¹) μ := by simpa using integrable_inv_pow μ hsupp hl₂ 1
  have hi3 : Integrable (fun c : ℝ => (c + l₃)⁻¹) μ := by simpa using integrable_inv_pow μ hsupp hl₃ 1
  rw [← integral_mul_left, ← integral_mul_left,
      ← integral_add (hi1.const_mul A) (hi3.const_mul B)]
  apply integral_mono_ae ((hi1.const_mul A).add (hi3.const_mul B)) hi2
  filter_upwards [hsupp] with c hc
  have hc1 : 0 < c + l₁ := by linarith
  have hc2 : 0 < c + l₂ := by linarith
  have hc3 : 0 < c + l₃ := by linarith
  have hdiff :
      (c + l₂)⁻¹ - (A * (c + l₁)⁻¹ + B * (c + l₃)⁻¹) =
      c * (l₂ - l₁) * (l₃ - l₂) / (l₂ * (c + l₁) * (c + l₂) * (c + l₃)) := by
    dsimp [A, B]
    field_simp [hl₂.ne', hl₁₃.ne', hc1.ne', hc2.ne', hc3.ne']
    ring
  have hnn : 0 ≤ c * (l₂ - l₁) * (l₃ - l₂) / (l₂ * (c + l₁) * (c + l₂) * (c + l₃)) := by
    have : 0 < l₂ - l₁ := by linarith
    have : 0 < l₃ - l₂ := by linarith
    positivity
  simp only [Pi.add_apply]
  linarith [hdiff, hnn]

/-- Lemma 4(iv): Convexity upper bound `γ₂ ≤ (1 - θ₁₃) γ₁ + θ₁₃ γ₃`. -/
theorem lens_ineq_iv (hsupp : ∀ᵐ c ∂μ, 0 < c) {l₁ l₂ l₃ : ℝ}
    (hl₁ : 0 < l₁) (hl₁₂ : l₁ < l₂) (hl₂₃ : l₂ < l₃) :
    let th := (l₂ - l₁) / (l₃ - l₁)
    U1 μ l₂ ≤ (1 - th) * U1 μ l₁ + th * U1 μ l₃ := by
  intro th
  have hl₂ : 0 < l₂ := lt_trans hl₁ hl₁₂
  have hl₃ : 0 < l₃ := lt_trans hl₂ hl₂₃
  have hl₁₃ : 0 < l₃ - l₁ := by linarith
  unfold U1
  have hi1 : Integrable (fun c : ℝ => (c + l₁)⁻¹) μ := by simpa using integrable_inv_pow μ hsupp hl₁ 1
  have hi2 : Integrable (fun c : ℝ => (c + l₂)⁻¹) μ := by simpa using integrable_inv_pow μ hsupp hl₂ 1
  have hi3 : Integrable (fun c : ℝ => (c + l₃)⁻¹) μ := by simpa using integrable_inv_pow μ hsupp hl₃ 1
  rw [← integral_mul_left, ← integral_mul_left,
      ← integral_add (hi1.const_mul (1 - th)) (hi3.const_mul th)]
  apply integral_mono_ae hi2 ((hi1.const_mul (1 - th)).add (hi3.const_mul th))
  filter_upwards [hsupp] with c hc
  have hc1 : 0 < c + l₁ := by linarith
  have hc2 : 0 < c + l₂ := by linarith
  have hc3 : 0 < c + l₃ := by linarith
  have hdiff :
      (1 - th) * (c + l₁)⁻¹ + th * (c + l₃)⁻¹ - (c + l₂)⁻¹ =
      (l₂ - l₁) * (l₃ - l₂) / ((c + l₁) * (c + l₂) * (c + l₃)) := by
    dsimp [th]
    field_simp [hl₁₃.ne', hc1.ne', hc2.ne', hc3.ne']
    ring
  have hnn : 0 ≤ (l₂ - l₁) * (l₃ - l₂) / ((c + l₁) * (c + l₂) * (c + l₃)) := by
    have : 0 < l₂ - l₁ := by linarith
    have : 0 < l₃ - l₂ := by linarith
    positivity
  simp only [Pi.add_apply]
  linarith [hdiff, hnn]

/-- Lemma 4(v) nonlinear harmonic bound: `γ₂ ≤ ((1 - θ₁₃)/γ₁ + θ₁₃/γ₃)⁻¹`. -/
theorem lens_ineq_v (hsupp : ∀ᵐ c ∂μ, 0 < c) {l₁ l₂ l₃ : ℝ}
    (hl₁ : 0 < l₁) (hl₁₂ : l₁ < l₂) (hl₂₃ : l₂ < l₃) :
    let th := (l₂ - l₁) / (l₃ - l₁)
    U1 μ l₂ ≤ ((1 - th) / U1 μ l₁ + th / U1 μ l₃)⁻¹ := by
  intro th
  have hl₂ : 0 < l₂ := lt_trans hl₁ hl₁₂
  have hl₃ : 0 < l₃ := lt_trans hl₂ hl₂₃
  have hl₁₃ : 0 < l₃ - l₁ := by linarith
  have hth0 : 0 ≤ th := div_nonneg (by linarith) hl₁₃.le
  have h1th0 : 0 ≤ 1 - th := by
    dsimp [th]
    rw [sub_nonneg, div_le_one hl₁₃]
    linarith
  have hsum : (1 - th) + th = 1 := by ring
  have hcomb : (1 - th) • l₁ + th • l₃ = l₂ := by
    rw [smul_eq_mul, smul_eq_mul]
    dsimp [th]
    field_simp [hl₁₃.ne']
    ring
  have hconc := (F_concaveOn μ hsupp).2 hl₁ hl₃ h1th0 hth0 hsum
  rw [hcomb, smul_eq_mul, smul_eq_mul] at hconc
  unfold F at hconc
  have hU1_1 : 0 < U1 μ l₁ := U1_pos μ hsupp hl₁
  have hU1_2 : 0 < U1 μ l₂ := U1_pos μ hsupp hl₂
  have hU1_3 : 0 < U1 μ l₃ := U1_pos μ hsupp hl₃
  have hden_pos : 0 < (1 - th) / U1 μ l₁ + th / U1 μ l₃ := by
    have : 0 < th := div_pos (by linarith) hl₁₃
    positivity
  have hconc' : (1 - th) / U1 μ l₁ + th / U1 μ l₃ ≤ (U1 μ l₂)⁻¹ := by
    simpa [div_eq_mul_inv] using hconc
  calc
    U1 μ l₂ = ((U1 μ l₂)⁻¹)⁻¹ := (inv_inv _).symm
    _ ≤ ((1 - th) / U1 μ l₁ + th / U1 μ l₃)⁻¹ := inv_anti₀ hden_pos hconc'

/-- Lemma 4(v) linear harmonic tangent plane: for all `p > 0`, `q > 0`, `θ ∈ (0, 1)`, `γ₁, γ₃ > 0`,
    `((1-θ)/γ₁ + θ/γ₃)⁻¹ ≤ ((1-θ) p² / ((1-θ) p + θ q)²) γ₁ + (θ q² / ((1-θ) p + θ q)²) γ₃`. -/
theorem harmonic_tangent_le {th g₁ g₃ p q : ℝ}
    (hth0 : 0 < th) (hth1 : th < 1) (hg₁ : 0 < g₁) (hg₃ : 0 < g₃) (hp : 0 < p) (hq : 0 < q) :
    ((1 - th) / g₁ + th / g₃)⁻¹ ≤
      ((1 - th) * p ^ 2 / ((1 - th) * p + th * q) ^ 2) * g₁ +
      (th * q ^ 2 / ((1 - th) * p + th * q) ^ 2) * g₃ := by
  have h1th : 0 < 1 - th := by linarith
  have hden1 : 0 < (1 - th) / g₁ + th / g₃ := by positivity
  have hden2 : 0 < (1 - th) * p + th * q := by positivity
  rw [inv_le_iff_one_le_mul₀' hden1]
  have hcs :
      ((1 - th) / g₁ + th / g₃) * ((1 - th) * p ^ 2 * g₁ + th * q ^ 2 * g₃) -
        ((1 - th) * p + th * q) ^ 2 =
      (1 - th) * th * (p * g₁ - q * g₃) ^ 2 / (g₁ * g₃) := by
    field_simp [hg₁.ne', hg₃.ne']
    ring
  have hnn : 0 ≤ (1 - th) * th * (p * g₁ - q * g₃) ^ 2 / (g₁ * g₃) := by positivity
  have hprod : ((1 - th) * p + th * q) ^ 2 ≤
      ((1 - th) / g₁ + th / g₃) * ((1 - th) * p ^ 2 * g₁ + th * q ^ 2 * g₃) := by linarith
  have hrewrite :
      ((1 - th) / g₁ + th / g₃) *
        (((1 - th) * p ^ 2 / ((1 - th) * p + th * q) ^ 2) * g₁ +
         (th * q ^ 2 / ((1 - th) * p + th * q) ^ 2) * g₃) =
      (((1 - th) / g₁ + th / g₃) * ((1 - th) * p ^ 2 * g₁ + th * q ^ 2 * g₃)) /
        ((1 - th) * p + th * q) ^ 2 := by
    ring
  rw [hrewrite, one_le_div (pow_pos hden2 2)]
  exact hprod

/-- Corollary 4: Component branch `u_i(t)` of the harmonic-secant upper envelope. -/
noncomputable def uBranch (li gbar t : ℝ) : ℝ :=
  if t ≤ li then (li / t) * gbar else (gbar⁻¹ - li + t)⁻¹

/-- Corollary 4: Secant branch `s_i(t)` on `[l_i, l_{i+1}]`. -/
noncomputable def sBranch (la lb ga gb t : ℝ) : ℝ :=
  (((lb - t) / (lb - la)) * ga⁻¹ + ((t - la) / (lb - la)) * gb⁻¹)⁻¹

/-- Corollary 4: Full harmonic-secant upper envelope `Ubar(t; gbar)`. -/
noncomputable def Ubar (l₁ l₂ l₃ g₁ g₂ g₃ t : ℝ) : ℝ :=
  let u0 := min (t⁻¹) (min (uBranch l₁ g₁ t) (min (uBranch l₂ g₂ t) (uBranch l₃ g₃ t)))
  let u1 := if l₁ ≤ t ∧ t ≤ l₂ then min u0 (sBranch l₁ l₂ g₁ g₂ t) else u0
  if l₂ ≤ t ∧ t ≤ l₃ then min u1 (sBranch l₂ l₃ g₂ g₃ t) else u1

lemma U1_le_uBranch (hsupp : ∀ᵐ c ∂μ, 0 < c) {li gbar t : ℝ}
    (hli : 0 < li) (ht : 0 < t)
    (hg : U1 μ li ≤ gbar) (hg_le : gbar ≤ li⁻¹) :
    U1 μ t ≤ uBranch li gbar t := by
  have hUli : 0 < U1 μ li := U1_pos μ hsupp hli
  have hUt : 0 < U1 μ t := U1_pos μ hsupp ht
  have hgbar_pos : 0 < gbar := lt_of_lt_of_le hUli hg
  unfold uBranch
  split_ifs with htle
  · -- 0 < t ≤ li: concavity on (s, t, li) for any s ∈ (0, t) gives F(t) ≥ (t - s)/(li - s) * F(li)
    have hF_ge : (t / li) * F μ li ≤ F μ t := by
      by_cases hteq : t = li
      · subst hteq; simp [div_self hli.ne']
      · have htlt : t < li := lt_of_le_of_ne htle hteq
        by_contra hlt_F
        push_neg at hlt_F
        set δ := (t / li) * F μ li - F μ t
        have hδ : 0 < δ := sub_pos.mpr hlt_F
        have hFli_pos : 0 < F μ li := inv_pos.mpr hUli
        -- Choose s ∈ (0, t) small enough that (t - s)/(li - s) * F(li) > F(t)
        set s := min (t / 2) (δ * li / (2 * F μ li))
        have hs_pos : 0 < s := lt_min (half_pos ht) (by positivity)
        have hs_lt_t : s < t := lt_of_le_of_lt (min_le_left _ _) (half_lt_self ht)
        have hs_lt_li : s < li := lt_trans hs_lt_t htlt
        have hls_pos : 0 < li - s := sub_pos.mpr hs_lt_li
        set a := (li - t) / (li - s)
        set b := (t - s) / (li - s)
        have ha : 0 ≤ a := div_nonneg (by linarith) hls_pos.le
        have hb : 0 ≤ b := div_nonneg (by linarith) hls_pos.le
        have hab : a + b = 1 := by dsimp [a, b]; field_simp [hls_pos.ne']
        have hcomb : a • s + b • li = t := by
          rw [smul_eq_mul, smul_eq_mul]; dsimp [a, b]; field_simp [hls_pos.ne']; ring
        have hconc := (F_concaveOn μ hsupp).2 hs_pos hli ha hb hab
        rw [hcomb, smul_eq_mul, smul_eq_mul] at hconc
        have hFs_pos : 0 ≤ F μ s := le_trans hs_pos.le (F_ge_self μ hsupp hs_pos)
        have hbF : b * F μ li ≤ F μ t := by nlinarith
        -- Show (t/li - b) * F(li) = s * (li - t) / (li * (li - s)) * F(li) ≤ (s / li) * F(li) ≤ δ / 2
        have hgap : (t / li - b) * F μ li = (s * (li - t) / (li * (li - s))) * F μ li := by
          have hb_eq : t / li - b = s * (li - t) / (li * (li - s)) := by
            dsimp [b]; field_simp [hli.ne', hls_pos.ne']; ring
          rw [hb_eq]
        have hratio : s * (li - t) / (li * (li - s)) ≤ s / li := by
          rw [div_le_div_iff₀ (mul_pos hli hls_pos) hli]
          have hts : 0 < t - s := sub_pos.mpr hs_lt_t
          have hneg : 0 ≤ s * li * (t - s) := mul_nonneg (mul_nonneg hs_pos.le hli.le) hts.le
          have hsub : s * (li - t) * li - s * (li * (li - s)) = -(s * li * (t - s)) := by ring
          linarith
        have hgap_le : (t / li - b) * F μ li ≤ (s / li) * F μ li := by
          rw [hgap]
          exact mul_le_mul_of_nonneg_right hratio hFli_pos.le
        have hs_bound : (s / li) * F μ li ≤ δ / 2 := by
          have hs2 : s ≤ δ * li / (2 * F μ li) := min_le_right _ _
          have := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs2 hli.le) hFli_pos.le
          have hsimp : δ * li / (2 * F μ li) / li * F μ li = δ / 2 := by
            field_simp [hli.ne', hFli_pos.ne']
            ring
          linarith
        linarith
    have hinv_le : gbar⁻¹ ≤ (U1 μ li)⁻¹ := inv_anti₀ hUli hg
    have hF_ge' : (t / li) * gbar⁻¹ ≤ F μ t :=
      le_trans (mul_le_mul_of_nonneg_left hinv_le (by positivity)) hF_ge
    unfold F at hF_ge'
    have hpos_lhs : 0 < (t / li) * gbar⁻¹ := by positivity
    calc
      U1 μ t = ((U1 μ t)⁻¹)⁻¹ := (inv_inv _).symm
      _ ≤ ((t / li) * gbar⁻¹)⁻¹ := inv_anti₀ hpos_lhs hF_ge'
      _ = (li / t) * gbar := by field_simp [hli.ne', ht.ne', hgbar_pos.ne']
  · -- t > li: F(t) ≥ F(li) + (t - li) ≥ gbar⁻¹ - li + t > 0
    push_neg at htle
    have hF := F_sub_ge μ hsupp hli htle.le
    unfold F at hF
    have hinv_le : gbar⁻¹ ≤ (U1 μ li)⁻¹ := inv_anti₀ hUli hg
    have hli_le : li ≤ gbar⁻¹ := by
      calc li = (li⁻¹)⁻¹ := (inv_inv li).symm
        _ ≤ gbar⁻¹ := inv_anti₀ hgbar_pos hg_le
    have hden_pos : 0 < gbar⁻¹ - li + t := by linarith
    have hle' : gbar⁻¹ - li + t ≤ (U1 μ t)⁻¹ := by linarith
    calc
      U1 μ t = ((U1 μ t)⁻¹)⁻¹ := (inv_inv _).symm
      _ ≤ (gbar⁻¹ - li + t)⁻¹ := inv_anti₀ hden_pos hle'

lemma U1_le_sBranch (hsupp : ∀ᵐ c ∂μ, 0 < c) {la lb ga gb t : ℝ}
    (hla : 0 < la) (hlab : la < lb) (ht1 : la ≤ t) (ht2 : t ≤ lb)
    (hga : U1 μ la ≤ ga) (hgb : U1 μ lb ≤ gb) :
    U1 μ t ≤ sBranch la lb ga gb t := by
  have hlb : 0 < lb := lt_trans hla hlab
  have hUa : 0 < U1 μ la := U1_pos μ hsupp hla
  have hUb : 0 < U1 μ lb := U1_pos μ hsupp hlb
  have hga_pos : 0 < ga := lt_of_lt_of_le hUa hga
  have hgb_pos : 0 < gb := lt_of_lt_of_le hUb hgb
  have hdl : 0 < lb - la := sub_pos.mpr hlab
  set a := (lb - t) / (lb - la)
  set b := (t - la) / (lb - la)
  have ha : 0 ≤ a := div_nonneg (by linarith) hdl.le
  have hb : 0 ≤ b := div_nonneg (by linarith) hdl.le
  have hab : a + b = 1 := by dsimp [a, b]; field_simp [hdl.ne']
  have hcomb : a • la + b • lb = t := by
    rw [smul_eq_mul, smul_eq_mul]; dsimp [a, b]; field_simp [hdl.ne']; ring
  have hconc := (F_concaveOn μ hsupp).2 hla hlb ha hb hab
  rw [hcomb, smul_eq_mul, smul_eq_mul] at hconc
  unfold F at hconc
  have hia : ga⁻¹ ≤ (U1 μ la)⁻¹ := inv_anti₀ hUa hga
  have hib : gb⁻¹ ≤ (U1 μ lb)⁻¹ := inv_anti₀ hUb hgb
  have hle : a * ga⁻¹ + b * gb⁻¹ ≤ (U1 μ t)⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_left hia ha
    have h2 := mul_le_mul_of_nonneg_left hib hb
    linarith
  have hpos_lhs : 0 < a * ga⁻¹ + b * gb⁻¹ := by
    have hm1 : a * min ga⁻¹ gb⁻¹ ≤ a * ga⁻¹ := mul_le_mul_of_nonneg_left (min_le_left _ _) ha
    have hm2 : b * min ga⁻¹ gb⁻¹ ≤ b * gb⁻¹ := mul_le_mul_of_nonneg_left (min_le_right _ _) hb
    have hsum_m : a * min ga⁻¹ gb⁻¹ + b * min ga⁻¹ gb⁻¹ = min ga⁻¹ gb⁻¹ := by
      rw [← add_mul, hab, one_mul]
    have hmin_pos : 0 < min ga⁻¹ gb⁻¹ := lt_min (inv_pos.mpr hga_pos) (inv_pos.mpr hgb_pos)
    linarith
  unfold sBranch
  calc
    U1 μ t = ((U1 μ t)⁻¹)⁻¹ := (inv_inv _).symm
    _ ≤ (a * ga⁻¹ + b * gb⁻¹)⁻¹ := inv_anti₀ hpos_lhs hle

/-- Corollary 4 (`cor:ubar`): `U_1(t) ≤ Ubar(t; gbar) ≤ t⁻¹` for all `t > 0`. -/
theorem U1_le_Ubar_le_inv (hsupp : ∀ᵐ c ∂μ, 0 < c) {l₁ l₂ l₃ g₁ g₂ g₃ t : ℝ}
    (hl₁ : 0 < l₁) (hl₁₂ : l₁ < l₂) (hl₂₃ : l₂ < l₃) (ht : 0 < t)
    (hg₁ : U1 μ l₁ ≤ g₁) (hg₁_le : g₁ ≤ l₁⁻¹)
    (hg₂ : U1 μ l₂ ≤ g₂) (hg₂_le : g₂ ≤ l₂⁻¹)
    (hg₃ : U1 μ l₃ ≤ g₃) (hg₃_le : g₃ ≤ l₃⁻¹) :
    U1 μ t ≤ Ubar l₁ l₂ l₃ g₁ g₂ g₃ t ∧ Ubar l₁ l₂ l₃ g₁ g₂ g₃ t ≤ t⁻¹ := by
  have hl₂ : 0 < l₂ := lt_trans hl₁ hl₁₂
  have hl₃ : 0 < l₃ := lt_trans hl₂ hl₂₃
  have h0 : U1 μ t ≤ t⁻¹ := U1_le_inv μ hsupp ht
  have hu1 : U1 μ t ≤ uBranch l₁ g₁ t := U1_le_uBranch μ hsupp hl₁ ht hg₁ hg₁_le
  have hu2 : U1 μ t ≤ uBranch l₂ g₂ t := U1_le_uBranch μ hsupp hl₂ ht hg₂ hg₂_le
  have hu3 : U1 μ t ≤ uBranch l₃ g₃ t := U1_le_uBranch μ hsupp hl₃ ht hg₃ hg₃_le
  have hu0_ge : U1 μ t ≤ min t⁻¹ (min (uBranch l₁ g₁ t) (min (uBranch l₂ g₂ t) (uBranch l₃ g₃ t))) :=
    le_min h0 (le_min hu1 (le_min hu2 hu3))
  have hu0_le : min t⁻¹ (min (uBranch l₁ g₁ t) (min (uBranch l₂ g₂ t) (uBranch l₃ g₃ t))) ≤ t⁻¹ :=
    min_le_left _ _
  unfold Ubar
  constructor
  · split_ifs with h12 h23 h23'
    · exact le_min (le_min hu0_ge (U1_le_sBranch μ hsupp hl₁ hl₁₂ h12.1 h12.2 hg₁ hg₂))
        (U1_le_sBranch μ hsupp hl₂ hl₂₃ h23.1 h23.2 hg₂ hg₃)
    · exact le_min hu0_ge (U1_le_sBranch μ hsupp hl₁ hl₁₂ h12.1 h12.2 hg₁ hg₂)
    · exact le_min hu0_ge (U1_le_sBranch μ hsupp hl₂ hl₂₃ h23'.1 h23'.2 hg₂ hg₃)
    · exact hu0_ge
  · split_ifs
    · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) hu0_le)
    · exact le_trans (min_le_left _ _) hu0_le
    · exact le_trans (min_le_left _ _) hu0_le
    · exact hu0_le

end MomentLensAndEnvelope

section PolytopeAndFarkas

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- The 14-row linear relaxation matrix `D ∈ ℝ^{14 × 3}` and RHS `d ∈ ℝ^{14}` of Section 5
    for a box `[g1a, g1b] × [g2a, g2b] × [g3a, g3b]` at scales `0 < l₁ < l₂ < l₃`. -/
noncomputable def polytopeDd (l₁ l₂ l₃ g1a g1b g2a g2b g3a g3b : ℝ) :
    (Fin 14 → Fin 3 → ℝ) × (Fin 14 → ℝ) :=
  let g1m := (g1a + g1b) / 2
  let g2m := (g2a + g2b) / 2
  let g3m := (g3a + g3b) / 2
  let A := l₁ * (l₃ - l₂) / (l₂ * (l₃ - l₁))
  let B := l₃ * (l₂ - l₁) / (l₂ * (l₃ - l₁))
  let th := (l₂ - l₁) / (l₃ - l₁)
  let d12 := 1 + (l₂ - l₁) * g1m
  let d23 := 1 + (l₃ - l₂) * g2m
  let d13 := 1 + (l₃ - l₁) * g1m
  let m12 := 1 / d12 ^ 2
  let r12 := g1m / d12 - g1m / d12 ^ 2
  let m23 := 1 / d23 ^ 2
  let r23 := g2m / d23 - g2m / d23 ^ 2
  let m13 := 1 / d13 ^ 2
  let r13 := g1m / d13 - g1m / d13 ^ 2
  let p := max g3m (1 / 1000000)
  let q := max g1m (1 / 1000000)
  let hd := ((1 - th) * p + th * q) ^ 2
  let h1 := (1 - th) * p ^ 2 / hd
  let h3 := th * q ^ 2 / hd
  let D : Fin 14 → Fin 3 → ℝ := fun r c =>
    match r.val, c.val with
    | 0, 0 => 1       | 0, _ => 0
    | 1, 0 => -1      | 1, _ => 0
    | 2, 1 => 1       | 2, _ => 0
    | 3, 1 => -1      | 3, _ => 0
    | 4, 2 => 1       | 4, _ => 0
    | 5, 2 => -1      | 5, _ => 0
    | 6, 0 => l₁ / l₂ | 6, 1 => -1 | 6, _ => 0
    | 7, 1 => l₂ / l₃ | 7, 2 => -1 | 7, _ => 0
    | 8, 0 => A       | 8, 1 => -1 | 8, 2 => B
    | 9, 0 => -(1 - th) | 9, 1 => 1 | 9, 2 => -th
    | 10, 0 => -m12   | 10, 1 => 1 | 10, _ => 0
    | 11, 1 => -m23   | 11, 2 => 1 | 11, _ => 0
    | 12, 0 => -m13   | 12, 2 => 1 | 12, _ => 0
    | 13, 0 => -h1    | 13, 1 => 1 | 13, 2 => -h3
    | _, _ => 0
  let d : Fin 14 → ℝ := fun r =>
    match r.val with
    | 0 => g1b  | 1 => -g1a
    | 2 => g2b  | 3 => -g2a
    | 4 => g3b  | 5 => -g3a
    | 6 => 0    | 7 => 0    | 8 => 0    | 9 => 0
    | 10 => r12 | 11 => r23 | 12 => r13 | 13 => 0
    | _ => 0
  (D, d)

/-- All 14 linear inequalities `D γ ≤ d` hold for every feasible moment triple `γ(μ) ∈ R ∩ L`. -/
theorem polytope_valid (hsupp : ∀ᵐ c ∂μ, 0 < c)
    {l₁ l₂ l₃ g1a g1b g2a g2b g3a g3b : ℝ}
    (hl₁ : 0 < l₁) (hl₁₂ : l₁ < l₂) (hl₂₃ : l₂ < l₃)
    (_hg1a : 0 ≤ g1a) (_hg2a : 0 ≤ g2a) (_hg3a : 0 ≤ g3a)
    (hb1 : g1a ≤ U1 μ l₁ ∧ U1 μ l₁ ≤ g1b)
    (hb2 : g2a ≤ U1 μ l₂ ∧ U1 μ l₂ ≤ g2b)
    (hb3 : g3a ≤ U1 μ l₃ ∧ U1 μ l₃ ≤ g3b) :
    let Dd := polytopeDd l₁ l₂ l₃ g1a g1b g2a g2b g3a g3b
    let γ : Fin 3 → ℝ := fun i => match i.val with | 0 => U1 μ l₁ | 1 => U1 μ l₂ | _ => U1 μ l₃
    ∀ r : Fin 14, ∑ c : Fin 3, Dd.1 r c * γ c ≤ Dd.2 r := by
  intro Dd γ r
  have hl₂ : 0 < l₂ := lt_trans hl₁ hl₁₂
  have hl₃ : 0 < l₃ := lt_trans hl₂ hl₂₃
  have hU1 : 0 < U1 μ l₁ := U1_pos μ hsupp hl₁
  have hU2 : 0 < U1 μ l₂ := U1_pos μ hsupp hl₂
  have hU3 : 0 < U1 μ l₃ := U1_pos μ hsupp hl₃
  have hg1m : 0 ≤ (g1a + g1b) / 2 := by linarith [hb1.1, hb1.2]
  have hg2m : 0 ≤ (g2a + g2b) / 2 := by linarith [hb2.1, hb2.2]
  rw [Fin.sum_univ_three]
  fin_cases r
  · -- row 0: γ1 ≤ g1b
    dsimp only [Dd, polytopeDd, γ]; linarith [hb1.2]
  · -- row 1: -γ1 ≤ -g1a
    dsimp only [Dd, polytopeDd, γ]; linarith [hb1.1]
  · -- row 2: γ2 ≤ g2b
    dsimp only [Dd, polytopeDd, γ]; linarith [hb2.2]
  · -- row 3: -γ2 ≤ -g2a
    dsimp only [Dd, polytopeDd, γ]; linarith [hb2.1]
  · -- row 4: γ3 ≤ g3b
    dsimp only [Dd, polytopeDd, γ]; linarith [hb3.2]
  · -- row 5: -γ3 ≤ -g3a
    dsimp only [Dd, polytopeDd, γ]; linarith [hb3.1]
  · -- row 6: (l1/l2) γ1 - γ2 ≤ 0
    have h := lens_ineq_i μ hsupp hl₁ hl₁₂
    dsimp only [Dd, polytopeDd, γ]; linarith
  · -- row 7: (l2/l3) γ2 - γ3 ≤ 0
    have h := lens_ineq_i μ hsupp hl₂ hl₂₃
    dsimp only [Dd, polytopeDd, γ]; linarith
  · -- row 8: A γ1 - γ2 + B γ3 ≤ 0
    have h := lens_ineq_iii μ hsupp hl₁ hl₁₂ hl₂₃
    dsimp only [Dd, polytopeDd, γ]; linarith
  · -- row 9: -(1-th) γ1 + γ2 - th γ3 ≤ 0
    have h := lens_ineq_iv μ hsupp hl₁ hl₁₂ hl₂₃
    dsimp only [Dd, polytopeDd, γ]; linarith
  · -- row 10: tangent (1, 2)
    have h1 := lens_ineq_ii μ hsupp hl₁ hl₁₂.le
    have h2 := phiMap_tangent_le (dl := l₂ - l₁) (g₀ := (g1a + g1b) / 2) (g := U1 μ l₁)
      (by linarith) hg1m hU1.le
    have h3 : U1 μ l₂ ≤ (g1a + g1b) / 2 / (1 + (l₂ - l₁) * ((g1a + g1b) / 2)) +
        (U1 μ l₁ - (g1a + g1b) / 2) / (1 + (l₂ - l₁) * ((g1a + g1b) / 2)) ^ 2 := le_trans h1 h2
    dsimp only [Dd, polytopeDd, γ]
    ring_nf at h3 ⊢; linarith
  · -- row 11: tangent (2, 3)
    have h1 := lens_ineq_ii μ hsupp hl₂ hl₂₃.le
    have h2 := phiMap_tangent_le (dl := l₃ - l₂) (g₀ := (g2a + g2b) / 2) (g := U1 μ l₂)
      (by linarith) hg2m hU2.le
    have h3 : U1 μ l₃ ≤ (g2a + g2b) / 2 / (1 + (l₃ - l₂) * ((g2a + g2b) / 2)) +
        (U1 μ l₂ - (g2a + g2b) / 2) / (1 + (l₃ - l₂) * ((g2a + g2b) / 2)) ^ 2 := le_trans h1 h2
    dsimp only [Dd, polytopeDd, γ]
    ring_nf at h3 ⊢; linarith
  · -- row 12: tangent (1, 3)
    have h1 := lens_ineq_ii μ hsupp hl₁ (lt_trans hl₁₂ hl₂₃).le
    have h2 := phiMap_tangent_le (dl := l₃ - l₁) (g₀ := (g1a + g1b) / 2) (g := U1 μ l₁)
      (by linarith) hg1m hU1.le
    have h3 : U1 μ l₃ ≤ (g1a + g1b) / 2 / (1 + (l₃ - l₁) * ((g1a + g1b) / 2)) +
        (U1 μ l₁ - (g1a + g1b) / 2) / (1 + (l₃ - l₁) * ((g1a + g1b) / 2)) ^ 2 := le_trans h1 h2
    dsimp only [Dd, polytopeDd, γ]
    ring_nf at h3 ⊢; linarith
  · -- row 13: harmonic tangent plane
    have hl₁₃ : 0 < l₃ - l₁ := by linarith
    have hth0 : 0 < (l₂ - l₁) / (l₃ - l₁) := div_pos (by linarith) hl₁₃
    have hth1 : (l₂ - l₁) / (l₃ - l₁) < 1 := (div_lt_one hl₁₃).mpr (by linarith)
    have hp : 0 < max ((g3a + g3b) / 2) (1 / 1000000) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hq : 0 < max ((g1a + g1b) / 2) (1 / 1000000) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have h1 := lens_ineq_v μ hsupp hl₁ hl₁₂ hl₂₃
    have h2 := harmonic_tangent_le hth0 hth1 hU1 hU3 hp hq
    have h3 := le_trans h1 h2
    dsimp only [Dd, polytopeDd, γ]; linarith

/-- Lemma 5 (`lem:farkas`): Farkas decoupling step.
    If `D γ ≤ d`, `y ≥ 0`, `η := Dᵀ y`, and `Ψ(c) ≤ η₀ + ∑_i η_i / (c + l_i) + Δ` for `c > 0`,
    then `∫ Ψ dμ ≤ η₀ + dᵀ y + Δ`. -/
theorem farkas_decoupling (hsupp : ∀ᵐ c ∂μ, 0 < c)
    {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i)
    (D : Fin 14 → Fin 3 → ℝ) (d y : Fin 14 → ℝ)
    (hy : ∀ r, 0 ≤ y r)
    (hpoly : ∀ r, ∑ i : Fin 3, D r i * U1 μ (l i) ≤ d r)
    (η₀ Δ : ℝ) (Ψ : ℝ → ℝ) (hΨ_int : Integrable Ψ μ)
    (hΨ_le : ∀ c, 0 < c → Ψ c ≤ η₀ + (∑ i : Fin 3, (∑ r : Fin 14, D r i * y r) * (c + l i)⁻¹) + Δ) :
    ∫ c, Ψ c ∂μ ≤ η₀ + (∑ r : Fin 14, d r * y r) + Δ := by
  let η : Fin 3 → ℝ := fun i => ∑ r : Fin 14, D r i * y r
  -- Step 1: ηᵀ γ ≤ dᵀ y
  have hη_le : ∑ i : Fin 3, η i * U1 μ (l i) ≤ ∑ r : Fin 14, d r * y r := by
    have hswap :
        ∑ i : Fin 3, η i * U1 μ (l i) =
        ∑ r : Fin 14, (∑ i : Fin 3, D r i * U1 μ (l i)) * y r := by
      dsimp [η]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hswap]
    apply Finset.sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_right (hpoly r) (hy r)
  -- Step 2: Integrate pointwise upper bound against μ
  have hint_terms : ∀ i : Fin 3, Integrable (fun c : ℝ => η i * (c + l i)⁻¹) μ := fun i => by
    have hb : Integrable (fun c : ℝ => (c + l i)⁻¹) μ := by
      simpa using integrable_inv_pow μ hsupp (hl i) 1
    exact hb.const_mul (η i)
  have hint_sum : Integrable (fun c : ℝ => ∑ i : Fin 3, η i * (c + l i)⁻¹) μ :=
    integrable_finset_sum _ (fun i _ => hint_terms i)
  have hint_12 : Integrable (fun c : ℝ => η₀ + ∑ i : Fin 3, η i * (c + l i)⁻¹) μ :=
    (integrable_const η₀).add hint_sum
  have hint_rhs : Integrable (fun c : ℝ => (η₀ + ∑ i : Fin 3, η i * (c + l i)⁻¹) + Δ) μ :=
    hint_12.add (integrable_const Δ)
  have hint_le :
      ∫ c, Ψ c ∂μ ≤ ∫ c, ((η₀ + ∑ i : Fin 3, η i * (c + l i)⁻¹) + Δ) ∂μ := by
    apply integral_mono_ae hΨ_int hint_rhs
    filter_upwards [hsupp] with c hc
    exact hΨ_le c hc
  have hsplit1 :
      ∫ c, ((η₀ + ∑ i : Fin 3, η i * (c + l i)⁻¹) + Δ) ∂μ =
      (∫ c, (η₀ + ∑ i : Fin 3, η i * (c + l i)⁻¹) ∂μ) + (∫ _c, Δ ∂μ) :=
    integral_add hint_12 (integrable_const Δ)
  have hsplit2 :
      ∫ c, (η₀ + ∑ i : Fin 3, η i * (c + l i)⁻¹) ∂μ =
      (∫ _c, η₀ ∂μ) + (∫ c, ∑ i : Fin 3, η i * (c + l i)⁻¹ ∂μ) :=
    integral_add (integrable_const η₀) hint_sum
  rw [hsplit1, hsplit2, integral_finset_sum _ (fun i _ => hint_terms i)] at hint_le
  simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul,
             integral_mul_left] at hint_le
  have hU1_sum : (∑ i : Fin 3, η i * ∫ c, (c + l i)⁻¹ ∂μ) = ∑ i : Fin 3, η i * U1 μ (l i) := rfl
  rw [hU1_sum] at hint_le
  linarith

end PolytopeAndFarkas

section KernelTreeVerification

open MathForgeMechDesign.Cert248

/-- Normalize exact rational by dividing out `Nat.gcd`. -/
def qNorm (n : Int) (d : Nat) : Q :=
  if d == 0 then ⟨0, 1⟩
  else
    let g := Nat.gcd n.natAbs d
    if g ≤ 1 then ⟨n, d⟩ else ⟨n / (g : Int), d / g⟩

def qZero : Q := ⟨0, 1⟩
def qOne : Q := ⟨1, 1⟩
def qNeg (a : Q) : Q := ⟨-a.num, a.den⟩
def qAdd (a b : Q) : Q := qNorm (a.num * (b.den : Int) + b.num * (a.den : Int)) (a.den * b.den)
def qSub (a b : Q) : Q := qNorm (a.num * (b.den : Int) - b.num * (a.den : Int)) (a.den * b.den)
def qMul (a b : Q) : Q := qNorm (a.num * b.num) (a.den * b.den)
def qDiv (a b : Q) : Q :=
  if b.num > 0 then qNorm (a.num * (b.den : Int)) (a.den * b.num.natAbs)
  else if b.num < 0 then qNorm (-(a.num * (b.den : Int))) (a.den * b.num.natAbs)
  else ⟨0, 1⟩

def qEq (a b : Q) : Bool := a.den > 0 && b.den > 0 && a.num * (b.den : Int) == b.num * (a.den : Int)
def qLe (a b : Q) : Bool := a.den > 0 && b.den > 0 && decide (a.num * (b.den : Int) ≤ b.num * (a.den : Int))
def qLt (a b : Q) : Bool := a.den > 0 && b.den > 0 && decide (a.num * (b.den : Int) < b.num * (a.den : Int))
def qNonneg (a : Q) : Bool := a.den > 0 && decide (0 ≤ a.num)
def qPos (a : Q) : Bool := a.den > 0 && decide (0 < a.num)
def qMin (a b : Q) : Q := if qLe a b then a else b
def qMax (a b : Q) : Q := if qLe a b then b else a

def qSum : List Q → Q
  | [] => qZero
  | x :: xs => qAdd x (qSum xs)

def qAllNonneg : List Q → Bool
  | [] => true
  | x :: xs => qNonneg x && qAllNonneg xs

def qAllPos : List Q → Bool
  | [] => true
  | x :: xs => qPos x && qAllPos xs

def qDot : List Q → List Q → Q
  | [], [] => qZero
  | x :: xs, y :: ys => qAdd (qMul x y) (qDot xs ys)
  | _, _ => qZero

def boxValid (b : Box) : Bool :=
  qNonneg b.g1a && qLt b.g1a b.g1b &&
  qNonneg b.g2a && qLt b.g2a b.g2b &&
  qNonneg b.g3a && qLt b.g3a b.g3b

def treeBox : CertTree → Box
  | CertTree.split b _ _ _ => b
  | CertTree.leaf b _ _ _ _ => b
  | CertTree.disjoint b _ => b

/-- Exact split partition check along `axis ∈ {0, 1, 2}` with zero gaps or overlaps. -/
def splitMatches (parent c1 c2 : Box) (axis : Nat) : Bool :=
  match axis with
  | 0 =>
    qEq c1.g1a parent.g1a && qEq c1.g1b c2.g1a && qEq c2.g1b parent.g1b &&
    qEq c1.g2a parent.g2a && qEq c1.g2b parent.g2b && qEq c2.g2a parent.g2a && qEq c2.g2b parent.g2b &&
    qEq c1.g3a parent.g3a && qEq c1.g3b parent.g3b && qEq c2.g3a parent.g3a && qEq c2.g3b parent.g3b
  | 1 =>
    qEq c1.g1a parent.g1a && qEq c1.g1b parent.g1b && qEq c2.g1a parent.g1a && qEq c2.g1b parent.g1b &&
    qEq c1.g2a parent.g2a && qEq c1.g2b c2.g2a && qEq c2.g2b parent.g2b &&
    qEq c1.g3a parent.g3a && qEq c1.g3b parent.g3b && qEq c2.g3a parent.g3a && qEq c2.g3b parent.g3b
  | 2 =>
    qEq c1.g1a parent.g1a && qEq c1.g1b parent.g1b && qEq c2.g1a parent.g1a && qEq c2.g1b parent.g1b &&
    qEq c1.g2a parent.g2a && qEq c1.g2b parent.g2b && qEq c2.g2a parent.g2a && qEq c2.g2b parent.g2b &&
    qEq c1.g3a parent.g3a && qEq c1.g3b c2.g3a && qEq c2.g3b parent.g3b
  | _ => false

/-- Exact rational constants for `(l₁, l₂, l₃) = (3/50, 7/20, 9/5)`:
    `l₁/l₂ = 6/35`, `l₂/l₃ = 7/36`, `l₂ - l₁ = 29/100`, `l₃ - l₂ = 29/20`, `l₃ - l₁ = 87/50`,
    `A_sec = 1/7`, `B_sec = 6/7`, `θ₁₃ = 1/6`, `1 - θ₁₃ = 5/6`. -/
def qL1DivL2 : Q := qDiv certL1 certL2
def qL2DivL3 : Q := qDiv certL2 certL3
def qDL12 : Q := qSub certL2 certL1
def qDL23 : Q := qSub certL3 certL2
def qDL13 : Q := qSub certL3 certL1
def qASec : Q := qDiv (qMul certL1 qDL23) (qMul certL2 qDL13)
def qBSec : Q := qDiv (qMul certL3 qDL12) (qMul certL2 qDL13)
def qTh : Q := qDiv qDL12 qDL13
def qOneSubTh : Q := qSub qOne qTh

/-- Exact rational 14-inequality Farkas ray disjointness check (`dᵀ y < lhs_min`). -/
def farkasRayDisjoint (b : Box) (fy : List Q) : Bool :=
  if fy.length != 14 || !qAllNonneg fy then false
  else
    let half : Q := ⟨1, 2⟩
    let g1m := qMul half (qAdd b.g1a b.g1b)
    let g2m := qMul half (qAdd b.g2a b.g2b)
    let g3m := qMul half (qAdd b.g3a b.g3b)
    let d12 := qAdd qOne (qMul qDL12 g1m)
    let d23 := qAdd qOne (qMul qDL23 g2m)
    let d13 := qAdd qOne (qMul qDL13 g1m)
    let m12 := qDiv qOne (qMul d12 d12)
    let r12 := qSub (qDiv g1m d12) (qDiv g1m (qMul d12 d12))
    let m23 := qDiv qOne (qMul d23 d23)
    let r23 := qSub (qDiv g2m d23) (qDiv g2m (qMul d23 d23))
    let m13 := qDiv qOne (qMul d13 d13)
    let r13 := qSub (qDiv g1m d13) (qDiv g1m (qMul d13 d13))
    let eps : Q := ⟨1, 1000000⟩
    let p := qMax g3m eps
    let q := qMax g1m eps
    let hd0 := qAdd (qMul qOneSubTh p) (qMul qTh q)
    let hd := qMul hd0 hd0
    let h1 := qDiv (qMul qOneSubTh (qMul p p)) hd
    let h3 := qDiv (qMul qTh (qMul q q)) hd
    let col0 : List Q :=
      [qOne, qNeg qOne, qZero, qZero, qZero, qZero,
       qL1DivL2, qZero, qASec, qNeg qOneSubTh, qNeg m12, qZero, qNeg m13, qNeg h1]
    let col1 : List Q :=
      [qZero, qZero, qOne, qNeg qOne, qZero, qZero,
       qNeg qOne, qL2DivL3, qNeg qOne, qOne, qOne, qNeg m23, qZero, qOne]
    let col2 : List Q :=
      [qZero, qZero, qZero, qZero, qOne, qNeg qOne,
       qZero, qNeg qOne, qBSec, qNeg qTh, qZero, qOne, qOne, qNeg h3]
    let dVec : List Q :=
      [b.g1b, qNeg b.g1a, b.g2b, qNeg b.g2a, b.g3b, qNeg b.g3a,
       qZero, qZero, qZero, qZero, r12, r23, r13, qZero]
    let eta0 := qDot col0 fy
    let eta1 := qDot col1 fy
    let eta2 := qDot col2 fy
    let lhsMin :=
      qAdd (qMin (qMul eta0 b.g1a) (qMul eta0 b.g1b))
        (qAdd (qMin (qMul eta1 b.g2a) (qMul eta1 b.g2b))
              (qMin (qMul eta2 b.g3a) (qMul eta2 b.g3b)))
    let rhs := qDot dVec fy
    qLt rhs lhsMin

/-- Disjointness check: either one of the 7 closed-form monotone exclusions from Lemma 4
    OR the exact rational Farkas ray test. -/
def disjointCheck (b : Box) (fy : Option (List Q)) : Bool :=
  let c1 := qLe b.g2b (qMul qL1DivL2 b.g1a)
  let c2 := qLe b.g3b (qMul qL2DivL3 b.g2a)
  let c3 := qLe b.g1b (qMul b.g2a (qAdd qOne (qMul qDL12 b.g1b)))
  let c4 := qLe b.g2b (qMul b.g3a (qAdd qOne (qMul qDL23 b.g2b)))
  let c5 := qLe b.g1b (qMul b.g3a (qAdd qOne (qMul qDL13 b.g1b)))
  let c6 := qLe b.g2b (qAdd (qMul qASec b.g1a) (qMul qBSec b.g3a))
  let c7 := qPos b.g1b && qPos b.g3b &&
    qLe (qMul b.g1b b.g3b) (qMul b.g2a (qAdd (qMul qOneSubTh b.g3b) (qMul qTh b.g1b)))
  if c1 || c2 || c3 || c4 || c5 || c6 || c7 then true
  else
    match fy with
    | some y => farkasRayDisjoint b y
    | none => false

/-- Leaf validity check: valid probability weights `a ≥ 0`, `∑ a = 1`, `lam > 0`, `y ≥ 0`, `len y = 14`. -/
def leafValid (a lam : List Q) (eta0 : Q) (y : List Q) : Bool :=
  a.length > 0 && a.length == lam.length &&
  qAllNonneg a && qEq (qSum a) qOne &&
  qAllPos lam && (eta0.den > 0) &&
  y.length == 14 && qAllNonneg y

/-- Structurally recursive certificate tree verifier (evaluated directly by Lean 4 kernel). -/
def treeValid : CertTree → Bool
  | CertTree.split b ax l r =>
    boxValid b && splitMatches b (treeBox l) (treeBox r) ax && treeValid l && treeValid r
  | CertTree.leaf b a lam eta0 y =>
    boxValid b && leafValid a lam eta0 y
  | CertTree.disjoint b fy =>
    boxValid b && disjointCheck b fy

def countLeaves : CertTree → Nat
  | CertTree.split _ _ l r => countLeaves l + countLeaves r
  | CertTree.leaf _ _ _ _ _ => 1
  | CertTree.disjoint _ _ => 0

def countDisjoint : CertTree → Nat
  | CertTree.split _ _ l r => countDisjoint l + countDisjoint r
  | CertTree.leaf _ _ _ _ _ => 0
  | CertTree.disjoint _ _ => 1

/-- Root box `[0, 17] × [0, 3] × [0, 5/8]` covers `[0, 50/3] × [0, 20/7] × [0, 5/9]`
    and pins `(l₁, l₂, l₃) = (3/50, 7/20, 9/5)` and `target = 62/25`. -/
def rootCovers : Bool :=
  let rb := treeBox certTree248
  qEq certL1 ⟨3, 50⟩ && qEq certL2 ⟨7, 20⟩ && qEq certL3 ⟨9, 5⟩ && qEq certTarget ⟨62, 25⟩ &&
  qEq rb.g1a ⟨0, 1⟩ && qEq rb.g1b ⟨17, 1⟩ &&
  qEq rb.g2a ⟨0, 1⟩ && qEq rb.g2b ⟨3, 1⟩ &&
  qEq rb.g3a ⟨0, 1⟩ && qEq rb.g3b ⟨5, 8⟩ &&
  qLe (qDiv qOne certL1) rb.g1b &&
  qLe (qDiv qOne certL2) rb.g2b &&
  qLe (qDiv qOne certL3) rb.g3b

set_option maxRecDepth 2000000 in
theorem cert248_root_covers : rootCovers = true := by decide

set_option maxRecDepth 2000000 in
theorem cert248_leaf_count : countLeaves certTree248 = 722 := by decide

set_option maxRecDepth 2000000 in
theorem cert248_disjoint_count : countDisjoint certTree248 = 32 := by decide

set_option maxRecDepth 2000000 in
theorem cert248_tree_valid : treeValid certTree248 = true := by decide

/-- Real-valued interpretation of an exact rational `Q`. -/
noncomputable def qToReal (q : Q) : ℝ := (q.num : ℝ) / (q.den : ℝ)

/-- Real-space box membership `(x₁, x₂, x₃) ∈ b`. -/
def memBox (b : Box) (x : ℝ × ℝ × ℝ) : Prop :=
  qToReal b.g1a ≤ x.1 ∧ x.1 ≤ qToReal b.g1b ∧
  qToReal b.g2a ≤ x.2.1 ∧ x.2.1 ≤ qToReal b.g2b ∧
  qToReal b.g3a ≤ x.2.2 ∧ x.2.2 ≤ qToReal b.g3b

/-- Soundness predicate: `x` lies in some leaf or disjoint box of `t`. -/
def coveredByTree : CertTree → (ℝ × ℝ × ℝ) → Prop
  | CertTree.split _ _ l r, x => coveredByTree l x ∨ coveredByTree r x
  | CertTree.leaf b _ _ _ _, x => memBox b x
  | CertTree.disjoint b _, x => memBox b x

private lemma qEq_sound {a b : Q} (h : qEq a b = true) : qToReal a = qToReal b := by
  unfold qEq at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨ha, hb⟩, heq⟩ := h
  unfold qToReal
  have ha' : (a.den : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hb' : (b.den : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have heqR : (a.num : ℝ) * (b.den : ℝ) = (b.num : ℝ) * (a.den : ℝ) := by exact_mod_cast heq
  rw [div_eq_div_iff ha' hb']
  exact heqR

/-- Real-space exact coverage soundness: whenever `treeValid t = true`, EVERY real point
    `x ∈ treeBox t` is covered by at least one leaf or disjoint box of `t` with zero gaps! -/
theorem treeValid_covers_real (t : CertTree) (hv : treeValid t = true)
    (x : ℝ × ℝ × ℝ) (hx : memBox (treeBox t) x) :
    coveredByTree t x := by
  induction t with
  | leaf b a lam eta0 y =>
    exact hx
  | disjoint b fy =>
    exact hx
  | split b ax l r ihl ihr =>
    simp only [treeValid, Bool.and_eq_true] at hv
    obtain ⟨⟨⟨_, hsp⟩, hvl⟩, hvr⟩ := hv
    simp only [treeBox] at hx
    rcases hx with ⟨h1a, h1b, h2a, h2b, h3a, h3b⟩
    match ax with
    | 0 =>
      simp only [splitMatches, Bool.and_eq_true] at hsp
      rcases hsp with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩, e10⟩, e11⟩
      by_cases hmid : x.1 ≤ qToReal (treeBox l).g1b
      · left
        apply ihl hvl
        refine ⟨?_, hmid, ?_, ?_, ?_, ?_⟩
        · rw [qEq_sound e1]; exact h1a
        · rw [qEq_sound e4]; exact h2a
        · rw [qEq_sound e5]; exact h2b
        · rw [qEq_sound e8]; exact h3a
        · rw [qEq_sound e9]; exact h3b
      · right
        apply ihr hvr
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← qEq_sound e2]; linarith
        · rw [qEq_sound e3]; exact h1b
        · rw [qEq_sound e6]; exact h2a
        · rw [qEq_sound e7]; exact h2b
        · rw [qEq_sound e10]; exact h3a
        · rw [qEq_sound e11]; exact h3b
    | 1 =>
      simp only [splitMatches, Bool.and_eq_true] at hsp
      rcases hsp with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩, e10⟩, e11⟩
      by_cases hmid : x.2.1 ≤ qToReal (treeBox l).g2b
      · left
        apply ihl hvl
        refine ⟨?_, ?_, ?_, hmid, ?_, ?_⟩
        · rw [qEq_sound e1]; exact h1a
        · rw [qEq_sound e2]; exact h1b
        · rw [qEq_sound e5]; exact h2a
        · rw [qEq_sound e8]; exact h3a
        · rw [qEq_sound e9]; exact h3b
      · right
        apply ihr hvr
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [qEq_sound e3]; exact h1a
        · rw [qEq_sound e4]; exact h1b
        · rw [← qEq_sound e6]; linarith
        · rw [qEq_sound e7]; exact h2b
        · rw [qEq_sound e10]; exact h3a
        · rw [qEq_sound e11]; exact h3b
    | 2 =>
      simp only [splitMatches, Bool.and_eq_true] at hsp
      rcases hsp with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩, e9⟩, e10⟩, e11⟩
      by_cases hmid : x.2.2 ≤ qToReal (treeBox l).g3b
      · left
        apply ihl hvl
        refine ⟨?_, ?_, ?_, ?_, ?_, hmid⟩
        · rw [qEq_sound e1]; exact h1a
        · rw [qEq_sound e2]; exact h1b
        · rw [qEq_sound e5]; exact h2a
        · rw [qEq_sound e6]; exact h2b
        · rw [qEq_sound e9]; exact h3a
      · right
        apply ihr hvr
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [qEq_sound e3]; exact h1a
        · rw [qEq_sound e4]; exact h1b
        · rw [qEq_sound e7]; exact h2a
        · rw [qEq_sound e8]; exact h2b
        · rw [← qEq_sound e10]; linarith
        · rw [qEq_sound e11]; exact h3b
    | n + 3 =>
      simp [splitMatches] at hsp

/-- Corollary: Every point in `R_0 = [0, 17] × [0, 3] × [0, 5/8]` (in particular every feasible
    3-moment triple in `[0, 50/3] × [0, 20/7] × [0, 5/9]`) is covered by `certTree248`. -/
theorem certTree248_covers_R0 (x : ℝ × ℝ × ℝ)
    (hx : memBox (treeBox certTree248) x) :
    coveredByTree certTree248 x :=
  treeValid_covers_real certTree248 cert248_tree_valid x hx

end KernelTreeVerification

end MathForgeMechDesign.UpperBoundRecipAndTree
