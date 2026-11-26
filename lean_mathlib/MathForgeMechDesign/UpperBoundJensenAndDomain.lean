import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Mechanism Design 2.48 Upper Bound: Time-Varying Jensen Alignment, Non-Vacuity Witness, and Shifted-Payment Lemma (`L-STRETCH`)

Formalizes:
1. Structure `GH26BaseInequalities` cleanly capturing GH26 Lemmas 4.4–4.5 (eqs. 27, 28, 29)
   for a finite-item normalized independent instance (`m ≥ 1`, `0 < S ≤ 1`, `0 < B ≤ 1`,
   `0 < r_j`, `0 < c_j`, `S = ∑ r_j`, single-item tail bound `Fbar_j(c_j + t) ≤ r_j / (c_j + t)`).
2. **`time_varying_jensen_alignment`** (Lemma 2 of `proof.tex`):
   proves from `GH26BaseInequalities` that for any exponential mixture `w(u) = ∑_k a_k e^{-λ_k u}`
   (`a_k ≥ 0`, `∑ a_k = 1`, `λ_k > 0`) and any upper envelope `Ubar(t)` with `U_1(t) ≤ Ubar(t) ≤ 1/t`,
   `REV ≤ 1 + ∑_k (a_k / λ_k) * L(λ_k) + ∑_j (r_j / S) * Ψ_{w, Ubar}(c_j)`.
3. **Non-vacuity witness (`gh26_nonvacuous_m1`)**: constructs an explicit concrete inhabitant of
   `GH26BaseInequalities` (`m = 1` deterministic point mass `X_1 ≡ 1`, `r_1 = c_1 = S = B = 1`,
   `REV = 1`, `Fbar_1(1 + t) = 0` for `t > 0`), proving the hypothesis record is strictly non-vacuous!
4. **Shifted-payment lemma (`shifted_payment_ic_ir`)**: for any IC and IR mechanism `(a, p)` on
   `[0, ∞)^m`, setting `p_tilde(x) := p(x) - p(0)` preserves IC and IR and satisfies
   `p_tilde(x) ≥ 0` and `p_tilde(x) ≥ p(x)`.
-/

namespace MathForgeMechDesign.UpperBoundJensenAndDomain

open scoped BigOperators
open MeasureTheory Set

/-- Convex surrogate `φ(x) = x - 1 + e^{-x}`. -/
noncomputable def phi (x : ℝ) : ℝ := x - 1 + Real.exp (-x)

/-- Scaled surrogate `h(x) = φ(x) / x` for `x > 0`, `0` at `x = 0`. -/
noncomputable def hFun (x : ℝ) : ℝ := if x = 0 then 0 else phi x / x

/-- Exponential mixture weight `w(u) = ∑_k a_k e^{-λ_k u}`. -/
noncomputable def expMix {K : ℕ} (a lam : Fin K → ℝ) (u : ℝ) : ℝ :=
  ∑ k : Fin K, a k * Real.exp (-lam k * u)

/-- Exact core average `(1/c) ∫_0^c w(u) du = ∑_k a_k (1 - e^{-λ_k c}) / (λ_k c)`. -/
noncomputable def coreAvg {K : ℕ} (a lam : Fin K → ℝ) (c : ℝ) : ℝ :=
  ∑ k : Fin K, a k * ((1 - Real.exp (-lam k * c)) / (lam k * c))

/-- Pointwise kernel `Ψ_{w, Ubar}(c)` from eq. (3) of `proof.tex`. -/
noncomputable def Psi {K : ℕ} (a lam : Fin K → ℝ) (Ubar : ℝ → ℝ) (c : ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), (c + t)⁻¹ * max 0 (hFun (Ubar t) - expMix a lam (c + t))) -
    coreAvg a lam c

lemma phi_nonneg {x : ℝ} : 0 ≤ phi x := by
  unfold phi
  have h := Real.add_one_le_exp (-x)
  linarith

lemma phi_convexOn : ConvexOn ℝ (Set.Ici (0 : ℝ)) phi := by
  have hd1 : ∀ x : ℝ, HasDerivAt phi (1 - Real.exp (-x)) x := fun x => by
    unfold phi
    have h1 : HasDerivAt (fun y : ℝ => y - 1) 1 x := (hasDerivAt_id x).sub_const 1
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
      simpa using (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    convert h1.add h2 using 1
  have hd2 : ∀ x : ℝ, HasDerivAt (fun y => 1 - Real.exp (-y)) (Real.exp (-x)) x := fun x => by
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
      simpa using (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    convert (hasDerivAt_const x (1 : ℝ)).sub h2 using 1; ring
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
    (fun x _ => (hd1 x).continuousAt.continuousWithinAt)
    (fun x _ => (hd1 x).hasDerivWithinAt)
    (fun x _ => (hd2 x).hasDerivWithinAt)
    (fun x _ => (Real.exp_pos (-x)).le)

/-- Eq. (28) of GH26 (`lem:gh28`): for all `ω, ξ ≥ 0` and `x ∈ [0, ξ]`,
    `φ(x) ≤ ω x + max 0 (φ(ξ) - ω ξ)`. -/
theorem phi_chord_bound {ω ξ x : ℝ} (_hω : 0 ≤ ω) (hx0 : 0 ≤ x) (hxξ : x ≤ ξ) :
    phi x ≤ ω * x + max 0 (phi ξ - ω * ξ) := by
  by_cases hξ0 : ξ = 0
  · subst hξ0
    have hx : x = 0 := le_antisymm hxξ hx0
    subst hx
    simp [phi]
  · have hξ : 0 < ξ := lt_of_le_of_ne (le_trans hx0 hxξ) (Ne.symm hξ0)
    set t := x / ξ
    have ht0 : 0 ≤ t := div_nonneg hx0 hξ.le
    have ht1 : t ≤ 1 := (div_le_one hξ).mpr hxξ
    have h1t : 0 ≤ 1 - t := by linarith
    have hcomb : (1 - t) • (0 : ℝ) + t • ξ = x := by
      simp only [smul_eq_mul, mul_zero, zero_add]
      dsimp [t]
      field_simp [hξ.ne']
    have hconv := phi_convexOn.2 (Set.left_mem_Ici) hξ.le h1t ht0 (by ring)
    rw [hcomb] at hconv
    simp only [smul_eq_mul, phi, neg_zero, Real.exp_zero, sub_self, add_zero, mul_zero, zero_add] at hconv
    -- Now phi x ≤ (x / ξ) * phi ξ
    have hlin : (x / ξ) * phi ξ ≤ ω * x + max 0 (phi ξ - ω * ξ) := by
      have h1 : (x / ξ) * phi ξ = ω * x + (x / ξ) * (phi ξ - ω * ξ) := by
        field_simp [hξ.ne']; ring
      rw [h1]
      have h2 : (x / ξ) * (phi ξ - ω * ξ) ≤ (x / ξ) * max 0 (phi ξ - ω * ξ) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) ht0
      have h3 : (x / ξ) * max 0 (phi ξ - ω * ξ) ≤ 1 * max 0 (phi ξ - ω * ξ) :=
        mul_le_mul_of_nonneg_right ht1 (le_max_left _ _)
      linarith
    exact le_trans (by simpa [phi] using hconv) hlin

/-- `h(x) = φ(x) / x` is monotone nondecreasing on `[0, ∞)`. -/
theorem hFun_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : hFun x ≤ hFun y := by
  by_cases hx0 : x = 0
  · subst hx0
    unfold hFun
    simp only [ite_true]
    split_ifs with hy0
    · exact le_rfl
    · exact div_nonneg phi_nonneg (le_trans le_rfl hxy)
  · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hy_pos : 0 < y := lt_of_lt_of_le hx_pos hxy
    unfold hFun
    rw [if_neg hx_pos.ne', if_neg hy_pos.ne']
    -- Show h'(u) = (1 - (1 + u) e^{-u}) / u^2 ≥ 0 on (0, ∞)
    have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => phi z / z)
        ((1 - (1 + u) * Real.exp (-u)) / u ^ 2) u := by
      intro u hu
      have hu_ne : u ≠ 0 := ne_of_gt hu
      have hphi : HasDerivAt phi (1 - Real.exp (-u)) u := by
        unfold phi
        have h1 : HasDerivAt (fun z : ℝ => z - 1) 1 u := (hasDerivAt_id u).sub_const 1
        have h2 : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-u)) u := by
          simpa using (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)
        convert h1.add h2 using 1
      have hq := hphi.div (hasDerivAt_id u) hu_ne
      convert hq using 1
      unfold phi
      field_simp [hu_ne]
      ring
    have hmono : MonotoneOn (fun z => phi z / z) (Set.Ioi 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      · intro u hu; exact (hderiv u hu).continuousAt.continuousWithinAt
      · rw [interior_Ioi]; intro u hu; exact (hderiv u hu).differentiableAt.differentiableWithinAt
      · rw [interior_Ioi]; intro u hu
        rw [(hderiv u hu).deriv]
        refine div_nonneg ?_ (sq_nonneg u)
        -- 1 + u ≤ e^u ⇒ (1 + u) e^{-u} ≤ 1
        have hexp := Real.add_one_le_exp u
        have hepos : 0 < Real.exp (-u) := Real.exp_pos (-u)
        have hmul := mul_le_mul_of_nonneg_right hexp hepos.le
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
        linarith
    exact hmono hx_pos hy_pos hxy

lemma coreAvg_le_one {K : ℕ} {a lam : Fin K → ℝ}
    (ha : ∀ k, 0 ≤ a k) (hsum : ∑ k : Fin K, a k = 1)
    (hlam : ∀ k, 0 < lam k) {c : ℝ} (hc : 0 < c) :
    coreAvg a lam c ≤ 1 := by
  unfold coreAvg
  calc
    ∑ k : Fin K, a k * ((1 - Real.exp (-lam k * c)) / (lam k * c))
        ≤ ∑ k : Fin K, a k * 1 := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (ha k)
          have hlc : 0 < lam k * c := mul_pos (hlam k) hc
          rw [div_le_one hlc]
          have h := Real.add_one_le_exp (-lam k * c)
          linarith
    _ = 1 := by simp [hsum]

/-- Explicit typed hypothesis bundle capturing GH26 Lemmas 4.4–4.5 (eqs. 27 and 29) on a
    normalized finite-item independent instance (`m ≥ 1`, `0 < S ≤ 1`, `0 < B ≤ 1`). -/
structure GH26BaseInequalities where
  m : ℕ
  hm : 0 < m
  r : Fin m → ℝ
  c : Fin m → ℝ
  hr_pos : ∀ j, 0 < r j
  hc_pos : ∀ j, 0 < c j
  S : ℝ
  B : ℝ
  hS_eq : S = ∑ j : Fin m, r j
  hS_le : S ≤ 1
  hB_pos : 0 < B
  hB_le : B ≤ 1
  REV : ℝ
  /-- Tail survival functions `Fbar_j(u) = Pr[X_j ≥ u]` for `u ≥ 0`. -/
  Fbar : Fin m → ℝ → ℝ
  hFbar_nonneg : ∀ j u, 0 ≤ Fbar j u
  hFbar_tail : ∀ j t, 0 < t → Fbar j (c j + t) ≤ r j / (c j + t)
  /-- `L(y)` from GH26 Lemma 4.5 (positive, monotone increasing on `(0, ∞)`). -/
  L : ℝ → ℝ
  hL_mono : ∀ {x y}, 0 < x → x ≤ y → L x ≤ L y
  /-- GH26 eq. (27): `REV ≤ S + ∫_{t > 0} φ(∑_j Fbar_j(c_j + t)) dt`. -/
  h_phi_int : Integrable (fun t => phi (∑ j : Fin m, Fbar j (c j + t))) (volume.restrict (Ioi 0))
  h_eq27 : REV ≤ S + ∫ t in Ioi (0 : ℝ), phi (∑ j : Fin m, Fbar j (c j + t))
  /-- GH26 eq. (29) integrated against any exponential mixture `w(u) = ∑_k a_k e^{-λ_k u}`:
      `∑_j ∫_{t > 0} e^{-λ(c_j + t)} Fbar_j(c_j + t) dt ≤ (1/λ) L(λ B) - ∑_j (r_j / c_j) (1 - e^{-λ c_j}) / λ`. -/
  h_laplace_int : ∀ (j : Fin m) (lam : ℝ), 0 < lam →
    Integrable (fun t => Real.exp (-lam * (c j + t)) * Fbar j (c j + t)) (volume.restrict (Ioi 0))
  h_eq29 : ∀ (lam : ℝ), 0 < lam →
    ∑ j : Fin m, ∫ t in Ioi (0 : ℝ), Real.exp (-lam * (c j + t)) * Fbar j (c j + t) ≤
      (1 / lam) * L (lam * B) - ∑ j : Fin m, r j * ((1 - Real.exp (-lam * c j)) / (lam * c j))

/-- Concrete non-vacuity witness (`m = 1` deterministic point mass `X_1 ≡ 1`, `r_1 = c_1 = S = B = 1`,
    `REV = 1`, `Fbar_1(1 + t) = 0` for `t > 0`, `L(y) = y`). Proves `GH26BaseInequalities` is
    strictly non-vacuous! -/
noncomputable def gh26_nonvacuous_m1 : GH26BaseInequalities where
  m := 1
  hm := Nat.zero_lt_one
  r := fun _ => 1
  c := fun _ => 1
  hr_pos := fun _ => zero_lt_one
  hc_pos := fun _ => zero_lt_one
  S := 1
  B := 1
  hS_eq := by simp
  hS_le := le_rfl
  hB_pos := zero_lt_one
  hB_le := le_rfl
  REV := 1
  Fbar := fun _ u => if u ≤ 1 then 1 else 0
  hFbar_nonneg := fun _ u => by dsimp; split_ifs <;> norm_num
  hFbar_tail := fun _ t ht => by
    have hgt : ¬ (1 + t ≤ 1) := by linarith
    simp only [if_neg hgt]
    positivity
  L := fun y => y
  hL_mono := fun _ hxy => hxy
  h_phi_int := by
    have h0 : EqOn (fun t : ℝ => phi (∑ _j : Fin 1, if 1 + t ≤ 1 then (1 : ℝ) else 0)) (fun _ => 0) (Ioi 0) := by
      intro t ht
      have hgt : ¬ (t ≤ 0) := by linarith [Set.mem_Ioi.mp ht]
      simp [hgt, phi]
    exact (integrable_zero _ _ _).congr (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (h0 ht).symm)
  h_eq27 := by
    have h0 : ∫ t in Ioi (0 : ℝ), phi (∑ _j : Fin 1, if 1 + t ≤ 1 then (1 : ℝ) else 0) = 0 := by
      rw [setIntegral_eq_zero_of_forall_eq_zero]
      intro t ht
      have hgt : ¬ (t ≤ 0) := by linarith [Set.mem_Ioi.mp ht]
      simp [hgt, phi]
    rw [h0]; norm_num
  h_laplace_int := fun _ lam _ => by
    have h0 : EqOn (fun t : ℝ => Real.exp (-lam * (1 + t)) * if 1 + t ≤ 1 then (1 : ℝ) else 0) (fun _ => 0) (Ioi 0) := by
      intro t ht
      have hgt : ¬ (t ≤ 0) := by linarith [Set.mem_Ioi.mp ht]
      simp [hgt]
    exact (integrable_zero _ _ _).congr (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (h0 ht).symm)
  h_eq29 := fun lam hlam => by
    have h0 : ∫ t in Ioi (0 : ℝ), Real.exp (-lam * (1 + t)) * (if 1 + t ≤ 1 then (1 : ℝ) else 0) = 0 := by
      rw [setIntegral_eq_zero_of_forall_eq_zero]
      intro t ht
      have hgt : ¬ (t ≤ 0) := by linarith [Set.mem_Ioi.mp ht]
      simp [hgt]
    simp only [Fin.sum_univ_one, h0, mul_one, one_mul]
    -- Need: 0 ≤ 1 - (1 - e^{-lam}) / lam
    have hle : (1 - Real.exp (-lam)) / lam ≤ 1 := by
      rw [div_le_one hlam]
      have := Real.add_one_le_exp (-lam)
      linarith
    have h1 : (1 / lam) * lam = 1 := by field_simp [hlam.ne']
    linarith

/-- Non-vacuity theorem: `GH26BaseInequalities` is inhabited (`Nonempty`). -/
theorem gh26_nonvacuous : Nonempty GH26BaseInequalities := ⟨gh26_nonvacuous_m1⟩

/-- Lemma 2 (`lem:jensen-mono`): Time-Varying Jensen Alignment and Monotonicity Reduction to `S = B = 1`.
    From `GH26BaseInequalities`, for any exponential mixture `(a, lam)` and upper envelope `Ubar`
    satisfying `U_1(t) ≤ Ubar(t)` for `t > 0` (where `U_1(t) = ∑_j (r_j / S) / (c_j + t)`),
    `REV ≤ 1 + ∑_k (a_k / λ_k) L(λ_k) + ∑_j (r_j / S) Ψ_{w, Ubar}(c_j)`. -/
theorem time_varying_jensen_alignment
    (inst : GH26BaseInequalities)
    {K : ℕ} (a lam : Fin K → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hsum : ∑ k : Fin K, a k = 1) (hlam : ∀ k, 0 < lam k)
    (Ubar : ℝ → ℝ)
    (hUbar : ∀ t, 0 < t → (∑ j : Fin inst.m, (inst.r j / inst.S) / (inst.c j + t)) ≤ Ubar t)
    (hPsi_int : ∀ j : Fin inst.m,
      Integrable (fun t => (inst.c j + t)⁻¹ * max 0 (hFun (Ubar t) - expMix a lam (inst.c j + t)))
        (volume.restrict (Ioi 0))) :
    inst.REV ≤
      1 + (∑ k : Fin K, (a k / lam k) * inst.L (lam k)) +
        ∑ j : Fin inst.m, (inst.r j / inst.S) * Psi a lam Ubar (inst.c j) := by
  haveI : Nonempty (Fin inst.m) := ⟨⟨0, inst.hm⟩⟩
  have hS_pos : 0 < inst.S := by
    rw [inst.hS_eq]
    exact Finset.sum_pos (fun j _ => inst.hr_pos j) Finset.univ_nonempty
  -- Pointwise Jensen + chord inequality for every t > 0
  have hpt : ∀ t, 0 < t →
      phi (∑ j : Fin inst.m, inst.Fbar j (inst.c j + t)) ≤
        (∑ j : Fin inst.m, expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t)) +
        (∑ j : Fin inst.m, inst.r j *
          ((inst.c j + t)⁻¹ * max 0 (hFun (Ubar t) - expMix a lam (inst.c j + t)))) := by
    intro t ht
    let U := ∑ j : Fin inst.m, inst.r j / (inst.c j + t)
    have hU_pos : 0 < U :=
      Finset.sum_pos (fun j _ => div_pos (inst.hr_pos j) (add_pos (inst.hc_pos j) ht)) Finset.univ_nonempty
    let π : Fin inst.m → ℝ := fun j => (inst.r j / (inst.c j + t)) / U
    have hπ_pos : ∀ j, 0 < π j := fun j =>
      div_pos (div_pos (inst.hr_pos j) (add_pos (inst.hc_pos j) ht)) hU_pos
    have hπ_sum : ∑ j : Fin inst.m, π j = 1 := by
      dsimp [π]
      rw [← Finset.sum_div, div_self hU_pos.ne']
    -- Step 1: Pointwise Jensen on convex φ
    have hsum_eq :
        ∑ j : Fin inst.m, inst.Fbar j (inst.c j + t) =
        ∑ j : Fin inst.m, π j • (inst.Fbar j (inst.c j + t) / π j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [smul_eq_mul]
      field_simp [(hπ_pos j).ne']
    have hjensen :
        phi (∑ j : Fin inst.m, inst.Fbar j (inst.c j + t)) ≤
        ∑ j : Fin inst.m, π j * phi (inst.Fbar j (inst.c j + t) / π j) := by
      rw [hsum_eq]
      have h := phi_convexOn.map_sum_le (t := Finset.univ)
        (w := π) (p := fun j => inst.Fbar j (inst.c j + t) / π j)
        (fun j _ => (hπ_pos j).le) hπ_sum
        (fun j _ => div_nonneg (inst.hFbar_nonneg j _) (hπ_pos j).le)
      simpa [smul_eq_mul] using h
    -- Step 2: Chord bound (eq. 28) per item j with ξ = U, ω = w(c_j + t)
    have hU_le_Ubar : U ≤ Ubar t := by
      have hU1 : U = inst.S * (∑ j : Fin inst.m, (inst.r j / inst.S) / (inst.c j + t)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        have hct : inst.c j + t ≠ 0 := (add_pos (inst.hc_pos j) ht).ne'
        field_simp [hS_pos.ne', hct]
        ring
      have hU1_nonneg : 0 ≤ ∑ j : Fin inst.m, (inst.r j / inst.S) / (inst.c j + t) :=
        Finset.sum_nonneg fun j _ => div_nonneg (div_nonneg (inst.hr_pos j).le hS_pos.le) (add_pos (inst.hc_pos j) ht).le
      calc
        U = inst.S * (∑ j : Fin inst.m, (inst.r j / inst.S) / (inst.c j + t)) := hU1
        _ ≤ 1 * (∑ j : Fin inst.m, (inst.r j / inst.S) / (inst.c j + t)) :=
            mul_le_mul_of_nonneg_right inst.hS_le hU1_nonneg
        _ ≤ Ubar t := by simpa using hUbar t ht
    have hterm : ∀ j : Fin inst.m,
        π j * phi (inst.Fbar j (inst.c j + t) / π j) ≤
          expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t) +
          inst.r j * ((inst.c j + t)⁻¹ * max 0 (hFun (Ubar t) - expMix a lam (inst.c j + t))) := by
      intro j
      have hct_pos : 0 < inst.c j + t := add_pos (inst.hc_pos j) ht
      have hw_nn : 0 ≤ expMix a lam (inst.c j + t) :=
        Finset.sum_nonneg fun k _ => mul_nonneg (ha k) (Real.exp_pos _).le
      have hx_le : inst.Fbar j (inst.c j + t) / π j ≤ U := by
        rw [div_le_iff₀ (hπ_pos j)]
        have hπU : U * π j = inst.r j / (inst.c j + t) := by
          dsimp [π]; field_simp [hU_pos.ne', hct_pos.ne']; ring
        rw [hπU]
        exact inst.hFbar_tail j t ht
      have hch := phi_chord_bound hw_nn (div_nonneg (inst.hFbar_nonneg j _) (hπ_pos j).le) hx_le
      have hmul := mul_le_mul_of_nonneg_left hch (hπ_pos j).le
      have h1 : π j * (expMix a lam (inst.c j + t) * (inst.Fbar j (inst.c j + t) / π j)) =
          expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t) := by
        field_simp [(hπ_pos j).ne']
      have h2 : π j * max 0 (phi U - expMix a lam (inst.c j + t) * U) =
          inst.r j * ((inst.c j + t)⁻¹ * max 0 (hFun U - expMix a lam (inst.c j + t))) := by
        have hfac : phi U - expMix a lam (inst.c j + t) * U =
            U * (hFun U - expMix a lam (inst.c j + t)) := by
          unfold hFun; rw [if_neg hU_pos.ne']; field_simp [hU_pos.ne']; ring
        rw [hfac, ← mul_zero U, ← mul_max_of_nonneg _ _ hU_pos.le, mul_zero]
        dsimp [π]
        field_simp [hU_pos.ne', hct_pos.ne']
        ring
      have hh_le : hFun U ≤ hFun (Ubar t) := hFun_mono hU_pos.le hU_le_Ubar
      have hmax_le : max 0 (hFun U - expMix a lam (inst.c j + t)) ≤
          max 0 (hFun (Ubar t) - expMix a lam (inst.c j + t)) :=
        max_le_max_left 0 (sub_le_sub_right hh_le _)
      have h3 : inst.r j * ((inst.c j + t)⁻¹ * max 0 (hFun U - expMix a lam (inst.c j + t))) ≤
          inst.r j * ((inst.c j + t)⁻¹ * max 0 (hFun (Ubar t) - expMix a lam (inst.c j + t))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmax_le (inv_pos.mpr hct_pos).le)
          (inst.hr_pos j).le
      linarith
    calc
      phi (∑ j : Fin inst.m, inst.Fbar j (inst.c j + t))
          ≤ ∑ j : Fin inst.m, π j * phi (inst.Fbar j (inst.c j + t) / π j) := hjensen
      _ ≤ ∑ j : Fin inst.m, (expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t) +
            inst.r j * ((inst.c j + t)⁻¹ * max 0 (hFun (Ubar t) - expMix a lam (inst.c j + t)))) :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = _ := Finset.sum_add_distrib
  -- Integrate hpt over t > 0
  have hint_mix : ∀ j : Fin inst.m,
      Integrable (fun t => expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t))
        (volume.restrict (Ioi 0)) := by
    intro j
    have heq :
        (fun t => expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t)) =
        fun t => ∑ k : Fin K, a k * (Real.exp (-lam k * (inst.c j + t)) * inst.Fbar j (inst.c j + t)) := by
      ext t; unfold expMix; rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [heq]
    exact integrable_finset_sum _ (fun k _ => (inst.h_laplace_int j (lam k) (hlam k)).const_mul (a k))
  have hint_rhs1 : Integrable (fun t => ∑ j : Fin inst.m, expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t))
      (volume.restrict (Ioi 0)) := integrable_finset_sum _ (fun j _ => hint_mix j)
  have hint_rhs2 : Integrable (fun t => ∑ j : Fin inst.m, inst.r j *
      ((inst.c j + t)⁻¹ * max 0 (hFun (Ubar t) - expMix a lam (inst.c j + t))))
      (volume.restrict (Ioi 0)) :=
    integrable_finset_sum _ (fun j _ => (hPsi_int j).const_mul (inst.r j))
  have hint_le :
      ∫ t in Ioi (0 : ℝ), phi (∑ j : Fin inst.m, inst.Fbar j (inst.c j + t)) ≤
        (∑ j : Fin inst.m, ∫ t in Ioi (0 : ℝ), expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t)) +
        (∑ j : Fin inst.m, inst.r j * ∫ t in Ioi (0 : ℝ),
          (inst.c j + t)⁻¹ * max 0 (hFun (Ubar t) - expMix a lam (inst.c j + t))) := by
    have h1 := integral_mono_ae inst.h_phi_int (Integrable.add hint_rhs1 hint_rhs2)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        simpa [Pi.add_apply] using hpt t ht)
    have hadd :
        ∫ t in Ioi (0 : ℝ),
          ((fun t => ∑ j : Fin inst.m, expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t)) +
           (fun t => ∑ j : Fin inst.m, inst.r j *
             ((inst.c j + t)⁻¹ * max 0 (hFun (Ubar t) - expMix a lam (inst.c j + t))))) t =
        (∫ t in Ioi (0 : ℝ), ∑ j : Fin inst.m, expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t)) +
        (∫ t in Ioi (0 : ℝ), ∑ j : Fin inst.m, inst.r j *
          ((inst.c j + t)⁻¹ * max 0 (hFun (Ubar t) - expMix a lam (inst.c j + t)))) :=
      integral_add hint_rhs1 hint_rhs2
    rw [hadd,
        integral_finset_sum _ (fun j _ => hint_mix j),
        integral_finset_sum _ (fun j _ => (hPsi_int j).const_mul (inst.r j))] at h1
    simpa [integral_mul_left] using h1
  -- Apply GH26 eq. (29) across the mixture weights a_k
  have hlaplace :
      ∑ j : Fin inst.m, ∫ t in Ioi (0 : ℝ), expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t) ≤
        (∑ k : Fin K, (a k / lam k) * inst.L (lam k)) -
        ∑ j : Fin inst.m, inst.r j * coreAvg a lam (inst.c j) := by
    have hrewrite :
        ∑ j : Fin inst.m, ∫ t in Ioi (0 : ℝ), expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t) =
        ∑ k : Fin K, a k * (∑ j : Fin inst.m, ∫ t in Ioi (0 : ℝ),
          Real.exp (-lam k * (inst.c j + t)) * inst.Fbar j (inst.c j + t)) := by
      have hinner : ∀ j : Fin inst.m,
          ∫ t in Ioi (0 : ℝ), expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t) =
          ∑ k : Fin K, a k * ∫ t in Ioi (0 : ℝ),
            Real.exp (-lam k * (inst.c j + t)) * inst.Fbar j (inst.c j + t) := by
        intro j
        have heq :
            (fun t => expMix a lam (inst.c j + t) * inst.Fbar j (inst.c j + t)) =
            fun t => ∑ k : Fin K, a k * (Real.exp (-lam k * (inst.c j + t)) * inst.Fbar j (inst.c j + t)) := by
          ext t; unfold expMix; rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro k _; ring
        rw [heq, integral_finset_sum _ (fun k _ => (inst.h_laplace_int j (lam k) (hlam k)).const_mul (a k))]
        simp [integral_mul_left]
      simp_rw [hinner]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.mul_sum]
    rw [hrewrite]
    have hstep1 :
        ∑ k : Fin K, a k * (∑ j : Fin inst.m, ∫ t in Ioi (0 : ℝ),
          Real.exp (-lam k * (inst.c j + t)) * inst.Fbar j (inst.c j + t)) ≤
        ∑ k : Fin K, a k * ((1 / lam k) * inst.L (lam k * inst.B) -
          ∑ j : Fin inst.m, inst.r j * ((1 - Real.exp (-lam k * inst.c j)) / (lam k * inst.c j))) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (inst.h_eq29 (lam k) (hlam k)) (ha k)
    have hstep2 :
        ∑ k : Fin K, a k * ((1 / lam k) * inst.L (lam k * inst.B) -
          ∑ j : Fin inst.m, inst.r j * ((1 - Real.exp (-lam k * inst.c j)) / (lam k * inst.c j))) ≤
        ∑ k : Fin K, a k * ((1 / lam k) * inst.L (lam k) -
          ∑ j : Fin inst.m, inst.r j * ((1 - Real.exp (-lam k * inst.c j)) / (lam k * inst.c j))) := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (ha k)
      have hLle : inst.L (lam k * inst.B) ≤ inst.L (lam k) :=
        inst.hL_mono (mul_pos (hlam k) inst.hB_pos) (by nlinarith [hlam k, inst.hB_le])
      have hinv : 0 ≤ 1 / lam k := div_nonneg zero_le_one (hlam k).le
      linarith [mul_le_mul_of_nonneg_left hLle hinv]
    have hstep3 :
        ∑ k : Fin K, a k * ((1 / lam k) * inst.L (lam k) -
          ∑ j : Fin inst.m, inst.r j * ((1 - Real.exp (-lam k * inst.c j)) / (lam k * inst.c j))) =
        (∑ k : Fin K, (a k / lam k) * inst.L (lam k)) -
        ∑ j : Fin inst.m, inst.r j * coreAvg a lam (inst.c j) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      congr 1
      · apply Finset.sum_congr rfl; intro k _; ring
      · simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        unfold coreAvg
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _; ring
    linarith
  -- Combine with eq. (27) and use S ≤ 1 with 1 + ∑ (r_j/S) Ψ(c_j) ≥ 0
  have hPsi_combine :
      (∑ j : Fin inst.m, inst.r j * ∫ t in Ioi (0 : ℝ),
          (inst.c j + t)⁻¹ * max 0 (hFun (Ubar t) - expMix a lam (inst.c j + t))) -
        (∑ j : Fin inst.m, inst.r j * coreAvg a lam (inst.c j)) =
      inst.S * ∑ j : Fin inst.m, (inst.r j / inst.S) * Psi a lam Ubar (inst.c j) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold Psi
    field_simp [hS_pos.ne']
    ring
  have h1Psi_nn : 0 ≤ 1 + ∑ j : Fin inst.m, (inst.r j / inst.S) * Psi a lam Ubar (inst.c j) := by
    have hsum_w : ∑ j : Fin inst.m, inst.r j / inst.S = 1 := by
      rw [← Finset.sum_div, ← inst.hS_eq, div_self hS_pos.ne']
    rw [← hsum_w, ← Finset.sum_add_distrib]
    apply Finset.sum_nonneg
    intro j _
    have hint_nn : 0 ≤ ∫ t in Ioi (0 : ℝ),
        (inst.c j + t)⁻¹ * max 0 (hFun (Ubar t) - expMix a lam (inst.c j + t)) := by
      apply setIntegral_nonneg measurableSet_Ioi
      intro t ht
      have hct : 0 < inst.c j + t := add_pos (inst.hc_pos j) ht
      exact mul_nonneg (inv_pos.mpr hct).le (le_max_left _ _)
    have hca : coreAvg a lam (inst.c j) ≤ 1 := coreAvg_le_one ha hsum hlam (inst.hc_pos j)
    have hPsi_ge : -1 ≤ Psi a lam Ubar (inst.c j) := by unfold Psi; linarith
    have hw_nn : 0 ≤ inst.r j / inst.S := div_nonneg (inst.hr_pos j).le hS_pos.le
    nlinarith
  have hS_scale :
      inst.S * (1 + ∑ j : Fin inst.m, (inst.r j / inst.S) * Psi a lam Ubar (inst.c j)) ≤
      1 + ∑ j : Fin inst.m, (inst.r j / inst.S) * Psi a lam Ubar (inst.c j) := by
    nlinarith [inst.hS_le, h1Psi_nn]
  linarith [inst.h_eq27]

/-- Shifted-payment lemma (Section 2 domain reduction):
    given any IC and IR mechanism `(a, p)` on `[0, ∞)^m` (with `a(x) ∈ [0, 1]^m`),
    the shifted payment `p̃(x) := p(x) - p(0)` preserves IC and IR and satisfies
    `0 ≤ p̃(x)` and `p(x) ≤ p̃(x)` for all `x ∈ [0, ∞)^m`. -/
theorem shifted_payment_ic_ir {m : ℕ}
    (a : (Fin m → ℝ) → (Fin m → ℝ)) (p : (Fin m → ℝ) → ℝ)
    (ha_nn : ∀ x j, 0 ≤ a x j)
    (hIC : ∀ x x', (∀ j, 0 ≤ x j) → (∀ j, 0 ≤ x' j) →
      (∑ j : Fin m, x j * a x' j) - p x' ≤ (∑ j : Fin m, x j * a x j) - p x)
    (hIR : ∀ x, (∀ j, 0 ≤ x j) → 0 ≤ (∑ j : Fin m, x j * a x j) - p x) :
    let pTilde : (Fin m → ℝ) → ℝ := fun x => p x - p 0
    -- (1) p̃ preserves IC
    (∀ x x', (∀ j, 0 ≤ x j) → (∀ j, 0 ≤ x' j) →
      (∑ j : Fin m, x j * a x' j) - pTilde x' ≤ (∑ j : Fin m, x j * a x j) - pTilde x) ∧
    -- (2) p̃ preserves IR
    (∀ x, (∀ j, 0 ≤ x j) → 0 ≤ (∑ j : Fin m, x j * a x j) - pTilde x) ∧
    -- (3) p̃(x) ≥ 0 for all x ≥ 0
    (∀ x, (∀ j, 0 ≤ x j) → 0 ≤ pTilde x) ∧
    -- (4) p̃(x) ≥ p(x) for all x
    (∀ x, p x ≤ pTilde x) := by
  intro pTilde
  have h0_nn : ∀ j : Fin m, 0 ≤ (0 : Fin m → ℝ) j := fun _ => le_rfl
  have hp0_le : p 0 ≤ 0 := by
    have h := hIR 0 h0_nn
    simp at h
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' hx hx'
    have h := hIC x x' hx hx'
    dsimp [pTilde]
    linarith
  · intro x hx
    have h := hIC x 0 hx h0_nn
    have hdot_nn : 0 ≤ ∑ j : Fin m, x j * a 0 j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hx j) (ha_nn 0 j)
    dsimp [pTilde]
    linarith
  · intro x hx
    have h := hIC 0 x h0_nn hx
    simp at h
    dsimp [pTilde]
    linarith
  · intro x
    dsimp [pTilde]
    linarith

end MathForgeMechDesign.UpperBoundJensenAndDomain
