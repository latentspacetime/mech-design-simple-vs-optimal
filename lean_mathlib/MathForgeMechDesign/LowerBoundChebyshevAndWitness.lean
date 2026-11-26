import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.BigOperators.Group.Finset

/-!
# Mechanism Design 2.195 Lower Bound: Concentrating Bundle `B`, Chebyshev/BREV Bound, and Conservative Finite Witness (`L-SHOULD`)

Proves:
1. Exact moments of the concentrating bundle `B` (`N_b ≥ 2`, `Δ = S_A / (N_b^2 * H_{N_b})`):
   - `REV(Y) = Δ`, `SREV(B) = S_A / H_{N_b}`, `SREV(A ∪ B) = S_A * (1 + 1 / H_{N_b})`.
   - `E[Y] = S_A / N_b^2`, `E[Y^2] = Δ^2 * (2 * N_b - H_{N_b})`, `E[Z_B] = S_A`,
     and `Var(Z_B) < 2 * S_A^2 / (N_b * H_{N_b}^2)`.
2. Deterministic/probabilistic case-split lemma:
   `∀ x ≥ 0, ∀ p ≥ 0, (∀ q ≥ 0, q * P(q) ≤ S_A) → p * P_shift(x, p) ≤ max S_A x`,
   and the `BREV(A ∪ B) ≤ SREV(A ∪ B)` deduction for all `N_b ≥ 2` using `E|Z_B - S_A| ≤ √Var(Z_B)`
   and `√(2 / N_b) ≤ 1`.
3. Dyadic harmonic lower bound by induction on `m : ℕ`:
   `1 + (m : ℝ) / 2 ≤ (harmonic (2 ^ m) : ℝ)` (so `23401 ≤ (harmonic (2 ^ 46800) : ℝ)`).
4. Exact conservative finite witness `N_b = 2 ^ 46800`, `δ = S_A / 10 ^ 8` for
   `r = 2195136628895 / 10^12`:
   - `r - 439 / 200 > (3195 / 1000) / H + 2 * (1 - 1 / H) / N_b + δ / S_A` (with slack `> 8.62e-8`),
   - `(E_A + (S_A - S_A / H) * (1 - 2 / N_b) - δ) / (S_A + S_A / H) > 439 / 200`
     whenever `(E_A + S_A) / S_A ≥ r`.
-/

namespace MathForgeMechDesign.LowerBoundChebyshev

open scoped BigOperators

/-- Real-valued harmonic number `H_n = ∑_{k=1}^n 1 / k`. -/
noncomputable def H (n : ℕ) : ℝ := (harmonic n : ℝ)

lemma H_eq_sum_Icc (n : ℕ) : H n = ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) := by
  unfold H
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp [one_div]

lemma H_pos {n : ℕ} (hn : n ≠ 0) : 0 < H n := by
  unfold H
  exact_mod_cast harmonic_pos hn

lemma H_ge_one {n : ℕ} (hn : 1 ≤ n) : 1 ≤ H n := by
  rw [H_eq_sum_Icc]
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨le_rfl, hn⟩
  have hle := Finset.single_le_sum (f := fun k : ℕ => (1 : ℝ) / (k : ℝ))
    (fun k _ => by positivity) h1
  simpa using hle

/-- Step size `Δ = S_A / (N_b^2 * H_{N_b})`. -/
noncomputable def deltaStep (S_A : ℝ) (Nb : ℕ) : ℝ :=
  S_A / ((Nb : ℝ) ^ 2 * H Nb)

/-- Point mass of one item `Y ∈ B` at `k * Δ` for `k ∈ {1, ..., N_b}`:
    `Pr[Y ≥ k Δ] = 1/k`, so `Pr[Y = k Δ] = 1/k - 1/(k+1)` for `k < N_b` and `1/N_b` for `k = N_b`. -/
noncomputable def pmfB (Nb : ℕ) (k : ℕ) : ℝ :=
  if 1 ≤ k ∧ k ≤ Nb then
    if k = Nb then (1 : ℝ) / (Nb : ℝ)
    else (1 : ℝ) / (k : ℝ) - (1 : ℝ) / ((k + 1 : ℕ) : ℝ)
  else 0

lemma sum_pmfB_tail (Nb m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ Nb) :
    ∑ k ∈ Finset.Icc m Nb, pmfB Nb k = (1 : ℝ) / (m : ℝ) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hm2
  induction d generalizing m with
  | zero =>
    have hm_eq : m = Nb := by omega
    subst hm_eq
    simp [pmfB, hm1]
  | succ d ih =>
    have hm_lt : m < Nb := by omega
    have hm_ne : m ≠ Nb := ne_of_lt hm_lt
    have hsplit : Finset.Icc m Nb = insert m (Finset.Icc (m + 1) Nb) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    rw [ih (m + 1) (by omega) (by omega) (by omega)]
    unfold pmfB
    rw [if_pos ⟨hm1, hm2⟩, if_neg hm_ne]
    ring

lemma pmfB_sum_one {Nb : ℕ} (hNb : 1 ≤ Nb) :
    ∑ k ∈ Finset.Icc 1 Nb, pmfB Nb k = 1 := by
  simpa using sum_pmfB_tail Nb 1 le_rfl hNb

/-- Single-item survival probability `Pr[Y ≥ v]` for `v > 0`. -/
noncomputable def survB (S_A : ℝ) (Nb : ℕ) (v : ℝ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 Nb).filter (fun k : ℕ => v ≤ (k : ℝ) * deltaStep S_A Nb), pmfB Nb k

/-- Single-item revenue `REV(Y) = Δ`: upper bound for all `v > 0` and attainment at `v = k * Δ`. -/
theorem revY_le (S_A : ℝ) (hSA : 0 < S_A) (Nb : ℕ) (hNb : 2 ≤ Nb) (v : ℝ) (_hv : 0 < v) :
    v * survB S_A Nb v ≤ deltaStep S_A Nb := by
  have hNb_ne : Nb ≠ 0 := by omega
  have hH_pos : 0 < H Nb := H_pos hNb_ne
  have hNb_pos : (0 : ℝ) < (Nb : ℝ) := by exact_mod_cast (show 0 < Nb by omega)
  have hΔ_pos : 0 < deltaStep S_A Nb := by unfold deltaStep; positivity
  by_cases hgt : (Nb : ℝ) * deltaStep S_A Nb < v
  · have hempty :
        (Finset.Icc 1 Nb).filter (fun k : ℕ => v ≤ (k : ℝ) * deltaStep S_A Nb) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have : (k : ℝ) * deltaStep S_A Nb ≤ (Nb : ℝ) * deltaStep S_A Nb :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk.2) hΔ_pos.le
      linarith
    unfold survB
    rw [hempty, Finset.sum_empty, mul_zero]
    exact hΔ_pos.le
  · push_neg at hgt
    set kStar := max 1 ⌈v / deltaStep S_A Nb⌉₊
    have hk1 : 1 ≤ kStar := le_max_left _ _
    have hk2 : kStar ≤ Nb := by
      refine max_le (by omega) ?_
      rw [Nat.ceil_le]
      exact (div_le_iff₀ hΔ_pos).mpr hgt
    have hvk : v ≤ (kStar : ℝ) * deltaStep S_A Nb := by
      have h1 : v / deltaStep S_A Nb ≤ (⌈v / deltaStep S_A Nb⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈v / deltaStep S_A Nb⌉₊ : ℝ) ≤ (kStar : ℝ) := by
        exact_mod_cast le_max_right 1 ⌈v / deltaStep S_A Nb⌉₊
      exact (div_le_iff₀ hΔ_pos).mp (le_trans h1 h2)
    have hfilt :
        (Finset.Icc 1 Nb).filter (fun k : ℕ => v ≤ (k : ℝ) * deltaStep S_A Nb) =
        Finset.Icc kStar Nb := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hka, hkb⟩, hvka⟩
        refine ⟨max_le hka ?_, hkb⟩
        rw [Nat.ceil_le]
        exact (div_le_iff₀ hΔ_pos).mpr hvka
      · rintro ⟨hka, hkb⟩
        refine ⟨⟨le_trans hk1 hka, hkb⟩, ?_⟩
        exact le_trans hvk (mul_le_mul_of_nonneg_right (by exact_mod_cast hka) hΔ_pos.le)
    unfold survB
    rw [hfilt, sum_pmfB_tail Nb kStar hk1 hk2]
    have hk_pos : (0 : ℝ) < (kStar : ℝ) := by exact_mod_cast hk1
    calc
      v * ((1 : ℝ) / (kStar : ℝ))
          ≤ ((kStar : ℝ) * deltaStep S_A Nb) * ((1 : ℝ) / (kStar : ℝ)) :=
            mul_le_mul_of_nonneg_right hvk (by positivity)
      _ = deltaStep S_A Nb := by field_simp [hk_pos.ne']

theorem revY_eq_on_grid (S_A : ℝ) (hSA : 0 < S_A) (Nb : ℕ) (hNb : 2 ≤ Nb)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ Nb) :
    ((k : ℝ) * deltaStep S_A Nb) * survB S_A Nb ((k : ℝ) * deltaStep S_A Nb) =
      deltaStep S_A Nb := by
  have hH_pos : 0 < H Nb := H_pos (by omega)
  have hNb_pos : (0 : ℝ) < (Nb : ℝ) := by exact_mod_cast (show 0 < Nb by omega)
  have hΔ_pos : 0 < deltaStep S_A Nb := by unfold deltaStep; positivity
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hfilt :
      (Finset.Icc 1 Nb).filter
        (fun j : ℕ => (k : ℝ) * deltaStep S_A Nb ≤ (j : ℝ) * deltaStep S_A Nb) =
      Finset.Icc k Nb := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨_, hj2⟩, hkj⟩
      have : (k : ℝ) ≤ (j : ℝ) := le_of_mul_le_mul_right hkj hΔ_pos
      exact ⟨by exact_mod_cast this, hj2⟩
    · rintro ⟨hkj, hj2⟩
      exact ⟨⟨le_trans hk1 hkj, hj2⟩,
        mul_le_mul_of_nonneg_right (by exact_mod_cast hkj) hΔ_pos.le⟩
  unfold survB
  rw [hfilt, sum_pmfB_tail Nb k hk1 hk2]
  field_simp [hk_pos.ne']

theorem srevB_eq (S_A : ℝ) (Nb : ℕ) (hNb : 2 ≤ Nb) :
    (Nb : ℝ) ^ 2 * deltaStep S_A Nb = S_A / H Nb := by
  have hNb_ne : (Nb : ℝ) ≠ 0 := by exact_mod_cast (show Nb ≠ 0 by omega)
  have hH_ne : H Nb ≠ 0 := (H_pos (by omega)).ne'
  unfold deltaStep
  field_simp [hNb_ne, hH_ne]
  ring

theorem srev_union_eq (S_A : ℝ) (Nb : ℕ) (hNb : 2 ≤ Nb) :
    S_A + (Nb : ℝ) ^ 2 * deltaStep S_A Nb = S_A * (1 + 1 / H Nb) := by
  rw [srevB_eq S_A Nb hNb]
  ring

/-- Exact first moment `E[Y] = ∑_{k=1}^{N_b} (k * Δ) * Pr[Y = k * Δ] = S_A / N_b^2`. -/
noncomputable def expY (S_A : ℝ) (Nb : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 Nb, ((k : ℝ) * deltaStep S_A Nb) * pmfB Nb k

/-- Exact second moment `E[Y^2] = ∑_{k=1}^{N_b} (k * Δ)^2 * Pr[Y = k * Δ]`. -/
noncomputable def expY2 (S_A : ℝ) (Nb : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 Nb, ((k : ℝ) * deltaStep S_A Nb) ^ 2 * pmfB Nb k

private lemma sum_k_pmfB (Nb : ℕ) (_hNb : 1 ≤ Nb) :
    ∑ k ∈ Finset.Icc 1 Nb, (k : ℝ) * pmfB Nb k = H Nb := by
  -- Use ∑_{k=1}^{N} k * pmfB(k) = ∑_{j=1}^{N} ∑_{k=j}^{N} pmfB(k) = ∑_{j=1}^N 1/j = H_N
  have h1 :
      ∑ k ∈ Finset.Icc 1 Nb, (k : ℝ) * pmfB Nb k =
      ∑ k ∈ Finset.Icc 1 Nb, ∑ _j ∈ Finset.Icc 1 k, pmfB Nb k := by
    apply Finset.sum_congr rfl
    intro k _
    simp [Finset.sum_const, Nat.card_Icc]
  rw [h1]
  -- Swap sums over {(k, j) : 1 ≤ j ≤ k ≤ Nb}
  have hswap :
      ∑ k ∈ Finset.Icc 1 Nb, ∑ _j ∈ Finset.Icc 1 k, pmfB Nb k =
      ∑ j ∈ Finset.Icc 1 Nb, ∑ k ∈ Finset.Icc j Nb, pmfB Nb k := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
      omega
    · intro p1 _ p2 _ heq
      cases p1; cases p2; simp_all
    · intro q hq
      refine ⟨⟨q.2, q.1⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hq ⊢
      omega
    · intro _ _; rfl
  rw [hswap, H_eq_sum_Icc]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Icc] at hj
  exact sum_pmfB_tail Nb j hj.1 hj.2

private lemma sum_k_sq_eq (k : ℕ) :
    ((k : ℝ) ^ 2) = ∑ j ∈ Finset.Icc 1 k, (2 * (j : ℝ) - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp), ← ih]
    push_cast
    ring

private lemma sum_k2_pmfB (Nb : ℕ) (_hNb : 1 ≤ Nb) :
    ∑ k ∈ Finset.Icc 1 Nb, (k : ℝ) ^ 2 * pmfB Nb k = 2 * (Nb : ℝ) - H Nb := by
  have h1 :
      ∑ k ∈ Finset.Icc 1 Nb, (k : ℝ) ^ 2 * pmfB Nb k =
      ∑ k ∈ Finset.Icc 1 Nb, ∑ j ∈ Finset.Icc 1 k, (2 * (j : ℝ) - 1) * pmfB Nb k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [sum_k_sq_eq k, Finset.sum_mul]
  rw [h1]
  have hswap :
      ∑ k ∈ Finset.Icc 1 Nb, ∑ j ∈ Finset.Icc 1 k, (2 * (j : ℝ) - 1) * pmfB Nb k =
      ∑ j ∈ Finset.Icc 1 Nb, ∑ k ∈ Finset.Icc j Nb, (2 * (j : ℝ) - 1) * pmfB Nb k := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
      omega
    · intro p1 _ p2 _ heq
      cases p1; cases p2; simp_all
    · intro q hq
      refine ⟨⟨q.2, q.1⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hq ⊢
      omega
    · intro _ _; rfl
  rw [hswap]
  have h2 :
      ∑ j ∈ Finset.Icc 1 Nb, ∑ k ∈ Finset.Icc j Nb, (2 * (j : ℝ) - 1) * pmfB Nb k =
      ∑ j ∈ Finset.Icc 1 Nb, ((2 : ℝ) - (1 : ℝ) / (j : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_Icc] at hj
    rw [← Finset.mul_sum, sum_pmfB_tail Nb j hj.1 hj.2]
    have hj_pos : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    field_simp [hj_pos]
  rw [h2, Finset.sum_sub_distrib, ← H_eq_sum_Icc]
  simp [Finset.sum_const, Nat.card_Icc]
  ring

/-- `E[Y] = S_A / N_b^2`. -/
theorem expY_eq (S_A : ℝ) (Nb : ℕ) (hNb : 2 ≤ Nb) :
    expY S_A Nb = S_A / (Nb : ℝ) ^ 2 := by
  have hNb_ne : (Nb : ℝ) ≠ 0 := by exact_mod_cast (show Nb ≠ 0 by omega)
  have hH_ne : H Nb ≠ 0 := (H_pos (by omega)).ne'
  unfold expY
  have hpull :
      ∑ k ∈ Finset.Icc 1 Nb, ((k : ℝ) * deltaStep S_A Nb) * pmfB Nb k =
      deltaStep S_A Nb * ∑ k ∈ Finset.Icc 1 Nb, (k : ℝ) * pmfB Nb k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [hpull, sum_k_pmfB Nb (by omega)]
  unfold deltaStep
  field_simp [hNb_ne, hH_ne]
  ring

/-- `E[Y^2] = Δ^2 * (2 * N_b - H_{N_b})`. -/
theorem expY2_eq (S_A : ℝ) (Nb : ℕ) (hNb : 2 ≤ Nb) :
    expY2 S_A Nb = (deltaStep S_A Nb) ^ 2 * (2 * (Nb : ℝ) - H Nb) := by
  unfold expY2
  have hpull :
      ∑ k ∈ Finset.Icc 1 Nb, ((k : ℝ) * deltaStep S_A Nb) ^ 2 * pmfB Nb k =
      (deltaStep S_A Nb) ^ 2 * ∑ k ∈ Finset.Icc 1 Nb, (k : ℝ) ^ 2 * pmfB Nb k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [hpull, sum_k2_pmfB Nb (by omega)]

/-- `E[Z_B] = N_b^2 * E[Y] = S_A`. -/
theorem expZB_eq (S_A : ℝ) (Nb : ℕ) (hNb : 2 ≤ Nb) :
    (Nb : ℝ) ^ 2 * expY S_A Nb = S_A := by
  have hNb_ne : (Nb : ℝ) ≠ 0 := by exact_mod_cast (show Nb ≠ 0 by omega)
  rw [expY_eq S_A Nb hNb]
  field_simp [hNb_ne]

/-- Exact variance of `Z_B = ∑_{j ∈ B} Y_j` (i.i.d. sum of `N_b^2` copies of `Y`):
    `Var(Z_B) = N_b^2 * (E[Y^2] - E[Y]^2) < 2 * S_A^2 / (N_b * H_{N_b}^2)`. -/
theorem varZB_lt (S_A : ℝ) (hSA : 0 < S_A) (Nb : ℕ) (hNb : 2 ≤ Nb) :
    (Nb : ℝ) ^ 2 * (expY2 S_A Nb - (expY S_A Nb) ^ 2) <
      2 * S_A ^ 2 / ((Nb : ℝ) * (H Nb) ^ 2) := by
  have hNb_pos : (0 : ℝ) < (Nb : ℝ) := by exact_mod_cast (show 0 < Nb by omega)
  have hH_pos : 0 < H Nb := H_pos (by omega)
  rw [expY2_eq S_A Nb hNb, expY_eq S_A Nb hNb]
  unfold deltaStep
  have heq :
      (Nb : ℝ) ^ 2 *
        ((S_A / ((Nb : ℝ) ^ 2 * H Nb)) ^ 2 * (2 * (Nb : ℝ) - H Nb) -
          (S_A / (Nb : ℝ) ^ 2) ^ 2) =
      S_A ^ 2 / ((Nb : ℝ) ^ 2 * (H Nb) ^ 2) * (2 * (Nb : ℝ) - H Nb - (H Nb) ^ 2) := by
    field_simp [hNb_pos.ne', hH_pos.ne']
    ring
  rw [heq]
  have hrhs :
      2 * S_A ^ 2 / ((Nb : ℝ) * (H Nb) ^ 2) =
      S_A ^ 2 / ((Nb : ℝ) ^ 2 * (H Nb) ^ 2) * (2 * (Nb : ℝ)) := by
    field_simp [hNb_pos.ne', hH_pos.ne']
    ring
  rw [hrhs]
  have hfac : 0 < S_A ^ 2 / ((Nb : ℝ) ^ 2 * (H Nb) ^ 2) := by positivity
  have hsub : 2 * (Nb : ℝ) - H Nb - (H Nb) ^ 2 < 2 * (Nb : ℝ) := by
    nlinarith
  exact mul_lt_mul_of_pos_left hsub hfac

/-- Deterministic case-split inequality (Lemma 2(3)):
    if `P` is a nonincreasing survival function in `[0, 1]` satisfying `q * P(q) ≤ S_A` for all
    `q ≥ 0` (where `P(q) = Pr[S_A + Z_A ≥ q]`), then for every `x ≥ 0` and `p ≥ 0`,
    `p * P(p - (x - S_A)) ≤ max S_A x`. -/
theorem shifted_bundle_price_le_max
    (S_A : ℝ) (hSA : 0 < S_A)
    (P : ℝ → ℝ)
    (hP_le_one : ∀ q, P q ≤ 1)
    (hP_anti : ∀ {a b}, a ≤ b → P b ≤ P a)
    (hP_brev : ∀ q, 0 ≤ q → q * P q ≤ S_A)
    (x p : ℝ) (_hx : 0 ≤ x) (hp : 0 ≤ p) :
    p * P (p - (x - S_A)) ≤ max S_A x := by
  by_cases hxSA : x ≤ S_A
  · have hle : p ≤ p - (x - S_A) := by linarith
    have h1 : P (p - (x - S_A)) ≤ P p := hP_anti hle
    have h2 : p * P (p - (x - S_A)) ≤ p * P p := mul_le_mul_of_nonneg_left h1 hp
    exact le_trans h2 (le_trans (hP_brev p hp) (le_max_left S_A x))
  · push_neg at hxSA
    by_cases hpx : p ≤ x
    · have h1 : p * P (p - (x - S_A)) ≤ p * 1 :=
        mul_le_mul_of_nonneg_left (hP_le_one _) hp
      exact le_trans (by linarith) (le_trans hpx (le_max_right S_A x))
    · push_neg at hpx
      set p' := p - (x - S_A)
      have hp'_gt_SA : S_A < p' := by dsimp [p']; linarith
      have hp'_pos : 0 < p' := lt_trans hSA hp'_gt_SA
      have hP_le : P p' ≤ S_A / p' := (le_div_iff₀ hp'_pos).mpr (by
        have := hP_brev p' hp'_pos.le; linarith)
      have h1 : p * P p' ≤ p * (S_A / p') := mul_le_mul_of_nonneg_left hP_le hp
      have h2 : p * (S_A / p') = S_A + (S_A / p') * (x - S_A) := by
        have hp_eq : p = p' + (x - S_A) := by dsimp [p']; ring
        rw [hp_eq]
        field_simp [hp'_pos.ne']
        ring
      have hSA_div_lt : S_A / p' < 1 := (div_lt_one hp'_pos).mpr hp'_gt_SA
      have h3 : (S_A / p') * (x - S_A) < 1 * (x - S_A) :=
        mul_lt_mul_of_pos_right hSA_div_lt (sub_pos.mpr hxSA)
      have h4 : p * P p' ≤ x := by linarith
      exact le_trans h4 (le_max_right S_A x)

/-- Abstract `BREV(A ∪ B) ≤ SREV(A ∪ B)` bound from Cauchy-Schwarz `E|Z_B - S_A| ≤ √Var(Z_B)`
    and `N_b ≥ 2` (`√(2 / N_b) ≤ 1`). -/
theorem brev_le_srev_of_var_bound
    (S_A : ℝ) (hSA : 0 < S_A) (Nb : ℕ) (hNb : 2 ≤ Nb)
    (brevVal eAbsDev varZB : ℝ)
    (h_brev_le : brevVal ≤ S_A + eAbsDev)
    (h_cs : eAbsDev ≤ Real.sqrt varZB)
    (h_var_lt : varZB < 2 * S_A ^ 2 / ((Nb : ℝ) * (H Nb) ^ 2)) :
    brevVal < S_A + S_A / H Nb := by
  have hNb_pos : (0 : ℝ) < (Nb : ℝ) := by exact_mod_cast (show 0 < Nb by omega)
  have hNb_ge2 : (2 : ℝ) ≤ (Nb : ℝ) := by exact_mod_cast hNb
  have hH_pos : 0 < H Nb := H_pos (by omega)
  have h2div_le1 : 2 / (Nb : ℝ) ≤ 1 := (div_le_one hNb_pos).mpr hNb_ge2
  have hvar_le : varZB < (S_A / H Nb) ^ 2 := by
    have h1 : 2 * S_A ^ 2 / ((Nb : ℝ) * (H Nb) ^ 2) = (S_A / H Nb) ^ 2 * (2 / (Nb : ℝ)) := by
      field_simp [hNb_pos.ne', hH_pos.ne']
      ring
    have h2 : (S_A / H Nb) ^ 2 * (2 / (Nb : ℝ)) ≤ (S_A / H Nb) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left h2div_le1 (sq_nonneg _)
    linarith
  have hsqrt_lt : Real.sqrt varZB < S_A / H Nb := by
    by_cases h0 : 0 ≤ varZB
    · calc
        Real.sqrt varZB < Real.sqrt ((S_A / H Nb) ^ 2) :=
          Real.sqrt_lt_sqrt h0 hvar_le
        _ = S_A / H Nb := Real.sqrt_sq (by positivity)
    · push_neg at h0
      rw [Real.sqrt_eq_zero_of_nonpos h0.le]
      positivity
  linarith

/-- Dyadic harmonic lower bound by induction on `m : ℕ`:
    `1 + (m : ℝ) / 2 ≤ H (2 ^ m)`. -/
theorem harmonic_two_pow_ge (m : ℕ) :
    1 + (m : ℝ) / 2 ≤ H (2 ^ m) := by
  induction m with
  | zero =>
    rw [H_eq_sum_Icc]
    norm_num
  | succ m ih =>
    have hpow_pos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
    have hsplit :
        Finset.Icc 1 (2 ^ (m + 1)) =
        Finset.Icc 1 (2 ^ m) ∪ Finset.Icc (2 ^ m + 1) (2 ^ (m + 1)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_union]
      have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
      omega
    have hdisj : Disjoint (Finset.Icc 1 (2 ^ m)) (Finset.Icc (2 ^ m + 1) (2 ^ (m + 1))) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      simp only [Finset.mem_Icc] at hk1 hk2
      omega
    rw [H_eq_sum_Icc, hsplit, Finset.sum_union hdisj, ← H_eq_sum_Icc]
    -- Each of the 2^m terms in (2^m, 2^(m+1)] is ≥ 1 / 2^(m+1)
    have hblock :
        (1 : ℝ) / 2 ≤ ∑ k ∈ Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1)), (1 : ℝ) / (k : ℝ) := by
      have hterm :
          ∀ k ∈ Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1)),
            (1 : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ) ≤ (1 : ℝ) / (k : ℝ) := by
        intro k hk
        simp only [Finset.mem_Icc] at hk
        have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
        exact one_div_le_one_div_of_le hk_pos (by exact_mod_cast hk.2)
      have hsum_ge := Finset.sum_le_sum hterm
      rw [Finset.sum_const, Nat.card_Icc] at hsum_ge
      have hcard : 2 ^ (m + 1) + 1 - (2 ^ m + 1) = 2 ^ m := by
        have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
        omega
      rw [hcard, nsmul_eq_mul] at hsum_ge
      have hval : ((2 ^ m : ℕ) : ℝ) * ((1 : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ)) = (1 : ℝ) / 2 := by
        have h2m : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
        push_cast
        rw [pow_succ]
        field_simp [h2m]
      linarith
    push_cast
    linarith

/-- Conservative finite witness parameters: `N_b = 2 ^ 46800`, `S_A = 1949 / 400`, `δ = S_A / 10^8`. -/
def witnessExp : ℕ := 46800
def witnessNb : ℕ := 2 ^ witnessExp
noncomputable def witnessSA : ℝ := 1949 / 400
noncomputable def witnessDelta : ℝ := witnessSA / (10 : ℝ) ^ 8
noncomputable def certRatioR : ℝ := 2195136628895 / (10 : ℝ) ^ 12

lemma witnessH_ge : (23401 : ℝ) ≤ H witnessNb := by
  have h := harmonic_two_pow_ge witnessExp
  have h2 : (23401 : ℝ) ≤ 1 + (witnessExp : ℝ) / 2 := by
    unfold witnessExp; norm_num
  exact le_trans h2 h

private lemma pow_two_ge_ten_pow_12 {e : ℕ} (he : 40 ≤ e) :
    (10 : ℝ) ^ 12 ≤ ((2 ^ e : ℕ) : ℝ) := by
  have hpow : (2 : ℕ) ^ 40 ≤ 2 ^ e := Nat.pow_le_pow_right (Nat.succ_pos 1) he
  have h40 : (10 : ℕ) ^ 12 ≤ 2 ^ 40 := by norm_num
  have hle : (10 : ℕ) ^ 12 ≤ 2 ^ e := le_trans h40 hpow
  have hR : ((10 ^ 12 : ℕ) : ℝ) ≤ ((2 ^ e : ℕ) : ℝ) := Nat.cast_le.mpr hle
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hR

lemma witnessNb_ge : (10 : ℝ) ^ 12 ≤ (witnessNb : ℝ) :=
  pow_two_ge_ten_pow_12 (by decide)

/-- Exact slack inequality for the conservative finite witness `N_b = 2^46800`, `δ = S_A / 10^8`:
    `r - 439/200 > (3195/1000) / H_{N_b} + 2 * (1 - 1 / H_{N_b}) / N_b + δ / S_A`
    (with explicit margin `> 8.62e-8`). -/
theorem finite_witness_margin :
    (3195 / 1000 : ℝ) / H witnessNb +
      2 * (1 - 1 / H witnessNb) / (witnessNb : ℝ) +
      witnessDelta / witnessSA + (862 : ℝ) / (10 : ℝ) ^ 10 <
    certRatioR - 439 / 200 := by
  have hH : (23401 : ℝ) ≤ H witnessNb := witnessH_ge
  have hH_pos : 0 < H witnessNb := by linarith
  have hNb : (10 : ℝ) ^ 12 ≤ (witnessNb : ℝ) := witnessNb_ge
  have hNb_pos : (0 : ℝ) < (witnessNb : ℝ) := by linarith
  have hterm1 : (3195 / 1000 : ℝ) / H witnessNb ≤ (3195 / 1000 : ℝ) / 23401 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hH
  have hterm2 : 2 * (1 - 1 / H witnessNb) / (witnessNb : ℝ) ≤ 2 / (10 : ℝ) ^ 12 := by
    have hnum : 2 * (1 - 1 / H witnessNb) ≤ 2 := by
      have : 0 ≤ 1 / H witnessNb := by positivity
      linarith
    calc
      2 * (1 - 1 / H witnessNb) / (witnessNb : ℝ)
          ≤ 2 / (witnessNb : ℝ) := div_le_div_of_nonneg_right hnum hNb_pos.le
      _ ≤ 2 / (10 : ℝ) ^ 12 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hNb
  have hterm3 : witnessDelta / witnessSA = (1 : ℝ) / (10 : ℝ) ^ 8 := by
    unfold witnessDelta witnessSA
    norm_num
  rw [hterm3]
  have hnum_strict :
      (3195 / 1000 : ℝ) / 23401 + 2 / (10 : ℝ) ^ 12 + (1 : ℝ) / (10 : ℝ) ^ 8 +
        (862 : ℝ) / (10 : ℝ) ^ 10 < certRatioR - 439 / 200 := by
    unfold certRatioR
    norm_num
  linarith

/-- Main finite-witness theorem: whenever `(E_A + S_A) / S_A ≥ 2.195136628895`,
    the conservative finite instance with `N_b = 2 ^ 46800` and `δ = S_A / 10 ^ 8` satisfies
    `(E_A + (S_A - S_A / H_{N_b}) * (1 - 2 / N_b) - δ) / (S_A + S_A / H_{N_b}) > 439 / 200`. -/
theorem finite_witness_ratio_gt (E_A : ℝ)
    (hEA : certRatioR ≤ (E_A + witnessSA) / witnessSA) :
    (439 : ℝ) / 200 <
      (E_A + (witnessSA - witnessSA / H witnessNb) * (1 - 2 / (witnessNb : ℝ)) - witnessDelta) /
        (witnessSA + witnessSA / H witnessNb) := by
  have hSA_pos : 0 < witnessSA := by unfold witnessSA; norm_num
  have hH_pos : 0 < H witnessNb := by linarith [witnessH_ge]
  have hden_pos : 0 < witnessSA + witnessSA / H witnessNb := by positivity
  rw [lt_div_iff₀ hden_pos]
  have hmargin := finite_witness_margin
  have hEA_ge : certRatioR * witnessSA ≤ E_A + witnessSA := (le_div_iff₀ hSA_pos).mp hEA
  have hstep :
      (3195 / 1000 : ℝ) / H witnessNb +
        2 * (1 - 1 / H witnessNb) / (witnessNb : ℝ) +
        witnessDelta / witnessSA <
      certRatioR - 439 / 200 := by
    linarith
  have hmul :
      ((3195 / 1000 : ℝ) / H witnessNb +
        2 * (1 - 1 / H witnessNb) / (witnessNb : ℝ) +
        witnessDelta / witnessSA) * witnessSA <
      (certRatioR - 439 / 200) * witnessSA :=
    mul_lt_mul_of_pos_right hstep hSA_pos
  have hident :
      ((3195 / 1000 : ℝ) / H witnessNb +
        2 * (1 - 1 / H witnessNb) / (witnessNb : ℝ) +
        witnessDelta / witnessSA) * witnessSA =
      (439 / 200 : ℝ) * (witnessSA / H witnessNb) +
        witnessSA / H witnessNb +
        (witnessSA - witnessSA / H witnessNb) * (2 / (witnessNb : ℝ)) +
        witnessDelta := by
    field_simp [hSA_pos.ne']
    ring
  linarith

end MathForgeMechDesign.LowerBoundChebyshev
