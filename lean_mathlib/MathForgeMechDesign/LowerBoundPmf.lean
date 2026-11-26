import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor

/-!
# Mechanism Design 2.195 Lower Bound: 8-Group All-Paid Multi-Scale PMF (`L-MUST`)

Formalizes the exact 8-group all-paid multi-scale equal-revenue distribution matching
`cert_lb_2195.json` (`D = 100`, `N_a = 5000`, `F = 7`, `S_A = 1949/400`):
- Strict positivity of every support point mass `p_k > 0` and `p_0 > 0`.
- Exact PMF normalization (`p_0 + ∑_{k=k_min}^{k_max} p_k = 1`).
- Exact single-item revenue `REV(X_g) = r_g / N_a` for every posted price `v > 0`
  (including off-grid prices via the exact ceiling `k* = max(k_min, ⌈D * v⌉₊)`),
  with equality at every grid point `v = k / D` (`k_min ≤ k ≤ k_max`).
- Exact separate revenue `SREV(A) = ∑_{g : Fin 8} N_a * (r_g / N_a) = 1949 / 400`.
-/

namespace MathForgeMechDesign.LowerBoundPmf

open scoped BigOperators

/-- Grid denominator `D = 100`. -/
def gridDen : ℕ := 100

/-- Number of i.i.d. items per group `N_a = 5000`. -/
def groupSizeNa : ℕ := 5000

/-- Entry fee in grid ticks `F_ticks = 700` (`F = 7`). -/
def entryFeeTicks : ℕ := 700

/-- Exact total separate revenue of `A`: `S_A = 1949 / 400 = 4.8725`. -/
noncomputable def S_A : ℝ := 1949 / 400

/-- Exact integer specification of one item group matching `cert_lb_2195.json`. -/
structure GroupSpec where
  name : String
  rNum : ℕ
  rDen : ℕ
  kMin : ℕ
  kMax : ℕ
  pTick : ℕ
  deriving DecidableEq, Repr

/-- Exact 8-group specification matching Table 1 and `cert_lb_2195.json`. -/
def groupSpec : Fin 8 → GroupSpec
  | ⟨0, _⟩ => ⟨"A1", 227,  2000, 7,    707,  7⟩
  | ⟨1, _⟩ => ⟨"A2", 207,  2000, 11,   711,  11⟩
  | ⟨2, _⟩ => ⟨"A3", 9,    250,  16,   716,  16⟩
  | ⟨3, _⟩ => ⟨"A4", 547,  2000, 46,   746,  46⟩
  | ⟨4, _⟩ => ⟨"A5", 179,  1000, 82,   782,  82⟩
  | ⟨5, _⟩ => ⟨"A6", 199,  1000, 118,  818,  118⟩
  | ⟨6, _⟩ => ⟨"A7", 817,  2000, 166,  866,  166⟩
  | ⟨7, _⟩ => ⟨"A8", 7119, 2000, 1545, 2245, 1545⟩

/-- Group revenue parameter `r_g = rNum / rDen`. -/
noncomputable def rVal (g : Fin 8) : ℝ :=
  ((groupSpec g).rNum : ℝ) / ((groupSpec g).rDen : ℝ)

lemma groupSpec_valid (g : Fin 8) :
    0 < (groupSpec g).rNum ∧ 0 < (groupSpec g).rDen ∧
    1 ≤ (groupSpec g).kMin ∧ (groupSpec g).kMin ≤ (groupSpec g).kMax ∧
    (groupSpec g).kMax = (groupSpec g).kMin + entryFeeTicks ∧
    (groupSpec g).pTick = (groupSpec g).kMin := by
  fin_cases g <;> simp [groupSpec, entryFeeTicks]

lemma rVal_pos (g : Fin 8) : 0 < rVal g := by
  have h := groupSpec_valid g
  unfold rVal
  exact div_pos (by exact_mod_cast h.1) (by exact_mod_cast h.2.1)

/-- Discrete survival probability formula `S_g(k) = D * r_g / (N_a * k)` for positive integer `k`. -/
noncomputable def survFormula (g : Fin 8) (k : ℕ) : ℝ :=
  (gridDen : ℝ) * rVal g / ((groupSizeNa : ℝ) * (k : ℝ))

/-- Point mass `Pr[X_g = k / D]` for `k ∈ [kMin, kMax]` (and `0` outside). -/
noncomputable def pmfPos (g : Fin 8) (k : ℕ) : ℝ :=
  if (groupSpec g).kMin ≤ k ∧ k ≤ (groupSpec g).kMax then
    if k = (groupSpec g).kMax then survFormula g k
    else survFormula g k - survFormula g (k + 1)
  else 0

/-- Point mass at zero `Pr[X_g = 0] = 1 - D * r_g / (N_a * kMin)`. -/
noncomputable def p0 (g : Fin 8) : ℝ :=
  1 - survFormula g (groupSpec g).kMin

/-- Exact support point mass positivity for every `k ∈ [kMin, kMax]`. -/
theorem pmfPos_pos (g : Fin 8) (k : ℕ)
    (hk1 : (groupSpec g).kMin ≤ k) (hk2 : k ≤ (groupSpec g).kMax) :
    0 < pmfPos g k := by
  have hval := groupSpec_valid g
  have hr : 0 < rVal g := rVal_pos g
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := lt_of_lt_of_le hval.2.2.1 hk1
    exact_mod_cast this
  have hD : (0 : ℝ) < (gridDen : ℝ) := by norm_num [gridDen]
  have hN : (0 : ℝ) < (groupSizeNa : ℝ) := by norm_num [groupSizeNa]
  unfold pmfPos
  rw [if_pos ⟨hk1, hk2⟩]
  split_ifs with hmax
  · unfold survFormula
    positivity
  · unfold survFormula
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hlt : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self k
    have hsub :
        (gridDen : ℝ) * rVal g / ((groupSizeNa : ℝ) * (k : ℝ)) -
        (gridDen : ℝ) * rVal g / ((groupSizeNa : ℝ) * ((k + 1 : ℕ) : ℝ)) =
        (gridDen : ℝ) * rVal g / (groupSizeNa : ℝ) *
          (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
      ring
    rw [hsub]
    have hdiff : 0 < 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
      rw [sub_pos]
      exact one_div_lt_one_div_of_lt hk_pos hlt
    positivity

/-- Exact positivity of the zero-atom probability `p_0 > 0` for every group `g : Fin 8`. -/
theorem p0_pos (g : Fin 8) : 0 < p0 g := by
  fin_cases g <;> norm_num [p0, survFormula, rVal, groupSpec, gridDen, groupSizeNa]

/-- Exact telescoping survival sum `∑_{k=m}^{kMax} pmfPos g k = survFormula g m`
    for all `kMin ≤ m ≤ kMax`. -/
theorem sum_pmfPos_Icc (g : Fin 8) (m : ℕ)
    (hm1 : (groupSpec g).kMin ≤ m) (hm2 : m ≤ (groupSpec g).kMax) :
    ∑ k ∈ Finset.Icc m (groupSpec g).kMax, pmfPos g k = survFormula g m := by
  -- Induct on d = kMax - m
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hm2
  induction d generalizing m with
  | zero =>
    have hm_eq : m = (groupSpec g).kMax := by omega
    subst hm_eq
    simp [pmfPos, hm1]
  | succ d ih =>
    have hm_lt : m < (groupSpec g).kMax := by omega
    have hm_ne : m ≠ (groupSpec g).kMax := ne_of_lt hm_lt
    have hsucc_le : m + 1 ≤ (groupSpec g).kMax := by omega
    have hsplit :
        Finset.Icc m (groupSpec g).kMax =
        insert m (Finset.Icc (m + 1) (groupSpec g).kMax) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : m ∉ Finset.Icc (m + 1) (groupSpec g).kMax := by
      simp
    rw [hsplit, Finset.sum_insert hnotmem]
    have hih : ∑ k ∈ Finset.Icc (m + 1) (groupSpec g).kMax, pmfPos g k = survFormula g (m + 1) :=
      ih (m + 1) (by omega) hsucc_le (by omega)
    rw [hih]
    unfold pmfPos
    rw [if_pos ⟨hm1, hm2⟩, if_neg hm_ne]
    ring

/-- Exact PMF normalization: `p_0 + ∑_{k=kMin}^{kMax} pmfPos g k = 1` for every group `g`. -/
theorem pmf_sum_eq_one (g : Fin 8) :
    p0 g + ∑ k ∈ Finset.Icc (groupSpec g).kMin (groupSpec g).kMax, pmfPos g k = 1 := by
  have hval := groupSpec_valid g
  rw [sum_pmfPos_Icc g (groupSpec g).kMin le_rfl hval.2.2.2.1]
  unfold p0
  ring

/-- Survival probability `Pr[X_g ≥ v]` for any positive posted price `v > 0`. -/
noncomputable def survReal (g : Fin 8) (v : ℝ) : ℝ :=
  ∑ k ∈ (Finset.Icc (groupSpec g).kMin (groupSpec g).kMax).filter
      (fun k : ℕ => v ≤ (k : ℝ) / (gridDen : ℝ)), pmfPos g k

lemma survReal_eq_zero_of_gt (g : Fin 8) (v : ℝ)
    (hv : ((groupSpec g).kMax : ℝ) / (gridDen : ℝ) < v) :
    survReal g v = 0 := by
  unfold survReal
  have hD : (0 : ℝ) < (gridDen : ℝ) := by norm_num [gridDen]
  have hempty :
      (Finset.Icc (groupSpec g).kMin (groupSpec g).kMax).filter
        (fun k : ℕ => v ≤ (k : ℝ) / (gridDen : ℝ)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk_le : (k : ℝ) / (gridDen : ℝ) ≤ ((groupSpec g).kMax : ℝ) / (gridDen : ℝ) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hk.2) hD.le
    linarith
  rw [hempty, Finset.sum_empty]

lemma survReal_eq_survFormula_ceil (g : Fin 8) (v : ℝ)
    (hv_le : v ≤ ((groupSpec g).kMax : ℝ) / (gridDen : ℝ)) :
    let kStar := max (groupSpec g).kMin ⌈(gridDen : ℝ) * v⌉₊
    survReal g v = survFormula g kStar ∧
      (groupSpec g).kMin ≤ kStar ∧ kStar ≤ (groupSpec g).kMax ∧
      v ≤ (kStar : ℝ) / (gridDen : ℝ) := by
  intro kStar
  have hval := groupSpec_valid g
  have hD : (0 : ℝ) < (gridDen : ℝ) := by norm_num [gridDen]
  have hkMin_le : (groupSpec g).kMin ≤ kStar := le_max_left _ _
  have hceil_le_max : ⌈(gridDen : ℝ) * v⌉₊ ≤ (groupSpec g).kMax := by
    rw [Nat.ceil_le]
    have := (le_div_iff₀ hD).mp hv_le
    linarith
  have hkStar_le : kStar ≤ (groupSpec g).kMax := max_le hval.2.2.2.1 hceil_le_max
  have hv_le_kStar : v ≤ (kStar : ℝ) / (gridDen : ℝ) := by
    rw [le_div_iff₀ hD]
    have h1 : (gridDen : ℝ) * v ≤ (⌈(gridDen : ℝ) * v⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(gridDen : ℝ) * v⌉₊ : ℝ) ≤ (kStar : ℝ) := by
      exact_mod_cast le_max_right (groupSpec g).kMin ⌈(gridDen : ℝ) * v⌉₊
    linarith
  have hfilt :
      (Finset.Icc (groupSpec g).kMin (groupSpec g).kMax).filter
        (fun k : ℕ => v ≤ (k : ℝ) / (gridDen : ℝ)) =
      Finset.Icc kStar (groupSpec g).kMax := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, hvk⟩
      refine ⟨max_le hk1 ?_, hk2⟩
      rw [Nat.ceil_le]
      have := (le_div_iff₀ hD).mp hvk
      linarith
    · rintro ⟨hk1, hk2⟩
      refine ⟨⟨le_trans hkMin_le hk1, hk2⟩, ?_⟩
      have hk1R : (kStar : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      exact le_trans hv_le_kStar (div_le_div_of_nonneg_right hk1R hD.le)
  refine ⟨?_, hkMin_le, hkStar_le, hv_le_kStar⟩
  unfold survReal
  rw [hfilt]
  exact sum_pmfPos_Icc g kStar hkMin_le hkStar_le

/-- Single-item revenue upper bound for EVERY positive posted price `v > 0` (including off-grid). -/
theorem posted_price_rev_le (g : Fin 8) (v : ℝ) (hv : 0 < v) :
    v * survReal g v ≤ rVal g / (groupSizeNa : ℝ) := by
  have hr : 0 < rVal g := rVal_pos g
  have hD : (0 : ℝ) < (gridDen : ℝ) := by norm_num [gridDen]
  have hN : (0 : ℝ) < (groupSizeNa : ℝ) := by norm_num [groupSizeNa]
  by_cases hgt : ((groupSpec g).kMax : ℝ) / (gridDen : ℝ) < v
  · rw [survReal_eq_zero_of_gt g v hgt, mul_zero]
    positivity
  · push_neg at hgt
    obtain ⟨hsurv, hk1, _, hvk⟩ := survReal_eq_survFormula_ceil g v hgt
    set kStar := max (groupSpec g).kMin ⌈(gridDen : ℝ) * v⌉₊
    have hval := groupSpec_valid g
    have hk_pos : (0 : ℝ) < (kStar : ℝ) := by
      have : 0 < kStar := lt_of_lt_of_le hval.2.2.1 hk1
      exact_mod_cast this
    have hsf_nonneg : 0 ≤ survFormula g kStar := by
      unfold survFormula; positivity
    rw [hsurv]
    calc
      v * survFormula g kStar
          ≤ ((kStar : ℝ) / (gridDen : ℝ)) * survFormula g kStar :=
            mul_le_mul_of_nonneg_right hvk hsf_nonneg
      _ = rVal g / (groupSizeNa : ℝ) := by
            unfold survFormula
            field_simp [hD.ne', hN.ne', hk_pos.ne']
            ring

/-- Exact equality at every positive grid support point `v = k / D` (`kMin ≤ k ≤ kMax`). -/
theorem posted_price_rev_eq_on_grid (g : Fin 8) (k : ℕ)
    (hk1 : (groupSpec g).kMin ≤ k) (hk2 : k ≤ (groupSpec g).kMax) :
    ((k : ℝ) / (gridDen : ℝ)) * survReal g ((k : ℝ) / (gridDen : ℝ)) =
      rVal g / (groupSizeNa : ℝ) := by
  have hval := groupSpec_valid g
  have hD : (0 : ℝ) < (gridDen : ℝ) := by norm_num [gridDen]
  have hN : (0 : ℝ) < (groupSizeNa : ℝ) := by norm_num [groupSizeNa]
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := lt_of_lt_of_le hval.2.2.1 hk1
    exact_mod_cast this
  have hfilt :
      (Finset.Icc (groupSpec g).kMin (groupSpec g).kMax).filter
        (fun j : ℕ => (k : ℝ) / (gridDen : ℝ) ≤ (j : ℝ) / (gridDen : ℝ)) =
      Finset.Icc k (groupSpec g).kMax := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨_, hj2⟩, hkj⟩
      have hkj' : (k : ℝ) ≤ (j : ℝ) := (div_le_div_iff_of_pos_right hD).mp hkj
      exact ⟨by exact_mod_cast hkj', hj2⟩
    · rintro ⟨hkj, hj2⟩
      exact ⟨⟨le_trans hk1 hkj, hj2⟩, div_le_div_of_nonneg_right (by exact_mod_cast hkj) hD.le⟩
  unfold survReal
  rw [hfilt, sum_pmfPos_Icc g k hk1 hk2]
  unfold survFormula
  field_simp [hD.ne', hN.ne', hk_pos.ne']
  ring

/-- Single-item monopoly revenue `REV(X_g) := sup_{v > 0} v * Pr[X_g ≥ v]`. -/
noncomputable def singleItemRev (g : Fin 8) : ℝ :=
  sSup { x : ℝ | ∃ v : ℝ, 0 < v ∧ x = v * survReal g v }

/-- Exact single-item revenue equality `REV(X_g) = r_g / N_a` for every group `g : Fin 8`. -/
theorem singleItemRev_eq (g : Fin 8) :
    singleItemRev g = rVal g / (groupSizeNa : ℝ) := by
  unfold singleItemRev
  have hval := groupSpec_valid g
  have hD : (0 : ℝ) < (gridDen : ℝ) := by norm_num [gridDen]
  have hkmin_pos : (0 : ℝ) < ((groupSpec g).kMin : ℝ) := by exact_mod_cast hval.2.2.1
  have hv0 : 0 < ((groupSpec g).kMin : ℝ) / (gridDen : ℝ) := div_pos hkmin_pos hD
  have hmem :
      rVal g / (groupSizeNa : ℝ) ∈ { x : ℝ | ∃ v : ℝ, 0 < v ∧ x = v * survReal g v } :=
    ⟨((groupSpec g).kMin : ℝ) / (gridDen : ℝ), hv0,
      (posted_price_rev_eq_on_grid g (groupSpec g).kMin le_rfl hval.2.2.2.1).symm⟩
  have hbdd :
      BddAbove { x : ℝ | ∃ v : ℝ, 0 < v ∧ x = v * survReal g v } := by
    refine ⟨rVal g / (groupSizeNa : ℝ), ?_⟩
    rintro x ⟨v, hv, rfl⟩
    exact posted_price_rev_le g v hv
  apply le_antisymm
  · apply csSup_le ⟨_, hmem⟩
    rintro x ⟨v, hv, rfl⟩
    exact posted_price_rev_le g v hv
  · exact le_csSup hbdd hmem

/-- Exact separate revenue of the 8-group instance `A`:
    `SREV(A) = ∑_{g : Fin 8} N_a * REV(X_g) = 1949 / 400`. -/
theorem srev_A_eq :
    ∑ g : Fin 8, (groupSizeNa : ℝ) * singleItemRev g = S_A := by
  have hN : (groupSizeNa : ℝ) ≠ 0 := by norm_num [groupSizeNa]
  have hsum :
      ∑ g : Fin 8, (groupSizeNa : ℝ) * singleItemRev g = ∑ g : Fin 8, rVal g := by
    apply Finset.sum_congr rfl
    intro g _
    rw [singleItemRev_eq g]
    field_simp [hN]
  rw [hsum, Fin.sum_univ_eight]
  norm_num [rVal, groupSpec, S_A]

end MathForgeMechDesign.LowerBoundPmf
