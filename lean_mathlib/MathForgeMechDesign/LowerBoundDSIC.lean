import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

/-!
# Mechanism Design 2.195 Lower Bound: DSIC, IR, and Tie-Breaking Invariance (`L-STRETCH`)

Formalizes Lemma 6 of `proof-forge/v2/paper/proof.tex`:
- The posted-menu mechanism `M_0` on `A ∪ B` (offering bundle `B` at price `p_B`, and an entry-fee
  menu on `A` with entry fee `F` and item prices `p_j`).
- The downward `(ε_1, ε_2, ε_3)`-perturbed mechanism `M_δ` on `A ∪ B`.
- Proof that any posted-menu mechanism with free opt-out `0` is DSIC and IR under EVERY buyer
  tie-breaking rule.
- Exact tie-breaking invariance: on every valuation profile `(x_A, z_B)` with `x_j ∈ {0} ∪ [p_j, ∞)`,
  EVERY utility-maximizing choice of the buyer under `M_δ` yields payment at least the
  seller-favoring payment of `M_0` minus `ε_1 + |A| * ε_2 + ε_3` (hence `≥ rev(M_0) - δ`).
-/

namespace MathForgeMechDesign.LowerBoundDSIC

open scoped BigOperators

/-- A menu outcome on finite item set `A` plus grand bundle `B`:
    `allocA : A → Bool` (which items in `A` are purchased) and `buyB : Bool` (whether `B` is purchased). -/
structure Outcome (A : Type*) where
  allocA : A → Bool
  buyB : Bool

/-- Opt-out outcome (buy nothing). -/
def Outcome.empty {A : Type*} : Outcome A := ⟨fun _ => false, false⟩

/-- Additive valuation of an outcome `(allocA, buyB)` given item values `xA : A → ℝ` and bundle value `zB : ℝ`. -/
noncomputable def valOf {A : Type*} [Fintype A] (xA : A → ℝ) (zB : ℝ) (o : Outcome A) : ℝ :=
  (∑ j : A, if o.allocA j then xA j else 0) + (if o.buyB then zB else 0)

/-- Posted-menu price of an outcome for parameters `(pB, F, pA)`:
    bundle `B` costs `pB` if bought; any nonempty subset `T ⊆ A` costs `F + ∑_{j ∈ T} pA j`. -/
noncomputable def menuPrice {A : Type*} [Fintype A] (pB F : ℝ) (pA : A → ℝ) (o : Outcome A) : ℝ :=
  (if ∃ j : A, o.allocA j = true then F else 0) +
  (∑ j : A, if o.allocA j then pA j else 0) +
  (if o.buyB then pB else 0)

/-- Buyer utility `u(v, o) = val(v, o) - price(o)`. -/
noncomputable def utility {A : Type*} [Fintype A] (pB F : ℝ) (pA : A → ℝ) (xA : A → ℝ) (zB : ℝ) (o : Outcome A) : ℝ :=
  valOf xA zB o - menuPrice pB F pA o

/-- Opt-out has valuation 0 and price 0, hence utility 0. -/
lemma utility_empty {A : Type*} [Fintype A] (pB F : ℝ) (pA : A → ℝ) (xA : A → ℝ) (zB : ℝ) :
    utility pB F pA xA zB Outcome.empty = 0 := by
  simp [utility, valOf, menuPrice, Outcome.empty]

/-- Any buyer tie-breaking rule `choice` selecting a utility-maximizing menu option is
    dominant-strategy incentive-compatible (DSIC) and individually rational (IR). -/
theorem posted_menu_dsic_ir {A : Type*} [Fintype A]
    (pB F : ℝ) (pA : A → ℝ)
    (choice : (A → ℝ) → ℝ → Outcome A)
    (hmax : ∀ xA zB o, utility pB F pA xA zB o ≤ utility pB F pA xA zB (choice xA zB)) :
    -- DSIC: reporting true type `(xA, zB)` weakly dominates any misreport `(xA', zB')`
    (∀ xA zB xA' zB',
      utility pB F pA xA zB (choice xA' zB') ≤ utility pB F pA xA zB (choice xA zB)) ∧
    -- IR: utility at true type is nonnegative
    (∀ xA zB, 0 ≤ utility pB F pA xA zB (choice xA zB)) := by
  constructor
  · intro xA zB xA' zB'
    exact hmax xA zB (choice xA' zB')
  · intro xA zB
    have h0 := hmax xA zB Outcome.empty
    rwa [utility_empty] at h0

/-- Surplus of item `j ∈ A` under base prices `pA`: `max 0 (xA j - pA j)`. -/
noncomputable def itemSurplus (x p : ℝ) : ℝ := max 0 (x - p)

/-- Total surplus on `A` under base prices `pA`: `U_A = ∑_{j ∈ A} (x_j - p_j)_+`. -/
noncomputable def totalSurplusA {A : Type*} [Fintype A] (pA xA : A → ℝ) : ℝ :=
  ∑ j : A, itemSurplus (xA j) (pA j)

/-- Seller-favoring payment of the unperturbed mechanism `M_0` at valuation profile `(xA, zB)`:
    buys `B` iff `zB ≥ pB`, and enters `A` (buying all `j` with `xA j ≥ pA j`) iff `U_A ≥ F`. -/
noncomputable def sellerFavPaymentM0 {A : Type*} [Fintype A] (pB F : ℝ) (pA xA : A → ℝ) (zB : ℝ) : ℝ :=
  (if totalSurplusA pA xA ≥ F then
    F + ∑ j : A, if xA j ≥ pA j then pA j else 0
   else 0) +
  (if zB ≥ pB then pB else 0)

/-- Exact pointwise tie-breaking invariance under downward `(ε₁, ε₂, ε₃)` perturbation (Lemma 6):
    if `0 < ε₁ < pB`, `0 < ε₂ < pA j` for all `j`, `0 < ε₃ < F`, and every item valuation
    lies in `{0} ∪ [pA j, ∞)`, then EVERY utility-maximizing menu choice `o*` under the
    perturbed prices `(pB - ε₁, F - ε₃, pA - ε₂)` achieves payment at least
    `sellerFavPaymentM0 - (ε₁ + |A| * ε₂ + ε₃)`. -/
theorem perturbed_menu_payment_ge {A : Type*} [Fintype A]
    (pB F ε₁ ε₂ ε₃ : ℝ) (pA xA : A → ℝ) (zB : ℝ)
    (hε₁ : 0 < ε₁) (hε₁_lt : ε₁ < pB)
    (hε₂ : 0 < ε₂) (hε₂_lt : ∀ j, ε₂ < pA j)
    (hε₃ : 0 < ε₃) (hε₃_lt : ε₃ < F)
    (_hsupp : ∀ j, xA j = 0 ∨ pA j ≤ xA j)
    (o : Outcome A)
    (hopt : ∀ o', utility (pB - ε₁) (F - ε₃) (fun j => pA j - ε₂) xA zB o' ≤
                  utility (pB - ε₁) (F - ε₃) (fun j => pA j - ε₂) xA zB o) :
    sellerFavPaymentM0 pB F pA xA zB - (ε₁ + (Fintype.card A : ℝ) * ε₂ + ε₃) ≤
      menuPrice (pB - ε₁) (F - ε₃) (fun j => pA j - ε₂) o := by
  classical
  have hpB' : 0 < pB - ε₁ := sub_pos.mpr hε₁_lt
  have hF' : 0 < F - ε₃ := sub_pos.mpr hε₃_lt
  have hpA' : ∀ j, 0 < pA j - ε₂ := fun j => sub_pos.mpr (hε₂_lt j)
  -- Helper: utility splits additively into A-part and B-part
  have hutil_split : ∀ (o' : Outcome A),
      utility (pB - ε₁) (F - ε₃) (fun j => pA j - ε₂) xA zB o' =
        ((∑ j : A, if o'.allocA j then xA j - (pA j - ε₂) else 0) -
          (if ∃ j : A, o'.allocA j = true then F - ε₃ else 0)) +
        (if o'.buyB then zB - (pB - ε₁) else 0) := by
    intro o'
    unfold utility valOf menuPrice
    have hsum :
        (∑ j : A, if o'.allocA j then xA j else 0) -
        (∑ j : A, if o'.allocA j then pA j - ε₂ else 0) =
        ∑ j : A, if o'.allocA j then xA j - (pA j - ε₂) else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      cases o'.allocA j <;> simp
    split_ifs <;> linarith
  -- Part 1: Bundle B payment under `o` is ≥ (if zB ≥ pB then pB else 0) - ε₁
  have hB_pay :
      (if zB ≥ pB then pB else 0) - ε₁ ≤ (if o.buyB then pB - ε₁ else 0) := by
    by_cases hz : zB ≥ pB
    · have hbuyB : o.buyB = true := by
        by_contra hnb
        have hnb' : o.buyB = false := Bool.eq_false_iff.mpr hnb
        let oFlip : Outcome A := ⟨o.allocA, true⟩
        have hle := hopt oFlip
        rw [hutil_split oFlip, hutil_split o, hnb'] at hle
        simp [oFlip] at hle
        linarith
      simp [hz, hbuyB]
    · simp only [hz, ite_false]
      split_ifs <;> linarith
  -- Part 2: Inside A, if `o` enters A (`∃ j, o.allocA j = true`), then it buys EVERY j with xA j ≥ pA j
  -- (since adding such j strictly increases utility by ≥ ε₂ > 0), and if U_A ≥ F then `o` MUST enter A.
  have hA_pay :
      (if totalSurplusA pA xA ≥ F then
        F + ∑ j : A, if xA j ≥ pA j then pA j else 0
       else 0) - ((Fintype.card A : ℝ) * ε₂ + ε₃) ≤
      (if ∃ j : A, o.allocA j = true then F - ε₃ else 0) +
      (∑ j : A, if o.allocA j then pA j - ε₂ else 0) := by
    by_cases hU : totalSurplusA pA xA ≥ F
    · -- First show `o` MUST enter A: compare with `oEnter` buying `{j | xA j ≥ pA j}`
      let allocBest : A → Bool := fun j => decide (pA j ≤ xA j)
      have hexBest : ∃ j : A, allocBest j = true := by
        by_contra hnone
        push_neg at hnone
        have hzero : totalSurplusA pA xA = 0 := by
          unfold totalSurplusA itemSurplus
          apply Finset.sum_eq_zero
          intro j _
          have hnot : ¬ (pA j ≤ xA j) := by
            have := hnone j
            simpa [allocBest] using this
          simp [max_eq_left (by linarith : xA j - pA j ≤ 0)]
        linarith
      have hU_enter :
          F - ε₃ < ∑ j : A, if allocBest j then xA j - (pA j - ε₂) else 0 := by
        have hge :
            totalSurplusA pA xA ≤
            ∑ j : A, if allocBest j then xA j - (pA j - ε₂) else 0 := by
          unfold totalSurplusA itemSurplus
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : pA j ≤ xA j
          · simp [allocBest, hj, max_eq_right (sub_nonneg.mpr hj)]
            linarith
          · simp [allocBest, hj, max_eq_left (by linarith : xA j - pA j ≤ 0)]
        linarith
      have hex_o : ∃ j : A, o.allocA j = true := by
        by_contra hnone
        have hnone' : ∀ j, o.allocA j = false := fun j =>
          Bool.eq_false_iff.mpr (fun hj => hnone ⟨j, hj⟩)
        let oAlt : Outcome A := ⟨allocBest, o.buyB⟩
        have hle := hopt oAlt
        rw [hutil_split oAlt, hutil_split o] at hle
        simp [oAlt, hnone', hexBest, hnone] at hle
        linarith
      -- Second, since `o` enters A, for every j with xA j ≥ pA j we MUST have o.allocA j = true
      have hall_ge : ∀ j : A, pA j ≤ xA j → o.allocA j = true := by
        intro j hj
        by_contra hnf
        have hnf' : o.allocA j = false := Bool.eq_false_iff.mpr hnf
        let allocAdd : A → Bool := fun i => if i = j then true else o.allocA i
        have hexAdd : ∃ i : A, allocAdd i = true := ⟨j, by simp [allocAdd]⟩
        let oAdd : Outcome A := ⟨allocAdd, o.buyB⟩
        have hle := hopt oAdd
        rw [hutil_split oAdd, hutil_split o] at hle
        simp only [oAdd, if_pos hexAdd, if_pos hex_o] at hle
        have hdiff :
            (∑ i : A, if allocAdd i then xA i - (pA i - ε₂) else 0) -
            (∑ i : A, if o.allocA i then xA i - (pA i - ε₂) else 0) =
            xA j - (pA j - ε₂) := by
          rw [← Finset.sum_sub_distrib]
          rw [Finset.sum_eq_single j]
          · simp [allocAdd, hnf']
          · intro i _ hij
            simp [allocAdd, hij]
          · intro hjmem; exact absurd (Finset.mem_univ j) hjmem
        linarith
      -- Therefore payment on A is ≥ (F - ε₃) + ∑_{j : xA j ≥ pA j} (pA j - ε₂)
      simp only [if_pos hU, if_pos hex_o]
      have hsum_ge :
          (∑ j : A, if xA j ≥ pA j then pA j else 0) - (Fintype.card A : ℝ) * ε₂ ≤
          ∑ j : A, if o.allocA j then pA j - ε₂ else 0 := by
        have hcard :
            (Fintype.card A : ℝ) * ε₂ = ∑ _j : A, ε₂ := by
          simp [Finset.sum_const, nsmul_eq_mul]
        rw [hcard, ← Finset.sum_sub_distrib]
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : xA j ≥ pA j
        · have hoj := hall_ge j hj
          simp [hj, hoj]
        · simp only [hj, ite_false]
          have hnonneg : 0 ≤ (if o.allocA j then pA j - ε₂ else 0) := by
            split_ifs
            · exact (hpA' j).le
            · exact le_rfl
          linarith
      linarith
    · -- When U_A < F, M_0 collects 0 on A, while M_δ collects ≥ 0 on A
      simp only [if_neg hU]
      have hF_nonneg : 0 ≤ (if ∃ j : A, o.allocA j = true then F - ε₃ else 0) := by
        split_ifs
        · exact hF'.le
        · exact le_rfl
      have hsum_nonneg : 0 ≤ ∑ j : A, if o.allocA j then pA j - ε₂ else 0 := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs
        · exact (hpA' j).le
        · exact le_rfl
      have hcard_nonneg : 0 ≤ (Fintype.card A : ℝ) * ε₂ := by positivity
      linarith
  unfold sellerFavPaymentM0 menuPrice
  linarith

end MathForgeMechDesign.LowerBoundDSIC
