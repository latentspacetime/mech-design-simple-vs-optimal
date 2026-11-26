import MathForgeMechDesign.CertTreeData248
import MathForgeMechDesign.UpperBoundRecipAndTree
import MathForgeMechDesign.LowerBoundPmf
import MathForgeMechDesign.LowerBoundChebyshevAndWitness
import MathForgeMechDesign.UpperBoundJensenAndDomain
import MathForgeMechDesign.LowerBoundDSIC

/-!
# MathForgeMechDesign: Root Export Module & Axiom Audit

Imports all completed `L-MUST`, `L-SHOULD`, and `L-STRETCH` formalizations for the
Mechanism Design `[2.195, 2.48]` separation (`[439/200, 62/25]`) and emits `#print axioms`
for every exported theorem (verifying ONLY standard Lean foundation axioms:
`propext`, `Classical.choice`, `Quot.sound`).
-/

-- L-MUST #1: Reciprocal-Concavity, Discrete Cap Measure, 3-Moment Lens, Envelope, Farkas, Kernel Tree Cover
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.U1_pos
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.U1_le_inv
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.F_ge_self
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.hasDerivAt_U1
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.hasDerivAt_U1Deriv
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.F_deriv_ge_one
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.F_deriv2_le_zero
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.F_concaveOn
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.capMeasure_isProbabilityMeasure
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.capMeasure_ae_pos
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.lens_ineq_i
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.F_sub_ge
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.lens_ineq_ii
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.phiMap_tangent_le
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.lens_ineq_iii
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.lens_ineq_iv
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.lens_ineq_v
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.harmonic_tangent_le
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.U1_le_Ubar_le_inv
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.polytope_valid
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.farkas_decoupling
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.cert248_root_covers
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.cert248_leaf_count
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.cert248_disjoint_count
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.cert248_tree_valid
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.treeValid_covers_real
#print axioms MathForgeMechDesign.UpperBoundRecipAndTree.certTree248_covers_R0

-- L-MUST #2: 8-Group All-Paid Multi-Scale PMF, Single-Item REV, and SREV(A) = 1949/400
#print axioms MathForgeMechDesign.LowerBoundPmf.pmfPos_pos
#print axioms MathForgeMechDesign.LowerBoundPmf.p0_pos
#print axioms MathForgeMechDesign.LowerBoundPmf.sum_pmfPos_Icc
#print axioms MathForgeMechDesign.LowerBoundPmf.pmf_sum_eq_one
#print axioms MathForgeMechDesign.LowerBoundPmf.posted_price_rev_le
#print axioms MathForgeMechDesign.LowerBoundPmf.posted_price_rev_eq_on_grid
#print axioms MathForgeMechDesign.LowerBoundPmf.singleItemRev_eq
#print axioms MathForgeMechDesign.LowerBoundPmf.srev_A_eq

-- L-SHOULD #3: Concentrating Bundle B Moments, BREV <= SREV, Dyadic Harmonic Bound, Conservative Witness
#print axioms MathForgeMechDesign.LowerBoundChebyshev.revY_le
#print axioms MathForgeMechDesign.LowerBoundChebyshev.revY_eq_on_grid
#print axioms MathForgeMechDesign.LowerBoundChebyshev.srevB_eq
#print axioms MathForgeMechDesign.LowerBoundChebyshev.srev_union_eq
#print axioms MathForgeMechDesign.LowerBoundChebyshev.expY_eq
#print axioms MathForgeMechDesign.LowerBoundChebyshev.expY2_eq
#print axioms MathForgeMechDesign.LowerBoundChebyshev.expZB_eq
#print axioms MathForgeMechDesign.LowerBoundChebyshev.varZB_lt
#print axioms MathForgeMechDesign.LowerBoundChebyshev.shifted_bundle_price_le_max
#print axioms MathForgeMechDesign.LowerBoundChebyshev.brev_le_srev_of_var_bound
#print axioms MathForgeMechDesign.LowerBoundChebyshev.harmonic_two_pow_ge
#print axioms MathForgeMechDesign.LowerBoundChebyshev.finite_witness_margin
#print axioms MathForgeMechDesign.LowerBoundChebyshev.finite_witness_ratio_gt

-- L-STRETCH #4: GH26BaseInequalities, Time-Varying Jensen Alignment, Non-Vacuity Witness, Shifted-Payment Lemma
#print axioms MathForgeMechDesign.UpperBoundJensenAndDomain.phi_chord_bound
#print axioms MathForgeMechDesign.UpperBoundJensenAndDomain.hFun_mono
#print axioms MathForgeMechDesign.UpperBoundJensenAndDomain.gh26_nonvacuous
#print axioms MathForgeMechDesign.UpperBoundJensenAndDomain.time_varying_jensen_alignment
#print axioms MathForgeMechDesign.UpperBoundJensenAndDomain.shifted_payment_ic_ir

-- L-STRETCH #5: Posted-Menu DSIC/IR and Tie-Breaking Invariance under (eps_1, eps_2, eps_3) Perturbation
#print axioms MathForgeMechDesign.LowerBoundDSIC.posted_menu_dsic_ir
#print axioms MathForgeMechDesign.LowerBoundDSIC.perturbed_menu_payment_ge
