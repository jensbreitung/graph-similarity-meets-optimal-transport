/-
Prints the axioms used by the main results.  The expected output for every result is
`[propext, Classical.choice, Quot.sound]` — the standard axioms of Lean/Mathlib.  In particular
no `sorryAx` and no user-declared axiom may appear.

Lemma 30 (the dependent rounding theorem of Chekuri–Vondrák–Zenklusen) is *not* an axiom: it is
the explicit hypothesis `hCVZ : CVZRounding` of `GsimOT.theorem10`.  Likewise, Theorem 35 (thin
permutations, [HOG26, Theorem 1.4]) is the explicit hypothesis `hThin : ThinPermutationTheorem` of
`GsimOT.theorem13_of_thin` (Theorem 11).
Statement numbers refer to the paper; docs/NUMBERING.md lists the declarations of every numbered
statement.
-/
import GsimOT
import ThinMatching

-- Theorem 1 and its lemmas
#print axioms GsimOT.theorem1
#print axioms GsimOT.theorem1_tendsto
#print axioms GsimOT.theorem1_of_tendsto
#print axioms GsimOT.claim20
#print axioms GsimOT.eq13
#print axioms GsimOT.deltaOTPQ_le_blowupSeq
#print axioms GsimOT.eq16
#print axioms GsimOT.exists_integral_approx
#print axioms GsimOT.lemma24
-- Proposition 5 and Theorem 3 (1) (edit distance) with Lemmas 23–25 and Claim 26
#print axioms GsimOT.Prop6.proposition6_dEdit
#print axioms GsimOT.Prop6.proposition6_delta_of_le
#print axioms GsimOT.Prop6.proposition6
#print axioms GsimOT.Prop6.proposition6_delta
#print axioms GsimOT.Prop6.theorem4_item1
#print axioms GsimOT.Prop6.lemma28
#print axioms GsimOT.Prop6.lemma29
#print axioms GsimOT.Prop6.costEdit_witness
#print axioms GsimOT.Prop6.lemma30
#print axioms GsimOT.Prop6.claim31
-- Theorem 6 and Theorem 2 (edit distance)
#print axioms GsimOT.theorem7
#print axioms GsimOT.theorem7_dEdit
#print axioms GsimOT.theorem3_edit
#print axioms GsimOT.costEdit_eq_frob
-- Cut distance: Proposition 10 (Prop12.*), Theorem 11 (theorem13*), Proposition 12 (proposition11)
#print axioms GsimOT.Prop12.theorem4_item3
#print axioms GsimOT.theorem13_power_lt_one_of_thin
#print axioms GsimOT.theorem2_cut_of_thin
#print axioms GsimOT.theorem38
#print axioms GsimOT.Prop12.proposition12
#print axioms GsimOT.Prop12.lemma39
#print axioms GsimOT.Prop12.lemma40
#print axioms GsimOT.Prop12.four_le_costCut
#print axioms GsimOT.Prop12.dOTCut_eq_four
#print axioms GsimOT.theorem13_of_thin
#print axioms GsimOT.theorem13_power_of_thin
#print axioms GsimOT.eq33
#print axioms GsimOT.theorem52
#print axioms GsimOT.theorem45
#print axioms GsimOT.corollary46
#print axioms GsimOT.lemma45
#print axioms GsimOT.lemma41
#print axioms GsimOT.lemma47
#print axioms GsimOT.lemma48
#print axioms GsimOT.contractionPrinciple
#print axioms GsimOT.proposition11
-- Theorem 11 assuming only [RS14] (via the ThinMatching library)
#print axioms GsimOT.theorem13_power_lt_one_of_rackeShah
#print axioms GsimOT.theorem2_cut_of_rackeShah
#print axioms GsimOT.theorem13_of_rackeShah
#print axioms GsimOT.theorem13_power_of_rackeShah
#print axioms GsimOT.thinPermutationTheorem_of_rackeShah
-- ThinMatching: [HOG26]
#print axioms ThinMatching.theorem14_bip
#print axioms ThinMatching.theorem14
#print axioms ThinMatching.lemma12
#print axioms ThinMatching.theorem13_support
#print axioms ThinMatching.lemma32
#print axioms ThinMatching.lemma35
#print axioms ThinMatching.lemma46_bip
#print axioms ThinMatching.lemma46
#print axioms ThinMatching.prop43
#print axioms ThinMatching.lemma45_bip
#print axioms ThinMatching.lemma45
-- Spectral distance: Proposition 13, Theorem 14
#print axioms GsimOT.Prop14.proposition13
#print axioms GsimOT.theorem14
#print axioms GsimOT.theorem15_h
#print axioms GsimOT.Prop14.proposition14
#print axioms GsimOT.Prop14.lemma53
#print axioms GsimOT.Prop14.theorem4_item4
#print axioms GsimOT.Prop14.no_power_bound
#print axioms GsimOT.theorem15
#print axioms GsimOT.theorem15_sqrt
#print axioms GsimOT.deltaOTPQ_eq_dOT
-- Proposition 8 and its lemmas
#print axioms GsimOT.Prop9.no_power_bound
#print axioms GsimOT.Prop9.proposition9
#print axioms GsimOT.Prop9.theorem4_item2
#print axioms GsimOT.Prop9.no_linear_bound
#print axioms GsimOT.Prop9.lemma33
#print axioms GsimOT.Prop9.lemma34
#print axioms GsimOT.Prop9.lemma34_dOne
-- Theorem 9 and its lemmas
#print axioms GsimOT.theorem10_power
#print axioms GsimOT.theorem10
#print axioms GsimOT.theorem10_of_isDS
#print axioms GsimOT.proposition38
#print axioms GsimOT.prop38_of_matching
#print axioms GsimOT.lemma37
-- Section 4: Theorems 15 and 16
#print axioms GsimOT.Hardness.ThreePartition.dOTEdit_le_iff
#print axioms GsimOT.Hardness.ThreePartition.dOTEdit_shift_le_iff
#print axioms GsimOT.Hardness.ThreePartition.dOTOne_le_of_isYes
#print axioms GsimOT.Hardness.ThreePartition.two_le_dOTOne_of_not_isYes
#print axioms GsimOT.Hardness.ThreePartition.dOTOne_shift_gap
-- Section 4: Theorem 17 with Lemma 53, Corollary 54 and Claims 55, 56
#print axioms GsimOT.Hardness.ThreePartition.dOT_le_one_of_isYes
#print axioms GsimOT.Hardness.ThreePartition.lt_dOT_of_not_isYes
#print axioms GsimOT.Hardness.ThreePartition.dOT_shift_gap
#print axioms GsimOT.Hardness.opNorm_aggMatrix_le
#print axioms GsimOT.Hardness.rpow_bExp_mul_le_opNorm_Bpq
#print axioms GsimOT.Hardness.lt_opNorm_Bpq
#print axioms GsimOT.Hardness.claim54
#print axioms GsimOT.Hardness.claim55
-- Section 4: Theorem 18 with Eq. (47) and Claims 58–61
#print axioms GsimOT.Hardness.maxcut_dOTCut_bounds_paper
#print axioms GsimOT.Hardness.maxcut_dOTCut_bounds_eq47
#print axioms GsimOT.Hardness.maxcut_dOTCut_bounds
#print axioms GsimOT.Hardness.le_dOTCut_addLeaves
#print axioms GsimOT.Hardness.dOTCut_addLeaves_le
#print axioms GsimOT.Hardness.cutNorm_anG_sub_anH
#print axioms GsimOT.Hardness.claim56
#print axioms GsimOT.Hardness.claim57
#print axioms GsimOT.Hardness.claim58
#print axioms GsimOT.Hardness.claim58'
#print axioms GsimOT.Hardness.claim59
#print axioms GsimOT.Hardness.claim59_delta
-- shared lemmas (Observation 21, Lemma 22, Lemma 29, Eq. (3))
#print axioms GsimOT.claim26
#print axioms GsimOT.lemma27_bij
#print axioms GsimOT.lemma27_cost
#print axioms GsimOT.lemma27_bij_edit
#print axioms GsimOT.lemma27_cost_edit
#print axioms GsimOT.lemma35_rho_le
#print axioms GsimOT.lemma35_iso
#print axioms GsimOT.exists_bij_subset_supp
#print axioms GsimOT.exists_birkhoff_decomposition
#print axioms GsimOT.exists_dOTEdit_eq
#print axioms GsimOT.costEdit_eq_entrywiseNorm_B
#print axioms GsimOT.dOT_one_one_eq_dOTOne
