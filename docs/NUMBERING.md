# Paper statements and their Lean files

This file lists, for every numbered statement, equation and appendix of the paper
([`Graph_Similarity_Meets_Optimal_Transport.pdf`](../Graph_Similarity_Meets_Optimal_Transport.pdf),
66 pages), where it is formalised. Pages are the printed page numbers (the title page is page 0, so the
printed page is the PDF page index minus 1). All folders are below `GsimOT/` unless they start with
`ThinMatching/`; the correspondence PDF in each folder gives the line of every declaration.

## Statements

| Paper | Page | Lean folder / file | Main declarations |
|---|---|---|---|
| Theorem 1 | 3 | `Theorem1_BlowupEqualsOT/Theorem1.lean` | `theorem1`, `theorem1_tendsto` |
| Theorem 2 (upper bounds) | 3 | from Theorems 6, 9, 11, 14 | `theorem2_edit`, `theorem9`, `theorem2_cut_of_thin`, `theorem2_cut_of_rackeShah`, `theorem14_sqrt` |
| Theorem 3 (lower bounds) | 4 | from Propositions 5, 8, 10, 13 | `Prop5.theorem3_item1`, `Prop8.theorem3_item2`, `Prop10.theorem3_item3`, `Prop13.theorem3_item4` |
| Theorem 4 (hardness) | 4 | from Theorems 15–18 (correctness of the reductions) | see Theorems 15–18 |
| Proposition 5 | 6 | `Proposition5_EditLowerBound/Proposition5.lean` | `Prop5.proposition5`, `Prop5.proposition5_dEdit`, `Prop5.proposition5_delta` |
| Theorem 6 | 7 | `Theorem6_EditUpperBound/Theorem6.lean` | `theorem6`, `theorem6_dEdit` |
| Example 7 | 7 | not formalised | — |
| Proposition 8 | 7 | `Proposition8_LocalEditLowerBound/Proposition8.lean` | `Prop8.proposition8` |
| Theorem 9 | 9 | `Theorem9_LocalEditUpperBound/Theorem9.lean` | `theorem9` |
| Proposition 10 | 9 | `Proposition10_CutLowerBound/Proposition10.lean`; `OptimalAlignment.lean` (`d^OT_□(G, H) = 4`, p. 10) | `Prop10.proposition10`, `Prop10.dOTCut_eq_four` |
| Theorem 11 | 10 | `Theorem11_CutUpperBound/Theorem11.lean`, `FromThinMatching.lean` | `theorem11_of_thin`, `theorem11_of_rackeShah`, `theorem11_power_lt_one_of_thin` |
| Proposition 12 | 11 | `Proposition12_CutVsSpectral/Proposition12.lean` | `proposition12` |
| Proposition 13 | 11 | `Proposition13_SpectralLowerBound/Proposition13.lean` | `Prop13.proposition13`, `Prop13.proposition13_explicit`, `Prop13.no_power_bound` |
| Theorem 14 | 12 | `Theorem14_SpectralUpperBound/Theorem14.lean` | `theorem14`, `theorem14_min`, `theorem14_sqrt` |
| Theorem 15 | 12 | `Theorem15_EditHardness/Theorem15.lean` | `Hardness.ThreePartition.dOTEdit_le_iff` |
| Theorem 16 | 12 | `Theorem16_LocalEditHardness/Theorem16.lean` | `Hardness.ThreePartition.dOTOne_le_of_isYes`, `two_le_dOTOne_of_not_isYes` |
| Theorem 17 | 12 | `Theorem17_OperatorNormHardness/Theorem17.lean` | `Hardness.ThreePartition.dOT_le_one_of_isYes`, `lt_dOT_of_not_isYes` |
| Theorem 18 | 13 | `Theorem18_CutHardness/Theorem18.lean` | `Hardness.maxcut_dOTCut_bounds_paper` |
| Lemma 19 | 14 | `Common/OperatorNorm.lean` | `lemma19` |
| Claim 20 | 17 | `Theorem1_BlowupEqualsOT/Claim20.lean` (and `Approximation.lean`) | `claim20` |
| Observation 21 | 20 | `Common/Observation21_DegreeBound.lean` | `observation21` |
| Lemma 22 | 20 | `Common/Lemma22_LockingMarkers.lean`, `Common/Lemma22_LockingMarkersEdit.lean` | `lemma22_bij`, `lemma22_cost`, `lemma22_bij_edit`, `lemma22_cost_edit` |
| Lemma 23 | 22 | `Proposition5_EditLowerBound/Lemma23_MarkerCost.lean` | `Prop5.lemma23` |
| Lemma 24 | 22 | `Proposition5_EditLowerBound/Lemma24_FractionalCost.lean` | `Prop5.lemma24` |
| Lemma 25 | 23 | `Proposition5_EditLowerBound/Lemma25_BijectionCost.lean` | `Prop5.lemma25` |
| Claim 26 | 24 | `Proposition5_EditLowerBound/Lemma25_BijectionCost.lean` | `Prop5.claim26` |
| Lemma 27 | 27 | `Proposition8_LocalEditLowerBound/Lemma27_FractionalCost.lean`, `Proposition8.lean` | `Prop8.lemma27` |
| Lemma 28 | 27 | `Proposition8_LocalEditLowerBound/Lemma28_BijectionCost.lean`, `Proposition8.lean` | `Prop8.lemma28`, `Prop8.lemma28_dOne` |
| Lemma 29 | 28 | `Common/Lemma29_Integrality.lean` | `lemma29_rho_le`, `lemma29_iso`, `lemma29_one_le_dOTOne` |
| Lemma 30 ([CVZ11]) | 29 | `Theorem9_LocalEditUpperBound/Lemma30_DependentRounding.lean` (hypothesis) | `CVZRounding` |
| Lemma 31 | 29 | `Theorem9_LocalEditUpperBound/Lemma31_GoodMatching.lean` | `lemma31` |
| Proposition 32 | 29 | `Theorem9_LocalEditUpperBound/Proposition32_Rounding.lean`, `PathCutting.lean` | `proposition32` |
| Lemma 33 | 31 | `Proposition10_CutLowerBound/Lemma33_BijectionCost.lean` | `Prop10.lemma33` |
| Lemma 34 | 31 | `Proposition10_CutLowerBound/Lemma34_FractionalCost.lean` | `Prop10.lemma34` |
| Theorem 35 ([HOG26]) | 32 | `Theorem11_CutUpperBound/Definitions.lean` (hypothesis); derived from `ThinMatching/` in `FromThinMatching.lean` | `ThinPermutationTheorem`, `thinPermutationTheorem_of_rackeShah` |
| Lemma 36 | 33 | `Theorem11_CutUpperBound/Theorem38_ThinRounding.lean` | `lemma36` |
| Lemma 37 | 33 | `Theorem11_CutUpperBound/Theorem38_ThinRounding.lean` | `lemma37` |
| Theorem 38 | 34 | `Theorem11_CutUpperBound/Theorem38_ThinRounding.lean` | `theorem38` |
| Theorem 39 | 36 | `Theorem11_CutUpperBound/Theorem39_AdditiveRounding.lean` | `theorem39` |
| Lemma 40 | 36 | `Theorem11_CutUpperBound/Corollary46_SpectralTruncation.lean` | `lemma40_fst`, `lemma40_snd` |
| Lemma 41 | 37 | `Theorem11_CutUpperBound/Corollary46_SpectralTruncation.lean` | `lemma41` |
| Lemma 42 | 37 | `Theorem11_CutUpperBound/Lemma47_MergingPermutations.lean` | `Lemma47.lemma42` |
| Lemma 43 ([LT91]) | 38 | `Theorem11_CutUpperBound/ContractionPrinciple.lean` | `contractionPrinciple` |
| Lemma 44 | 38 | `Theorem11_CutUpperBound/Lemma47_MergingPermutations.lean` | `Lemma47.lemma44` |
| Lemma 45 | 39 | `Theorem11_CutUpperBound/Corollary46_SpectralTruncation.lean` | `lemma45` |
| Corollary 46 | 41 | `Theorem11_CutUpperBound/Corollary46_SpectralTruncation.lean` | `corollary46` |
| Lemma 47 | 41 | `Theorem11_CutUpperBound/Lemma47_MergingPermutations.lean` | `lemma47` |
| Lemma 48 | 43 | `Theorem11_CutUpperBound/Theorem39_AdditiveRounding.lean` | `lemma48` |
| Lemma 49 | 45 | `Proposition13_SpectralLowerBound/Lemma49.lean` | `Prop13.lemma49` |
| Lemma 50 | 47 | `Theorem14_SpectralUpperBound/RandomBijection.lean` | `Theorem14.lemma50` |
| Lemma 51 | 48 | `Theorem14_SpectralUpperBound/RandomBijection.lean` | `Theorem14.lemma51` |
| Lemma 52 | 48 | `Theorem14_SpectralUpperBound/RandomBijection.lean` | `Theorem14.lemma52` |
| Lemma 53 | 53 | `Theorem17_OperatorNormHardness/Lemma53_AggregatedMatrix.lean` | `Hardness.opNorm_aggMatrix_le` |
| Corollary 54 | 54 | `Theorem17_OperatorNormHardness/Corollary54_ColumnBound.lean` | `Hardness.rpow_bExp_mul_le_opNorm_Bpq`, `Hardness.lt_opNorm_Bpq` |
| Claim 55 | 55 | `Theorem17_OperatorNormHardness/Claim55_LeafMass.lean` | `Hardness.claim55` |
| Claim 56 | 55 | `Theorem17_OperatorNormHardness/Claim56_SplitMass.lean` | `Hardness.claim56` |
| Proposition 57 | 57 | not formalised | — |
| Claim 58 | 58 | `Theorem18_CutHardness/Claim58_LeafMass.lean` | `Hardness.claim58` |
| Claim 59 | 59 | `Theorem18_CutHardness/Claim59_SplitMass.lean` | `Hardness.claim59` |
| Claim 60 | 60 | `Theorem18_CutHardness/Claim60_WrongVertex.lean` | `Hardness.claim60`, `Hardness.claim60'` |
| Claim 61 | 61 | `Theorem18_CutHardness/Claim61_NearIdentity.lean` | `Hardness.claim61`, `Hardness.claim61_delta` |
| Remark 62 | 62 | not formalised | — |

Namespaces: all declarations are in `GsimOT`; `Prop5`, `Prop8`, `Prop10`, `Prop13`, `Theorem14`,
`Lemma47` and `Hardness` are sub-namespaces (`GsimOT.Prop5.lemma23`, …).

## Equations

| Equation | Page | Content | Lean |
|---|---|---|---|
| (1) | 2 | `δ^OT_ed` as a minimum over fractional alignments | `Common/EditDistance.lean` |
| (2) | 3 | `δ^OT_{p→q}` | `Common/OTDistances.lean` |
| (3) | 5 | Birkhoff decomposition | `Common/Birkhoff.lean`, `Common/BirkhoffDecomposition.lean` |
| (4) | 11 | `ζ_R` as a maximum over `S, T ⊆ V × W` (proof overview of Theorem 11) | `Common/CutNorm.lean` |
| (5) | 14 | Hölder: `Σ |x(v)| ≤ ‖x‖_q |V|^{1−1/q}` | `Common/OperatorNorm.lean` |
| (6) | 14 | discrepancy matrix `D_{A,B}` | `Common/Basic.lean` |
| (7) | 14 | `δ^OT_1` as a min–max over the support | `Common/MatrixNorms.lean` |
| (8)–(11) | 15 | Appendix B, first direction | `Theorem1_BlowupEqualsOT/LowerBound.lean` |
| (12) | 17 | Appendix B, converse inequality | `Theorem1_BlowupEqualsOT/Theorem1.lean` |
| (13) | 17 | rational `ε`-approximation `Q*` (Claim 20) | `Theorem1_BlowupEqualsOT/Claim20.lean`, `Approximation.lean` |
| (14), (15) | 18 | Appendix B, second direction | `Theorem1_BlowupEqualsOT/UpperBound.lean`, `Claim20.lean` |
| (16) | 21 | `C_ed` and `C_1` via local costs (Lemma 22) | `Common/Lemma22_LockingMarkers*.lean` |
| (17) | 24 | `C_ed(Q) = ‖A_G‖²_F + ‖A_H‖²_F − 2⟨A_G Q, Q A_H⟩_F` | `Theorem6_EditUpperBound/TraceFormula.lean` |
| (18) | 28 | reference bijection `σ` with `Q(v, σ(v)) > 0` | `Theorem9_LocalEditUpperBound/` |
| (19) | 29 | tail bound of [CVZ11] | `Theorem9_LocalEditUpperBound/Lemma30_DependentRounding.lean` |
| (20) | 30 | `d₁ ≤ 4L + 2√(2nL) + 4√(5n ln 4n)` | `Theorem9_LocalEditUpperBound/Theorem9.lean` |
| (21), (22) | 32 | `ζ_Q` with sets / with `[0,1]`-valued functions | `Common/CutNorm.lean`, `Theorem11_CutUpperBound/` |
| (23) | 32 | thinness | `Theorem11_CutUpperBound/Definitions.lean` |
| (24)–(27) | 33–35 | Lemma 37, Theorem 38 | `Theorem11_CutUpperBound/Theorem38_ThinRounding.lean` |
| (28) | 35 | `A − RARᵀ = EA + R(EA)ᵀ` | `Theorem11_CutUpperBound/Theorem38_ThinRounding.lean` |
| (29)–(38) | 38–42 | Appendix E.2.2 | `Theorem11_CutUpperBound/` |
| (39) | 44 | proof of Theorem 11 | `Theorem11_CutUpperBound/Theorem11.lean` |
| (40)–(43) | 47–49 | Appendix F.2: `γ_Q`, Lemma 51 | `Theorem14_SpectralUpperBound/RandomBijection.lean` |
| (44) | 52 | proof of Theorem 16 | `Theorem16_LocalEditHardness/Theorem16.lean` |
| (45) | 53 | `A^Q_{G,H} = A_G − Q A_H Qᵀ` | `Theorem17_OperatorNormHardness/Lemma53_AggregatedMatrix.lean` |
| (46) | 56 | choice of `M` in Theorem 17 | `Theorem17_OperatorNormHardness/Theorem17.lean` |
| (47) | 58 | `(33/17)·maxcut(F) ≤ d^OT_□(G, H) ≤ 2·maxcut(F)` | `Theorem18_CutHardness/Theorem18.lean` (`maxcut_dOTCut_bounds_eq47`) |

## Appendices

| Appendix | Pages | Content | Lean |
|---|---|---|---|
| A | 14–15 | extended preliminaries (graphs, matrix norms, optimal transport distances) | `Common/` |
| B | 15–20 | proof of Theorem 1 | `Theorem1_BlowupEqualsOT/` |
| C | 20–25 | edit distance: Observation 21, Lemma 22, C.1 lower bound, C.2 upper bound | `Common/`, `Proposition5_EditLowerBound/`, `Theorem6_EditUpperBound/` |
| D | 25–30 | local edit distance: D.1 lower bound, D.2 upper bound | `Proposition8_LocalEditLowerBound/`, `Theorem9_LocalEditUpperBound/` |
| E | 30–44 | cut distance: E.1 lower bound, E.2 upper bound (E.2.1 multiplicative, E.2.2 additive, E.2.3 proof of Theorem 11) | `Proposition10_CutLowerBound/`, `Theorem11_CutUpperBound/` |
| F | 44–50 | spectral distance: Proposition 12, F.1 lower bound, F.2 upper bound | `Proposition12_CutVsSpectral/`, `Proposition13_SpectralLowerBound/`, `Theorem14_SpectralUpperBound/` |
| G | 50–62 | proofs omitted from Section 4 | `Theorem15_EditHardness/`, `Theorem16_LocalEditHardness/`, `Theorem17_OperatorNormHardness/`, `Theorem18_CutHardness/` |
