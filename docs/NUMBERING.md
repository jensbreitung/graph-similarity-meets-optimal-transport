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
| Theorem 2 (upper bounds) | 3 | from Theorems 6, 9, 11, 14 | `theorem3_edit`, `theorem10`, `theorem2_cut_of_thin`, `theorem2_cut_of_rackeShah`, `theorem15_sqrt` |
| Theorem 3 (lower bounds) | 4 | from Propositions 5, 8, 10, 13 | `Prop6.theorem4_item1`, `Prop9.theorem4_item2`, `Prop12.theorem4_item3`, `Prop14.theorem4_item4` |
| Theorem 4 (hardness) | 4 | from Theorems 15–18 (correctness of the reductions) | see Theorems 15–18 |
| Proposition 5 | 6 | `Proposition6_EditLowerBound/Proposition6.lean` | `Prop6.proposition6`, `Prop6.proposition6_dEdit`, `Prop6.proposition6_delta` |
| Theorem 6 | 7 | `Theorem7_EditUpperBound/Theorem7.lean` | `theorem7`, `theorem7_dEdit` |
| Example 7 | 7 | not formalised | — |
| Proposition 8 | 7 | `Proposition9_LocalEditLowerBound/Proposition9.lean` | `Prop9.proposition9` |
| Theorem 9 | 9 | `Theorem10_LocalEditUpperBound/Theorem10.lean` | `theorem10` |
| Proposition 10 | 9 | `Proposition12_CutLowerBound/Proposition12.lean`; `OptimalAlignment.lean` (`d^OT_□(G, H) = 4`, p. 10) | `Prop12.proposition12`, `Prop12.dOTCut_eq_four` |
| Theorem 11 | 10 | `Theorem13_CutUpperBound/Theorem13.lean`, `FromThinMatching.lean` | `theorem13_of_thin`, `theorem13_of_rackeShah`, `theorem13_power_lt_one_of_thin` |
| Proposition 12 | 11 | `Proposition11_CutVsSpectral/Proposition11.lean` | `proposition11` |
| Proposition 13 | 11 | `Proposition14_SpectralLowerBound/Proposition14.lean` | `Prop14.proposition13`, `Prop14.proposition14`, `Prop14.no_power_bound` |
| Theorem 14 | 12 | `Theorem15_SpectralUpperBound/Theorem15.lean` | `theorem14`, `theorem15`, `theorem15_sqrt` |
| Theorem 15 | 12 | `Theorem16_EditHardness/Theorem16.lean` | `Hardness.ThreePartition.dOTEdit_le_iff` |
| Theorem 16 | 12 | `Theorem17_LocalEditHardness/Theorem17.lean` | `Hardness.ThreePartition.dOTOne_le_of_isYes`, `two_le_dOTOne_of_not_isYes` |
| Theorem 17 | 12 | `Theorem18_OperatorNormHardness/Theorem18.lean` | `Hardness.ThreePartition.dOT_le_one_of_isYes`, `lt_dOT_of_not_isYes` |
| Theorem 18 | 13 | `Theorem22_CutHardness/Theorem22.lean` | `Hardness.maxcut_dOTCut_bounds_paper` |
| Lemma 19 | 14 | `Common/OperatorNorm.lean` | `lemma24` |
| Claim 20 | 17 | `Theorem1_BlowupEqualsOT/Claim20.lean` (and `Approximation.lean`) | `claim20` |
| Observation 21 | 20 | `Common/Claim26_DegreeBound.lean` | `claim26` |
| Lemma 22 | 20 | `Common/Lemma27_LockingMarkers.lean`, `Common/Lemma27_LockingMarkersEdit.lean` | `lemma27_bij`, `lemma27_cost`, `lemma27_bij_edit`, `lemma27_cost_edit` |
| Lemma 23 | 22 | `Proposition6_EditLowerBound/Lemma28_MarkerCost.lean` | `Prop6.lemma28` |
| Lemma 24 | 22 | `Proposition6_EditLowerBound/Lemma29_FractionalCost.lean` | `Prop6.lemma29` |
| Lemma 25 | 23 | `Proposition6_EditLowerBound/Lemma30_BijectionCost.lean` | `Prop6.lemma30` |
| Claim 26 | 24 | `Proposition6_EditLowerBound/Lemma30_BijectionCost.lean` | `Prop6.claim31` |
| Lemma 27 | 27 | `Proposition9_LocalEditLowerBound/Lemma33_FractionalCost.lean`, `Proposition9.lean` | `Prop9.lemma33` |
| Lemma 28 | 27 | `Proposition9_LocalEditLowerBound/Lemma34_BijectionCost.lean`, `Proposition9.lean` | `Prop9.lemma34`, `Prop9.lemma34_dOne` |
| Lemma 29 | 28 | `Common/Lemma35_Integrality.lean` | `lemma35_rho_le`, `lemma35_iso`, `lemma35_one_le_dOTOne` |
| Lemma 30 ([CVZ11]) | 29 | `Theorem10_LocalEditUpperBound/Lemma36_DependentRounding.lean` (hypothesis) | `CVZRounding` |
| Lemma 31 | 29 | `Theorem10_LocalEditUpperBound/Lemma37_GoodMatching.lean` | `lemma37` |
| Proposition 32 | 29 | `Theorem10_LocalEditUpperBound/Proposition38_Rounding.lean`, `PathCutting.lean` | `proposition38` |
| Lemma 33 | 31 | `Proposition12_CutLowerBound/Lemma39_BijectionCost.lean` | `Prop12.lemma39` |
| Lemma 34 | 31 | `Proposition12_CutLowerBound/Lemma40_FractionalCost.lean` | `Prop12.lemma40` |
| Theorem 35 ([HOG26]) | 32 | `Theorem13_CutUpperBound/Definitions.lean` (hypothesis); derived from `ThinMatching/` in `FromThinMatching.lean` | `ThinPermutationTheorem`, `thinPermutationTheorem_of_rackeShah` |
| Lemma 36 | 33 | `Theorem13_CutUpperBound/Theorem52_ThinRounding.lean` | `lemma50` |
| Lemma 37 | 33 | `Theorem13_CutUpperBound/Theorem52_ThinRounding.lean` | `lemma51` |
| Theorem 38 | 34 | `Theorem13_CutUpperBound/Theorem52_ThinRounding.lean` | `theorem38` |
| Theorem 39 | 36 | `Theorem13_CutUpperBound/Theorem45_AdditiveRounding.lean` | `theorem45` |
| Lemma 40 | 36 | `Theorem13_CutUpperBound/Lemma46_SpectralTruncation.lean` | `lemma41_2_fst`, `lemma41_2_snd` |
| Lemma 41 | 37 | `Theorem13_CutUpperBound/Lemma46_SpectralTruncation.lean` | `lemma41` |
| Lemma 42 | 37 | `Theorem13_CutUpperBound/Lemma47_MergingPermutations.lean` | `Lemma47.lemma43` |
| Lemma 43 ([LT91]) | 38 | `Theorem13_CutUpperBound/ContractionPrinciple.lean` | `contractionPrinciple` |
| Lemma 44 | 38 | `Theorem13_CutUpperBound/Lemma47_MergingPermutations.lean` | `Lemma47.lemma44` |
| Lemma 45 | 39 | `Theorem13_CutUpperBound/Lemma46_SpectralTruncation.lean` | `lemma45` |
| Corollary 46 | 41 | `Theorem13_CutUpperBound/Lemma46_SpectralTruncation.lean` | `corollary46` |
| Lemma 47 | 41 | `Theorem13_CutUpperBound/Lemma47_MergingPermutations.lean` | `lemma47` |
| Lemma 48 | 43 | `Theorem13_CutUpperBound/Theorem45_AdditiveRounding.lean` | `lemma48` |
| Lemma 49 | 45 | `Proposition14_SpectralLowerBound/Lemma53.lean` | `Prop14.lemma53` |
| Lemma 50 | 47 | `Theorem15_SpectralUpperBound/RandomBijection.lean` | `Theorem15.lemma50` |
| Lemma 51 | 48 | `Theorem15_SpectralUpperBound/RandomBijection.lean` | `Theorem15.lemma51` |
| Lemma 52 | 48 | `Theorem15_SpectralUpperBound/RandomBijection.lean` | `Theorem15.lemma52` |
| Lemma 53 | 53 | `Theorem18_OperatorNormHardness/Lemma19_AggregatedMatrix.lean` | `Hardness.opNorm_aggMatrix_le` |
| Corollary 54 | 54 | `Theorem18_OperatorNormHardness/Corollary20_ColumnBound.lean` | `Hardness.rpow_bExp_mul_le_opNorm_Bpq`, `Hardness.lt_opNorm_Bpq` |
| Claim 55 | 55 | `Theorem18_OperatorNormHardness/Claim54_LeafMass.lean` | `Hardness.claim54` |
| Claim 56 | 55 | `Theorem18_OperatorNormHardness/Claim55_SplitMass.lean` | `Hardness.claim55` |
| Proposition 57 | 57 | not formalised | — |
| Claim 58 | 58 | `Theorem22_CutHardness/Claim56_LeafMass.lean` | `Hardness.claim56` |
| Claim 59 | 59 | `Theorem22_CutHardness/Claim57_SplitMass.lean` | `Hardness.claim57` |
| Claim 60 | 60 | `Theorem22_CutHardness/Claim58_WrongVertex.lean` | `Hardness.claim58`, `Hardness.claim58'` |
| Claim 61 | 61 | `Theorem22_CutHardness/Claim59_NearIdentity.lean` | `Hardness.claim59`, `Hardness.claim59_delta` |
| Remark 62 | 62 | not formalised | — |

Namespaces: all declarations are in `GsimOT`; `Prop6`, `Prop9`, `Prop12`, `Prop14`, `Theorem15`,
`Lemma47` and `Hardness` are sub-namespaces (`GsimOT.Prop6.lemma28`, …).

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
| (8)–(11) | 15 | App. B, first direction | `Theorem1_BlowupEqualsOT/LowerBound.lean` |
| (12) | 17 | App. B, converse inequality | `Theorem1_BlowupEqualsOT/Theorem1.lean` |
| (13) | 17 | rational `ε`-approximation `Q*` (Claim 20) | `Theorem1_BlowupEqualsOT/Claim20.lean`, `Approximation.lean` |
| (14), (15) | 18 | App. B, second direction | `Theorem1_BlowupEqualsOT/UpperBound.lean`, `Claim20.lean` |
| (16) | 21 | `C_ed` and `C_1` via local costs (Lemma 22) | `Common/Lemma27_LockingMarkers*.lean` |
| (17) | 24 | `C_ed(Q) = ‖A_G‖²_F + ‖A_H‖²_F − 2⟨A_G Q, Q A_H⟩_F` | `Theorem7_EditUpperBound/TraceFormula.lean` |
| (18) | 28 | reference bijection `σ` with `Q(v, σ(v)) > 0` | `Theorem10_LocalEditUpperBound/` |
| (19) | 29 | tail bound of [CVZ11] | `Theorem10_LocalEditUpperBound/Lemma36_DependentRounding.lean` |
| (20) | 30 | `d₁ ≤ 4L + 2√(2nL) + 4√(5n ln 4n)` | `Theorem10_LocalEditUpperBound/Theorem10.lean` |
| (21), (22) | 32 | `ζ_Q` with sets / with `[0,1]`-valued functions | `Common/CutNorm.lean`, `Theorem13_CutUpperBound/` |
| (23) | 32 | thinness | `Theorem13_CutUpperBound/Definitions.lean` |
| (24)–(27) | 33–35 | Lemma 37, Theorem 38 | `Theorem13_CutUpperBound/Theorem52_ThinRounding.lean` |
| (28) | 35 | `A − RARᵀ = EA + R(EA)ᵀ` | `Theorem13_CutUpperBound/Theorem52_ThinRounding.lean` |
| (29)–(38) | 38–42 | App. E.2.2 | `Theorem13_CutUpperBound/` |
| (39) | 44 | proof of Theorem 11 | `Theorem13_CutUpperBound/Theorem13.lean` |
| (40)–(43) | 47–49 | App. F.2: `γ_Q`, Lemma 51 | `Theorem15_SpectralUpperBound/RandomBijection.lean` |
| (44) | 52 | proof of Theorem 16 | `Theorem17_LocalEditHardness/Theorem17.lean` |
| (45) | 53 | `A^Q_{G,H} = A_G − Q A_H Qᵀ` | `Theorem18_OperatorNormHardness/Lemma19_AggregatedMatrix.lean` |
| (46) | 56 | choice of `M` in Theorem 17 | `Theorem18_OperatorNormHardness/Theorem18.lean` |
| (47) | 58 | `(33/17)·maxcut(F) ≤ d^OT_□(G, H) ≤ 2·maxcut(F)` | `Theorem22_CutHardness/Theorem22.lean` (`maxcut_dOTCut_bounds_eq47`) |

## Appendices

| Appendix | Pages | Content | Lean |
|---|---|---|---|
| A | 14–15 | extended preliminaries (graphs, matrix norms, optimal transport distances) | `Common/` |
| B | 15–20 | proof of Theorem 1 | `Theorem1_BlowupEqualsOT/` |
| C | 20–25 | edit distance: Observation 21, Lemma 22, C.1 lower bound, C.2 upper bound | `Common/`, `Proposition6_EditLowerBound/`, `Theorem7_EditUpperBound/` |
| D | 25–30 | local edit distance: D.1 lower bound, D.2 upper bound | `Proposition9_LocalEditLowerBound/`, `Theorem10_LocalEditUpperBound/` |
| E | 30–44 | cut distance: E.1 lower bound, E.2 upper bound (E.2.1 multiplicative, E.2.2 additive, E.2.3 proof of Theorem 11) | `Proposition12_CutLowerBound/`, `Theorem13_CutUpperBound/` |
| F | 44–50 | spectral distance: Proposition 12, F.1 lower bound, F.2 upper bound | `Proposition11_CutVsSpectral/`, `Proposition14_SpectralLowerBound/`, `Theorem15_SpectralUpperBound/` |
| G | 50–62 | proofs omitted from Section 4 | `Theorem16_EditHardness/`, `Theorem17_LocalEditHardness/`, `Theorem18_OperatorNormHardness/`, `Theorem22_CutHardness/` |
