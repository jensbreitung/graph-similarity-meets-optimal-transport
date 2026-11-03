/-
# Graph Similarity Meets Optimal Transport — Lean formalisation

Root module.  Importing this file checks every formalised result.

* `GsimOT.Common.*` — shared notions (graphs, doubly stochastic matrices, local costs,
  `d₁`, `d₁^OT`, `C_ed`, `d_ed`, `d_ed^OT`, the matrices `B`, matrix norms, `d^OT_□`,
  `d^OT_{p→q}`) and shared lemmas (Lemma 19, Observation 21, Lemma 22, Lemma 29, Eqs. (3), (7),
  attainment of the minima, App. A); for Section 4 also unions of paths and cycles,
  Three-Partition and attached leaves (namespace `GsimOT.Hardness`).
* `GsimOT.Theorem1_BlowupEqualsOT.*` — Theorem 1 (blowup distances = OT distances, all `p → q`).
* `GsimOT.Proposition6_EditLowerBound.*` — Proposition 5 (with Lemmas 23–25, Claim 26) and
  Theorem 3 (1).
* `GsimOT.Theorem7_EditUpperBound.*` — Theorem 6 (with Eq. (17)) and the `δ_ed` part of
  Theorem 2.
* `GsimOT.Proposition9_LocalEditLowerBound.*` — Proposition 8 (with Lemmas 27, 28).
* `GsimOT.Theorem10_LocalEditUpperBound.*` — Theorem 9 (with Lemmas 30, 31, Prop. 32).
* `GsimOT.Proposition12_CutLowerBound.*`, `GsimOT.Theorem13_CutUpperBound.*` — Proposition 10 and
  Theorem 11, the cut distance results of Section 3.3.
* `GsimOT.Proposition11_CutVsSpectral.*` — Proposition 12 (cut and spectral distance).
* `GsimOT.Proposition14_SpectralLowerBound.*`, `GsimOT.Theorem15_SpectralUpperBound.*` — the
  spectral distance results of Section 3.4 (Proposition 13, Theorem 14).
* `GsimOT.Theorem16_EditHardness.*`, `GsimOT.Theorem17_LocalEditHardness.*`,
  `GsimOT.Theorem18_OperatorNormHardness.*`, `GsimOT.Theorem22_CutHardness.*` — the hardness
  results of Section 4, Theorems 15–18 (with Lemma 53, Corollary 54, Claims 55–61).

Statement numbers refer to the paper (`Graph_Similarity_Meets_Optimal_Transport.pdf`);
`docs/NUMBERING.md` lists the files and declarations of every numbered statement.
-/
import GsimOT.Common.Basic
import GsimOT.Common.Claim26_DegreeBound
import GsimOT.Common.Birkhoff
import GsimOT.Common.BirkhoffDecomposition
import GsimOT.Common.DoublyStochastic
import GsimOT.Common.EditDistance
import GsimOT.Common.Lemma27_LockingMarkers
import GsimOT.Common.Lemma27_LockingMarkersEdit
import GsimOT.Common.Lemma35_Integrality
import GsimOT.Common.OperatorNorm
import GsimOT.Common.AlignedDistances
import GsimOT.Common.OTDistances
import GsimOT.Common.CutNorm
import GsimOT.Common.MatrixNorms
import GsimOT.Common.PathsAndCycles
import GsimOT.Common.ThreePartition
import GsimOT.Common.Leaves
import GsimOT.Theorem1_BlowupEqualsOT.Theorem1
import GsimOT.Proposition6_EditLowerBound.Proposition6
import GsimOT.Theorem7_EditUpperBound.Theorem7
import GsimOT.Proposition9_LocalEditLowerBound.Proposition9
import GsimOT.Theorem10_LocalEditUpperBound.Theorem10
import GsimOT.Proposition11_CutVsSpectral.Proposition11
import GsimOT.Proposition12_CutLowerBound.Proposition12
import GsimOT.Theorem13_CutUpperBound.Theorem13
import GsimOT.Theorem13_CutUpperBound.FromThinMatching
import GsimOT.Proposition14_SpectralLowerBound.Proposition14
import GsimOT.Theorem15_SpectralUpperBound.Theorem15
import GsimOT.Theorem16_EditHardness.Theorem16
import GsimOT.Theorem17_LocalEditHardness.Theorem17
import GsimOT.Theorem18_OperatorNormHardness.Theorem18
import GsimOT.Theorem22_CutHardness.Theorem22
