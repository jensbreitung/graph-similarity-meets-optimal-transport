/-
# Theorem 35 from the formalisation of [HOG26]

Theorem 35 of the paper (p. 32, l. 1021–1022) is [HOG26, Theorem 1.4]. It is formalised in
the separate library `ThinMatching` (independent of `GsimOT`), assuming the tree-cut sparsifier
theorem of Räcke and Shah [RS14] (`ThinMatching.RackeShahTheorem`, cited in [HOG26] as
Theorem 2.2). This file derives the hypothesis `ThinPermutationTheorem` of Theorem 11 from it, so
that Theorem 11 (and the cut part of Theorem 2) holds assuming only [RS14].
-/
import GsimOT.Theorem11_CutUpperBound.Theorem11
import ThinMatching.Theorem14

open Finset

namespace GsimOT

/-- **Theorem 35 = [HOG26, Theorem 1.4]**, assuming [RS14]. -/
theorem thinPermutationTheorem_of_rackeShah (hRS : ThinMatching.RackeShahTheorem) :
    ThinPermutationTheorem := by
  obtain ⟨C, hC, hthin⟩ := ThinMatching.theorem14_bip hRS
  refine ⟨C, hC, fun V W _ _ _ _ Q hQ hcard => ?_⟩
  obtain ⟨π, hπ⟩ := hthin V W Q ⟨hQ.nonneg, hQ.row_sum, hQ.col_sum⟩ hcard
  refine ⟨π, fun UV UW => ?_⟩
  have h := hπ UV UW
  simpa [ThinMatching.bipCrossCount, ThinMatching.bipCutWeight, ite_not] using h

/-- **Theorem 11**, assuming only the tree-cut sparsifier theorem [RS14]. -/
theorem theorem11_of_rackeShah (hRS : ThinMatching.RackeShahTheorem) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card V = Fintype.card W →
      deltaOTCut G H ≤ deltaCut G H ∧
      deltaCut G H ≤ C * deltaOTCut G H * Real.log (Real.exp 1 / deltaOTCut G H) *
        Real.log (Real.exp 1 * Real.log (Real.exp 1 / deltaOTCut G H)) :=
  theorem11_of_thin (thinPermutationTheorem_of_rackeShah hRS)

/-- **Theorem 11, power bound** for `0 < α < 1`, assuming only [RS14]. -/
theorem theorem11_power_of_rackeShah (hRS : ThinMatching.RackeShahTheorem) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ Cα : ℝ, 0 < Cα ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card V = Fintype.card W →
      deltaCut G H ≤ Cα * deltaOTCut G H ^ α :=
  theorem11_power_of_thin (thinPermutationTheorem_of_rackeShah hRS) hα0 hα1

/-- **Theorem 11, power bound for every `α < 1`**, assuming only [RS14]. -/
theorem theorem11_power_lt_one_of_rackeShah (hRS : ThinMatching.RackeShahTheorem) {α : ℝ}
    (hα1 : α < 1) :
    ∃ Cα : ℝ, 0 < Cα ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card V = Fintype.card W →
      deltaCut G H ≤ Cα * deltaOTCut G H ^ α :=
  theorem11_power_lt_one_of_thin (thinPermutationTheorem_of_rackeShah hRS) hα1

/-- **Theorem 2, cut part**: `δ_□ ≤ C_ε (δ^OT_□)^{1-ε}` for every `ε > 0`, assuming only [RS14]. -/
theorem theorem2_cut_of_rackeShah (hRS : ThinMatching.RackeShahTheorem) {ε : ℝ} (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card V = Fintype.card W →
      deltaCut G H ≤ Cε * deltaOTCut G H ^ (1 - ε) :=
  theorem2_cut_of_thin (thinPermutationTheorem_of_rackeShah hRS) hε

end GsimOT
