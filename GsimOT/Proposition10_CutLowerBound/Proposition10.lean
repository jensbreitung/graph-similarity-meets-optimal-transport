/-
# Proposition 10: integrality gap of the cut distance

Paper: Section 3.3, Proposition 10 (p. 9, l. 324) and Figure 3 (p. 10); proof in Appendix E.1
(pp. 30–32, l. 950–1001).

There are graphs `G, H` on `145` vertices with `d_□(G, H) = 8` and `d_□^OT(G, H) ≤ 4`, exactly
as stated in the paper. The graphs are `G12, H12` of `Construction.lean`; the two bounds
are Lemma 33 and Lemma 34. The remark after Proposition 10 (p. 10, l. 330), `d_□^OT(G, H) = 4`, is
`dOTCut_eq_four` (`OptimalAlignment.lean`, the Lean certificate linked in footnote 2 of the paper);
with it, `theorem3_item3` proves Theorem 3 (3), `δ_□(G, H) = 2 · δ_□^OT(G, H)`, for these graphs.
-/
import GsimOT.Proposition10_CutLowerBound.Lemma33_BijectionCost
import GsimOT.Proposition10_CutLowerBound.OptimalAlignment

namespace GsimOT.Prop10

/-- **Proposition 10** (p. 9, l. 324). The graphs `G, H` of Appendix E.1 have `145` vertices,
`d_□(G, H) = 8` (Lemma 33) and `d_□^OT(G, H) ≤ 4` (Lemma 34). -/
theorem proposition10 : Fintype.card Vtx = 145 ∧ dCut G12 H12 = 8 ∧ dOTCut G12 H12 ≤ 4 :=
  ⟨card_Vtx, lemma33, lemma34⟩

/-- **Theorem 3 (3)** (p. 4, l. 126). `δ_□(G, H) = 2 · δ_□^OT(G, H)` for the graphs of
Proposition 10, by Lemma 33 and `d_□^OT(G, H) = 4` (the remark after Proposition 10, p. 10,
l. 330). -/
theorem theorem3_item3 : deltaCut G12 H12 = 2 * deltaOTCut G12 H12 := by
  unfold deltaOTCut deltaCut
  rw [lemma33, dOTCut_eq_four, card_Vtx]
  ring

end GsimOT.Prop10
