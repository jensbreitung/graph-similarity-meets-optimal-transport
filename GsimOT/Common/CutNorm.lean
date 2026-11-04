/-
# The cut norm and the cut distance

Paper, Appendix A (cut norm, p. 14, l. 480–481), Section 1 (`δ^OT_□`, p. 2, l. 75–77), Section 2
(`C_♢(Q)`, `d_♢`, `d_♢^OT`, p. 5, l. 184–187) and Appendix E.2 (`ζ_Q`, Eq. (21), p. 32, l. 1006, and
the weighted cut norm of Appendix E.2.2, p. 36, l. 1129–1139).

* `cutNorm A`        : `‖A‖_□ = max_{S ⊆ ι, T ⊆ κ} |A(S, T)|` for `A ∈ ℝ^{ι×κ}`.
* `B G H Q` (Common/OTDistances.lean): `B(G, H, Q)` with entries `Q(v,w) D(v,w,v',w') Q(v',w')`.
* `costCut G H Q`    : `C_□(Q) = ‖B(G, H, Q)‖_□` (unnormalised, for `Q ∈ DS(V, W)`).
* `dCut G H`         : `d_□(G, H) = min_π ‖A_G^π - A_H‖_□`.
* `dOTCut G H`       : `d_□^OT(G, H) = min_{Q ∈ DS(V,W)} C_□(Q)` (infimum).
* `deltaCut`, `deltaOTCut` : the normalisations `n⁻² d_□`, `n⁻² d_□^OT` (p. 1, l. 26–27).
* `epsR A B R`       : `ζ_R(A, B) = ‖D_{A,B}‖_{□, μ_R}` for real matrices `A ∈ ℝ^{V×V}`,
  `B ∈ ℝ^{W×W}` and `R ∈ DS(V, W)` with `μ_R = R/n` (Appendix E.2.2, where the matrix is called `Q`
  and the paper writes `ζ_Q(A, B)`); `ζ_R = n⁻² C_□(R)` for graphs (p. 10, l. 340, and
  Eq. (21)).
-/
import GsimOT.Common.Basic
import GsimOT.Common.AlignedDistances
import GsimOT.Common.OTDistances

open Finset

namespace GsimOT

section CutNorm

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The cut norm `‖A‖_□ = max_{S, T} |∑_{i ∈ S, j ∈ T} A i j|`. -/
noncomputable def cutNorm (A : Matrix ι κ ℝ) : ℝ :=
  ⨆ ST : Finset ι × Finset κ, |∑ i ∈ ST.1, ∑ j ∈ ST.2, A i j|

lemma bddAbove_cutNorm (A : Matrix ι κ ℝ) :
    BddAbove (Set.range fun ST : Finset ι × Finset κ => |∑ i ∈ ST.1, ∑ j ∈ ST.2, A i j|) :=
  (Set.finite_range _).bddAbove

lemma le_cutNorm (A : Matrix ι κ ℝ) (S : Finset ι) (T : Finset κ) :
    |∑ i ∈ S, ∑ j ∈ T, A i j| ≤ cutNorm A :=
  le_ciSup (f := fun ST : Finset ι × Finset κ => |∑ i ∈ ST.1, ∑ j ∈ ST.2, A i j|)
    (bddAbove_cutNorm A) (S, T)

lemma cutNorm_le (A : Matrix ι κ ℝ) {c : ℝ}
    (h : ∀ (S : Finset ι) (T : Finset κ), |∑ i ∈ S, ∑ j ∈ T, A i j| ≤ c) : cutNorm A ≤ c :=
  ciSup_le fun ST => h ST.1 ST.2

lemma cutNorm_nonneg (A : Matrix ι κ ℝ) : 0 ≤ cutNorm A :=
  (abs_nonneg _).trans (le_cutNorm A ∅ ∅)

/-- The cut norm is attained. -/
lemma exists_eq_cutNorm (A : Matrix ι κ ℝ) :
    ∃ (S : Finset ι) (T : Finset κ), |∑ i ∈ S, ∑ j ∈ T, A i j| = cutNorm A := by
  obtain ⟨ST, h⟩ := exists_eq_ciSup_of_finite
    (f := fun ST : Finset ι × Finset κ => |∑ i ∈ ST.1, ∑ j ∈ ST.2, A i j|)
  exact ⟨ST.1, ST.2, h⟩

/-- `‖c A‖_□ = |c| ‖A‖_□`. -/
lemma cutNorm_smul (c : ℝ) (A : Matrix ι κ ℝ) :
    cutNorm (fun i j => c * A i j) = |c| * cutNorm A := by
  have hsum : ∀ (S : Finset ι) (T : Finset κ),
      |∑ i ∈ S, ∑ j ∈ T, c * A i j| = |c| * |∑ i ∈ S, ∑ j ∈ T, A i j| := by
    intro S T; rw [← abs_mul, Finset.mul_sum]; simp_rw [Finset.mul_sum]
  apply le_antisymm
  · exact cutNorm_le _ fun S T => by
      rw [hsum]; exact mul_le_mul_of_nonneg_left (le_cutNorm A S T) (abs_nonneg c)
  · obtain ⟨S, T, h⟩ := exists_eq_cutNorm A
    rw [← h, ← hsum]
    exact le_cutNorm _ S T

end CutNorm

section Graphs

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- `C_□(Q) = ‖B(G, H, Q)‖_□` (Section 2, p. 5, l. 184–185). -/
noncomputable def costCut (Q : V → W → ℝ) : ℝ := cutNorm (B G H Q)

/-- `d_□(G, H) = min_{π} ‖A_G^π - A_H‖_□`. -/
noncomputable def dCut : ℝ := ⨅ π : V ≃ W, cutNorm (alignedDiff G H π)

/-- `d_□^OT(G, H) = inf_{Q ∈ DS(V, W)} C_□(Q)`. -/
noncomputable def dOTCut : ℝ := ⨅ Q : {Q : V → W → ℝ // IsDS Q}, costCut G H Q.1

/-- `δ_□(G, H) = n⁻² d_□(G, H)`. -/
noncomputable def deltaCut : ℝ := dCut G H / (Fintype.card V : ℝ) ^ 2

/-- `δ_□^OT(G, H) = n⁻² d_□^OT(G, H)`. -/
noncomputable def deltaOTCut : ℝ := dOTCut G H / (Fintype.card V : ℝ) ^ 2

/-- The adjacency matrix `A_G` as a `Matrix`. -/
def adjMat : Matrix V V ℝ := fun v v' => adj G v v'

end Graphs

section Weighted

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- `ζ_R(A, B) = ‖D_{A,B}‖_{□, μ_R}` with `μ_R(v, w) = R(v, w)/n` (Appendix E.2.2, p. 36,
l. 1129–1138), i.e.
`max_{S, T ⊆ V × W} |∑_{x ∈ S, y ∈ T} μ_R(x) μ_R(y) (A(x₁, y₁) - B(x₂, y₂))|`. -/
noncomputable def epsR (A : Matrix V V ℝ) (B : Matrix W W ℝ) (R : V → W → ℝ) : ℝ :=
  cutNorm (fun x y : V × W =>
    (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) * (A x.1 y.1 - B x.2 y.2))

/-- For graphs, `ζ_R(A_G, A_H) = ζ_R = n⁻² C_□(R)` (p. 36, l. 1139, and Eq. (21)). -/
lemma epsR_adjMat (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
    [DecidableRel H.Adj] (R : V → W → ℝ) :
    epsR (adjMat G) (adjMat H) R = costCut G H R / (Fintype.card V : ℝ) ^ 2 := by
  have h : (fun x y : V × W => (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
      (adjMat G x.1 y.1 - adjMat H x.2 y.2)) =
      fun x y => (1 / (Fintype.card V : ℝ) ^ 2) * B G H R x y := by
    funext x y; simp only [B, disc, adjMat]; ring
  unfold epsR costCut
  rw [h, cutNorm_smul, abs_of_nonneg (by positivity)]
  ring

end Weighted

end GsimOT
