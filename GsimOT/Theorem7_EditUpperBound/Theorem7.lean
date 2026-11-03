/-
# Theorem 6: upper bound for the edit distance

Paper, Section 3.1, Theorem 6 (p. 7, l. 245–247): Let `Q ∈ DS(V, W)` with a decomposition
`Q = ∑ᵢ λᵢ P_{πᵢ}` as in Eq. (3).  Then `∑ᵢ λᵢ C_ed(πᵢ) ≤ 2 · C_ed(Q)`.  In particular,
`d_ed(G, H) ≤ 2 · d^OT_ed(G, H)` for all graphs `G, H` of the same order.
Normalised by `n²`, the second statement is the first bound of Theorem 2 (p. 3, l. 119),
`δ_ed ≤ 2 · δ^OT_ed`.

The proof (App. C.2, pp. 24–25, l. 761–785) takes the random bijection `π` with
`Pr(π = πᵢ) = λᵢ`, so that `E[P_π] = Q`, and bounds `E[C_ed(π)]` by the chain of l. 767–777:
`C_ed(π) = ‖A_G - P A_H Pᵀ‖²_F` (l. 767), permutation invariance of `‖·‖_F` (a), adding and
subtracting `QA_H` (l. 769), the squared triangle inequality `‖X + Y‖²_F ≤ 2‖X‖²_F + 2‖Y‖²_F` (b),
expanding the squares (c), (f), `E[P] = Q` (d), `⟨QA_H, QA_H⟩_F = ‖QA_H‖²_F` (e), cancelling
`‖QA_H‖²_F` (l. 775), `E[P] = Q` and permutation invariance (g), and finally Eq. (17)
(`costEdit_eq_frob`).

Formalisation notes.
* A decomposition is given by weights `wt : ι → ℝ` and bijections `π : ι → V ≃ W` over a finite
  index type `ι` (e.g. `Fin m`); the expectation `E[f(π)]` is the sum `∑ᵢ λᵢ f(πᵢ)`.  Only
  `λᵢ ≥ 0` and `∑ᵢ λᵢ = 1` are assumed, so every decomposition as in Eq. (3) is covered, and
  `Q ∈ DS(V, W)` follows from the decomposition (`isDS_of_decomposition`).
* The `calc` block of `theorem7` has one step per line of the chain (l. 767–777); the comments
  give the paper's line and, where the paper has one, the label (a)–(g) of each step.
* The paper applies Theorem 6 to a minimiser `Q` of `C_ed` over `DS(V, W)` (l. 783–785).  As
  `d^OT_ed` is defined as an infimum, `theorem7_dEdit` applies it to every `Q ∈ DS(V, W)` and its
  Birkhoff decomposition (`exists_birkhoff_decomposition`).
* `theorem7_dEdit` and `theorem3_edit` hold without assuming `|V| = |W|`: otherwise there is no
  bijection, and `d_ed(G, H) = 0`.
-/
import GsimOT.Theorem7_EditUpperBound.TraceFormula
import GsimOT.Common.BirkhoffDecomposition

open Finset

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- **Theorem 6** (p. 7, l. 245–246). Let `Q = ∑ᵢ λᵢ P_{πᵢ}` be a convex combination of
permutation matrices, i.e. `Q ∈ DS(V, W)` with a decomposition as in Eq. (3). Then
`∑ᵢ λᵢ C_ed(πᵢ) ≤ 2 · C_ed(Q)`. -/
theorem theorem7 {ι : Type*} [Fintype ι] (wt : ι → ℝ) (π : ι → V ≃ W) (hwt : ∀ i, 0 ≤ wt i)
    (hsum : ∑ i, wt i = 1) {Q : V → W → ℝ}
    (hQ : ∀ v w, Q v w = ∑ i, wt i * permMat (π i) v w) :
    ∑ i, wt i * costEditBij G H (π i) ≤ 2 * costEdit G H Q := by
  -- `X i = A_G P_{πᵢ}`, `Y i = P_{πᵢ} A_H` and `C = Q A_H`
  set X : ι → V → W → ℝ := fun i => adjMul G (permMat (π i)) with hX
  set Y : ι → V → W → ℝ := fun i => mulAdj H (permMat (π i)) with hY
  set C : V → W → ℝ := mulAdj H Q with hC
  -- `E[P] = Q`: `E[P A_H] = Q A_H` and `E[A_G P] = A_G Q`
  have hEY : ∀ v w, C v w = ∑ i, wt i * Y i v w := mulAdj_eq_sum wt _ hQ
  have hEX : ∀ v w, adjMul G Q v w = ∑ i, wt i * X i v w := adjMul_eq_sum wt _ hQ
  -- `E[c] = c` for constants
  have hconst : ∀ c : ℝ, ∑ i, wt i * c = c := fun c => by rw [← sum_mul, hsum, one_mul]
  -- the chain of App. C.2, pp. 24–25, l. 767–777
  calc ∑ i, wt i * costEditBij G H (π i)
      -- l. 767: `E[C_ed(π)] = E‖A_G - P A_H Pᵀ‖²_F`
      = ∑ i, wt i * frob (adj G - conjMul H (permMat (π i)))
          (adj G - conjMul H (permMat (π i))) := by
        simp only [costEditBij_eq_frob_conjMul]
    -- (a), l. 768: permutation invariance
    _ = ∑ i, wt i * frob (X i - Y i) (X i - Y i) := by
        simp only [hX, hY, frob_conjMul_eq]
    -- l. 769: regrouping
    _ = ∑ i, wt i * frob ((X i - C) + (C - Y i)) ((X i - C) + (C - Y i)) := by
        simp only [sub_add_sub_cancel]
    -- (b), l. 770: squared triangle inequality
    _ ≤ 2 * ∑ i, wt i * (frob (X i - C) (X i - C) + frob (C - Y i) (C - Y i)) := by
        rw [mul_sum]
        refine sum_le_sum fun i _ => ?_
        have := mul_le_mul_of_nonneg_left (frob_add_self_le (X i - C) (C - Y i)) (hwt i)
        linarith
    -- (c), l. 771: expanding the second square
    _ = 2 * ∑ i, wt i * (frob (X i - C) (X i - C) + frob C C + frob (Y i) (Y i) -
          2 * frob C (Y i)) := by
        congr 1
        refine sum_congr rfl fun i _ => ?_
        rw [frob_sub_self C (Y i)]
        ring
    -- (d), l. 772: `E[P] = Q` and linearity
    _ = 2 * ∑ i, wt i * (frob (X i - C) (X i - C) + frob C C + frob (Y i) (Y i) -
          2 * frob C C) := by
        have hd : ∑ i, wt i * frob C (Y i) = ∑ i, wt i * frob C C := by
          rw [← frob_eq_sum_right wt C Y hEY, hconst]
        simp only [mul_sub, sum_sub_distrib, mul_left_comm _ (2 : ℝ), ← mul_sum, hd]
    -- (e), l. 773: `⟨QA_H, QA_H⟩_F = ‖QA_H‖²_F`
    _ = 2 * ∑ i, wt i * (frob (X i - C) (X i - C) - frob C C + frob (Y i) (Y i)) := by
        congr 1
        exact sum_congr rfl fun i _ => by ring
    -- (f), l. 774: expanding the first square
    _ = 2 * ∑ i, wt i * (frob (X i) (X i) + frob C C - 2 * frob (X i) C - frob C C +
          frob (Y i) (Y i)) := by
        simp only [frob_sub_self]
    -- l. 775: cancelling `‖QA_H‖²_F`
    _ = 2 * ∑ i, wt i * (frob (X i) (X i) + frob (Y i) (Y i) - 2 * frob (X i) C) := by
        congr 1
        exact sum_congr rfl fun i _ => by ring
    -- (g), l. 776: `E[P] = Q` and permutation invariance
    _ = 2 * (frob (adj G) (adj G) + frob (adj H) (adj H) - 2 * frob (adjMul G Q) C) := by
        rw [frob_eq_sum_left wt X hEX C]
        simp only [hX, hY, frob_adjMul_permMat, frob_mulAdj_permMat, mul_sub, mul_add,
          sum_sub_distrib, sum_add_distrib, mul_left_comm _ (2 : ℝ), ← mul_sum, hconst]
    -- Eq. (17), l. 777
    _ = 2 * costEdit G H Q := by
        rw [costEdit_eq_frob (isDS_of_decomposition wt π hwt hsum hQ)]

/-- **Theorem 6**, second statement (p. 7, l. 247; proof p. 25, l. 783–785):
`d_ed(G, H) ≤ 2 · d^OT_ed(G, H)`. It holds for all `G, H`, not only for graphs of the same order:
otherwise there is no bijection and `d_ed(G, H) = 0`. -/
theorem theorem7_dEdit : dEdit G H ≤ 2 * dOTEdit G H := by
  rcases isEmpty_or_nonempty (V ≃ W) with h | h
  · have h0 : dEdit G H = 0 := by simp [dEdit]
    rw [h0]
    linarith [dOTEdit_nonneg (G := G) (H := H)]
  · have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr h.some
    suffices dEdit G H / 2 ≤ dOTEdit G H by linarith
    refine le_dOTEdit fun Q hQ => ?_
    obtain ⟨wt, π, hwt, hsum, hdec⟩ := exists_birkhoff_decomposition hQ hcard
    -- every bijection costs at least `d_ed`, so the average over the decomposition does
    have hd : dEdit G H ≤ ∑ σ, wt σ * costEditBij G H (π σ) :=
      calc dEdit G H = ∑ σ, wt σ * dEdit G H := by rw [← sum_mul, hsum, one_mul]
        _ ≤ ∑ σ, wt σ * costEditBij G H (π σ) :=
          sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (dEdit_le (π σ)) (hwt σ)
    linarith [theorem7 (G := G) (H := H) wt π hwt hsum hdec]

/-- **Theorem 2** (first bound, p. 3, l. 119): `δ_ed(G, H) ≤ 2 · δ^OT_ed(G, H)`. -/
theorem theorem3_edit : deltaEdit G H ≤ 2 * deltaOTEdit G H := by
  unfold deltaEdit deltaOTEdit
  rw [← mul_div_assoc]
  gcongr
  exact theorem7_dEdit

end GsimOT
