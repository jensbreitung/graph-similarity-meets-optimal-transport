/-
# Proposition 5: the lower bound `4/3` for the edit distance

Paper, Section 3.1, Proposition 5 (p. 6, l. 221–223): For every odd `N ≥ 3`, there are graphs
`G` and `H` with `d_ed(G, H) ≥ 4N - 2` and `d^OT_ed(G, H) ≤ 3N + 1`.  Thus, for every `ε > 0`,
there is a sufficiently large `N`, such that `δ_ed(G, H) ≥ (4/3 - ε) · δ^OT_ed(G, H)`.
The second statement gives Theorem 3 (1) (p. 4, l. 124).

Proof (paper, App. C.1, p. 24, l. 754–758).  By Lemmas 24 and 25,
`d_ed(G, H) ≥ 4N - 2 = (4/3 - 10/(3(3N + 1)))(3N + 1) ≥ (4/3 - 10/(3(3N + 1))) d^OT_ed(G, H)`.
The two distances have the same normalisation factor; for `ε > 0` choose an odd `N` so large that
`10/(3(3N + 1)) ≤ ε`.

Formalisation notes.
* `G` and `H` are `GN N` and `HN N`, on the common vertex set `VN N`; the construction is in
  `Construction.lean`.
* `proposition6_dEdit` is the first statement as in the paper; `proposition6` is the form with
  an explicit witness: every bijection costs at least `4N - 2`, and some `Q ∈ DS(V, W)` costs
  at most `3N + 1`.  This `Q` is the fractional alignment of Lemma 24 (`Qwit N`), with
  `C_ed(Q) = 3N` (`costEdit_witness`).
* `proposition6_delta_of_le` is the paper's computation, for every odd `N ≥ 3` with
  `10/(3(3N + 1)) ≤ ε`; `proposition6_delta` chooses such an `N`.
-/
import GsimOT.Proposition6_EditLowerBound.Lemma29_FractionalCost
import GsimOT.Proposition6_EditLowerBound.Lemma30_BijectionCost

namespace GsimOT.Prop6

/-- **Proposition 5**, first statement: for every odd `N ≥ 3`, the graphs `G = GN N` and
`H = HN N` satisfy `d_ed(G, H) ≥ 4N - 2` (Lemma 25) and `d^OT_ed(G, H) ≤ 3N + 1` (Lemma 24). -/
theorem proposition6_dEdit {N : ℕ} (hN : Odd N) (h3 : 3 ≤ N) :
    (4 * N - 2 : ℝ) ≤ dEdit (GN N) (HN N) ∧ dOTEdit (GN N) (HN N) ≤ 3 * N + 1 :=
  ⟨lemma30 hN, lemma29 hN h3⟩

/-- **Proposition 5**, first statement, in terms of costs: for every odd `N ≥ 3`, the graphs
`G = GN N` and `H = HN N` (of the same order) satisfy `C_ed(π) ≥ 4N - 2` for every bijection
`π`, whereas `C_ed(Q) ≤ 3N + 1` for some `Q ∈ DS(V, W)`. -/
theorem proposition6 {N : ℕ} (hN : Odd N) (h3 : 3 ≤ N) :
    (∀ π : VN N ≃ VN N, (4 * N - 2 : ℝ) ≤ costEditBij (GN N) (HN N) π) ∧
      ∃ Q, IsDS Q ∧ costEdit (GN N) (HN N) Q ≤ 3 * N + 1 :=
  ⟨lemma30_bij hN, Qwit N, Qwit_isDS, by rw [costEdit_witness hN h3]; linarith⟩

/-- The computation in the proof of **Proposition 5** (p. 24, l. 754–758): for every odd `N ≥ 3`
and every `ε` with `10/(3(3N + 1)) ≤ ε`, `δ_ed(G, H) ≥ (4/3 - ε) · δ^OT_ed(G, H)`. -/
theorem proposition6_delta_of_le {N : ℕ} (hN : Odd N) (h3 : 3 ≤ N) {ε : ℝ}
    (hε : 10 / (3 * (3 * N + 1)) ≤ ε) :
    (4 / 3 - ε) * deltaOTEdit (GN N) (HN N) ≤ deltaEdit (GN N) (HN N) := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast h3
  have hc0 : 0 ≤ 4 / 3 - 10 / (3 * (3 * N + 1) : ℝ) := by
    rw [sub_nonneg, div_le_iff₀ (by positivity)]
    nlinarith
  -- the paper's chain of inequalities, read from right to left
  have key : (4 / 3 - ε) * dOTEdit (GN N) (HN N) ≤ dEdit (GN N) (HN N) :=
    calc (4 / 3 - ε) * dOTEdit (GN N) (HN N)
        ≤ (4 / 3 - 10 / (3 * (3 * N + 1))) * dOTEdit (GN N) (HN N) :=
          mul_le_mul_of_nonneg_right (by linarith) dOTEdit_nonneg
      _ ≤ (4 / 3 - 10 / (3 * (3 * N + 1))) * (3 * N + 1) :=
          mul_le_mul_of_nonneg_left (lemma29 hN h3) hc0
      _ = 4 * N - 2 := by field_simp; ring
      _ ≤ dEdit (GN N) (HN N) := lemma30 hN
  -- the two distances have the same normalisation factor
  unfold deltaEdit deltaOTEdit
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right key (by positivity)

/-- **Proposition 5**, second statement: for every `ε > 0` there is an odd `N ≥ 3` such that
`δ_ed(G, H) ≥ (4/3 - ε) · δ^OT_ed(G, H)` for `G = GN N` and `H = HN N`. -/
theorem proposition6_delta {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, Odd N ∧ 3 ≤ N ∧
      (4 / 3 - ε) * deltaOTEdit (GN N) (HN N) ≤ deltaEdit (GN N) (HN N) := by
  -- an odd `N ≥ 3` with `10/(3(3N + 1)) ≤ ε`
  obtain ⟨k, hk⟩ := exists_nat_gt (10 / (9 * ε))
  have hN : Odd (2 * k + 3) := ⟨k + 1, by ring⟩
  refine ⟨2 * k + 3, hN, by omega, proposition6_delta_of_le hN (by omega) ?_⟩
  have hk' : 10 < k * (9 * ε) := (div_lt_iff₀ (by positivity)).1 hk
  rw [div_le_iff₀ (by positivity)]
  push_cast
  nlinarith

/-- **Theorem 3 (1)** (p. 4, l. 124), which follows from Proposition 5. For every `ε > 0` there
are graphs `G, H` with `δ_ed(G, H) ≥ (4/3 - ε) · δ^OT_ed(G, H)`. -/
theorem theorem4_item1 {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, Odd N ∧ 3 ≤ N ∧
      (4 / 3 - ε) * deltaOTEdit (GN N) (HN N) ≤ deltaEdit (GN N) (HN N) :=
  proposition6_delta hε

end GsimOT.Prop6
