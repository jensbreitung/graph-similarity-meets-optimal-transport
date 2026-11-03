import GsimOT.Common.EditDistance
import GsimOT.Common.ThreePartition

/-!
# Theorem 15: hardness of `d^OT_ed`

Theorem 15 of the paper (p. 12, l. 418; proof in App. G, pp. 50–51, l. 1577–1620). It gives
part (1) of Theorem 4 (p. 4, l. 134).

**Theorem 15.** `GSim(d^OT_ed)` is NP-hard, even when restricted to collections of paths.

The reduction of [GRW18, Theorem 8] maps an instance `(A, a₁, …, a_{3m})` of Three-Partition to
the forests `F₁ = pathUnion I.a` (paths on `aᵢ` vertices) and `F₂` (`m` paths on `A` vertices)
and the threshold `t = 4m`. Its correctness is `dOTEdit_le_iff`.

`d^OT_ed` is `GsimOT.dOTEdit` from `GsimOT.Common.EditDistance`, the definition Theorem 6
uses as well. For `Q ≥ 0` its cost `C_ed(Q)` is `‖B(F₁, F₂, Q)‖_(1)`
(`costEdit_eq_entrywiseNorm_B`).

## Proof

The paper argues with blowups, using `d^OT_ed = d^•_ed` from [Gro25, Theorem 3.10]
(p. 50, l. 1585–1586): for an alignment `π` of the `k`-blowups it counts the number `b` of edges
mapped to non-edges, `‖A^π_{F₁'} - A_{F₂'}‖_(1) = 4mk² + 4b` (p. 51, l. 1600–1602), and concludes
from `b ≤ γk²`, `γ = 1/(2mA)`, that almost all of each cloud goes into one path of `F₂`. We argue
directly with doubly stochastic matrices, which needs neither blowups nor the citation; the
count is the same with `b/k²` replaced by `lost(Q)/2`, and the `γ`-approximation becomes exact:

* for `a, b ∈ {0, 1}` we have `|a - b| = b - a + 2a(1 - b)`, so for every `Q ∈ DS(V, W)`
  `‖B(F₁, F₂, Q)‖_(1) = 2|E(F₂)| - 2|E(F₁)| + 2 · lost(Q) = 4m + 2 · lost(Q)`, where `lost(Q) ≥ 0`
  is the mass of edges of `F₁` that `Q` maps to non-edges of `F₂` (`entrywiseNorm_B_eq`);
* so `d^OT_ed(F₁, F₂) ≤ 4m` iff some `Q` has `lost(Q) = 0` (the minimum is attained,
  `exists_dOTEdit_eq`), i.e. `Q(v,w) Q(v',w') = 0` whenever `vv' ∈ E(F₁)` and `ww' ∉ E(F₂)`;
* such a `Q` maps every path of `F₁` into a single path of `F₂` (the paper's `j(·)` is constant
  on paths, l. 1611–1616), and counting mass gives a solution (`ThreePartition.isYes_of_isDS`,
  l. 1617–1620). Conversely a solution gives a bijection mapping edges to edges, which has
  `lost = 0` (pp. 50–51, l. 1588–1597).

The NP-hardness itself (polynomial size of the construction and NP-hardness of
Three-Partition in unary) is not formalized, nor is Proposition 57 (membership in NP).
-/

open Finset

namespace GsimOT.Hardness

section EditCost

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] (G : SimpleGraph V)
  (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] {Q : V → W → ℝ}

/-- The summand of `lost`: mass of the edge `vv'` of `G` mapped onto the non-edge `ww'` of `H`. -/
def lostTerm (Q : V → W → ℝ) (x y : V × W) : ℝ :=
  Q x.1 x.2 * (adj G x.1 y.1 * (1 - adj H x.2 y.2)) * Q y.1 y.2

/-- The mass of edges of `G` that `Q` maps to non-edges of `H`. -/
def lost (Q : V → W → ℝ) : ℝ := ∑ x, ∑ y, lostTerm G H Q x y

lemma lostTerm_nonneg (hQ : IsDS Q) (x y : V × W) : 0 ≤ lostTerm G H Q x y :=
  mul_nonneg (mul_nonneg (hQ.nonneg _ _) (mul_nonneg (adj_nonneg G _ _)
    (sub_nonneg.mpr (adj_le_one H _ _)))) (hQ.nonneg _ _)

lemma lost_nonneg (hQ : IsDS Q) : 0 ≤ lost G H Q :=
  sum_nonneg fun x _ ↦ sum_nonneg fun y _ ↦ lostTerm_nonneg G H hQ x y

/-- The expansion of the edit cost (as in the proof of Theorem 6):
`‖B(G, H, Q)‖_(1) = ∑ A_H - ∑ A_G + 2 · lost(Q)`. -/
lemma entrywiseNorm_B_eq (hQ : IsDS Q) :
    entrywiseNorm (B G H Q) =
      ∑ w, ∑ w', adj H w w' - ∑ v, ∑ v', adj G v v' + 2 * lost G H Q := by
  have habs (x y : V × W) : |B G H Q x y| =
      Q x.1 x.2 * adj H x.2 y.2 * Q y.1 y.2 -
        Q x.1 x.2 * adj G x.1 y.1 * Q y.1 y.2 + 2 * lostTerm G H Q x y := by
    have h1 := hQ.nonneg x.1 x.2
    have h2 := hQ.nonneg y.1 y.2
    simp only [B, disc, lostTerm, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2,
      adj]
    split_ifs <;> norm_num
    ring
  unfold entrywiseNorm lost
  simp_rw [habs, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [hQ.sum_mul_mul_snd (adj H), hQ.sum_mul_mul_fst (adj G)]
/-- If `lost(Q) = 0`, no edge of `G` is mapped to a non-edge of `H`. -/
lemma mul_eq_zero_of_lost_eq_zero (hQ : IsDS Q) (h : lost G H Q = 0) {v v' : V} {w w' : W}
    (hG : G.Adj v v') (hH : ¬H.Adj w w') : Q v w * Q v' w' = 0 := by
  have hx := (sum_eq_zero_iff_of_nonneg fun x _ ↦
    sum_nonneg fun y _ ↦ lostTerm_nonneg G H hQ x y).mp h (v, w) (mem_univ _)
  have hxy := (sum_eq_zero_iff_of_nonneg fun y _ ↦
    lostTerm_nonneg G H hQ (v, w) y).mp hx (v', w') (mem_univ _)
  simpa [lostTerm, adj, hG, hH] using hxy

/-- A bijection mapping edges to edges loses no edge mass. -/
lemma lost_permMat (π : V ≃ W)
    (hπ : ∀ v v', G.Adj v v' → H.Adj (π v) (π v')) : lost G H (permMat π) = 0 := by
  refine sum_eq_zero fun x _ ↦ sum_eq_zero fun y _ ↦ ?_
  by_cases h1 : π x.1 = x.2
  · by_cases h2 : π y.1 = y.2
    · by_cases hG : G.Adj x.1 y.1
      · have hH : H.Adj x.2 y.2 := h1 ▸ h2 ▸ hπ _ _ hG
        simp [lostTerm, adj, hG, hH]
      · simp [lostTerm, adj, hG]
    · simp [lostTerm, permMat, h2]
  · simp [lostTerm, permMat, h1]

end EditCost

namespace ThreePartition

variable (I : ThreePartition)

/-- `F₁` has `∑ (aᵢ - 1) = mA - 3m` edges and `F₂` has `m(A - 1)` edges, so
`2|E(F₂)| - 2|E(F₁)| = 4m`. -/
lemma sum_adj_sub_sum_adj :
    ∑ w, ∑ w', adj (pathUnion fun _ : Fin I.m ↦ I.A) w w' -
      ∑ v, ∑ v', adj (pathUnion I.a) v v' = 4 * I.m := by
  have hA : ∀ j : Fin I.m, 1 ≤ I.A := fun j ↦ by
    have := I.two_mul_lt ⟨0, by have := j.pos; omega⟩
    omega
  rw [sum_adj_pathUnion _ hA, sum_adj_pathUnion _ fun i ↦ I.a_pos i]
  have hsum : ∑ i, (I.a i : ℝ) = I.m * I.A := by exact_mod_cast I.sum_eq
  simp only [sum_sub_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    hsum]
  push_cast
  ring

/-- **Theorem 15** (correctness of the reduction, p. 50, l. 1584–1585): `d^OT_ed(F₁, F₂) ≤ 4m`
iff `I` is a YES-instance of Three-Partition. The formalisation assumes `aᵢ ≥ 2` for all `i`. -/
theorem dOTEdit_le_iff (h2 : ∀ i, 2 ≤ I.a i) :
    dOTEdit (pathUnion I.a) (pathUnion fun _ : Fin I.m ↦ I.A) ≤ 4 * I.m ↔ I.IsYes := by
  set G := pathUnion I.a
  set H := pathUnion fun _ : Fin I.m ↦ I.A
  have hcost (Q : _ → _ → ℝ) (hQ : IsDS Q) : costEdit G H Q = 4 * I.m + 2 * lost G H Q := by
    rw [costEdit_eq_entrywiseNorm_B G H hQ.nonneg, entrywiseNorm_B_eq G H hQ,
      I.sum_adj_sub_sum_adj]
  constructor
  · intro hle
    have := Nonempty.intro (Fintype.equivOfCardEq I.card_vertices)
    obtain ⟨Q, hQ, hQmin⟩ := exists_dOTEdit_eq (G := G) (H := H)
    have hlost : lost G H Q = 0 := by
      have := lost_nonneg G H hQ
      have := hcost Q hQ
      linarith
    -- edges of `F₁` go to edges of `F₂`, which stay inside one path of `F₂`
    have hcomp {v v' : Σ i, Fin (I.a i)} {w w' : Σ _ : Fin I.m, Fin I.A} (hG : G.Adj v v')
        (hw : Q v w ≠ 0) (hw' : Q v' w' ≠ 0) : w.1 = w'.1 := by
      by_contra hne
      exact mul_ne_zero hw hw' (mul_eq_zero_of_lost_eq_zero G H hQ hlost hG fun hH ↦ hne hH.1)
    -- the path of `F₂` receiving the mass of `v`
    choose wsel hwsel using hQ.exists_ne_zero
    have hc (v : Σ i, Fin (I.a i)) (w) (hw : Q v w ≠ 0) : w.1 = (wsel v).1 := by
      obtain ⟨u, hu⟩ := exists_pathUnion_adj I.a v (h2 v.1)
      exact (hcomp hu.symm hw (hwsel u)).trans (hcomp hu.symm (hwsel v) (hwsel u)).symm
    have hconst : ∀ u v, G.Adj u v → (wsel u).1 = (wsel v).1 := fun u v huv ↦
      hcomp huv (hwsel u) (hwsel v)
    refine I.isYes_of_isDS hQ (fun i ↦ (wsel ⟨i, ⟨0, by have := h2 i; omega⟩⟩).1)
      fun v w hw ↦ ?_
    rw [hc v w hw]
    exact eq_of_pathUnion_adj I.a (fun v ↦ (wsel v).1) hconst v
  · rintro ⟨σ, hσ⟩
    have hσ' : ∀ j, ∑ i with σ i = j, I.a i = I.A := fun j ↦ (hσ j).2
    set π := layoutEquiv σ hσ'
    have hlost : lost G H (permMat π) = 0 :=
      lost_permMat G H π fun v v' h ↦ layout_adj_pathUnion σ hσ' h
    calc dOTEdit G H ≤ costEdit G H (permMat π) :=
          dOTEdit_le (permMat_isDS π)
      _ = 4 * I.m := by rw [hcost _ (permMat_isDS π), hlost, mul_zero, add_zero]

/-- **Theorem 15** for arbitrary instances: after the w.l.o.g. shift (p. 50, l. 1586–1587), the
reduction `I ↦ (F₁, F₂, 4m)` is correct. -/
theorem dOTEdit_shift_le_iff :
    dOTEdit (pathUnion I.shift.a) (pathUnion fun _ : Fin I.shift.m ↦ I.shift.A) ≤ 4 * I.m ↔
      I.IsYes :=
  (I.shift.dOTEdit_le_iff fun i ↦ (by have := I.four_le_shift_a i; omega)).trans
    I.shift_isYes_iff

end ThreePartition

end GsimOT.Hardness
