import GsimOT.Theorem17_OperatorNormHardness.Claim55_LeafMass

/-!
# Claim 56

Claim 56 of the proof of Theorem 17 (p. 55, l. 1760–1761; proof pp. 55–56, l. 1762–1773).

If a base vertex `v` of `G` (with a base neighbour) sends mass `ε` to each of two distinct base
vertices of `H` with at most one common neighbour, and `M > 2(2/ε)² + 1`, then
`‖B_p(G, H, Q)‖_p > 2^{b(p)}` (`claim56`). The paper derives `|N_H(w) ∩ N_H(w')| ≤ 1` from
`|V(C_j)| = A ≥ 5` (l. 1762); here it is the hypothesis `hI`, discharged in `Theorem17.lean`.
-/

open Finset Matrix WithLp
open scoped ENNReal

namespace GsimOT.Hardness

section Claim56

variable {βG βH : Type*} [Fintype βG] [Fintype βH] [DecidableEq βG] [DecidableEq βH]
  {G' : SimpleGraph βG} {H' : SimpleGraph βH} [DecidableRel G'.Adj] [DecidableRel H'.Adj]
  {M : ℕ} {Q : (βG ⊕ Σ _ : βG, Fin M) → (βH ⊕ Σ _ : βH, Fin M) → ℝ} {p : ℝ≥0∞}
  [Fact (1 ≤ p)]

local notation "GG" => addLeaves G' fun _ : βG ↦ M
local notation "HH" => addLeaves H' fun _ : βH ↦ M

/-- **Claim 56.** If a base vertex `v` (with a base neighbour) sends mass `ε` to each of two
distinct base vertices `w, w'` with at most one common neighbour, and `M > 2(2/ε)² + 1`, then
`‖B_p(G, H, Q)‖_p > 2^{b(p)}`. -/
lemma claim56 (hQ : IsDS Q) {v : βG} (hv : ∃ u, G'.Adj u v) {w w' : βH} (hww' : w ≠ w')
    (hI : #({x | H'.Adj x w ∧ H'.Adj x w'} : Finset βH) ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (hvw : ε ≤ Q (.inl v) (.inl w)) (hvw' : ε ≤ Q (.inl v) (.inl w'))
    (hM : 2 * (2 / ε) ^ 2 + 1 < M) : 2 ^ bExp p < opNorm p p (Bmat p p GG HH Q) := by
  obtain ⟨u, hu⟩ := hv
  set N : Finset (βG ⊕ Σ _ : βG, Fin M) := {x | (GG).Adj x (.inl v)}
  have hN := card_adj_inl_ge (M := M) hu
  have hε1 : ε ≤ 1 := hvw.trans (hQ.le_one _ _)
  have hF (x : βG ⊕ Σ _ : βG, Fin M) (y y') :
      0 ≤ Q x y * (1 - adj HH y y') * Q (.inl v) y' :=
    mul_nonneg (mul_nonneg (hQ.nonneg _ _) (sub_nonneg.mpr (adj_le_one _ _ _)))
      (hQ.nonneg _ _)
  -- the common neighbours of `w` and `w'` in `H`
  set I : Finset (βH ⊕ Σ _ : βH, Fin M) := {y | (HH).Adj y (.inl w) ∧ (HH).Adj y (.inl w')}
  have hIcard : #I ≤ 1 := by
    calc #I ≤ #(({x | H'.Adj x w ∧ H'.Adj x w'} : Finset βH).map Function.Embedding.inl) := by
          refine card_le_card fun y hy ↦ ?_
          simp only [I, mem_filter, mem_univ, true_and] at hy
          cases y with
          | inl b => simpa using hy
          | inr t =>
            simp only [addLeaves_adj_inr_inl] at hy
            exact absurd (hy.1.symm.trans hy.2) hww'
      _ ≤ 1 := by rw [card_map]; exact hI
  set K := {x ∈ N | ∑ y ∈ I, Q x y ≤ 1 / 2}
  have hK : (M : ℝ) - 1 ≤ #K := by
    have h1 := card_mul_le_of_lt_mass hQ N I (1 / 2)
    have h2 := card_filter_add_card_filter_not (s := N) fun x ↦ ∑ y ∈ I, Q x y ≤ 1 / 2
    simp only [not_le] at h2
    have h3 : (#K : ℝ) + #{x ∈ N | 1 / 2 < ∑ y ∈ I, Q x y} = #N := by exact_mod_cast h2
    have h4 : (#I : ℝ) ≤ 1 := by exact_mod_cast hIcard
    linarith
  have hnum : (2 ^ bExp p / (ε / 2)) ^ (1 / bExp p) ≤ 2 * (2 / ε) ^ 2 := by
    have : 2 ^ bExp p / (ε / 2) = 2 ^ bExp p * (2 / ε) := by field_simp
    rw [this]
    exact rpow_inv_bExp_le (by rw [le_div_iff₀ hε]; linarith)
  refine lt_opNorm_Bpq GG HH hQ (v := .inl v) (K := K) (ε := ε / 2) (by positivity)
    (by positivity) (fun x hx ↦ ?_) (by linarith)
  obtain ⟨hxN, hxI⟩ := mem_filter.mp hx
  -- for `y ∉ I`, the vertex `v` sends mass `ε` to a vertex of `{w, w'}` not adjacent to `y`
  have hcol (y) (hy : y ∉ I) : ε ≤ ∑ y' ∈ ({.inl w, .inl w'} : Finset _),
      (1 - adj HH y y') * Q (.inl v) y' := by
    rw [sum_pair (by simpa using hww')]
    simp only [I, mem_filter, mem_univ, true_and, not_and_or] at hy
    have h0 := hQ.nonneg (.inl v) (.inl w)
    have h0' := hQ.nonneg (.inl v) (.inl w')
    have ha := adj_le_one (HH) y (.inl w)
    have ha' := adj_le_one (HH) y (.inl w')
    rcases hy with hy | hy
    · have : adj HH y (.inl w) = 0 := by simp [adj, hy]
      nlinarith
    · have : adj HH y (.inl w') = 0 := by simp [adj, hy]
      nlinarith
  have hlow : ε / 2 ≤ aggMatrix GG HH Q x (.inl v) := by
    rw [aggMatrix_of_adj _ _ _ (mem_filter.mp hxN).2]
    calc ε / 2 ≤ ∑ y ∈ univ \ I, Q x y * ε := by
          rw [← sum_mul, sum_sdiff_eq_sub (subset_univ I), hQ.row_sum]
          nlinarith
      _ ≤ ∑ y ∈ univ \ I, Q x y * ∑ y' ∈ ({.inl w, .inl w'} : Finset _),
            (1 - adj HH y y') * Q (.inl v) y' :=
          sum_le_sum fun y hy ↦
            mul_le_mul_of_nonneg_left (hcol y (mem_sdiff.mp hy).2) (hQ.nonneg _ _)
      _ = ∑ y ∈ univ \ I, ∑ y' ∈ ({.inl w, .inl w'} : Finset _),
            Q x y * (1 - adj HH y y') * Q (.inl v) y' := by
          refine sum_congr rfl fun y _ ↦ ?_
          rw [mul_sum]
          exact sum_congr rfl fun y' _ ↦ by ring
      _ ≤ ∑ y ∈ univ \ I, ∑ y', Q x y * (1 - adj HH y y') * Q (.inl v) y' :=
          sum_le_sum fun y _ ↦
            sum_le_sum_of_subset_of_nonneg (subset_univ _) fun y' _ _ ↦ hF x y y'
      _ ≤ ∑ y, ∑ y', Q x y * (1 - adj HH y y') * Q (.inl v) y' :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun y _ _ ↦
            sum_nonneg fun y' _ ↦ hF x y y'
  rw [abs_of_nonneg (by linarith)]
  exact hlow

end Claim56

end GsimOT.Hardness
