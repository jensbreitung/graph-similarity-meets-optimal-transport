/-
# The Birkhoff decomposition of a doubly stochastic matrix (Eq. (3))

Paper, Section 2, Eq. (3) (p. 5, l. 193–196): by the Birkhoff–von Neumann theorem, every
`Q ∈ DS(V, W)` with `|V| = |W|` is a convex combination `Q = ∑ᵢ λᵢ P_{πᵢ}` of permutation
matrices with `λᵢ > 0` and `∑ᵢ λᵢ = 1`. We derive the decomposition from Mathlib's
Birkhoff–von Neumann theorem `exists_eq_sum_perm_of_mem_doublyStochastic`, as
`GsimOT/Common/Birkhoff.lean` does for the consequence that `supp(Q)` contains a bijection.

* `isDS_of_decomposition`: a convex combination of permutation matrices is doubly stochastic.
* `exists_birkhoff_decomposition`: **Eq. (3)**, indexed by all permutations (weights `≥ 0`).
* `exists_birkhoff_decomposition_pos`: **Eq. (3)** as stated, with positive weights only.
-/
import GsimOT.Common.Basic

open Finset

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- A convex combination `∑ᵢ λᵢ P_{πᵢ}` of permutation matrices is doubly stochastic. -/
lemma isDS_of_decomposition {ι : Type*} [Fintype ι] (wt : ι → ℝ) (π : ι → V ≃ W)
    (hwt : ∀ i, 0 ≤ wt i) (hsum : ∑ i, wt i = 1) {Q : V → W → ℝ}
    (hQ : ∀ v w, Q v w = ∑ i, wt i * permMat (π i) v w) : IsDS Q where
  nonneg v w := by
    rw [hQ]
    exact sum_nonneg fun i _ => mul_nonneg (hwt i) ((permMat_isDS _).nonneg _ _)
  row_sum v := by
    simp_rw [hQ]
    rw [sum_comm]
    simp_rw [← mul_sum, (permMat_isDS _).row_sum, mul_one, hsum]
  col_sum w := by
    simp_rw [hQ]
    rw [sum_comm]
    simp_rw [← mul_sum, (permMat_isDS _).col_sum, mul_one, hsum]

/-- **Eq. (3)** (Birkhoff–von Neumann). If `|V| = |W|`, then every `Q ∈ DS(V, W)` is a convex
combination `Q = ∑_σ λ_σ P_{π_σ}` of permutation matrices, with `λ ≥ 0` and `∑_σ λ_σ = 1`.
Eq. (3) also asks for `λᵢ > 0`; here we index by all `σ ∈ Perm(V)` and allow zero weights, which
suffices for Theorems 6 and 14; `exists_birkhoff_decomposition_pos` is the exact form. -/
theorem exists_birkhoff_decomposition {Q : V → W → ℝ} (hQ : IsDS Q)
    (hcard : Fintype.card V = Fintype.card W) :
    ∃ (wt : Equiv.Perm V → ℝ) (π : Equiv.Perm V → V ≃ W), (∀ σ, 0 ≤ wt σ) ∧
      ∑ σ, wt σ = 1 ∧ ∀ v w, Q v w = ∑ σ, wt σ * permMat (π σ) v w := by
  let e : V ≃ W := Fintype.equivOfCardEq hcard
  -- the square matrix `M v v' = Q v (e v')`
  let M : Matrix V V ℝ := fun v v' => Q v (e v')
  have hM : M ∈ doublyStochastic ℝ V := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun v v' => hQ.nonneg _ _, fun v => ?_, fun v' => hQ.col_sum _⟩
    simpa [M] using (Equiv.sum_comp e (fun w => Q v w)).trans (hQ.row_sum v)
  obtain ⟨wt, hwt0, hwt1, hwtM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  refine ⟨wt, fun σ => σ.trans e, hwt0, hwt1, fun v w => ?_⟩
  have hentry : M v (e.symm w) = ∑ σ, wt σ * σ.permMatrix ℝ v (e.symm w) := by
    rw [← hwtM]; simp [Matrix.sum_apply]
  have hQM : Q v w = M v (e.symm w) := by simp [M]
  rw [hQM, hentry]
  refine sum_congr rfl fun σ _ => ?_
  congr 1
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply, permMat,
    Equiv.trans_apply]
  by_cases h : e (σ v) = w
  · have h' : e.symm w = σ v := by rw [← h, Equiv.symm_apply_apply]
    simp [h, h']
  · have h' : e.symm w ≠ σ v := fun h' => h (by rw [← h', Equiv.apply_symm_apply])
    simp [h, h']

/-- **Eq. (3)** exactly as stated (p. 5, l. 193–196): if `|V| = |W|`, every `Q ∈ DS(V, W)` is
`Q = ∑_{σ ∈ S} λ_σ P_{π_σ}` for a finite set `S` of indices with `λ_σ > 0` for all `σ ∈ S` and
`∑_{σ ∈ S} λ_σ = 1` (the support `{π_σ | σ ∈ S}` of the decomposition). -/
theorem exists_birkhoff_decomposition_pos {Q : V → W → ℝ} (hQ : IsDS Q)
    (hcard : Fintype.card V = Fintype.card W) :
    ∃ (S : Finset (Equiv.Perm V)) (wt : Equiv.Perm V → ℝ) (π : Equiv.Perm V → V ≃ W),
      (∀ σ ∈ S, 0 < wt σ) ∧ ∑ σ ∈ S, wt σ = 1 ∧
      ∀ v w, Q v w = ∑ σ ∈ S, wt σ * permMat (π σ) v w := by
  classical
  obtain ⟨wt, π, h0, h1, hQd⟩ := exists_birkhoff_decomposition hQ hcard
  have hpos : ∀ σ, wt σ ≠ 0 → 0 < wt σ := fun σ h => lt_of_le_of_ne (h0 σ) (Ne.symm h)
  refine ⟨univ.filter fun σ => 0 < wt σ, wt, π, fun σ hσ => (mem_filter.1 hσ).2, ?_, ?_⟩
  · rw [sum_filter_of_ne fun σ _ h => hpos σ h, h1]
  · intro v w
    rw [hQd, sum_filter_of_ne fun σ _ h => hpos σ (left_ne_zero_of_mul h)]

end GsimOT
