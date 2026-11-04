/-
# The support of a doubly stochastic matrix contains a bijection (Eq. (3))

Paper, Section 2, Eq. (3) (p. 5, l. 193–196): by the Birkhoff–von Neumann theorem every
`Q ∈ DS(V, W)` is a convex combination `∑ λᵢ P_{πᵢ}` of permutation matrices with `λᵢ > 0`.
Consequently the graph of each `πᵢ` is contained in `supp(Q)`, as used for the reference bijection
`σ` of Eq. (18) (Appendix D.2, p. 28, l. 867–869).  We only need this consequence, which we derive
from Mathlib's Birkhoff–von Neumann theorem `exists_eq_sum_perm_of_mem_doublyStochastic`.
-/
import GsimOT.Common.Basic

open Finset

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- **Eq. (3)** (consequence of Birkhoff–von Neumann). If `|V| = |W|`, then the support of every
`Q ∈ DS(V, W)` contains the graph of a bijection `σ : V ≃ W`. -/
theorem exists_bij_subset_supp {Q : V → W → ℝ} (hQ : IsDS Q)
    (hcard : Fintype.card V = Fintype.card W) :
    ∃ σ : V ≃ W, ∀ v, Q v (σ v) ≠ 0 := by
  let e : V ≃ W := Fintype.equivOfCardEq hcard
  -- the square matrix `M v v' = Q v (e v')`
  let M : Matrix V V ℝ := fun v v' => Q v (e v')
  have hM : M ∈ doublyStochastic ℝ V := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun v v' => hQ.nonneg _ _, fun v => ?_, fun v' => hQ.col_sum _⟩
    simpa [M] using (Equiv.sum_comp e (fun w => Q v w)).trans (hQ.row_sum v)
  obtain ⟨wt, hwt0, hwt1, hwtM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  -- some coefficient is positive
  obtain ⟨τ, hτ⟩ : ∃ τ, 0 < wt τ := by
    by_contra h
    push Not at h
    have : ∑ τ, wt τ ≤ 0 := Finset.sum_nonpos fun τ _ => h τ
    linarith
  refine ⟨τ.trans e, fun v => ?_⟩
  have hentry : M v (τ v) = ∑ σ, wt σ * σ.permMatrix ℝ v (τ v) := by
    rw [← hwtM]; simp [Matrix.sum_apply]
  have hge : wt τ ≤ M v (τ v) := by
    rw [hentry]
    have hle : wt τ * τ.permMatrix ℝ v (τ v) ≤ ∑ σ, wt σ * σ.permMatrix ℝ v (τ v) :=
      Finset.single_le_sum (f := fun σ => wt σ * σ.permMatrix ℝ v (τ v))
        (fun σ _ => mul_nonneg (hwt0 σ) (by
          simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
          split_ifs <;> norm_num)) (Finset.mem_univ τ)
    simpa [Equiv.Perm.permMatrix] using hle
  have : 0 < M v (τ v) := lt_of_lt_of_le hτ hge
  simpa [M] using this.ne'

end GsimOT
