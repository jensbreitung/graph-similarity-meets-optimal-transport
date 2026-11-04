import GsimOT.Theorem18_CutHardness.ProductSums
import GsimOT.Common.Leaves

/-!
# Claim 61

Claim 61 of the proof of Theorem 18 (p. 61, l. 1938–1939; proof l. 1940–1965): for `δ ∈ (0, 1)`
and `0 ≤ α ≤ δ/(2n')²`, if `Q(vᵢ, wᵢ) ≥ 1 - α` for all `i ∈ [n']`, then
`‖B(G, H, Q)‖_□ ≥ 2(1 - δ) · maxcut(F)`.

* `claim61`: for arbitrary base graphs, `‖B(G, H, Q)‖_□ ≥ ‖A_{G'} - A_{H'}‖_□ - 2α n'²` with
  `n' = |V(G')|`. As in the paper, the maximiser `(S, T)` of `‖A_{G'} - A_{H'}‖_□` is lifted to
  `S' = S × W`, `T' = T × W`; for each pair `(s, t)`, the main part and the error part are
  estimated together.
* `claim61_delta`: Claim 61 in the form of the paper, for `‖A_{G'} - A_{H'}‖_□ = 2c` with `c ∈ ℕ`.
-/

open Finset

namespace GsimOT.Hardness

section Claims

variable {β : Type*} [Fintype β] [DecidableEq β] {G' H' : SimpleGraph β} [DecidableRel G'.Adj]
  [DecidableRel H'.Adj] {ℓ : β → ℕ} {Q : (β ⊕ Σ b, Fin (ℓ b)) → (β ⊕ Σ b, Fin (ℓ b)) → ℝ}

local notation "G" => addLeaves G' ℓ
local notation "H" => addLeaves H' ℓ

/-- **Claim 61.** If `Q(vᵢ, wᵢ) ≥ 1 - α` for all base vertices, then
`‖B(G, H, Q)‖_□ ≥ ‖A_{G'} - A_{H'}‖_□ - 2α|V(G')|²`. -/
lemma claim61 (hQ : IsDS Q) {α : ℝ} (hα : 0 ≤ α) (hii : ∀ i, 1 - α ≤ Q (.inl i) (.inl i)) :
    cutNorm (adj G' - adj H') - 2 * α * (Fintype.card β) ^ 2 ≤
      cutNorm (B G H Q) := by
  obtain ⟨S, T, hST⟩ := exists_eq_cutNorm (adj G' - adj H')
  set X := sum4 G H Q (S.map Function.Embedding.inl) univ (T.map Function.Embedding.inl) univ
  have hX : X = ∑ s ∈ S, ∑ t ∈ T, (adj G' s t - ∑ w, ∑ w', Q (.inl s) w *
      Q (.inl t) w' * adj H w w') := by
    simp only [X, sum4, sum_map, Function.Embedding.inl_apply, adj_addLeaves_inl_inl]
    refine sum_congr rfl fun s _ ↦ ?_
    rw [sum_comm]
    refine sum_congr rfl fun t _ ↦ ?_
    have hone : ∑ w, ∑ w', Q (.inl s) w * Q (.inl t) w' = 1 := by
      rw [← sum_mul_sum, hQ.row_sum, hQ.row_sum, one_mul]
    calc ∑ w, ∑ w', Q (.inl s) w * (adj G' s t - adj H w w') * Q (.inl t) w'
        = adj G' s t * ∑ w, ∑ w', Q (.inl s) w * Q (.inl t) w' -
            ∑ w, ∑ w', Q (.inl s) w * Q (.inl t) w' * adj H w w' := by
          rw [mul_sum, ← sum_sub_distrib]
          refine sum_congr rfl fun w _ ↦ ?_
          rw [mul_sum, ← sum_sub_distrib]
          exact sum_congr rfl fun w' _ ↦ by ring
      _ = _ := by rw [hone, mul_one]
  have hclose : |X - ∑ s ∈ S, ∑ t ∈ T, (adj G' - adj H') s t| ≤
      2 * α * (Fintype.card β) ^ 2 := by
    rw [hX, ← sum_sub_distrib]
    calc |∑ s ∈ S, (∑ t ∈ T, (adj G' s t - ∑ w, ∑ w', Q (.inl s) w *
            Q (.inl t) w' * adj H w w') - ∑ t ∈ T, (adj G' - adj H') s t)|
        ≤ ∑ s ∈ S, ∑ t ∈ T, 2 * α := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ ↦ ?_)
          rw [← sum_sub_distrib]
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t _ ↦ ?_)
          have key := abs_sub_sum_mul_mul_le hQ (.inl s) (.inl t) (.inl s) (.inl t)
            (fun w w' ↦ adj H w w') (fun w w' ↦ adj_nonneg _ w w')
            fun w w' ↦ adj_le_one _ w w'
          simp only [adj_addLeaves_inl_inl] at key
          have h1 := hii s
          have h2 := hii t
          have h3 := hQ.le_one (.inl s) (.inl s)
          have h4 := hQ.le_one (.inl t) (.inl t)
          have hp : 1 - Q (.inl s) (.inl s) * Q (.inl t) (.inl t) ≤ 2 * α := by nlinarith
          calc |adj G' s t - ∑ w, ∑ w', Q (.inl s) w * Q (.inl t) w' *
                adj H w w' - (adj G' - adj H') s t|
              = |adj H' s t - ∑ w, ∑ w', Q (.inl s) w * Q (.inl t) w' *
                adj H w w'| := by
                rw [Pi.sub_apply, Pi.sub_apply]; congr 1; ring
            _ ≤ 2 * α := key.trans hp
      _ = #S * #T * (2 * α) := by simp; ring
      _ ≤ Fintype.card β * Fintype.card β * (2 * α) := by
          have hS : (#S : ℝ) ≤ Fintype.card β := by exact_mod_cast card_le_univ S
          have hT : (#T : ℝ) ≤ Fintype.card β := by exact_mod_cast card_le_univ T
          exact mul_le_mul_of_nonneg_right (mul_le_mul hS hT (by positivity) (by positivity))
            (by linarith)
      _ = 2 * α * (Fintype.card β) ^ 2 := by ring
  have hcut : cutNorm (adj G' - adj H') =
      |∑ s ∈ S, ∑ t ∈ T, (adj G' - adj H') s t| := hST.symm
  calc cutNorm (adj G' - adj H') - 2 * α * (Fintype.card β) ^ 2 ≤ |X| := by
        rw [hcut]
        have := abs_sub_abs_le_abs_sub (∑ s ∈ S, ∑ t ∈ T, (adj G' - adj H') s t) X
        rw [abs_sub_comm] at this
        linarith
    _ ≤ cutNorm (B G H Q) := abs_sum4_le_cutNorm G H Q _ _ _ _

/-- **Claim 61** in the form of the paper: if `‖A_{G'} - A_{H'}‖_□ = 2c` for a natural number `c`
(`c = maxcut(F)` in the reduction), `0 ≤ α ≤ δ/(2n')²` with `n' = |V(G')|`, and
`Q(vᵢ, wᵢ) ≥ 1 - α` for all base vertices, then `‖B(G, H, Q)‖_□ ≥ 2(1 - δ) c`. Here `δ ≥ 0`
is arbitrary; the paper takes `δ ∈ (0, 1)`. -/
lemma claim61_delta (hQ : IsDS Q) {c : ℕ} (hc : cutNorm (adj G' - adj H') = 2 * c) {α δ : ℝ}
    (hδ : 0 ≤ δ) (hα : 0 ≤ α) (hαδ : α ≤ δ / (2 * (Fintype.card β : ℝ)) ^ 2)
    (hii : ∀ i, 1 - α ≤ Q (.inl i) (.inl i)) :
    2 * (1 - δ) * c ≤ cutNorm (B G H Q) := by
  have h := claim61 (G' := G') (H' := H') hQ hα hii
  rw [hc] at h
  -- `4 α n'² ≤ δ`
  have hαn : 4 * α * (Fintype.card β : ℝ) ^ 2 ≤ δ := by
    have hsq : 4 * α * (Fintype.card β : ℝ) ^ 2 = α * (2 * (Fintype.card β : ℝ)) ^ 2 := by ring
    rw [hsq]
    rcases (sq_nonneg (2 * (Fintype.card β : ℝ))).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      exact hδ
    · calc α * (2 * (Fintype.card β : ℝ)) ^ 2
          ≤ δ / (2 * (Fintype.card β : ℝ)) ^ 2 * (2 * (Fintype.card β : ℝ)) ^ 2 := by gcongr
        _ = δ := div_mul_cancel₀ _ hpos.ne'
  rcases Nat.eq_zero_or_pos c with hc0 | hc1
  · subst hc0
    simpa using cutNorm_nonneg (B G H Q)
  · have hc1' : (1 : ℝ) ≤ c := by exact_mod_cast hc1
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hc1')]

end Claims

end GsimOT.Hardness
