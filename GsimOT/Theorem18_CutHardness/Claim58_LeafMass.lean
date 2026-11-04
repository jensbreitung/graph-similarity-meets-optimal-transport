import GsimOT.Theorem18_CutHardness.ProductSums
import GsimOT.Common.Leaves

/-!
# Claim 58

Claim 58 of the proof of Theorem 18 (p. 58, l. 1854–1855; proof pp. 58–59, l. 1856–1882).

If a base vertex `v` sends mass `η` to the leaves, then `‖B(G, H, Q)‖_□ ≥ η(M - 2)/4`, where
every base vertex has at least `M` leaves (`claim58`).
-/

open Finset

namespace GsimOT.Hardness

section Claims

variable {β : Type*} [Fintype β] [DecidableEq β] {G' H' : SimpleGraph β} [DecidableRel G'.Adj]
  [DecidableRel H'.Adj] {ℓ : β → ℕ} {Q : (β ⊕ Σ b, Fin (ℓ b)) → (β ⊕ Σ b, Fin (ℓ b)) → ℝ}

local notation "G" => addLeaves G' ℓ
local notation "H" => addLeaves H' ℓ

/-- **Claim 58.** If the base vertex `v` sends mass `η` to the leaves, then
`‖B(G, H, Q)‖_□ ≥ η(M - 2)/4`, where every base vertex has at least `M` leaves. -/
lemma claim58 (hQ : IsDS Q) {M : ℕ} (hM : ∀ b, M ≤ ℓ b) {v : β} {η : ℝ} (hη : 0 ≤ η)
    (hv : η ≤ ∑ t, Q (.inl v) (.inr t)) :
    η * (M - 2) / 4 ≤ cutNorm (B G H Q) := by
  have hMv : (M : ℝ) ≤ ℓ v := by exact_mod_cast hM v
  by_cases hcase : ∀ w : β, ∑ s : Fin (ℓ w), Q (.inl v) (.inr ⟨w, s⟩) ≤ η / 2
  · -- Case 1: `S' = {v} × L_H` and `T' = L(v) × W`
    have hinner (w' : β ⊕ Σ b, Fin (ℓ b)) :
        η / 2 ≤ ∑ t, Q (.inl v) (.inr t) * (1 - adj H (.inr t) w') := by
      have hsplit : ∑ t, Q (.inl v) (.inr t) * (1 - adj H (.inr t) w') =
          ∑ t, Q (.inl v) (.inr t) - ∑ t, Q (.inl v) (.inr t) * adj H (.inr t) w' := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun t _ ↦ by ring
      have hle : ∑ t, Q (.inl v) (.inr t) * adj H (.inr t) w' ≤ η / 2 := by
        cases w' with
        | inl b =>
          simp only [adj_addLeaves_inr, Sum.inl.injEq, mul_ite, mul_one, mul_zero]
          rw [Fintype.sum_sigma, Fintype.sum_eq_single b fun b' hb' ↦ by simp [Ne.symm hb']]
          simpa using hcase b
        | inr t' =>
          simp only [adj_addLeaves_inr, reduceCtorEq, ite_false, mul_zero, sum_const_zero]
          linarith
      rw [hsplit]
      linarith
    have h4 : sum4 G H Q {.inl v} (allLeaves ℓ) (leavesOf ℓ v) univ =
        ∑ s : Fin (ℓ v), ∑ w', Q (.inr ⟨v, s⟩) w' *
          ∑ t, Q (.inl v) (.inr t) * (1 - adj H (.inr t) w') := by
      simp only [sum4, sum_singleton, sum_allLeaves, sum_leavesOf, adj_addLeaves_inl_inr,
        mul_sum, ite_true]
      rw [sum_comm]
      refine sum_congr rfl fun s _ ↦ ?_
      rw [sum_comm]
      exact sum_congr rfl fun w' _ ↦ sum_congr rfl fun t _ ↦ by simp [adj]; ring
    calc η * (M - 2) / 4 ≤ ℓ v * (η / 2) := by nlinarith
      _ = ∑ s : Fin (ℓ v), ∑ w', Q (.inr ⟨v, s⟩) w' * (η / 2) := by
          simp [← sum_mul, hQ.row_sum]
      _ ≤ ∑ s : Fin (ℓ v), ∑ w', Q (.inr ⟨v, s⟩) w' *
            ∑ t, Q (.inl v) (.inr t) * (1 - adj H (.inr t) w') := by
          gcongr with s _ w' _
          · exact hQ.nonneg _ _
          · exact hinner w'
      _ = sum4 G H Q {.inl v} (allLeaves ℓ) (leavesOf ℓ v) univ := h4.symm
      _ ≤ cutNorm (B G H Q) := sum4_le_cutNorm G H Q _ _ _ _
  · -- Case 2: `S' = {v} × L(w)` and `T' = U' × (W \ {w})`
    obtain ⟨w, hw⟩ := not_forall.mp hcase
    replace hw := lt_of_not_ge hw
    set U' := {x ∈ leavesOf ℓ v | Q x (.inl w) ≤ 1 / 2}
    have hU' : (ℓ v : ℝ) - 2 ≤ #U' := by
      have h1 := card_mul_le_of_lt_mass hQ (leavesOf ℓ v) {.inl w} (1 / 2)
      have h2 := card_filter_add_card_filter_not
        (s := leavesOf ℓ v) (fun x ↦ Q x (.inl w) ≤ 1 / 2)
      simp only [sum_singleton, card_singleton, Nat.cast_one, not_le, card_leavesOf] at h1 h2
      have h3 : (#U' : ℝ) + #{x ∈ leavesOf ℓ v | 1 / 2 < Q x (.inl w)} = ℓ v := by
        exact_mod_cast h2
      linarith
    have hrow (x) (hx : x ∈ U') : 1 / 2 ≤ ∑ w' ∈ univ.erase (.inl w), Q x w' := by
      rw [sum_erase_eq_sub (mem_univ _), hQ.row_sum]
      have := (mem_filter.mp hx).2
      linarith
    have h4 : sum4 G H Q {.inl v} (leavesOf ℓ w) U' (univ.erase (.inl w)) =
        (∑ s : Fin (ℓ w), Q (.inl v) (.inr ⟨w, s⟩)) *
          ∑ x ∈ U', ∑ w' ∈ univ.erase (.inl w), Q x w' := by
      rw [sum_mul]
      simp only [sum4, sum_singleton, sum_leavesOf, mul_sum]
      refine sum_congr rfl fun s _ ↦ sum_congr rfl fun x hx ↦ sum_congr rfl fun w' hw' ↦ ?_
      obtain ⟨t, rfl⟩ := mem_leavesOf.mp (mem_filter.mp hx).1
      have hw'' : w' ≠ .inl w := ne_of_mem_erase hw'
      simp [adj, addLeaves_adj_inr_iff, hw'']
    calc η * (M - 2) / 4 ≤ η / 2 * ((ℓ v - 2) * (1 / 2)) := by nlinarith
      _ ≤ η / 2 * (#U' * (1 / 2)) := by gcongr
      _ = η / 2 * ∑ _x ∈ U', (1 / 2 : ℝ) := by simp
      _ ≤ (∑ s : Fin (ℓ w), Q (.inl v) (.inr ⟨w, s⟩)) *
            ∑ x ∈ U', ∑ w' ∈ univ.erase (.inl w), Q x w' :=
          mul_le_mul hw.le (sum_le_sum hrow) (by positivity)
            (sum_nonneg fun s _ ↦ hQ.nonneg _ _)
      _ = sum4 G H Q {.inl v} (leavesOf ℓ w) U' (univ.erase (.inl w)) := h4.symm
      _ ≤ cutNorm (B G H Q) := sum4_le_cutNorm G H Q _ _ _ _

end Claims

end GsimOT.Hardness
