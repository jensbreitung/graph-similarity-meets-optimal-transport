import GsimOT.Theorem22_CutHardness.ProductSums
import GsimOT.Common.Leaves

/-!
# Claim 59

Claim 59 of the proof of Theorem 18 (p. 59, l. 1883–1884; proof pp. 59–60, l. 1885–1905).

If a base vertex `v` sends mass `τ` to each of two distinct base vertices, then
`‖B(G, H, Q)‖_□ ≥ τ(M - 2d)/2`, where `d` bounds the degrees in `H'` (`claim57`).
-/

open Finset

namespace GsimOT.Hardness

section Claims

variable {β : Type*} [Fintype β] [DecidableEq β] {G' H' : SimpleGraph β} [DecidableRel G'.Adj]
  [DecidableRel H'.Adj] {ℓ : β → ℕ} {Q : (β ⊕ Σ b, Fin (ℓ b)) → (β ⊕ Σ b, Fin (ℓ b)) → ℝ}

local notation "G" => addLeaves G' ℓ
local notation "H" => addLeaves H' ℓ

/-- **Claim 59.** If the base vertex `v` sends mass `τ` to each of two distinct base vertices
`w, w'`, then `‖B(G, H, Q)‖_□ ≥ τ(M - 2d)/2`, where every base vertex has at least `M` leaves
and `d` bounds the degrees in `H'`. -/
lemma claim57 (hQ : IsDS Q) {M d : ℕ} (hM : ∀ b, M ≤ ℓ b) (hd : ∀ b, #{x | H'.Adj x b} ≤ d)
    {v w w' : β} (hww' : w ≠ w') {τ : ℝ} (hτ : 0 ≤ τ) (hvw : τ ≤ Q (.inl v) (.inl w))
    (hvw' : τ ≤ Q (.inl v) (.inl w')) : τ * (M - 2 * d) / 2 ≤ cutNorm (B G H Q) := by
  -- the common neighbours of `w` and `w'` in `H`; they are base vertices
  set I : Finset (β ⊕ Σ b, Fin (ℓ b)) := {x | (H).Adj x (.inl w) ∧ (H).Adj x (.inl w')}
  have hI : #I ≤ d := by
    calc #I ≤ #(({x | H'.Adj x w} : Finset β).map Function.Embedding.inl) := by
          refine card_le_card fun x hx ↦ ?_
          simp only [I, mem_filter, mem_univ, true_and] at hx
          cases x with
          | inl b => simpa using hx.1
          | inr t =>
            simp only [addLeaves_adj_inr_inl] at hx
            exact absurd (hx.1.symm.trans hx.2) hww'
      _ = #{x | H'.Adj x w} := card_map _
      _ ≤ d := hd w
  set U' := {x ∈ leavesOf ℓ v | ∑ y ∈ I, Q x y ≤ 1 / 2}
  have hU' : (ℓ v : ℝ) - 2 * d ≤ #U' := by
    have h1 := card_mul_le_of_lt_mass hQ (leavesOf ℓ v) I (1 / 2)
    have h2 := card_filter_add_card_filter_not (s := leavesOf ℓ v)
      (fun x ↦ ∑ y ∈ I, Q x y ≤ 1 / 2)
    simp only [not_le, card_leavesOf] at h2
    have h3 : (#U' : ℝ) + #{x ∈ leavesOf ℓ v | 1 / 2 < ∑ y ∈ I, Q x y} = ℓ v := by
      exact_mod_cast h2
    have h4 : (#I : ℝ) ≤ d := by exact_mod_cast hI
    linarith
  -- for `z' ∉ I`, `v` sends mass `τ` to a vertex of `{w, w'}` that is not adjacent to `z'`
  have hcol (z' : β ⊕ Σ b, Fin (ℓ b)) (hz' : z' ∉ I) :
      τ ≤ ∑ z ∈ ({.inl w, .inl w'} : Finset _), Q (.inl v) z * (1 - adj H z z') := by
    rw [sum_pair (by simpa using hww')]
    simp only [I, mem_filter, mem_univ, true_and, not_and_or] at hz'
    have h0 := hQ.nonneg (.inl v) (.inl w)
    have h0' := hQ.nonneg (.inl v) (.inl w')
    have ha := adj_le_one (H) (.inl w) z'
    have ha' := adj_le_one (H) (.inl w') z'
    rcases hz' with hz | hz
    · have : adj H (.inl w) z' = 0 := by
        simp [adj, (H).adj_comm _ z', hz]
      nlinarith
    · have : adj H (.inl w') z' = 0 := by
        simp [adj, (H).adj_comm _ z', hz]
      nlinarith
  have h4 : sum4 G H Q {.inl v} {.inl w, .inl w'} U' (univ \ I) =
      ∑ x ∈ U', ∑ z' ∈ univ \ I, Q x z' *
        ∑ z ∈ ({.inl w, .inl w'} : Finset _), Q (.inl v) z * (1 - adj H z z') := by
    simp only [sum4, sum_singleton]
    rw [sum_comm]
    refine sum_congr rfl fun x hx ↦ ?_
    rw [sum_comm]
    refine sum_congr rfl fun z' _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun z _ ↦ ?_
    obtain ⟨t, rfl⟩ := mem_leavesOf.mp (mem_filter.mp hx).1
    simp only [adj_addLeaves_inl_inr, ite_true]
    ring
  calc τ * (M - 2 * d) / 2 ≤ τ * (#U' * (1 / 2)) := by
        have := hM v
        have : (M : ℝ) ≤ ℓ v := by exact_mod_cast hM v
        nlinarith
    _ = ∑ _x ∈ U', τ * (1 / 2) := by simp; ring
    _ ≤ ∑ x ∈ U', ∑ z' ∈ univ \ I, Q x z' * τ := by
        refine sum_le_sum fun x hx ↦ ?_
        rw [← sum_mul]
        have : 1 / 2 ≤ ∑ z' ∈ univ \ I, Q x z' := by
          rw [sum_sdiff_eq_sub (subset_univ I), hQ.row_sum]
          linarith [(mem_filter.mp hx).2]
        nlinarith
    _ ≤ ∑ x ∈ U', ∑ z' ∈ univ \ I, Q x z' *
          ∑ z ∈ ({.inl w, .inl w'} : Finset _), Q (.inl v) z * (1 - adj H z z') :=
        sum_le_sum fun x _ ↦ sum_le_sum fun z' hz' ↦
          mul_le_mul_of_nonneg_left (hcol z' (mem_sdiff.mp hz').2) (hQ.nonneg _ _)
    _ = sum4 G H Q {.inl v} {.inl w, .inl w'} U' (univ \ I) := h4.symm
    _ ≤ cutNorm (B G H Q) := sum4_le_cutNorm G H Q _ _ _ _

end Claims

end GsimOT.Hardness
