import GsimOT.Theorem18_CutHardness.ProductSums
import GsimOT.Common.Leaves

/-!
# Claim 60

Claim 60 of the proof of Theorem 18 (p. 60, l. 1913–1914; proof l. 1915–1932).

If `Q(vᵢ, wⱼ) ≥ 1 - ρ` for distinct base vertices, then
`‖B(G, H, Q)‖_□ ≥ (1 - ρ)(ℓⱼ - ℓᵢ - d)` (`claim60`) and
`‖B(G, H, Q)‖_□ ≥ (1 - ρ)(ℓᵢ - ℓⱼ - d)` (`claim60'`, reversing the roles of the graphs), where
`d` bounds the base degrees.
-/

open Finset

namespace GsimOT.Hardness

section Claims

variable {β : Type*} [Fintype β] [DecidableEq β] {G' H' : SimpleGraph β} [DecidableRel G'.Adj]
  [DecidableRel H'.Adj] {ℓ : β → ℕ} {Q : (β ⊕ Σ b, Fin (ℓ b)) → (β ⊕ Σ b, Fin (ℓ b)) → ℝ}

local notation "G" => addLeaves G' ℓ
local notation "H" => addLeaves H' ℓ

/-- In `addLeaves G' ℓ`, the base vertex `i` has at most `ℓ i + d` neighbours. -/
lemma card_adj_inl_le {d : ℕ} (hd : ∀ b, #{x | G'.Adj x b} ≤ d) (i : β) :
    #{x | (G).Adj (.inl i) x} ≤ ℓ i + d := by
  calc #{x | (G).Adj (.inl i) x}
      ≤ #(leavesOf ℓ i ∪ ({x | G'.Adj x i} : Finset β).map Function.Embedding.inl) := by
        refine card_le_card fun x hx ↦ ?_
        simp only [mem_filter, mem_univ, true_and] at hx
        cases x with
        | inl b => exact mem_union_right _ (by simpa [G'.adj_comm] using hx)
        | inr t =>
          obtain ⟨b, s⟩ := t
          simp only [addLeaves_adj_inl_inr] at hx
          subst hx
          exact mem_union_left _ (mem_leavesOf.mpr ⟨s, rfl⟩)
    _ ≤ #(leavesOf ℓ i) + #(({x | G'.Adj x i} : Finset β).map Function.Embedding.inl) :=
        card_union_le _ _
    _ ≤ ℓ i + d := by rw [card_leavesOf, card_map]; exact Nat.add_le_add_left (hd i) _

/-- **Claim 60** (for `vᵢ` mapped to `wⱼ` with `ℓᵢ < ℓⱼ`): with `S' = {(vᵢ, wⱼ)}` and
`T' = (V \ N(vᵢ)) × L(wⱼ)`, `‖B(G, H, Q)‖_□ ≥ Q(vᵢ, wⱼ)(ℓⱼ - ℓᵢ - d)`. -/
lemma claim60 (hQ : IsDS Q) {d : ℕ} (hd : ∀ b, #{x | G'.Adj x b} ≤ d) {i j : β} {ρ : ℝ}
    (hρ : ρ ≤ 1) (hij : 1 - ρ ≤ Q (.inl i) (.inl j)) :
    (1 - ρ) * ((ℓ j : ℝ) - ℓ i - d) ≤ cutNorm (B G H Q) := by
  set R : Finset (β ⊕ Σ b, Fin (ℓ b)) := {x | ¬(G).Adj (.inl i) x}
  set N : Finset (β ⊕ Σ b, Fin (ℓ b)) := {x | (G).Adj (.inl i) x}
  have h4 : sum4 G H Q {.inl i} {.inl j} R (leavesOf ℓ j) =
      -(Q (.inl i) (.inl j) * mass Q R (leavesOf ℓ j)) := by
    simp only [sum4, sum_singleton, mass, mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun x hx ↦ sum_congr rfl fun y hy ↦ ?_
    obtain ⟨t, rfl⟩ := mem_leavesOf.mp hy
    have hx' : ¬(G).Adj (.inl i) x := (mem_filter.mp hx).2
    simp [adj, hx']
  have hmass : (ℓ j : ℝ) - ℓ i - d ≤ mass Q R (leavesOf ℓ j) := by
    have h1 := mass_univ_left hQ (leavesOf ℓ j)
    have h2 : mass Q univ (leavesOf ℓ j) = mass Q R (leavesOf ℓ j) + mass Q N (leavesOf ℓ j) := by
      unfold mass
      rw [← sum_filter_not_add_sum_filter univ fun x ↦ (G).Adj (.inl i) x]
    have h3 := mass_le_card_left hQ N (leavesOf ℓ j)
    have h5 : (#N : ℝ) ≤ ℓ i + d := by exact_mod_cast card_adj_inl_le hd i
    rw [card_leavesOf] at h1
    linarith
  have hm0 := mass_nonneg hQ R (leavesOf ℓ j)
  calc (1 - ρ) * ((ℓ j : ℝ) - ℓ i - d) ≤ (1 - ρ) * mass Q R (leavesOf ℓ j) :=
        mul_le_mul_of_nonneg_left hmass (by linarith)
    _ ≤ Q (.inl i) (.inl j) * mass Q R (leavesOf ℓ j) := mul_le_mul_of_nonneg_right hij hm0
    _ = -sum4 G H Q {.inl i} {.inl j} R (leavesOf ℓ j) := by rw [h4, neg_neg]
    _ ≤ cutNorm (B G H Q) := neg_sum4_le_cutNorm G H Q _ _ _ _

/-- **Claim 60** (for `vᵢ` mapped to `wⱼ` with `ℓᵢ > ℓⱼ`, reversing the roles of the graphs):
with `S' = {(vᵢ, wⱼ)}` and `T' = L(vᵢ) × (W \ N(wⱼ))`,
`‖B(G, H, Q)‖_□ ≥ Q(vᵢ, wⱼ)(ℓᵢ - ℓⱼ - d)`. -/
lemma claim60' (hQ : IsDS Q) {d : ℕ} (hd : ∀ b, #{x | H'.Adj x b} ≤ d) {i j : β} {ρ : ℝ}
    (hρ : ρ ≤ 1) (hij : 1 - ρ ≤ Q (.inl i) (.inl j)) :
    (1 - ρ) * ((ℓ i : ℝ) - ℓ j - d) ≤ cutNorm (B G H Q) := by
  set R : Finset (β ⊕ Σ b, Fin (ℓ b)) := {y | ¬(H).Adj (.inl j) y}
  set N : Finset (β ⊕ Σ b, Fin (ℓ b)) := {y | (H).Adj (.inl j) y}
  have h4 : sum4 G H Q {.inl i} {.inl j} (leavesOf ℓ i) R =
      Q (.inl i) (.inl j) * mass Q (leavesOf ℓ i) R := by
    simp only [sum4, sum_singleton, mass, mul_sum]
    refine sum_congr rfl fun x hx ↦ sum_congr rfl fun y hy ↦ ?_
    obtain ⟨t, rfl⟩ := mem_leavesOf.mp hx
    have hy' : ¬(H).Adj (.inl j) y := (mem_filter.mp hy).2
    simp [adj, hy']
  have hmass : (ℓ i : ℝ) - ℓ j - d ≤ mass Q (leavesOf ℓ i) R := by
    have h1 := mass_univ_right hQ (leavesOf ℓ i)
    have h2 : mass Q (leavesOf ℓ i) univ = mass Q (leavesOf ℓ i) R + mass Q (leavesOf ℓ i) N := by
      unfold mass
      rw [← sum_add_distrib]
      exact sum_congr rfl fun x _ ↦
        (sum_filter_not_add_sum_filter univ (fun y ↦ (H).Adj (.inl j) y) fun y ↦ Q x y).symm
    have h3 := mass_le_card_right hQ (leavesOf ℓ i) N
    have h5 : (#N : ℝ) ≤ ℓ j + d := by exact_mod_cast card_adj_inl_le hd j
    rw [card_leavesOf] at h1
    linarith
  have hm0 := mass_nonneg hQ (leavesOf ℓ i) R
  calc (1 - ρ) * ((ℓ i : ℝ) - ℓ j - d) ≤ (1 - ρ) * mass Q (leavesOf ℓ i) R :=
        mul_le_mul_of_nonneg_left hmass (by linarith)
    _ ≤ Q (.inl i) (.inl j) * mass Q (leavesOf ℓ i) R := mul_le_mul_of_nonneg_right hij hm0
    _ = sum4 G H Q {.inl i} {.inl j} (leavesOf ℓ i) R := h4.symm
    _ ≤ cutNorm (B G H Q) := sum4_le_cutNorm G H Q _ _ _ _

end Claims

end GsimOT.Hardness
