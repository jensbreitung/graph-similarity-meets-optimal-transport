import GsimOT.Common.MatrixNorms

/-!
# Entry sums of `B(G, H, Q)` over products of sets

`sum4 G H Q S₁ S₂ T₁ T₂` is the entry sum of `B(G, H, Q)` over `(S₁ × S₂) × (T₁ × T₂)`, written as a
fourfold sum; its absolute value is a lower bound for `‖B(G, H, Q)‖_□`.
Used in Claims 58–61 (proof of Theorem 18).
-/

open Finset

namespace GsimOT.Hardness

section Sum4

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
  (Q : V → W → ℝ)

/-- The entry sum of `B(G, H, Q)` over `(S₁ × S₂) × (T₁ × T₂)`. -/
def sum4 (S₁ : Finset V) (S₂ : Finset W) (T₁ : Finset V) (T₂ : Finset W) : ℝ :=
  ∑ v ∈ S₁, ∑ w ∈ S₂, ∑ v' ∈ T₁, ∑ w' ∈ T₂,
    Q v w * (adj G v v' - adj H w w') * Q v' w'

lemma abs_sum4_le_cutNorm (S₁ : Finset V) (S₂ : Finset W) (T₁ : Finset V) (T₂ : Finset W) :
    |sum4 G H Q S₁ S₂ T₁ T₂| ≤ cutNorm (B G H Q) := by
  have := abs_sum_le_cutNorm (B G H Q) (S₁ ×ˢ S₂) (T₁ ×ˢ T₂)
  simpa only [sum4, sum_product, B, disc] using this

lemma sum4_le_cutNorm (S₁ : Finset V) (S₂ : Finset W) (T₁ : Finset V) (T₂ : Finset W) :
    sum4 G H Q S₁ S₂ T₁ T₂ ≤ cutNorm (B G H Q) :=
  (le_abs_self _).trans (abs_sum4_le_cutNorm G H Q _ _ _ _)

lemma neg_sum4_le_cutNorm (S₁ : Finset V) (S₂ : Finset W) (T₁ : Finset V) (T₂ : Finset W) :
    -sum4 G H Q S₁ S₂ T₁ T₂ ≤ cutNorm (B G H Q) :=
  (neg_le_abs _).trans (abs_sum4_le_cutNorm G H Q _ _ _ _)

end Sum4

end GsimOT.Hardness
