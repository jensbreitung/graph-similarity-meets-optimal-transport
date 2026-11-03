import GsimOT.Common.MatrixNorms

/-!
# Attaching leaves

The reductions of Theorems 17 and 18 (App. G, p. 54, l. 1714–1715, and p. 57, l. 1832–1834)
attach `ℓ b` new leaves to every vertex `b` of a base graph `G'`. The resulting graph
`addLeaves G' ℓ` has vertex type `B ⊕ Σ b, Fin (ℓ b)`: the base vertex `b` is `inl b` and the
leaves of `b` are `inr ⟨b, t⟩`.

Partial sums `mass Q S T = Q(S, T)` of doubly stochastic matrices, which the proofs about these
graphs use, are in `GsimOT.Common.DoublyStochastic`.
-/

open Finset

namespace GsimOT.Hardness

/-! ### The graph -/

section AddLeaves

variable {B : Type*} (G' : SimpleGraph B) (ℓ : B → ℕ)

/-- The adjacency relation of `addLeaves G' ℓ`. -/
def addLeavesAdj : B ⊕ (Σ b, Fin (ℓ b)) → B ⊕ (Σ b, Fin (ℓ b)) → Prop
  | .inl b, .inl b' => G'.Adj b b'
  | .inl b, .inr t => t.1 = b
  | .inr t, .inl b => t.1 = b
  | .inr _, .inr _ => False

/-- `G'` with `ℓ b` leaves attached to every vertex `b`. -/
def addLeaves : SimpleGraph (B ⊕ Σ b, Fin (ℓ b)) where
  Adj := addLeavesAdj G' ℓ
  symm := ⟨fun u v h ↦ by
    cases u <;> cases v <;> first | exact G'.adj_symm h | exact h⟩
  loopless := ⟨fun u h ↦ by
    cases u
    · exact G'.irrefl h
    · exact h⟩

instance [DecidableEq B] [DecidableRel G'.Adj] : DecidableRel (addLeaves G' ℓ).Adj
  | .inl b, .inl b' => inferInstanceAs (Decidable (G'.Adj b b'))
  | .inl b, .inr t => inferInstanceAs (Decidable (t.1 = b))
  | .inr t, .inl b => inferInstanceAs (Decidable (t.1 = b))
  | .inr _, .inr _ => inferInstanceAs (Decidable False)

variable {G' ℓ}

@[simp] lemma addLeaves_adj_inl_inl {b b' : B} :
    (addLeaves G' ℓ).Adj (.inl b) (.inl b') ↔ G'.Adj b b' := Iff.rfl

@[simp] lemma addLeaves_adj_inl_inr {b : B} {t : Σ b, Fin (ℓ b)} :
    (addLeaves G' ℓ).Adj (.inl b) (.inr t) ↔ t.1 = b := Iff.rfl

@[simp] lemma addLeaves_adj_inr_inl {b : B} {t : Σ b, Fin (ℓ b)} :
    (addLeaves G' ℓ).Adj (.inr t) (.inl b) ↔ t.1 = b := Iff.rfl

@[simp] lemma addLeaves_adj_inr_inr {t t' : Σ b, Fin (ℓ b)} :
    ¬(addLeaves G' ℓ).Adj (.inr t) (.inr t') := id

/-- A leaf is adjacent exactly to its base vertex. -/
lemma addLeaves_adj_inr_iff {t : Σ b, Fin (ℓ b)} {x : B ⊕ Σ b, Fin (ℓ b)} :
    (addLeaves G' ℓ).Adj (.inr t) x ↔ x = .inl t.1 := by
  cases x with
  | inl b => simp [eq_comm]
  | inr t' => simp

section Entries

variable [DecidableEq B] [DecidableRel G'.Adj]

@[simp] lemma adj_addLeaves_inl_inl (b b' : B) :
    adj (addLeaves G' ℓ) (.inl b) (.inl b') = adj G' b b' := by
  simp [adj]

@[simp] lemma adj_addLeaves_inl_inr (b : B) (t : Σ b, Fin (ℓ b)) :
    adj (addLeaves G' ℓ) (.inl b) (.inr t) = if t.1 = b then 1 else 0 := by
  simp [adj]

lemma adj_addLeaves_inr (t : Σ b, Fin (ℓ b)) (x : B ⊕ Σ b, Fin (ℓ b)) :
    adj (addLeaves G' ℓ) (.inr t) x = if x = .inl t.1 then 1 else 0 := by
  simp [adj, addLeaves_adj_inr_iff]

end Entries

/-- The leaves attached to `b`. -/
def leavesOf (ℓ : B → ℕ) (b : B) : Finset (B ⊕ Σ b, Fin (ℓ b)) :=
  (univ : Finset (Fin (ℓ b))).map ⟨fun t ↦ .inr ⟨b, t⟩, fun t t' h ↦ by simpa using h⟩

/-- All leaves. -/
def allLeaves [Fintype B] (ℓ : B → ℕ) : Finset (B ⊕ Σ b, Fin (ℓ b)) :=
  (univ : Finset (Σ b, Fin (ℓ b))).map Function.Embedding.inr

/-- The base vertices. -/
def baseSet [Fintype B] (ℓ : B → ℕ) : Finset (B ⊕ Σ b, Fin (ℓ b)) :=
  (univ : Finset B).map Function.Embedding.inl

lemma sum_leavesOf {M : Type*} [AddCommMonoid M] (b : B) (f : B ⊕ (Σ b, Fin (ℓ b)) → M) :
    ∑ x ∈ leavesOf ℓ b, f x = ∑ t : Fin (ℓ b), f (.inr ⟨b, t⟩) := sum_map _ _ _

lemma sum_allLeaves [Fintype B] {M : Type*} [AddCommMonoid M] (f : B ⊕ (Σ b, Fin (ℓ b)) → M) :
    ∑ x ∈ allLeaves ℓ, f x = ∑ t, f (.inr t) := sum_map _ _ _

lemma sum_baseSet [Fintype B] {M : Type*} [AddCommMonoid M] (f : B ⊕ (Σ b, Fin (ℓ b)) → M) :
    ∑ x ∈ baseSet ℓ, f x = ∑ b, f (.inl b) := sum_map _ _ _

@[simp] lemma card_leavesOf (b : B) : #(leavesOf ℓ b) = ℓ b := by simp [leavesOf]

lemma mem_leavesOf {b : B} {x : B ⊕ Σ b, Fin (ℓ b)} : x ∈ leavesOf ℓ b ↔ ∃ t, x = .inr ⟨b, t⟩ := by
  simp only [leavesOf, mem_map, mem_univ, true_and]
  exact ⟨fun ⟨t, ht⟩ ↦ ⟨t, ht.symm⟩, fun ⟨t, ht⟩ ↦ ⟨t, ht.symm⟩⟩

end AddLeaves

end GsimOT.Hardness
