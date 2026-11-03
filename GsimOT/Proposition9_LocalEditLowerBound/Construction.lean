/-
# The graphs `G_r` and `H_r` of Proposition 8

Paper, App. D.1 (pp. 25–26, l. 792–818; see also Figure 2 on p. 8 and Figure 6 on p. 26).

Fix an even integer `r ≥ 2` and let `ℓ := r² + 2r`, `n_X := 1 + r(ℓ - 1)`, `n_M := 2r²`.
The core vertices are `X := {u} ∪ {v_{i,k} | i ∈ [r], k ∈ [ℓ-1]}` and the markers are
`M := C ∪ T ∪ B` with clock markers `c_{j,h}` (`j ∈ [r-1]`, `h ∈ [r]`), tags `t_{i,h}`
(`i, h ∈ [r]`) and bits `b_i` (`i ∈ [r]`).  The bipartite graph `G⁰_r` on `X ∪ M` has the edges

| core      | marker     | condition                                    |
|-----------|------------|----------------------------------------------|
| `v_{i,k}` | `c_{j,h}`  | `k ≥ j(r+1) + h`                             |
| `v_{i,k}` | `t_{i',h}` | `i = i'` and `h ≤ k < ℓ - r + h`             |
| `v_{i,k}` | `b_{i'}`   | `i = i'` and `⌊k/(r+1)⌋` is odd              |

`H⁰_r` is obtained from `G⁰_r` by joining `u` to all clock markers.  Finally `G_r, H_r` are
obtained from `G⁰_r, H⁰_r` by Lemma 22 with the markers enumerated non-decreasingly by their
degree in `G⁰_r`, `Δ := n_X`, `τ := r` and `δ := 1`.

Formalisation notes.
* Indices are 0-based in Lean: `Marker.clock j h` is `c_{j+1,h+1}`, `Marker.tag i h` is
  `t_{i+1,h+1}`, `Marker.bit i` is `b_{i+1}`, and `Core.v i k` is `v_{i+1,k+1}`.  Branch indices
  only matter up to equality.
* Adjacency of core vertices to markers is described by *patterns* (paper: `χ`).  We define the
  pattern `pat i t` of branch `i` at time `t ∈ [0, ℓ]` directly by the table above, so that
  `χ(v_{i,k}) = pat i k`, `χ_{G_r}(u) = pat i 0 = 0` and `χ_{H_r}(u) = pat i ℓ = 1_C`.
-/
import GsimOT.Common.Lemma27_LockingMarkers
import Mathlib.Data.Fin.Tuple.Sort

open Finset

namespace GsimOT.Prop9

/-- `ℓ := r² + 2r`. -/
def ell (r : ℕ) : ℕ := r * r + 2 * r

lemma ell_eq (r : ℕ) : ell r = r * (r + 1) + r := by unfold ell; ring

/-- Markers: clock markers `c_{j,h}`, tags `t_{i,h}`, bits `b_i`. -/
inductive Marker (r : ℕ) where
  | clock (j : Fin (r - 1)) (h : Fin r)
  | tag (i : Fin r) (h : Fin r)
  | bit (i : Fin r)
  deriving DecidableEq, Fintype

/-- Core vertices: the special vertex `u` and the branch vertices `v_{i,k}`. -/
inductive Core (r : ℕ) where
  | u
  | v (i : Fin r) (k : Fin (ell r - 1))
  deriving DecidableEq, Fintype

/-- The vertex set `X ∪ M` of `G⁰_r` and `H⁰_r`. -/
inductive Base (r : ℕ) where
  | core (x : Core r)
  | marker (z : Marker r)
  deriving DecidableEq, Fintype

variable {r : ℕ}

/-! ### Cardinalities -/

/-- `Marker r ≃ (Fin (r-1) × Fin r) ⊕ (Fin r × Fin r) ⊕ Fin r`. -/
def markerEquiv (r : ℕ) : Marker r ≃ (Fin (r - 1) × Fin r) ⊕ ((Fin r × Fin r) ⊕ Fin r) where
  toFun
    | .clock j h => .inl (j, h)
    | .tag i h => .inr (.inl (i, h))
    | .bit i => .inr (.inr i)
  invFun
    | .inl (j, h) => .clock j h
    | .inr (.inl (i, h)) => .tag i h
    | .inr (.inr i) => .bit i
  left_inv z := by cases z <;> rfl
  right_inv z := by rcases z with ⟨j, h⟩ | ⟨i, h⟩ | i <;> rfl

/-- `Core r ≃ Option (Fin r × Fin (ℓ - 1))`. -/
def coreEquiv (r : ℕ) : Core r ≃ Option (Fin r × Fin (ell r - 1)) where
  toFun
    | .u => none
    | .v i k => some (i, k)
  invFun
    | none => .u
    | some (i, k) => .v i k
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | ⟨i, k⟩ <;> rfl

/-- `Base r ≃ Core r ⊕ Marker r`. -/
def baseEquiv (r : ℕ) : Base r ≃ Core r ⊕ Marker r where
  toFun
    | .core x => .inl x
    | .marker z => .inr z
  invFun
    | .inl x => .core x
    | .inr z => .marker z
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

/-- `n_M = 2r²` (for `r ≥ 1`). -/
lemma card_marker (hr : 1 ≤ r) : Fintype.card (Marker r) = 2 * r * r := by
  rw [Fintype.card_congr (markerEquiv r)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  obtain ⟨r', rfl⟩ := Nat.exists_eq_add_of_le hr
  simp only [Nat.add_sub_cancel_left]; ring

/-- `n_X = 1 + r(ℓ - 1)`. -/
lemma card_core : Fintype.card (Core r) = 1 + r * (ell r - 1) := by
  rw [Fintype.card_congr (coreEquiv r)]
  simp [Fintype.card_option, Fintype.card_prod, Fintype.card_fin]; ring

lemma card_base : Fintype.card (Base r) = Fintype.card (Core r) + Fintype.card (Marker r) := by
  rw [Fintype.card_congr (baseEquiv r), Fintype.card_sum]

/-! ### Patterns -/

/-- The pattern of branch `i` at time `t`: which markers are adjacent to the branch vertex at time
`t` (the table of App. D.1, p. 26, l. 800, with `k` replaced by the time `t`). -/
def pat (r : ℕ) (i : Fin r) (t : ℕ) : Marker r → Bool
  | .clock j h => decide ((j.val + 1) * (r + 1) + (h.val + 1) ≤ t)
  | .tag i' h => decide (i' = i ∧ h.val + 1 ≤ t ∧ t < ell r - r + (h.val + 1))
  | .bit i' => decide (i' = i ∧ (t / (r + 1)) % 2 = 1)

/-- The indicator `1_C` of the clock markers. -/
def isClock : Marker r → Bool
  | .clock _ _ => true
  | _ => false

/-- The pattern `χ_{G_r}(x)` of a core vertex in `G_r`. -/
def chiG : Core r → Marker r → Bool
  | .u => fun _ => false
  | .v i k => pat r i (k.val + 1)

/-- The pattern `χ_{H_r}(x)` of a core vertex in `H_r`. -/
def chiH : Core r → Marker r → Bool
  | .u => isClock
  | .v i k => pat r i (k.val + 1)

lemma pat_zero (i : Fin r) : pat r i 0 = fun _ => false := by
  funext z; cases z <;> simp [pat]

/-- At time `ℓ` the pattern is `1_C` (here we use that `r` is even). -/
lemma pat_ell (hev : Even r) (i : Fin r) : pat r i (ell r) = isClock := by
  have hdiv : ell r / (r + 1) = r := by
    rw [ell_eq, Nat.div_eq_of_lt_le] <;> nlinarith
  funext z
  cases z with
  | clock j h =>
    simp only [pat, isClock, decide_eq_true_eq]
    have hj := j.isLt; have hh := h.isLt
    have : (j.val + 1) * (r + 1) ≤ (r - 1) * (r + 1) := Nat.mul_le_mul_right _ (by omega)
    have e : (r - 1) * (r + 1) + r ≤ ell r := by
      rw [ell_eq]; have : (r - 1) * (r + 1) ≤ r * (r + 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    omega
  | tag i' h =>
    have hh := h.isLt
    have : r ≤ ell r := by unfold ell; nlinarith
    simp only [pat, isClock, decide_eq_false_iff_not, not_and, not_lt]
    intro _ _; omega
  | bit i' =>
    simp only [pat, isClock, hdiv, decide_eq_false_iff_not, not_and]
    intro _; rw [Nat.even_iff.1 hev]; simp

lemma chiG_u : chiG (r := r) .u = fun _ => false := rfl
lemma chiH_u : chiH (r := r) .u = isClock := rfl

lemma chiG_eq_chiH_of_ne_u {x : Core r} (hx : x ≠ .u) : chiG x = chiH x := by
  cases x with
  | u => exact absurd rfl hx
  | v i k => rfl

/-! ### The base graphs `G⁰_r` and `H⁰_r` -/

/-- Adjacency relation of the bipartite graph on `X ∪ M` given by a pattern map `χ`. -/
def bipAdj (χ : Core r → Marker r → Bool) : Base r → Base r → Prop
  | .core x, .marker z => χ x z = true
  | .marker z, .core x => χ x z = true
  | _, _ => False

/-- The bipartite graph on `X ∪ M` in which core vertex `x` is adjacent to marker `z` iff
`χ x z`. -/
def bipGraph (χ : Core r → Marker r → Bool) : SimpleGraph (Base r) where
  Adj := bipAdj χ
  symm := ⟨by
    rintro (x | z) (x' | z') h <;> simp only [bipAdj] at h ⊢ <;> exact h⟩
  loopless := ⟨by
    rintro (x | z) h <;> simp only [bipAdj] at h⟩

instance (χ : Core r → Marker r → Bool) : DecidableRel (bipGraph χ).Adj := fun a b =>
  match a, b with
  | .core x, .marker z => inferInstanceAs (Decidable (χ x z = true))
  | .marker z, .core x => inferInstanceAs (Decidable (χ x z = true))
  | .core _, .core _ => inferInstanceAs (Decidable False)
  | .marker _, .marker _ => inferInstanceAs (Decidable False)

/-- `G⁰_r`. -/
abbrev G0 (r : ℕ) : SimpleGraph (Base r) := bipGraph chiG
/-- `H⁰_r`. -/
abbrev H0 (r : ℕ) : SimpleGraph (Base r) := bipGraph chiH

section adjLemmas

variable (χ : Core r → Marker r → Bool)

@[simp] lemma adj_bip_core_marker (x : Core r) (z : Marker r) :
    adj (bipGraph χ) (.core x) (.marker z) = if χ x z then 1 else 0 := by
  simp only [adj]; rfl

@[simp] lemma adj_bip_marker_core (x : Core r) (z : Marker r) :
    adj (bipGraph χ) (.marker z) (.core x) = if χ x z then 1 else 0 := by
  simp only [adj]; rfl

@[simp] lemma adj_bip_core_core (x y : Core r) :
    adj (bipGraph χ) (.core x) (.core y) = 0 := by
  simp only [adj]; rfl

@[simp] lemma adj_bip_marker_marker (z z' : Marker r) :
    adj (bipGraph χ) (.marker z) (.marker z') = 0 := by
  simp only [adj]; rfl

end adjLemmas

/-! ### Degrees and the application of Lemma 22 -/

/-- In a bipartite graph `X ∪ M`, a core vertex has degree at most `|M|` and a marker has degree
at most `|X|`. -/
lemma deg_bip_core_le (χ : Core r → Marker r → Bool) (x : Core r) :
    deg (bipGraph χ) (.core x) ≤ Fintype.card (Marker r) := by
  unfold deg
  rw [← Finset.card_univ (α := Marker r), ← Finset.card_map ⟨Base.marker, fun _ _ h => by
    cases h; rfl⟩]
  refine Finset.card_le_card fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  rcases b with x' | z
  · exact absurd hb (by simp [bipGraph, bipAdj])
  · simp only [Finset.mem_map, Finset.mem_univ, true_and]; exact ⟨z, rfl⟩

lemma deg_bip_marker_le (χ : Core r → Marker r → Bool) (z : Marker r) :
    deg (bipGraph χ) (.marker z) ≤ Fintype.card (Core r) := by
  unfold deg
  rw [← Finset.card_univ (α := Core r), ← Finset.card_map ⟨Base.core, fun _ _ h => by
    cases h; rfl⟩]
  refine Finset.card_le_card fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  rcases b with x | z'
  · simp only [Finset.mem_map, Finset.mem_univ, true_and]; exact ⟨x, rfl⟩
  · exact absurd hb (by simp [bipGraph, bipAdj])

/-- `n_M ≤ n_X`, so `Δ := n_X` bounds all degrees. -/
lemma card_marker_le_card_core (hr : 1 ≤ r) :
    Fintype.card (Marker r) ≤ Fintype.card (Core r) := by
  rw [card_marker hr, card_core]
  unfold ell
  have h1 : r * r + 2 * r - 1 = r * r + r + (r - 1) := by omega
  rw [h1]
  nlinarith

lemma deg_bip_le (hr : 1 ≤ r) (χ : Core r → Marker r → Bool) (a : Base r) :
    deg (bipGraph χ) a ≤ Fintype.card (Core r) := by
  rcases a with x | z
  · exact (deg_bip_core_le χ x).trans (card_marker_le_card_core hr)
  · exact deg_bip_marker_le χ z

/-- Splitting a sum over `X ∪ M`. -/
lemma sum_base (f : Base r → ℝ) : ∑ a, f a = ∑ x, f (.core x) + ∑ z, f (.marker z) := by
  rw [← Fintype.sum_equiv (baseEquiv r).symm _ f (fun _ => rfl), Fintype.sum_sum_type]; rfl

/-- Splitting a sum over the core `X = {u} ∪ {v_{i,k}}`. -/
lemma sum_core (f : Core r → ℝ) : ∑ x, f x = f .u + ∑ i, ∑ k, f (.v i k) := by
  rw [← Fintype.sum_equiv (coreEquiv r).symm _ f (fun _ => rfl), Fintype.sum_option,
    Fintype.sum_prod_type]; rfl

/-- The degree of a marker in `H⁰_r` exceeds that in `G⁰_r` by `1[z ∈ C]`. -/
lemma deg_H0_marker (z : Marker r) :
    deg (H0 r) (.marker z) = deg (G0 r) (.marker z) + if isClock z then 1 else 0 := by
  have h : (deg (H0 r) (.marker z) : ℝ) =
      deg (G0 r) (.marker z) + if isClock z then 1 else 0 := by
    rw [← sum_adj_eq_deg, ← sum_adj_eq_deg, sum_base, sum_base, sum_core, sum_core]
    simp only [adj_bip_marker_core, adj_bip_marker_marker, Finset.sum_const_zero, add_zero,
      chiG, chiH]
    simp only [Bool.false_eq_true, ite_false]
    rw [add_comm, zero_add]
    congr 1
  have : ((deg (H0 r) (.marker z) : ℕ) : ℝ) =
      ((deg (G0 r) (.marker z) + if isClock z then 1 else 0 : ℕ) : ℝ) := by
    rw [h]; push_cast; split_ifs <;> simp
  exact_mod_cast this

end GsimOT.Prop9
