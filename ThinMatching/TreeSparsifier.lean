/-
# Tree-cut sparsifiers

[HOG26], Definition 2.1 and Theorem 2.2 (Räcke–Shah [RS14]).

A weighted tree `T = (𝒱, ℰ, y)` with `V ⊆ 𝒱` (Steiner nodes allowed) is represented as a rooted
tree on a finite type `N` via a parent function; the tree edges are `{v, parent v}` for `v ≠ root`,
with weight `y v`.  (Every tree can be rooted, so this is no loss of generality.)  The inclusion
`V ⊆ 𝒱` is an embedding `e : V ↪ N`.

* `RootedTree N`             : a rooted tree on `N`.
* `subtree T v`              : the vertices whose path to the root passes through `v`.
* `treeCutWeight T y S'`     : `y(δ_T(S'))` for `S' ⊆ 𝒱`.
* `lambdaT T y e S`          : `λ_T(S)`, the minimum of `y(δ_T(S'))` over cuts `S'` of `T` that
                                project to `(S, V - S)`, i.e. `S' ∩ V ∈ {S, V - S}`.
* `IsTreeCutSparsifier q x T y e` : `x(δ(S)) ≤ λ_T(S) ≤ q x(δ(S))` for all `S ⊆ V`.
* `RackeShahTheorem`         : **[RS14] (Theorem 2.2 of [HOG26])** every weighted graph on `n`
  vertices has an `O(log n log log n)`-tree-cut sparsifier.  This cited result is **not** proved
  in [HOG26]; it is an explicit hypothesis here (no `axiom`).  The bound is written with an
  absolute constant as `C ln(2n) ln ln(4n)` (positive for all `n ≥ 1`).
-/
import ThinMatching.Basic

open Finset

namespace ThinMatching

/-- A rooted tree on `N`, given by a parent function in which every vertex reaches the root. -/
structure RootedTree (N : Type*) where
  root : N
  parent : N → N
  parent_root : parent root = root
  reach : ∀ v, ∃ k, parent^[k] v = root

variable {N : Type*} [Fintype N] [DecidableEq N]

open Classical in
/-- The subtree below `v`: all `u` with `v` among the ancestors of `u` (including `u = v`). -/
noncomputable def subtree (T : RootedTree N) (v : N) : Finset N :=
  univ.filter fun u => ∃ k, T.parent^[k] u = v

/-- `y(δ_T(S'))`: the weight of the tree edges `{v, parent v}` (`v ≠ root`) with exactly one
endpoint in `S'`. -/
def treeCutWeight (T : RootedTree N) (y : N → ℝ) (S' : Finset N) : ℝ :=
  ∑ v, if v ≠ T.root ∧ ¬ ((v ∈ S') ↔ (T.parent v ∈ S')) then y v else 0

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `λ_T(S) = min { y(δ_T(S')) : S' ⊆ 𝒱 projects to (S, V - S) }`. -/
noncomputable def lambdaT (T : RootedTree N) (y : N → ℝ) (e : V ↪ N) (S : Finset V) : ℝ :=
  ⨅ S' : {S' : Finset N // univ.filter (fun v => e v ∈ S') = S ∨
      univ.filter (fun v => e v ∈ S') = Sᶜ}, treeCutWeight T y S'.1

/-- `T` (with weights `y` and `V ↪ 𝒱`) is a `q`-tree-cut-sparsifier of `x` (Definition 2.1). -/
def IsTreeCutSparsifier (q : ℝ) (x : WGraph V) (T : RootedTree N) (y : N → ℝ) (e : V ↪ N) :
    Prop :=
  (∀ v, 0 ≤ y v) ∧ ∀ S : Finset V,
    cutWeight x S ≤ lambdaT T y e S ∧ lambdaT T y e S ≤ q * cutWeight x S

/-- **Theorem 2.2 ([RS14], Räcke–Shah)**, used as an explicit hypothesis: there is an absolute
constant `C > 0` such that every weighted graph on `n ≥ 1` vertices has a
`C ln(2n) ln ln(4n)`-tree-cut sparsifier. -/
def RackeShahTheorem : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (x : WGraph V),
    ∃ (N : Type) (_ : Fintype N) (_ : DecidableEq N) (T : RootedTree N) (y : N → ℝ) (e : V ↪ N),
      IsTreeCutSparsifier (C * Real.log (2 * Fintype.card V) *
        Real.log (Real.log (4 * Fintype.card V))) x T y e

end ThinMatching
