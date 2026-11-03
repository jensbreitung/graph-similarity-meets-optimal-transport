/-
# Loads of matchings on tree edges and discrepancies

[HOG26], Definitions 4.1, 4.2 and 4.4.

For a rooted tree `T` and the tree edge `f_v = {v, parent v}` (`v ≠ root`), the two sides of `f_v`
are `subtree T v` (the side `𝒱_s(f)` away from the root) and its complement (`𝒱_r(f)`).  The
unique path between two vertices of `T` uses `f_v` iff exactly one of them lies in `subtree T v`,
so the load of a matching on `f_v` counts the matching edges separated by `f_v`.

* `load T e M v`        : `load_M(f_v)` for a perfect matching `M` of `V` (`e : V → 𝒱`).
* `loadBip T eL eR π v` : `load_M(f_v)` for the bipartite perfect matching `M = {(l, π l)}`.
* `discBip T eL eR v`   : `Δ_bip(V ∩ subtree T v) = ||L ∩ ·| − |R ∩ ·||`.
* `discNonBip T e v`    : `Δ_non-bip(V ∩ subtree T v) = 1[|V ∩ ·| odd]`.

The paper uses `Δ(V_r(f))` (root side); since `|L| = |R|` resp. `|V|` is even, this equals `Δ` of
the subtree side `V_s(f)` used here.
-/
import ThinMatching.TreeSparsifier

open Finset

namespace ThinMatching

variable {N : Type*} [Fintype N] [DecidableEq N]

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `load_M(f_v)`: the number of matching edges `{u, M u}` whose tree path uses `f_v`. -/
noncomputable def load (T : RootedTree N) (e : V → N) (M : PerfectMatching V) (v : N) : ℕ :=
  #{u | e u ∈ subtree T v ∧ e (M.1 u) ∉ subtree T v}

/-- `Δ_non-bip(V ∩ subtree T v) = 1[|V ∩ subtree T v| is odd]`. -/
noncomputable def discNonBip (T : RootedTree N) (e : V → N) (v : N) : ℕ :=
  if Odd #{u | e u ∈ subtree T v} then 1 else 0

end General

section Bipartite

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- `load_M(f_v)` for the bipartite perfect matching `M = {(l, π l)}`. -/
noncomputable def loadBip (T : RootedTree N) (eL : L → N) (eR : R → N) (π : L ≃ R) (v : N) : ℕ :=
  #{l | ¬ ((eL l ∈ subtree T v) ↔ (eR (π l) ∈ subtree T v))}

/-- `Δ_bip(V ∩ subtree T v) = ||L ∩ subtree T v| − |R ∩ subtree T v||`. -/
noncomputable def discBip (T : RootedTree N) (eL : L → N) (eR : R → N) (v : N) : ℕ :=
  Int.natAbs ((#{l | eL l ∈ subtree T v} : ℤ) - #{r | eR r ∈ subtree T v})

end Bipartite

end ThinMatching
