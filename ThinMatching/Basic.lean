/-
# Thin perfect matchings: basic notions

Formalisation of A. Haqi, S. Oveis Gharan, *On Thin Perfect Matchings up to Polylogarithmic
Factors*, arXiv:2606.01330 [HOG26], Sections 1 and 2.  This library is independent of the
`GsimOT` formalisation (it imports only Mathlib).

* `WGraph V`            : a weighted graph `G = (V, E, x)`: symmetric weights `x : V → V → ℝ≥0`,
                           zero on the diagonal; the edge set is the support of `x`.
* `cutWeight x S`       : `x(δ(S)) = ∑_{u ∈ S, v ∉ S} x(u, v)`.
* `PerfectMatching V`   : perfect matchings of the complete graph on `V`, as fixed-point-free
                           involutions `σ` (`v` is matched to `σ v`).
* `crossCount M S`      : `|M ∩ δ(S)|`.
* `IsThin α x M`        : `M` is `α`-thin w.r.t. `x`: `|M ∩ δ(S)| ≤ α x(δ(S))` for all `S ⊆ V`.
* `IsFracPM x`          : `x ∈ PM(G)`: `x` is a convex combination of perfect matchings (Section 1).
* Bipartite versions for `G = (L ∪ R, E, x)` with `x : L → R → ℝ` and perfect matchings
  `π : L ≃ R`: `bipCutWeight`, `bipCrossCount`, `IsThinBip`, `IsFracPMBip` (degree constraints;
  by Birkhoff–von Neumann this is the bipartite perfect matching polytope).

The paper quantifies thinness over nonempty `S ⊊ V`; for `S = ∅` and `S = V` both sides vanish,
so quantifying over all `S` is equivalent.
-/
import Mathlib

open Finset

namespace ThinMatching

/-- A weighted graph on `V`: symmetric nonnegative weights, zero on the diagonal. -/
structure WGraph (V : Type*) where
  w : V → V → ℝ
  nonneg : ∀ u v, 0 ≤ w u v
  symm : ∀ u v, w u v = w v u
  diag : ∀ v, w v v = 0

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `x(δ(S)) = ∑_{u ∈ S, v ∉ S} x(u, v)`. -/
def cutWeight (x : WGraph V) (S : Finset V) : ℝ := ∑ u ∈ S, ∑ v ∈ Sᶜ, x.w u v

/-- Perfect matchings of the complete graph on `V`, as fixed-point-free involutions. -/
def PerfectMatching (V : Type*) [Fintype V] [DecidableEq V] : Type _ :=
  {σ : Equiv.Perm V // ∀ v, σ (σ v) = v ∧ σ v ≠ v}

instance : Fintype (PerfectMatching V) := by unfold PerfectMatching; infer_instance

/-- `|M ∩ δ(S)|`: the number of matching edges with exactly one endpoint in `S`. -/
def crossCount (M : PerfectMatching V) (S : Finset V) : ℕ := #{v ∈ S | M.1 v ∉ S}

/-- `M` is `α`-thin w.r.t. `x`. -/
def IsThin (α : ℝ) (x : WGraph V) (M : PerfectMatching V) : Prop :=
  ∀ S : Finset V, (crossCount M S : ℝ) ≤ α * cutWeight x S

/-- `M ⊆ supp(x)`. -/
def InSupport (x : WGraph V) (M : PerfectMatching V) : Prop := ∀ v, 0 < x.w v (M.1 v)

/-- `x ∈ PM(G)`: a convex combination of (incidence vectors of) perfect matchings. -/
def IsFracPM (x : WGraph V) : Prop :=
  ∃ c : PerfectMatching V → ℝ, (∀ M, 0 ≤ c M) ∧ ∑ M, c M = 1 ∧
    ∀ u v, x.w u v = ∑ M, c M * (if M.1 u = v then 1 else 0)

end General

section Bipartite

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- `x(δ(S))` for `S = S_L ∪ S_R ⊆ L ∪ R` in a bipartite weighted graph `x : L → R → ℝ`. -/
def bipCutWeight (x : L → R → ℝ) (SL : Finset L) (SR : Finset R) : ℝ :=
  ∑ l, ∑ r, if ((l ∈ SL) ↔ (r ∈ SR)) then 0 else x l r

/-- `|M ∩ δ(S)|` for the perfect matching `M = {(l, π l)}` of `L ∪ R`. -/
def bipCrossCount (π : L ≃ R) (SL : Finset L) (SR : Finset R) : ℕ :=
  #{l | ¬ ((l ∈ SL) ↔ (π l ∈ SR))}

/-- The perfect matching `π : L ≃ R` is `α`-thin w.r.t. `x`. -/
def IsThinBip (α : ℝ) (x : L → R → ℝ) (π : L ≃ R) : Prop :=
  ∀ (SL : Finset L) (SR : Finset R), (bipCrossCount π SL SR : ℝ) ≤ α * bipCutWeight x SL SR

/-- `x` is a fractional perfect matching of the bipartite graph `(L ∪ R, supp x)`: nonnegative
with all degrees `x(δ(v)) = 1`. -/
structure IsFracPMBip (x : L → R → ℝ) : Prop where
  nonneg : ∀ l r, 0 ≤ x l r
  row_sum : ∀ l, ∑ r, x l r = 1
  col_sum : ∀ r, ∑ l, x l r = 1

/-- The bipartite weighted graph `G = (L ∪ R, E, x)` as a weighted graph on `L ⊕ R`. -/
def bipGraph (x : L → R → ℝ) (hx : ∀ l r, 0 ≤ x l r) : WGraph (L ⊕ R) where
  w a b := match a, b with
    | .inl l, .inr r => x l r
    | .inr r, .inl l => x l r
    | _, _ => 0
  nonneg a b := by rcases a with l | r <;> rcases b with l' | r' <;> simp [hx]
  symm a b := by rcases a with l | r <;> rcases b with l' | r' <;> rfl
  diag a := by rcases a with l | r <;> rfl

end Bipartite

end ThinMatching
