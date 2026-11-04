/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Common definitions: local edit distance and its optimal-transport relaxation

This file fixes the notions of Section 2 and Appendix A of
*Graph Similarity Meets Optimal Transport* (Breitung, Gervens, Grohe) that are needed for the
local edit distance `d₁`, i.e. the distance induced by the operator `1 → 1`-norm.

Throughout, `G` is a graph on `V` and `H` a graph on `W`, both finite.

* `adj G v v'`        : the entry `A_G(v, v')` of the adjacency matrix (as a real number).
* `disc G H v w v' w'`: the discrepancy `D_{G,H}(v, w, v', w') = A_G(v,v') - A_H(w,w')` (Eq. (6), p. 14).
* `IsDS Q`            : `Q ∈ DS(V, W)`, i.e. `Q` is doubly stochastic.
* `localCost G H Q v w` : the local cost `L_Q(v, w)` (Section 2, p. 5, l. 187–188).
* `costOne G H Q`     : `C₁(Q) = max_{(v,w) ∈ supp Q} L_Q(v,w)` (Section 2, p. 5, l. 188; Eq. (7)).
* `costOneBij G H π`  : `C₁(π) = C₁(P_π)` for a bijection `π : V ≃ W`.
* `dOne G H`          : `d₁(G, H) = min_π C₁(π)`.
* `dOTOne G H`        : `d₁^OT(G, H) = min_{Q ∈ DS(V,W)} C₁(Q)` (we use the infimum; see below).
* `deltaOne`, `deltaOTOne` : the normalised versions `δ₁ = n⁻¹ d₁`, `δ₁^OT = n⁻¹ d₁^OT`
  (normalisation by `n^{-κ}`, `κ₁ = 1`).

The paper takes minima; the minimum over the finitely many bijections is attained trivially and we
take the infimum over `DS(V, W)` for `d₁^OT`.  All results are stated for the infimum, which
coincides with the paper's minimum since the minimum is attained (Appendix A, pp. 14–15, l. 503–510;
not needed for `d₁^OT` and not formalised for it; see `GsimOT.Common.Attainment` for the operator
norms).
-/
import Mathlib

open Finset

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-! ## Graphs and adjacency matrices -/

/-- The adjacency matrix `A_G ∈ {0,1}^{V×V}` of a simple graph, with real entries. -/
def adj (G : SimpleGraph V) [DecidableRel G.Adj] (v v' : V) : ℝ :=
  if G.Adj v v' then 1 else 0

/-- The degree of a vertex, `deg_G(v) = |N_G(v)|`, as a natural number. -/
def deg (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  #{v' | G.Adj v v'}

section Graph

variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma adj_nonneg (v v' : V) : 0 ≤ adj G v v' := by unfold adj; split_ifs <;> norm_num

lemma adj_le_one (v v' : V) : adj G v v' ≤ 1 := by unfold adj; split_ifs <;> norm_num

lemma adj_symm (v v' : V) : adj G v v' = adj G v' v := by
  unfold adj; simp [G.adj_comm]

lemma adj_self (v : V) : adj G v v = 0 := by simp [adj]

lemma adj_eq_zero_or_one (v v' : V) : adj G v v' = 0 ∨ adj G v v' = 1 := by
  unfold adj; split_ifs <;> simp

lemma abs_adj_sub_adj_le_one {W : Type*} (H : SimpleGraph W) [DecidableRel H.Adj]
    (v v' : V) (w w' : W) : |adj G v v' - adj H w w'| ≤ 1 := by
  unfold adj; split_ifs <;> norm_num

/-- The degree is the row sum of the adjacency matrix. -/
lemma sum_adj_eq_deg (v : V) : ∑ v', adj G v v' = (deg G v : ℝ) := by
  unfold adj deg
  rw [Finset.sum_boole]

end Graph

/-! ## The discrepancy matrix -/

/-- The discrepancy matrix `D_{G,H}(v, w, v', w') := A_G(v, v') - A_H(w, w')` (Eq. (6)). -/
def disc (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (v : V) (w : W) (v' : V) (w' : W) : ℝ :=
  adj G v v' - adj H w w'

/-! ## Doubly stochastic matrices -/

/-- `Q ∈ DS(V, W)`: nonnegative entries, all row and column sums equal to `1`. -/
structure IsDS (Q : V → W → ℝ) : Prop where
  nonneg : ∀ v w, 0 ≤ Q v w
  row_sum : ∀ v, ∑ w, Q v w = 1
  col_sum : ∀ w, ∑ v, Q v w = 1

/-- The permutation matrix `P_π ∈ Perm(V, W)` of a bijection `π`. -/
def permMat (π : V ≃ W) (v : V) (w : W) : ℝ := if π v = w then 1 else 0

lemma permMat_isDS (π : V ≃ W) : IsDS (permMat π) where
  nonneg v w := by unfold permMat; split_ifs <;> norm_num
  row_sum v := by simp [permMat]
  col_sum w := by
    simp only [permMat]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : ({v | π v = w} : Finset V) = {π.symm w} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact (Equiv.eq_symm_apply π).symm
    simp [this]

lemma permMat_ne_zero_iff (π : V ≃ W) (v : V) (w : W) : permMat π v w ≠ 0 ↔ π v = w := by
  simp [permMat]

/-- Sum over `V × W` against a permutation matrix collapses to a sum over `V`. -/
lemma sum_mul_permMat (π : V ≃ W) (f : V → W → ℝ) :
    ∑ v', ∑ w', f v' w' * permMat π v' w' = ∑ v', f v' (π v') := by
  refine Finset.sum_congr rfl fun v' _ => ?_
  simp [permMat]

lemma IsDS.le_one {Q : V → W → ℝ} (hQ : IsDS Q) (v : V) (w : W) : Q v w ≤ 1 := by
  rw [← hQ.row_sum v]
  exact Finset.single_le_sum (fun w _ => hQ.nonneg v w) (Finset.mem_univ w)

/-- The total mass of a doubly stochastic matrix is `|V|`. -/
lemma IsDS.sum_sum {Q : V → W → ℝ} (hQ : IsDS Q) :
    ∑ v, ∑ w, Q v w = Fintype.card V := by
  simp [hQ.row_sum]

/-! ## Local costs and the cost `C₁` -/

section Cost

variable (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The local cost of a pair `(v, w) ∈ V × W` under `Q` (Section 2, p. 5):
`L_Q(v, w) := ∑_{(v',w') ∈ V × W} |D(v, w, v', w')| Q(v', w')`. -/
def localCost (Q : V → W → ℝ) (v : V) (w : W) : ℝ :=
  ∑ v', ∑ w', |disc G H v w v' w'| * Q v' w'

/-- `C₁(Q) := max_{(v,w) ∈ supp(Q)} L_Q(v, w)` (Section 2, p. 5, and Eq. (7)).
We use the (conditionally complete) supremum over the support; it is `0` if the support is
empty. -/
noncomputable def costOne (Q : V → W → ℝ) : ℝ :=
  ⨆ p : {p : V × W // Q p.1 p.2 ≠ 0}, localCost G H Q p.1.1 p.1.2

/-- `C₁(π) := C₁(P_π) = ‖A_G^π - A_H‖₁` for a bijection `π`. -/
noncomputable def costOneBij (π : V ≃ W) : ℝ := costOne G H (permMat π)

/-- The (unnormalised) local edit distance `d₁(G, H) = min_{π ∈ Bij(V,W)} C₁(π)`. -/
noncomputable def dOne : ℝ := ⨅ π : V ≃ W, costOneBij G H π

/-- The (unnormalised) optimal-transport local edit distance
`d₁^OT(G, H) = inf_{Q ∈ DS(V,W)} C₁(Q)`. -/
noncomputable def dOTOne : ℝ := ⨅ Q : {Q : V → W → ℝ // IsDS Q}, costOne G H Q.1

/-- Normalised local edit distance `δ₁(G, H) = n⁻¹ d₁(G, H)` with `n = |V|`. -/
noncomputable def deltaOne : ℝ := dOne G H / Fintype.card V

/-- Normalised optimal-transport local edit distance `δ₁^OT(G, H) = n⁻¹ d₁^OT(G, H)`. -/
noncomputable def deltaOTOne : ℝ := dOTOne G H / Fintype.card V

variable {G H}

lemma localCost_nonneg {Q : V → W → ℝ} (hQ : ∀ v w, 0 ≤ Q v w) (v : V) (w : W) :
    0 ≤ localCost G H Q v w :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (hQ _ _)

/-- Local costs are at most the total mass `n`. -/
lemma localCost_le_card {Q : V → W → ℝ} (hQ : IsDS Q) (v : V) (w : W) :
    localCost G H Q v w ≤ Fintype.card V := by
  rw [← hQ.sum_sum]
  refine Finset.sum_le_sum fun v' _ => Finset.sum_le_sum fun w' _ => ?_
  calc |disc G H v w v' w'| * Q v' w' ≤ 1 * Q v' w' :=
        mul_le_mul_of_nonneg_right (abs_adj_sub_adj_le_one G H _ _ _ _) (hQ.nonneg _ _)
    _ = Q v' w' := one_mul _

lemma bddAbove_localCost (Q : V → W → ℝ) :
    BddAbove (Set.range fun p : {p : V × W // Q p.1 p.2 ≠ 0} => localCost G H Q p.1.1 p.1.2) :=
  (Set.finite_range _).bddAbove

/-- Every supported local cost is at most `C₁(Q)`. -/
lemma localCost_le_costOne {Q : V → W → ℝ} {v : V} {w : W} (h : Q v w ≠ 0) :
    localCost G H Q v w ≤ costOne G H Q :=
  le_ciSup (f := fun p : {p : V × W // Q p.1 p.2 ≠ 0} => localCost G H Q p.1.1 p.1.2)
    (bddAbove_localCost Q) ⟨(v, w), h⟩

/-- `C₁(Q) ≤ c` as soon as all supported local costs are at most `c ≥ 0`. -/
lemma costOne_le {Q : V → W → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v w, Q v w ≠ 0 → localCost G H Q v w ≤ c) : costOne G H Q ≤ c :=
  Real.iSup_le (fun p => h p.1.1 p.1.2 p.2) hc

lemma costOne_nonneg {Q : V → W → ℝ} (hQ : ∀ v w, 0 ≤ Q v w) : 0 ≤ costOne G H Q :=
  Real.iSup_nonneg fun _ => localCost_nonneg hQ _ _

/-- `C₁(Q) ≤ c` iff all supported local costs are at most `c`, for `c ≥ 0`. -/
lemma costOne_le_iff {Q : V → W → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    costOne G H Q ≤ c ↔ ∀ v w, Q v w ≠ 0 → localCost G H Q v w ≤ c :=
  ⟨fun h _ _ hvw => (localCost_le_costOne hvw).trans h, costOne_le hc⟩

lemma costOne_le_card {Q : V → W → ℝ} (hQ : IsDS Q) : costOne G H Q ≤ Fintype.card V :=
  costOne_le (Nat.cast_nonneg _) fun v w _ => localCost_le_card hQ v w

/-! ### Local costs of bijections -/

/-- For a bijection, `L_{P_π}(v, w) = ∑_{v'} |A_G(v, v') - A_H(w, π(v'))|`. -/
lemma localCost_permMat (π : V ≃ W) (v : V) (w : W) :
    localCost G H (permMat π) v w = ∑ v', |adj G v v' - adj H w (π v')| := by
  unfold localCost
  rw [sum_mul_permMat π (fun v' w' => |disc G H v w v' w'|)]
  rfl

/-- The local cost of `π` at `v`, i.e. `L_{P_π}(v, π(v)) = |π(N_G(v)) △ N_H(π(v))|`. -/
lemma localCost_permMat_apply (π : V ≃ W) (v : V) :
    localCost G H (permMat π) v (π v) = ∑ v', |adj G v v' - adj H (π v) (π v')| :=
  localCost_permMat π v (π v)

/-- `C₁(π) ≤ c` iff `L_π(v, π(v)) ≤ c` for all `v`, for `c ≥ 0`. -/
lemma costOneBij_le_iff (π : V ≃ W) {c : ℝ} (hc : 0 ≤ c) :
    costOneBij G H π ≤ c ↔ ∀ v, ∑ v', |adj G v v' - adj H (π v) (π v')| ≤ c := by
  unfold costOneBij
  rw [costOne_le_iff hc]
  constructor
  · intro h v
    rw [← localCost_permMat_apply]
    exact h v (π v) (by simp [permMat])
  · intro h v w hvw
    have : π v = w := (permMat_ne_zero_iff π v w).1 hvw
    subst this
    rw [localCost_permMat_apply]
    exact h v

lemma localCost_permMat_le_costOneBij (π : V ≃ W) (v : V) :
    ∑ v', |adj G v v' - adj H (π v) (π v')| ≤ costOneBij G H π := by
  rw [← localCost_permMat_apply]
  exact localCost_le_costOne (by simp [permMat])

lemma costOneBij_nonneg (π : V ≃ W) : 0 ≤ costOneBij G H π :=
  costOne_nonneg (permMat_isDS π).nonneg

/-! ### Basic properties of `d₁` and `d₁^OT` -/

lemma dOne_le (π : V ≃ W) : dOne G H ≤ costOneBij G H π :=
  ciInf_le ⟨0, by rintro _ ⟨σ, rfl⟩; exact costOneBij_nonneg σ⟩ π

lemma le_dOne [Nonempty (V ≃ W)] {c : ℝ} (h : ∀ π : V ≃ W, c ≤ costOneBij G H π) :
    c ≤ dOne G H :=
  le_ciInf h

lemma dOne_nonneg : 0 ≤ dOne G H := by
  rcases isEmpty_or_nonempty (V ≃ W) with h | h
  · simp [dOne]
  · exact le_dOne fun π => costOneBij_nonneg π

lemma dOTOne_le {Q : V → W → ℝ} (hQ : IsDS Q) : dOTOne G H ≤ costOne G H Q :=
  ciInf_le (f := fun Q : {Q : V → W → ℝ // IsDS Q} => costOne G H Q.1)
    ⟨0, by rintro _ ⟨Q, rfl⟩; exact costOne_nonneg Q.2.nonneg⟩ ⟨Q, hQ⟩

lemma le_dOTOne [Nonempty (V ≃ W)] {c : ℝ} (h : ∀ Q, IsDS Q → c ≤ costOne G H Q) :
    c ≤ dOTOne G H := by
  obtain ⟨π⟩ := ‹Nonempty (V ≃ W)›
  have : Nonempty {Q : V → W → ℝ // IsDS Q} := ⟨⟨permMat π, permMat_isDS π⟩⟩
  exact le_ciInf fun Q => h Q.1 Q.2

lemma dOTOne_nonneg : 0 ≤ dOTOne G H := by
  rcases isEmpty_or_nonempty {Q : V → W → ℝ // IsDS Q} with h | h
  · simp [dOTOne]
  · exact le_ciInf fun Q => costOne_nonneg Q.2.nonneg

/-- `d₁^OT ≤ d₁`, since permutation matrices are doubly stochastic. -/
lemma dOTOne_le_dOne [Nonempty (V ≃ W)] : dOTOne G H ≤ dOne G H :=
  le_dOne fun π => dOTOne_le (permMat_isDS π)

lemma exists_lt_of_dOTOne_lt [Nonempty (V ≃ W)] {c : ℝ} (h : dOTOne G H < c) :
    ∃ Q, IsDS Q ∧ costOne G H Q < c := by
  obtain ⟨π⟩ := ‹Nonempty (V ≃ W)›
  have : Nonempty {Q : V → W → ℝ // IsDS Q} := ⟨⟨permMat π, permMat_isDS π⟩⟩
  obtain ⟨Q, hQ⟩ := exists_lt_of_ciInf_lt h
  exact ⟨Q.1, Q.2, hQ⟩

lemma nonempty_equiv_of_card_eq (h : Fintype.card V = Fintype.card W) : Nonempty (V ≃ W) :=
  ⟨Fintype.equivOfCardEq h⟩

end Cost

end GsimOT
