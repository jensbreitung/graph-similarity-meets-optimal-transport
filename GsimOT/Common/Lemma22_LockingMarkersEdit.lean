/-
# Lemma 22 for the edit distance

Paper, Appendix C, Lemma 22 (Locking Markers, pp. 20–21), for `♢ = ed`. The construction of `G'`
and `H'` (the clique `K` on `m` new vertices, joined to the markers in a staircase) and the case
`♢ = 1` are in `GsimOT.Common.Lemma22_LockingMarkers`.

1. Every bijection `π` of `V'` with `C_ed(π) < τ` (w.r.t. `(G', H')`) fixes every marker and
   satisfies `π(V) = V`.
2. If `Q ∈ DS(V, V)` with `Q(z_j, z_j) = 1` for all `j`, and `Q'` extends `Q` by the identity on
   `K`, then `C_ed(Q')` w.r.t. `(G', H')` equals `C_ed(Q)` w.r.t. `(G, H)`.

The paper proves both items for `♢ ∈ {ed, 1}` at once from the local costs (Eq. (16), p. 21,
l. 661).  Here the first item follows from the case `♢ = 1`, as `C₁(π) ≤ C_ed(π)`
(`costOneBij_le_costEditBij`), and the second is proved directly: the terms of `C_ed(Q')` that
involve `K` vanish.
-/
import GsimOT.Common.Lemma22_LockingMarkers
import GsimOT.Common.EditDistance

open Finset

namespace GsimOT

/-- `C₁(π) ≤ C_ed(π)`: every local cost `L_π(v, π v)` is at most their sum `C_ed(π)`. -/
lemma costOneBij_le_costEditBij {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}
    [DecidableRel H.Adj] (π : V ≃ W) : costOneBij G H π ≤ costEditBij G H π := by
  rw [costOneBij_le_iff π (costEditBij_nonneg π)]
  intro v
  rw [costEditBij_eq]
  exact single_le_sum (f := fun v => ∑ v', |adj G v v' - adj H (π v) (π v')|)
    (fun v _ => sum_nonneg fun v' _ => abs_nonneg _) (mem_univ v)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
variable {k : ℕ} {z : Fin k → V} {Δ τ δ : ℕ}

/-- **Lemma 22 (1)** for `♢ = ed`. Every bijection `π` of `V' = V ⊕ K` with `C_ed(π) < τ`
w.r.t. `(G', H')` fixes every marker and maps `V` into `V` (hence `π(V) = V`). -/
theorem lemma22_bij_edit (hz : Function.Injective z)
    (hmono : ∀ i j : Fin k, i ≤ j → deg G (z i) ≤ deg G (z j))
    (hΔG : ∀ v, deg G v ≤ Δ) (hΔH : ∀ v, deg H v ≤ Δ)
    (hδ : ∀ j, deg G (z j) ≤ deg H (z j) + δ ∧ deg H (z j) ≤ deg G (z j) + δ)
    (π : (V ⊕ Fin (lockSize k Δ τ δ)) ≃ (V ⊕ Fin (lockSize k Δ τ δ)))
    (hπ : costEditBij (lockGraph G z Δ τ δ) (lockGraph H z Δ τ δ) π < τ) :
    (∀ j, π (.inl (z j)) = .inl (z j)) ∧ (∀ v, ∃ v', π (.inl v) = .inl v') :=
  lemma22_bij hz hmono hΔG hΔH hδ π ((costOneBij_le_costEditBij π).trans_lt hπ)

/-- **Lemma 22 (2)** for `♢ = ed`. If `Q ∈ DS(V, V)` fixes all markers (`Q(z_j, z_j) = 1`) and
`Q'` extends `Q` by the identity on `K`, then `C_ed(Q')` w.r.t. `(G', H')` equals `C_ed(Q)`
w.r.t. `(G, H)`. -/
theorem lemma22_cost_edit {Q : V → V → ℝ} (hQ : IsDS Q) (hz1 : ∀ j, Q (z j) (z j) = 1) :
    costEdit (lockGraph G z Δ τ δ) (lockGraph H z Δ τ δ) (extendId Q) = costEdit G H Q := by
  -- a supported pair `(a, b)` has the same neighbours in `K`
  have hstair : ∀ a b (y : Fin (lockSize k Δ τ δ)),
      |(if stair z Δ τ δ a y then (1 : ℝ) else 0) - (if stair z Δ τ δ b y then 1 else 0)| *
        Q a b = 0 := by
    intro a b y
    by_cases hab : Q a b = 0
    · simp [hab]
    · simp [stair_iff_of_supp hQ hz1 hab y]
  -- split the sums over `V' = V ⊕ K`; the terms with `(v, w) ∈ V × V` and `(v', w') ∈ K × K`
  -- vanish by `hstair`, those with mixed pairs because `Q'` vanishes on `V × K` and `K × V`
  unfold costEdit disc
  simp only [Fintype.sum_sum_type, adj_lock_inl_inl, adj_lock_inl_inr, adj_lock_inr_inl,
    adj_lock_inr_inr, extendId_inl_inl, extendId_inl_inr, extendId_inr_inl, extendId_inr_inr,
    mul_zero, zero_mul, sum_const_zero, add_zero, zero_add, mul_ite, mul_one, sum_ite_eq,
    mem_univ, ite_true, hstair]
  -- the terms with `(v, w) ∈ K × K` vanish as well
  rw [add_eq_left]
  refine sum_eq_zero fun y _ => sum_eq_zero fun y' _ => ?_
  by_cases hy : y = y'
  · subst hy
    simp only [ite_true, hstair, sum_const_zero, sub_self, abs_zero, zero_add]
  · simp [hy]

end GsimOT
