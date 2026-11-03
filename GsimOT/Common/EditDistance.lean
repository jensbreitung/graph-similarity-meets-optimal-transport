/-
# Common definitions: the edit distance and its optimal-transport relaxation

Paper, Section 1 (p. 1, l. 13–14 and footnote 1; Eq. (1), p. 2), Section 2 (p. 5) and App. A
(pp. 14–15): the edit distance `d_ed`, i.e. the distance induced by the entrywise `1`-norm
`‖·‖_ed = ‖·‖_(1)`, and its relaxation `d^OT_ed`. As in `GsimOT.Common.Basic`, `G` is a graph on
`V` and `H` a graph on `W`, both finite.

* `costEdit G H Q`    : `C_ed(Q) = ‖B(G, H, Q)‖_ed`, i.e.
  `∑_{v,w,v',w'} |D(v,w,v',w')| Q(v,w) Q(v',w')` (Section 2, p. 5, l. 184–185, for
  `Q ∈ DS(V, W)`).
* `costEditBij G H π` : `C_ed(π) = C_ed(P_π) = ‖A_G^π - A_H‖_ed` (`costEditBij_eq`), twice the
  number of vertex pairs mismatched by `π` (p. 5, l. 190–192).
* `dEdit G H`         : `d_ed(G, H) = min_π C_ed(π)`, twice the edit distance (footnote 1, p. 1).
* `dOTEdit G H`       : `d^OT_ed(G, H) = min_{Q ∈ DS(V,W)} C_ed(Q)` (p. 5, l. 186–187); as for
  `dOTOne` we take the infimum, which is attained (`exists_dOTEdit_eq`). Proposition 5, Theorem 6
  and Theorem 15 use it.
* `deltaEdit`, `deltaOTEdit` : the normalised versions `δ_ed = n⁻² d_ed` and
  `δ^OT_ed = n⁻² d^OT_ed` (normalisation by `n^{-κ_ed} = 1/n²`: p. 1, l. 26–27; `κ_ed = 2` as on
  p. 57, l. 1824).
-/
import GsimOT.Common.DoublyStochastic

open Finset

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

section Cost

variable (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The edit cost `C_ed(Q) = ‖B(G, H, Q)‖_ed = ∑_{v,w,v',w'} |D(v,w,v',w')| Q(v,w) Q(v',w')`. -/
def costEdit (Q : V → W → ℝ) : ℝ :=
  ∑ v, ∑ w, ∑ v', ∑ w', |disc G H v w v' w'| * Q v w * Q v' w'

/-- `C_ed(π) = C_ed(P_π)` for a bijection `π : V ≃ W`. -/
def costEditBij (π : V ≃ W) : ℝ := costEdit G H (permMat π)

/-- `d_ed(G, H) = min_π C_ed(π)`. -/
noncomputable def dEdit : ℝ := ⨅ π : V ≃ W, costEditBij G H π

/-- `d^OT_ed(G, H) = min_{Q ∈ DS(V,W)} C_ed(Q)` (as an infimum). -/
noncomputable def dOTEdit : ℝ := ⨅ Q : {Q : V → W → ℝ // IsDS Q}, costEdit G H Q.1

/-- `δ_ed(G, H) = n⁻² d_ed(G, H)`. -/
noncomputable def deltaEdit : ℝ := dEdit G H / (Fintype.card V : ℝ) ^ 2

/-- `δ^OT_ed(G, H) = n⁻² d^OT_ed(G, H)`. -/
noncomputable def deltaOTEdit : ℝ := dOTEdit G H / (Fintype.card V : ℝ) ^ 2

variable {G H}

lemma costEdit_nonneg {Q : V → W → ℝ} (hQ : ∀ v w, 0 ≤ Q v w) : 0 ≤ costEdit G H Q :=
  sum_nonneg fun v _ => sum_nonneg fun w _ => sum_nonneg fun v' _ => sum_nonneg fun w' _ =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (hQ v w)) (hQ v' w')

/-- `C_ed(π) = ‖A_G^π - A_H‖_ed = ∑_{v,v'} |A_G(v,v') - A_H(π v, π v')|`. -/
lemma costEditBij_eq (π : V ≃ W) :
    costEditBij G H π = ∑ v, ∑ v', |adj G v v' - adj H (π v) (π v')| := by
  unfold costEditBij costEdit
  refine sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_eq_single (π v) fun w hw => by simp [permMat, Ne.symm hw]]
  refine sum_congr rfl fun v' _ => ?_
  rw [Fintype.sum_eq_single (π v') fun w' hw' => by simp [permMat, Ne.symm hw']]
  simp [permMat, disc]

lemma costEditBij_nonneg (π : V ≃ W) : 0 ≤ costEditBij G H π :=
  costEdit_nonneg (permMat_isDS π).nonneg

/-! ### Basic properties of `d_ed` and `d^OT_ed` -/

lemma dEdit_le (π : V ≃ W) : dEdit G H ≤ costEditBij G H π :=
  ciInf_le ⟨0, by rintro _ ⟨σ, rfl⟩; exact costEditBij_nonneg σ⟩ π

lemma le_dEdit [Nonempty (V ≃ W)] {c : ℝ} (h : ∀ π : V ≃ W, c ≤ costEditBij G H π) :
    c ≤ dEdit G H :=
  le_ciInf h

lemma dEdit_nonneg : 0 ≤ dEdit G H := by
  rcases isEmpty_or_nonempty (V ≃ W) with h | h
  · simp [dEdit]
  · exact le_dEdit fun π => costEditBij_nonneg π

lemma dOTEdit_le {Q : V → W → ℝ} (hQ : IsDS Q) : dOTEdit G H ≤ costEdit G H Q :=
  ciInf_le (f := fun Q : {Q : V → W → ℝ // IsDS Q} => costEdit G H Q.1)
    ⟨0, by rintro _ ⟨Q, rfl⟩; exact costEdit_nonneg Q.2.nonneg⟩ ⟨Q, hQ⟩

lemma le_dOTEdit [Nonempty (V ≃ W)] {c : ℝ} (h : ∀ Q, IsDS Q → c ≤ costEdit G H Q) :
    c ≤ dOTEdit G H := by
  obtain ⟨π⟩ := ‹Nonempty (V ≃ W)›
  have : Nonempty {Q : V → W → ℝ // IsDS Q} := ⟨⟨permMat π, permMat_isDS π⟩⟩
  exact le_ciInf fun Q => h Q.1 Q.2

lemma dOTEdit_nonneg : 0 ≤ dOTEdit G H := by
  rcases isEmpty_or_nonempty {Q : V → W → ℝ // IsDS Q} with h | h
  · simp [dOTEdit]
  · exact le_ciInf fun Q => costEdit_nonneg Q.2.nonneg

/-- `d^OT_ed ≤ d_ed`, since permutation matrices are doubly stochastic. -/
lemma dOTEdit_le_dEdit [Nonempty (V ≃ W)] : dOTEdit G H ≤ dEdit G H :=
  le_dEdit fun π => dOTEdit_le (permMat_isDS π)

/-! ### The infimum `d^OT_ed` is a minimum -/

/-- The infimum `d^OT_ed(G, H)` is attained, as the paper's minimum (App. A, pp. 14–15,
l. 503–510): some `Q ∈ DS(V, W)` has `C_ed(Q) = d^OT_ed(G, H)`. -/
lemma exists_dOTEdit_eq [Nonempty (V ≃ W)] : ∃ Q, IsDS Q ∧ costEdit G H Q = dOTEdit G H := by
  have hne : {Q : V → W → ℝ | IsDS Q}.Nonempty :=
    ⟨permMat (Classical.arbitrary (V ≃ W)), permMat_isDS _⟩
  have hcont : Continuous fun Q : V → W → ℝ => costEdit G H Q := by
    unfold costEdit
    fun_prop
  obtain ⟨Q, hQ, hmin⟩ := isCompact_setOf_isDS.exists_isMinOn hne hcont.continuousOn
  exact ⟨Q, hQ, le_antisymm (le_dOTEdit fun Q' hQ' => hmin hQ') (dOTEdit_le hQ)⟩

end Cost

end GsimOT
