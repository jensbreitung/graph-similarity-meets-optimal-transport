/-
# Lemma 29: the reference bijection and integrality

Paper, Appendix D.2, Lemma 29 (p. 28, l. 872–873; proof l. 874–886), together with the
pseudometric `ρ_H` (l. 866) and Eq. (18) (p. 28, l. 869).

Throughout, `Q ∈ DS(V, W)` is a doubly stochastic matrix with all supported local costs at most
`L` (in the paper, l. 865–866, `Q` is optimal and `L = d₁^OT(G, H)`; the argument only uses the
bound on the local costs), and `σ : V ≃ W` is a bijection whose graph lies in `supp(Q)` (Eq. (18)).

Lemma 29 is used both in the proof of Theorem 9 (upper bound) and in the proof of Lemma 27
(lower bound construction of Proposition 8), so it lives in the common part of the development.
-/
import GsimOT.Common.Observation21_DegreeBound
import GsimOT.Common.Birkhoff

open Finset

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- The pseudometric `ρ_H(w, w') := |N_H(w) △ N_H(w')| = ∑_{w''} |A_H(w, w'') - A_H(w', w'')|`. -/
def rho (H : SimpleGraph W) [DecidableRel H.Adj] (w w' : W) : ℝ :=
  ∑ w'', |adj H w w'' - adj H w' w''|

lemma rho_nonneg (w w' : W) : 0 ≤ rho H w w' :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma rho_self (w : W) : rho H w w = 0 := by simp [rho]

lemma rho_comm (w w' : W) : rho H w w' = rho H w' w := by
  unfold rho; congr 1; ext; rw [abs_sub_comm]

lemma rho_triangle (w₁ w₂ w₃ : W) : rho H w₁ w₃ ≤ rho H w₁ w₂ + rho H w₂ w₃ := by
  unfold rho
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ => abs_sub_le _ _ _

/-- First part of the proof of Lemma 29:
`ρ_H(w, w') ≤ L_Q(v, w) + L_Q(v, w')` for all `v` (column sums plus triangle inequality). -/
theorem rho_le_localCost_add {Q : V → W → ℝ} (hQ : IsDS Q) (v : V) (w w' : W) :
    rho H w w' ≤ localCost G H Q v w + localCost G H Q v w' := by
  have hrho : rho H w w' = ∑ v', ∑ w'', Q v' w'' * |adj H w w'' - adj H w' w''| := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w'' _ => ?_
    rw [← Finset.sum_mul, hQ.col_sum, one_mul]
  rw [hrho, localCost, localCost, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v' _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w'' _ => ?_
  have h := abs_sub_le (adj H w w'') (adj G v v') (adj H w' w'')
  rw [abs_sub_comm (adj H w w'') (adj G v v')] at h
  have hq := hQ.nonneg v' w''
  unfold disc
  nlinarith [mul_le_mul_of_nonneg_left h hq]

/-- For every integer-valued sum of `{0,1}`-terms below `1`, all terms vanish. Used twice in the
integrality argument of Lemma 29. -/
private lemma abs_adj_sub_eq_zero_of_sum_lt_one {ι : Type*} [Fintype ι]
    {f : ι → ℝ} (hf : ∀ i, f i = 0 ∨ f i = 1) (hsum : ∑ i, f i < 1) (i : ι) : f i = 0 := by
  rcases hf i with h | h
  · exact h
  · exfalso
    have : f i ≤ ∑ j, f j :=
      Finset.single_le_sum (fun j _ => by rcases hf j with h | h <;> simp [h])
        (Finset.mem_univ i)
    linarith

private lemma abs_adj_sub_adj_cases {X Y : Type*} (G' : SimpleGraph X) [DecidableRel G'.Adj]
    (H' : SimpleGraph Y) [DecidableRel H'.Adj] (x x' : X) (y y' : Y) :
    |adj G' x x' - adj H' y y'| = 0 ∨ |adj G' x x' - adj H' y y'| = 1 := by
  unfold adj; split_ifs <;> simp

/-- `ρ_H(w, w') = deg(w) + deg(w') - 2 |N(w) ∩ N(w')|`; in particular `ρ_H(w, w')` is even
whenever `w` and `w'` have the same degree.  We record the consequence we need:
if `deg w = deg w'` and `ρ_H(w, w') < 2` then `ρ_H(w, w') = 0`. -/
lemma rho_eq_zero_of_deg_eq_of_lt_two {w w' : W} (hdeg : deg H w = deg H w')
    (hlt : rho H w w' < 2) : rho H w w' = 0 := by
  -- `|a - b| = a + b - 2ab` for `a, b ∈ {0, 1}`
  have key : ∀ w'', |adj H w w'' - adj H w' w''| =
      adj H w w'' + adj H w' w'' - 2 * (adj H w w'' * adj H w' w'') := by
    intro w''; unfold adj; split_ifs <;> norm_num
  set c : ℕ := #{w'' | H.Adj w w'' ∧ H.Adj w' w''} with hc
  have hcommon : ∑ w'', adj H w w'' * adj H w' w'' = (c : ℝ) := by
    rw [hc, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun w'' _ => ?_
    by_cases h1 : H.Adj w w'' <;> by_cases h2 : H.Adj w' w'' <;> simp [adj, h1, h2]
  have hrho : rho H w w' = 2 * ((deg H w : ℝ) - c) := by
    unfold rho
    simp_rw [key]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hcommon,
      sum_adj_eq_deg, sum_adj_eq_deg, hdeg]
    ring
  have hnn := rho_nonneg (H := H) w w'
  rw [hrho] at hlt hnn ⊢
  have h1 : (deg H w : ℝ) < c + 1 := by linarith
  have h2 : (c : ℝ) ≤ deg H w := by linarith
  have h1' : deg H w < c + 1 := by exact_mod_cast h1
  have h2' : c ≤ deg H w := by exact_mod_cast h2
  have : deg H w = c := by omega
  rw [this]; ring

section Lemma29

variable {Q : V → W → ℝ} {L : ℝ} {σ : V ≃ W}

/-- **Lemma 29, first statement.** If `Q(v, w) > 0`, then `ρ_H(σ(v), w) ≤ 2L`. -/
theorem lemma29_rho_le (hQ : IsDS Q) (hL : ∀ v w, Q v w ≠ 0 → localCost G H Q v w ≤ L)
    (hσ : ∀ v, Q v (σ v) ≠ 0) {v : V} {w : W} (hvw : Q v w ≠ 0) :
    rho H (σ v) w ≤ 2 * L := by
  have := rho_le_localCost_add (G := G) (H := H) hQ v (σ v) w
  have h1 := hL v (σ v) (hσ v)
  have h2 := hL v w hvw
  linarith

/-- **Lemma 29, second statement.** If `L < 1`, then `σ` is an isomorphism from `G` to `H`,
i.e. `A_G(v', v) = A_H(σ(v'), σ(v))` for all `v, v'`. -/
theorem lemma29_iso (hQ : IsDS Q) (hL : ∀ v w, Q v w ≠ 0 → localCost G H Q v w ≤ L)
    (hσ : ∀ v, Q v (σ v) ≠ 0) (hL1 : L < 1) (v' v : V) :
    adj G v' v = adj H (σ v') (σ v) := by
  -- By Observation 21, `deg_G(v) = deg_H(w)` for every supported pair.
  have hdeg : ∀ v w, Q v w ≠ 0 → deg G v = deg H w := by
    intro v w hvw
    have h := (observation21 (G := G) (H := H) hQ v w).trans (hL v w hvw)
    have hz : |((deg G v : ℤ) - deg H w : ℤ)| < 1 := by
      have : ((|((deg G v : ℤ) - deg H w)| : ℤ) : ℝ) < 1 := by push_cast; linarith
      exact_mod_cast this
    have := abs_lt.1 hz
    omega
  -- Hence `ρ_H(σ(v), w) = 0` on the support.
  have hrho0 : ∀ v w, Q v w ≠ 0 → ∀ x, adj H (σ v) x = adj H w x := by
    intro v w hvw x
    have hd : deg H (σ v) = deg H w := (hdeg v (σ v) (hσ v)).symm.trans (hdeg v w hvw)
    have hlt : rho H (σ v) w < 2 := by
      have := lemma29_rho_le hQ hL hσ hvw; linarith
    have h0 := rho_eq_zero_of_deg_eq_of_lt_two hd hlt
    unfold rho at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)).1 h0 x
      (Finset.mem_univ x)
    linarith [abs_eq_zero.1 this]
  -- Thus `L_Q(v', σ(v')) = ∑_v |A_G(v', v) - A_H(σ(v'), σ(v))|`, an integer below `1`.
  have hsum : localCost G H Q v' (σ v') = ∑ v, |adj G v' v - adj H (σ v') (σ v)| := by
    unfold localCost disc
    refine Finset.sum_congr rfl fun v _ => ?_
    have : ∀ w, |adj G v' v - adj H (σ v') w| * Q v w =
        |adj G v' v - adj H (σ v') (σ v)| * Q v w := by
      intro w
      by_cases hvw : Q v w = 0
      · simp [hvw]
      · rw [adj_symm H (σ v') w, ← hrho0 v w hvw (σ v'), adj_symm H (σ v) (σ v')]
    simp_rw [this, ← Finset.mul_sum, hQ.row_sum, mul_one]
  have hlt : ∑ v, |adj G v' v - adj H (σ v') (σ v)| < 1 := by
    rw [← hsum]; exact (hL v' (σ v') (hσ v')).trans_lt hL1
  have := abs_adj_sub_eq_zero_of_sum_lt_one
    (fun v => abs_adj_sub_adj_cases G H v' v (σ v') (σ v)) hlt v
  linarith [abs_eq_zero.1 this]

/-- **Lemma 29, consequence.** If some `Q ∈ DS(V, W)` has `C₁(Q) < 1`, then `G ≅ H`, i.e. there
is a bijection of cost `0`, and hence `d₁(G, H) = 0`. -/
theorem lemma29_dOne_eq_zero (hcard : Fintype.card V = Fintype.card W) (hQ : IsDS Q)
    (hC : costOne G H Q < 1) : dOne G H = 0 := by
  obtain ⟨σ, hσ⟩ := exists_bij_subset_supp hQ hcard
  have hL : ∀ v w, Q v w ≠ 0 → localCost G H Q v w ≤ costOne G H Q :=
    fun v w h => localCost_le_costOne h
  have hiso := lemma29_iso hQ hL hσ hC
  have hcost : costOneBij G H σ ≤ 0 := by
    rw [costOneBij_le_iff σ le_rfl]
    intro v
    simp [hiso]
  exact le_antisymm ((dOne_le σ).trans hcost) dOne_nonneg

/-- **Lemma 29, "in particular".** If `G` and `H` are not isomorphic (witnessed by `d₁ ≠ 0`), then
`d₁^OT(G, H) ≥ 1`. -/
theorem lemma29_one_le_dOTOne (hcard : Fintype.card V = Fintype.card W)
    (hne : dOne G H ≠ 0) : 1 ≤ dOTOne G H := by
  have := nonempty_equiv_of_card_eq hcard
  refine le_dOTOne fun Q hQ => ?_
  by_contra h
  exact hne (lemma29_dOne_eq_zero hcard hQ (not_le.1 h))

end Lemma29

end GsimOT
