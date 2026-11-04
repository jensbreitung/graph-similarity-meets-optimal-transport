/-
# Observation 21: the degree bound for local costs

Paper, Appendix C, Observation 21 (p. 20, l. 642–643): For all graphs `G, H` of the same order, all
`Q ∈ DS(V, W)` and `(v, w) ∈ V × W`,
`L_Q(v, w) ≥ |deg_G(v) - deg_H(w)|`.
-/
import GsimOT.Common.Basic

open Finset

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- **Observation 21** (p. 20, l. 642–643). `L_Q(v, w) ≥ |deg_G(v) - deg_H(w)|`.
The hypothesis that `G` and `H` have the same order is implicit in `Q ∈ DS(V, W)`.
The proof follows the paper (l. 644–646): triangle inequality, then use that all row and column
sums of `Q` equal `1`. -/
theorem observation21 {Q : V → W → ℝ} (hQ : IsDS Q) (v : V) (w : W) :
    |(deg G v : ℝ) - deg H w| ≤ localCost G H Q v w := by
  have h1 : ∑ v', ∑ w', disc G H v w v' w' * Q v' w' = (deg G v : ℝ) - deg H w := by
    simp only [disc, sub_mul, Finset.sum_sub_distrib]
    rw [← sum_adj_eq_deg, ← sum_adj_eq_deg]
    congr 1
    · simp [← Finset.mul_sum, hQ.row_sum]
    · rw [Finset.sum_comm]; simp [← Finset.mul_sum, hQ.col_sum]
  rw [← h1]
  calc |∑ v', ∑ w', disc G H v w v' w' * Q v' w'|
      ≤ ∑ v', |∑ w', disc G H v w v' w' * Q v' w'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v', ∑ w', |disc G H v w v' w' * Q v' w'| :=
        Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
    _ = localCost G H Q v w := by
        unfold localCost
        refine Finset.sum_congr rfl fun v' _ => Finset.sum_congr rfl fun w' _ => ?_
        rw [abs_mul, abs_of_nonneg (hQ.nonneg v' w')]

/-- Observation 21 for bijections: `L_π(v, π v) ≥ |deg_G(v) - deg_H(π v)|`. -/
theorem observation21_bij (π : V ≃ W) (v : V) :
    |(deg G v : ℝ) - deg H (π v)| ≤ ∑ v', |adj G v v' - adj H (π v) (π v')| := by
  rw [← localCost_permMat_apply]
  exact observation21 (permMat_isDS π) v (π v)

end GsimOT
