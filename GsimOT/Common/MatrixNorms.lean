/-
# Matrix norms and optimal transport distances

The general objects of Section 2 and Appendix A of the paper, for the unnormalised distances, on
top of `GsimOT.Common.Basic` (`adj`, `disc`, `IsDS`, `localCost`, `costOne`):

* `B G H Q` and `Bmat p q G H Q`: the matrices `B(G, H, Q)` and `B_{p→q}(G, H, Q)` (Eqs. (1), (2)), indexed
  by `V × W` and built from the discrepancy `disc G H`;
* `entrywiseNorm`, `cutNorm`, `opNorm p q`: the norms `‖·‖_ed = ‖·‖_(1)`, `‖·‖_□` and
  `‖·‖_{p→q}` (Appendix A, p. 14, l. 476–481);
* `dOTCut`, `dOT p q`: the distances `d^OT_□` and `d^OT_{p→q}` (Section 2, p. 5, l. 184–187). Like
  `dOTOne` and `dOTEdit` they are infima over `DS(V, W)`; the paper defines them as minima.
* `costEdit_eq_entrywiseNorm_B`: `C_ed(Q) = ‖B(G, H, Q)‖_ed` for `Q ≥ 0`, so `dOTEdit` is
  `d^OT_ed` as defined in Section 1 (Eq. (1)) and Section 2.
* **Eq. (7)** (`opNorm_Bpq_one_one_eq_costOne`, `dOT_one_one_eq_dOTOne`): for `Q ∈ DS(V, W)`,
  `‖B_{1→1}(G, H, Q)‖_{1→1} = C₁(Q)`, the largest local cost on `supp(Q)` (Section 2, p. 5,
  l. 188–189); hence `d^OT_{1→1} = d₁^OT`. Eq. (7) (Appendix A, p. 14, l. 500–502) is the same
  identity for couplings `Q* ∈ DS*(V, W)`, inside the minimum defining `δ₁^OT`.

The paper puts `Q ∈ DS(V, W)` (not `Q/n`) into `B` for graphs of the same order (Section 2, p. 5,
l. 184–185); so do we.
-/
import GsimOT.Common.EditDistance
import GsimOT.Common.OTDistances
import GsimOT.Common.CutNorm

open Finset Matrix
open scoped ENNReal

namespace GsimOT

variable {V W X Y : Type*} [Fintype V] [Fintype W] [Fintype X] [Fintype Y]

/-! ### The matrices `B` and `B_{p→q}` (defined in `Common/OTDistances.lean`) -/

section Graphs

variable (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]

omit [Fintype V] [Fintype W] in
/-- For `p = q = 1`, column `(v',w')` of `B_{1→1}(G, H, Q)` is `Q(·) D(·, (v',w'))` if
`Q(v',w') ≠ 0` and vanishes otherwise. -/
lemma Bpq_one_one_apply (Q : V → W → ℝ) (x y : V × W) :
    Bmat 1 1 G H Q x y = if Q y.1 y.2 = 0 then 0 else Q x.1 x.2 * disc G H x.1 x.2 y.1 y.2 := by
  simp only [Bmat, inv_one, ENNReal.toReal_one, powZ_one, sub_self, powZ_zero]
  split_ifs <;> ring

end Graphs

/-! ### Norms -/

/-- The entrywise 1-norm `‖M‖_ed = ‖M‖_(1) = ∑ |M(x,y)|` (Appendix A, p. 14, l. 476–477). -/
def entrywiseNorm (M : Matrix X Y ℝ) : ℝ := ∑ x, ∑ y, |M x y|

/-! The cut norm `cutNorm` (`Common/CutNorm.lean`) and the operator norm `opNorm p q`
(`Common/OperatorNorm.lean`) are the shared definitions. -/

lemma entrywiseNorm_nonneg (M : Matrix X Y ℝ) : 0 ≤ entrywiseNorm M := by
  unfold entrywiseNorm; positivity

lemma abs_sum_le_cutNorm [DecidableEq X] [DecidableEq Y] (M : Matrix X Y ℝ) (S : Finset X)
    (T : Finset Y) : |∑ x ∈ S, ∑ y ∈ T, M x y| ≤ cutNorm M :=
  le_cutNorm M S T

section OpNorm

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [DecidableEq Y]

/-- `‖M x‖_q ≤ ‖M‖_{p→q} ‖x‖_p`. -/
lemma norm_mulVec_le_opNorm (M : Matrix X Y ℝ) (x : Y → ℝ) :
    ‖WithLp.toLp q (M *ᵥ x)‖ ≤ opNorm p q M * ‖WithLp.toLp p x‖ :=
  lpNorm_mulVec_le (Fact.out) (Fact.out) M x

lemma opNorm_le_of_forall {M : Matrix X Y ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : Y → ℝ, ‖WithLp.toLp q (M *ᵥ x)‖ ≤ C * ‖WithLp.toLp p x‖) : opNorm p q M ≤ C :=
  opNorm_le_of_bound (Fact.out) (Fact.out) M hC fun x hx =>
    (h x).trans (by
      have := mul_le_mul_of_nonneg_left (show lpNorm p x ≤ 1 from hx) hC
      simpa [lpNorm] using this)

end OpNorm

lemma norm_toLp_one (x : X → ℝ) : ‖WithLp.toLp 1 x‖ = ∑ i, |x i| := by
  simp [PiLp.norm_eq_of_L1, Real.norm_eq_abs]

/-- Every absolute column sum is at most `‖M‖_1 = ‖M‖_{1→1}` (the maximum absolute column sum,
Appendix A, p. 14, l. 480). -/
lemma sum_abs_le_opNorm_one [DecidableEq Y] (M : Matrix X Y ℝ) (c : Y) :
    ∑ r, |M r c| ≤ opNorm 1 1 M := by
  have h := norm_mulVec_le_opNorm (p := 1) (q := 1) M (Pi.single c 1)
  simpa [norm_toLp_one, Matrix.mulVec_single, Pi.single_apply] using h

/-- `‖M‖_{1→1}` is at most the maximum absolute column sum. -/
lemma opNorm_one_le [DecidableEq Y] {M : Matrix X Y ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c, ∑ r, |M r c| ≤ C) : opNorm 1 1 M ≤ C := by
  refine opNorm_le_of_forall hC fun x ↦ ?_
  rw [norm_toLp_one, norm_toLp_one]
  calc ∑ r, |(M *ᵥ x) r| ≤ ∑ r, ∑ c, |M r c| * |x c| := by
        gcongr with r
        exact (abs_sum_le_sum_abs _ _).trans (by simp [abs_mul])
    _ = ∑ c, (∑ r, |M r c|) * |x c| := by rw [sum_comm]; simp [sum_mul]
    _ ≤ ∑ c, C * |x c| := by gcongr with c; exact h c
    _ = C * ∑ c, |x c| := by rw [mul_sum]


/-! ### Optimal transport distances

`d^OT_□` is `dOTCut` (`Common/CutNorm.lean`) and `d^OT_{p→q}` is `dOT p q`
(`Common/OTDistances.lean`). -/

/-! ### `C_ed` and `C₁` in terms of `B` -/

section Costs

variable [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
  [DecidableRel G.Adj] [DecidableRel H.Adj] {Q : V → W → ℝ}

/-- `C_ed(Q) = ‖B(G, H, Q)‖_ed` for `Q ≥ 0` (Section 2), so `dOTEdit` is `d^OT_ed`. -/
lemma costEdit_eq_entrywiseNorm_B (hQ : ∀ v w, 0 ≤ Q v w) :
    costEdit G H Q = entrywiseNorm (B G H Q) := by
  unfold costEdit entrywiseNorm B
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun v _ ↦ sum_congr rfl fun w _ ↦ sum_congr rfl fun v' _ ↦
    sum_congr rfl fun w' _ ↦ ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (hQ v w), abs_of_nonneg (hQ v' w')]
  ring

/-- The local cost as a column sum: `L_Q(v, w) = ∑_{(v',w')} Q(v',w') |D(v',w',v,w)|`, by the
symmetry of `D`. -/
lemma localCost_eq_sum_col (v : V) (w : W) :
    localCost G H Q v w = ∑ x : V × W, Q x.1 x.2 * |disc G H x.1 x.2 v w| := by
  unfold localCost
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun v' _ ↦ sum_congr rfl fun w' _ ↦ ?_
  simp only [disc]
  rw [adj_symm G v' v, adj_symm H w' w, mul_comm]

/-- Column `(v', w')` of `B_{1→1}(G, H, Q)` has absolute sum `L_Q(v', w')` if `Q(v', w') ≠ 0`,
and `0` otherwise. -/
lemma sum_abs_Bpq_one_one (hQ : ∀ v w, 0 ≤ Q v w) (y : V × W) :
    ∑ x, |Bmat 1 1 G H Q x y| = if Q y.1 y.2 = 0 then 0 else localCost G H Q y.1 y.2 := by
  simp only [Bpq_one_one_apply]
  split_ifs with hy
  · simp
  · rw [localCost_eq_sum_col]
    exact sum_congr rfl fun x _ ↦ by rw [abs_mul, abs_of_nonneg (hQ _ _)]

/-- **Eq. (7)** (Appendix A, p. 14, l. 500–502; Section 2, p. 5, l. 188–189): for `Q ∈ DS(V, W)`,
`‖B_{1→1}(G, H, Q)‖_{1→1} = C₁(Q)`, the largest local cost on `supp(Q)`. -/
lemma opNorm_Bpq_one_one_eq_costOne (hQ : IsDS Q) :
    opNorm 1 1 (Bmat 1 1 G H Q) = costOne G H Q := by
  have : Fact ((1 : ENNReal) ≤ 1) := ⟨le_rfl⟩
  apply le_antisymm
  · refine opNorm_one_le (costOne_nonneg hQ.nonneg) fun y ↦ ?_
    rw [sum_abs_Bpq_one_one G H hQ.nonneg]
    split_ifs with hy
    · exact costOne_nonneg hQ.nonneg
    · exact localCost_le_costOne hy
  · refine costOne_le (opNorm_nonneg _ _ _) fun v w hvw ↦ ?_
    have := sum_abs_le_opNorm_one (Bmat 1 1 G H Q) (v, w)
    rwa [sum_abs_Bpq_one_one G H hQ.nonneg, ite_eq_right hvw] at this

/-- **Eq. (7)**: `d^OT_{1→1}(G, H) = d₁^OT(G, H)`. -/
lemma dOT_one_one_eq_dOTOne : dOT 1 1 G H = dOTOne G H :=
  iInf_congr fun Q ↦ opNorm_Bpq_one_one_eq_costOne G H Q.2

end Costs

end GsimOT
