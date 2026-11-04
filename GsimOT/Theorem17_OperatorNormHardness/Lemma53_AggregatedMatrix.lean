import GsimOT.Theorem17_OperatorNormHardness.OperatorPNorms

/-!
# Lemma 53: the aggregated matrix

Lemma 53 of the paper (p. 53, l. 1676–1678; proof pp. 53–54, l. 1679–1697).

* `aggMatrix G H Q`: the aggregated matrix `A^Q_{G,H}` of Eq. (45) (p. 53, l. 1673–1674);
* `opNorm_aggMatrix_le` (**Lemma 53**): `‖A^Q_{G,H}‖_p ≤ ‖B_p(G, H, Q)‖_p` for `Q ∈ DS(V, W)`.

## Proof

The paper uses the duality of Lemma 19 (Appendix A, p. 14, l. 488). We factor `A^Q` through `B_p`
instead: with
`x̃(v,w) = Q(v,w)^{1/p} x(v)` we have `‖x̃‖_p ≤ ‖x‖_p` and
`(A^Q x)(v) = ∑_w Q(v,w)^{1-1/p} (B_p x̃)(v,w)`, and the right-hand side is a contraction of
`ℓ^p` by Jensen's inequality (`Q` has row sums `1`).
-/

open Finset Matrix WithLp
open scoped ENNReal

namespace GsimOT.Hardness

/-! ### Powers with `0 ^ 0 = 0` -/

lemma powZ_nonneg {q : ℝ} (hq : 0 ≤ q) (r : ℝ) : 0 ≤ powZ q r := by
  unfold powZ; split_ifs <;> positivity

lemma powZ_mul_powZ {q : ℝ} (hq : 0 ≤ q) (s : ℝ) : powZ q (1 - s) * powZ q s = q := by
  unfold powZ
  split_ifs with h
  · simp [h]
  · rw [← Real.rpow_add (lt_of_le_of_ne hq (Ne.symm h)), sub_add_cancel, Real.rpow_one]

lemma powZ_rpow_inv {q r : ℝ} (hq : 0 ≤ q) (hr : 0 < r) : powZ q (1 / r) ^ r = q := by
  unfold powZ
  split_ifs with h
  · simp [h, Real.zero_rpow hr.ne']
  · rw [← Real.rpow_mul hq, one_div_mul_cancel hr.ne', Real.rpow_one]

lemma abs_powZ_zero_le_one (q : ℝ) : |powZ q 0| ≤ 1 := by
  unfold powZ; split_ifs <;> simp

/-- Jensen's inequality behind Lemma 53: for a probability vector `q` and `b ≥ 0`,
`(∑_w q_w^{1-1/r} b_w)^r ≤ ∑_w b_w^r`. -/
lemma rpow_sum_powZ_mul_le {W : Type*} [Fintype W] (q b : W → ℝ) (hq : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hb : ∀ w, 0 ≤ b w) {r : ℝ} (hr : 1 ≤ r) :
    (∑ w, powZ (q w) (1 - 1 / r) * b w) ^ r ≤ ∑ w, b w ^ r := by
  have hr0 : 0 < r := by linarith
  set y : W → ℝ := fun w ↦ if q w = 0 then 0 else b w / q w ^ (1 / r)
  have hy0 (w : W) : 0 ≤ y w := by
    simp only [y]; split_ifs
    · rfl
    · have := hb w; have := hq w; positivity
  have hqy (w : W) : q w * y w = powZ (q w) (1 - 1 / r) * b w := by
    simp only [y, powZ]
    split_ifs with h
    · simp [h]
    · have hpos : 0 < q w := lt_of_le_of_ne (hq w) (Ne.symm h)
      rw [Real.rpow_sub hpos, Real.rpow_one]
      field_simp
  have hqyr (w : W) : q w * y w ^ r ≤ b w ^ r := by
    simp only [y]
    split_ifs with h
    · rw [h, zero_mul]
      exact Real.rpow_nonneg (hb w) r
    · have hpos : 0 < q w := lt_of_le_of_ne (hq w) (Ne.symm h)
      rw [Real.div_rpow (hb w) (by positivity), ← Real.rpow_mul hpos.le,
        one_div_mul_cancel hr0.ne', Real.rpow_one]
      field_simp
      rfl
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow (s := univ) q y (fun w _ ↦ hq w) hq1
    (fun w _ ↦ hy0 w) hr
  simp_rw [hqy] at hJ
  exact hJ.trans (sum_le_sum fun w _ ↦ hqyr w)

/-! ### The aggregated matrix and Lemma 53 -/

section Aggregated

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
  {Q : V → W → ℝ}

/-- The aggregated matrix `A^Q_{G,H}` of Eq. (45):
`A^Q(v, v') = ∑_{w,w'} Q(v,w) D((v,w),(v',w')) Q(v',w')`. -/
def aggMatrix (Q : V → W → ℝ) : Matrix V V ℝ :=
  fun v v' ↦ ∑ w, ∑ w', Q v w * disc G H v w v' w' * Q v' w'

lemma aggMatrix_isSymm (Q : V → W → ℝ) : (aggMatrix G H Q).IsSymm := by
  refine Matrix.IsSymm.ext fun v v' ↦ ?_
  simp only [aggMatrix, disc]
  rw [sum_comm]
  refine sum_congr rfl fun w _ ↦ sum_congr rfl fun w' _ ↦ ?_
  rw [adj_symm G v' v, adj_symm H w' w]
  ring

/-- **Lemma 53.** `‖A^Q_{G,H}‖_p ≤ ‖B_p(G, H, Q)‖_p` for every `Q ∈ DS(V, W)`. -/
theorem opNorm_aggMatrix_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hQ : IsDS Q) :
    opNorm p p (aggMatrix G H Q) ≤ opNorm p p (Bmat p p G H Q) := by
  refine opNorm_le_of_forall (opNorm_nonneg _ _ _) fun x ↦ ?_
  set s := p⁻¹.toReal
  set xt : V × W → ℝ := fun y ↦ powZ (Q y.1 y.2) s * x y.1
  set z := Bmat p p G H Q *ᵥ xt
  -- `A^Q x` is the `Q`-average of `B_p x̃`
  have hL (v : V) : (aggMatrix G H Q *ᵥ x) v = ∑ w, powZ (Q v w) (1 - s) * z (v, w) := by
    have hz (w : W) : z (v, w) =
        powZ (Q v w) s * ∑ y : V × W, disc G H v w y.1 y.2 * Q y.1 y.2 * x y.1 := by
      simp only [z, xt, Matrix.mulVec, dotProduct, Bmat, mul_sum]
      refine sum_congr rfl fun y _ ↦ ?_
      have := powZ_mul_powZ (hQ.nonneg y.1 y.2) s
      calc powZ (Q v w) s * disc G H v w y.1 y.2 * powZ (Q y.1 y.2) (1 - s) *
            (powZ (Q y.1 y.2) s * x y.1)
          = powZ (Q v w) s * disc G H v w y.1 y.2 *
              (powZ (Q y.1 y.2) (1 - s) * powZ (Q y.1 y.2) s) * x y.1 := by ring
        _ = _ := by rw [this]; ring
    calc (aggMatrix G H Q *ᵥ x) v
        = ∑ w, ∑ v', ∑ w', Q v w * disc G H v w v' w' * Q v' w' * x v' := by
          simp only [Matrix.mulVec, dotProduct, aggMatrix, sum_mul]
          rw [sum_comm]
      _ = ∑ w, powZ (Q v w) (1 - s) * z (v, w) := by
          refine sum_congr rfl fun w _ ↦ ?_
          rw [hz, ← mul_assoc, powZ_mul_powZ (hQ.nonneg v w), mul_sum, Fintype.sum_prod_type]
          exact sum_congr rfl fun v' _ ↦ sum_congr rfl fun w' _ ↦ by ring
  -- `‖x̃‖_p ≤ ‖x‖_p` and averaging is a contraction
  have hxt : ‖toLp p xt‖ ≤ ‖toLp p x‖ := by
    by_cases hp : p = ∞
    · subst hp
      refine norm_toLp_top_le (norm_nonneg _) fun y ↦ ?_
      have hs : s = 0 := by simp [s]
      simp only [xt, hs, abs_mul]
      calc |powZ (Q y.1 y.2) 0| * |x y.1| ≤ 1 * |x y.1| := by
            gcongr; exact abs_powZ_zero_le_one _
        _ ≤ ‖toLp ⊤ x‖ := by rw [one_mul]; exact abs_le_norm_toLp x y.1
    · have hr0 := toReal_pos' hp
      have hs : s = 1 / p.toReal := toReal_inv_eq p
      refine norm_toLp_le_norm_toLp hp (le_of_eq ?_)
      simp only [xt, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), Fintype.sum_prod_type]
      refine sum_congr rfl fun v _ ↦ ?_
      rw [← sum_mul]
      have : ∑ w, |powZ (Q v w) s| ^ p.toReal = 1 := by
        rw [← hQ.row_sum v]
        refine sum_congr rfl fun w _ ↦ ?_
        rw [abs_of_nonneg (powZ_nonneg (hQ.nonneg v w) s), hs,
          powZ_rpow_inv (hQ.nonneg v w) hr0]
      rw [this, one_mul]
  have hcontr : ‖toLp p (aggMatrix G H Q *ᵥ x)‖ ≤ ‖toLp p z‖ := by
    by_cases hp : p = ∞
    · subst hp
      refine norm_toLp_top_le (norm_nonneg _) fun v ↦ ?_
      have hs : s = 0 := by simp [s]
      rw [hL, hs, sub_zero]
      calc |∑ w, powZ (Q v w) 1 * z (v, w)| ≤ ∑ w, Q v w * |z (v, w)| := by
            refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun w _ ↦ ?_))
            rw [powZ_one, abs_mul, abs_of_nonneg (hQ.nonneg v w)]
        _ ≤ ∑ w, Q v w * ‖toLp ⊤ z‖ := by
            gcongr with w
            · exact hQ.nonneg v w
            · exact abs_le_norm_toLp z (v, w)
        _ = ‖toLp ⊤ z‖ := by rw [← sum_mul, hQ.row_sum, one_mul]
    · have hr := one_le_toReal hp
      have hr0 := toReal_pos' hp
      have hs : s = 1 / p.toReal := toReal_inv_eq p
      refine norm_toLp_le_norm_toLp hp ?_
      rw [Fintype.sum_prod_type]
      refine sum_le_sum fun v _ ↦ ?_
      rw [hL]
      calc |∑ w, powZ (Q v w) (1 - s) * z (v, w)| ^ p.toReal
          ≤ (∑ w, powZ (Q v w) (1 - 1 / p.toReal) * |z (v, w)|) ^ p.toReal := by
            rw [← hs]
            refine Real.rpow_le_rpow (abs_nonneg _) ((abs_sum_le_sum_abs _ _).trans
              (le_of_eq (sum_congr rfl fun w _ ↦ ?_))) hr0.le
            rw [abs_mul, abs_of_nonneg (powZ_nonneg (hQ.nonneg v w) _)]
        _ ≤ ∑ w, |z (v, w)| ^ p.toReal :=
            rpow_sum_powZ_mul_le (Q v) (fun w ↦ |z (v, w)|) (hQ.nonneg v) (hQ.row_sum v)
              (fun w ↦ abs_nonneg _) hr
  calc ‖toLp p (aggMatrix G H Q *ᵥ x)‖ ≤ ‖toLp p z‖ := hcontr
    _ ≤ opNorm p p (Bmat p p G H Q) * ‖toLp p xt‖ := norm_mulVec_le_opNorm _ _
    _ ≤ opNorm p p (Bmat p p G H Q) * ‖toLp p x‖ := by gcongr; exact opNorm_nonneg _ _ _

end Aggregated

end GsimOT.Hardness
