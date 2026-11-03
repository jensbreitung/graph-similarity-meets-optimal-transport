import GsimOT.Theorem18_OperatorNormHardness.Lemma19_AggregatedMatrix

/-!
# Corollary 54

Corollary 54 of the paper (p. 54, l. 1699–1701; proof l. 1702–1709).

If a column of `A^Q_{G,H}` has `k` entries of absolute value at least `ε`, then
`‖A^Q_{G,H}‖_p ≥ k^{b(p)} ε`, hence `‖B_p(G, H, Q)‖_p ≥ k^{b(p)} ε` by Lemma 53
(`rpow_bExp_mul_le_opNorm_Bpq`), and `‖B_p(G, H, Q)‖_p > c` whenever `k > (c/ε)^{1/b(p)}`
(`lt_opNorm_Bpq`). Here `b(p) = max(1/p, 1 - 1/p)`. The bound for `A^Q` is
`rpow_bExp_mul_le_opNorm` (`OperatorPNorms.lean`), combined with Lemma 53.
-/

open Finset Matrix WithLp
open scoped ENNReal

namespace GsimOT.Hardness

lemma half_le_bExp (p : ℝ≥0∞) : 1 / 2 ≤ bExp p := by
  unfold bExp
  rcases le_total p⁻¹.toReal (1 / 2) with h | h
  · exact le_max_of_le_right (by linarith)
  · exact le_max_of_le_left h

lemma bExp_le_one (p : ℝ≥0∞) [Fact (1 ≤ p)] : bExp p ≤ 1 :=
  max_le toReal_inv_le_one (by linarith [ENNReal.toReal_nonneg (a := p⁻¹)])

section Aggregated

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
  {Q : V → W → ℝ}

section Corollary20

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Corollary 54**, with Lemma 53: if column `v` of `A^Q_{G,H}` has `#K` entries of absolute
value at least `ε`, then `‖B_p(G, H, Q)‖_p ≥ #K^{b(p)} ε`. -/
theorem rpow_bExp_mul_le_opNorm_Bpq (hQ : IsDS Q) {v : V} {K : Finset V} {ε : ℝ} (hε : 0 ≤ ε)
    (hK : ∀ i ∈ K, ε ≤ |aggMatrix G H Q i v|) :
    ((#K : ℕ) : ℝ) ^ bExp p * ε ≤ opNorm p p (Bmat p p G H Q) :=
  (rpow_bExp_mul_le_opNorm (aggMatrix_isSymm G H Q) hε hK).trans (opNorm_aggMatrix_le G H hQ)

/-- **Corollary 54**, second part: if `#K > (c/ε)^{1/b(p)}`, then `‖B_p(G, H, Q)‖_p > c`. -/
theorem lt_opNorm_Bpq (hQ : IsDS Q) {v : V} {K : Finset V} {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hK : ∀ i ∈ K, ε ≤ |aggMatrix G H Q i v|) (hk : (c / ε) ^ (1 / bExp p) < #K) :
    c < opNorm p p (Bmat p p G H Q) := by
  have hb : 0 < bExp p := lt_of_lt_of_le (by norm_num) (half_le_bExp p)
  refine lt_of_lt_of_le ?_ (rpow_bExp_mul_le_opNorm_Bpq G H hQ hε.le hK)
  have h1 : c / ε < ((#K : ℕ) : ℝ) ^ bExp p := by
    calc c / ε = ((c / ε) ^ (1 / bExp p)) ^ bExp p := by
          rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hb.ne', Real.rpow_one]
      _ < _ := Real.rpow_lt_rpow (by positivity) hk hb
  calc c = c / ε * ε := by field_simp
    _ < ((#K : ℕ) : ℝ) ^ bExp p * ε := by gcongr

end Corollary20

end Aggregated

end GsimOT.Hardness
