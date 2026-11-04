/-
# The matrices `B`, `B_{p→q}` and the optimal transport distances

Paper, Section 1 (Fractional Alignments and Optimal Transport, pp. 2–3, Eqs. (1), (2)), Section 2
(p. 5) and Appendix A (pp. 14–15).

* `IsCoupling Q`      : `Q ∈ DS*(V, W)`, a fractional alignment (coupling of the uniform
                         distributions): nonnegative, row sums `1/|V|`, column sums `1/|W|`
                         (p. 2, l. 50–54; Appendix A, p. 14, l. 493–494).
* `powZ x a`          : `x^a` with the convention `0^a := 0` (in particular `0^0 = 0`, p. 3, l. 84;
                         Appendix A, p. 14, l. 500).
* `B G H Q`           : `B(G, H, Q)` with entries `Q(v,w) D(v,w,v',w') Q(v',w')` (edit and cut
                         distance; p. 2, l. 68–69).
* `Bmat p q G H Q`    : `B_{p→q}(G, H, Q)` with entries `Q(v,w)^{1/q} D(v,w,v',w') Q(v',w')^{1-1/p}`
                         (p. 3, l. 84–85; Appendix A, p. 14, l. 499).
* `deltaOTPQ p q G H` : `δ^OT_{p→q}(G, H) = min_{Q ∈ DS*(V,W)} ‖B_{p→q}(G,H,Q)‖_{p→q}`
                         (Eq. (2), p. 3).
* `dOT p q G H`       : `d^OT_{p→q}(G, H) = min_{Q ∈ DS(V,W)} ‖B_{p→q}(G,H,Q)‖_{p→q}`, the
                         minimum of the unnormalised cost `C_{p→q}` over `DS(V, W)` (Section 2,
                         p. 5, l. 184–187; graphs of the same order).

All minima are taken as infima; that they are attained (Appendix A, pp. 14–15, l. 503–510) is
proved in `GsimOT.Common.Attainment`.
-/
import GsimOT.Common.Basic
import GsimOT.Common.OperatorNorm
import GsimOT.Common.AlignedDistances

open Finset Matrix

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W]

/-- `Q ∈ DS*(V, W)`: a coupling of the uniform distributions on `V` and `W`. -/
structure IsCoupling (Q : V → W → ℝ) : Prop where
  nonneg : ∀ v w, 0 ≤ Q v w
  row_sum : ∀ v, ∑ w, Q v w = 1 / Fintype.card V
  col_sum : ∀ w, ∑ v, Q v w = 1 / Fintype.card W

/-- `x^a` with the convention `0^a = 0` for all `a` (so `0^0 = 0`, p. 3, l. 84). -/
noncomputable def powZ (x a : ℝ) : ℝ := if x = 0 then 0 else x ^ a

@[simp] lemma powZ_zero_left (r : ℝ) : powZ 0 r = 0 := by simp [powZ]

@[simp] lemma powZ_one (x : ℝ) : powZ x 1 = x := by
  unfold powZ; split_ifs with h <;> simp [h]

lemma powZ_zero (x : ℝ) : powZ x 0 = if x = 0 then 0 else 1 := by
  unfold powZ; split_ifs <;> simp

section Graphs

variable (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- `B(G, H, Q)` with entries `Q(v,w) D(v,w,v',w') Q(v',w')`; it defines the edit and the cut
distance. -/
def B (Q : V → W → ℝ) : Matrix (V × W) (V × W) ℝ :=
  fun x y ↦ Q x.1 x.2 * disc G H x.1 x.2 y.1 y.2 * Q y.1 y.2

end Graphs

section PQ

variable (p q : ENNReal) (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
  [DecidableRel H.Adj]

/-- The matrix `B_{p→q}(G, H, Q) ∈ ℝ^{(V×W)×(V×W)}` with entries
`Q(v,w)^{1/q} D(v,w,v',w') Q(v',w')^{1-1/p}` (convention `0^0 = 0`). -/
noncomputable def Bmat (Q : V → W → ℝ) : Matrix (V × W) (V × W) ℝ := fun a b =>
  powZ (Q a.1 a.2) q⁻¹.toReal * disc G H a.1 a.2 b.1 b.2 * powZ (Q b.1 b.2) (1 - p⁻¹.toReal)

/-- `δ^OT_{p→q}(G, H) = inf_{Q ∈ DS*(V,W)} ‖B_{p→q}(G, H, Q)‖_{p→q}` (Eq. (2)). -/
noncomputable def deltaOTPQ : ℝ :=
  ⨅ Q : {Q : V → W → ℝ // IsCoupling Q}, opNorm p q (Bmat p q G H Q.1)

/-- `d^OT_{p→q}(G, H) = inf_{Q ∈ DS(V,W)} ‖B_{p→q}(G, H, Q)‖_{p→q}` (Section 2, p. 5,
l. 184–187, unnormalised). -/
noncomputable def dOT : ℝ :=
  ⨅ Q : {Q : V → W → ℝ // IsDS Q}, opNorm p q (Bmat p q G H Q.1)

end PQ

/-! ### Normalised versus unnormalised OT distances -/

lemma powZ_mul_left {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    powZ (c * x) a = c ^ a * powZ x a := by
  unfold powZ
  by_cases h : x = 0
  · simp [h]
  · rw [ite_eq_right (mul_ne_zero hc.ne' h), ite_eq_right h, Real.mul_rpow hc.le hx]

/-- Positive homogeneity of the operator norm. -/
lemma opNorm_smul_of_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] {p q : ENNReal} (hp : 1 ≤ p)
    (hq : 1 ≤ q) {c : ℝ} (hc : 0 ≤ c) (M : Matrix ι κ ℝ) :
    opNorm p q (fun i j => c * M i j) = c * opNorm p q M := by
  have hmul : ∀ x : κ → ℝ, (fun i j => c * M i j : Matrix ι κ ℝ) *ᵥ x = c • (M *ᵥ x) := by
    intro x; funext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  apply le_antisymm
  · refine opNorm_le_of_bound hp hq _ (mul_nonneg hc (opNorm_nonneg _ _ _)) fun x hx => ?_
    rw [hmul, lpNorm_smul hq, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left
      ((lpNorm_mulVec_le hp hq M x).trans (by nlinarith [opNorm_nonneg p q M])) hc
  · obtain ⟨x, hx, hxM⟩ := exists_lpNorm_mulVec_eq_opNorm hp hq M
    have := lpNorm_mulVec_le hp hq (fun i j => c * M i j) x
    rw [hmul, lpNorm_smul hq, abs_of_nonneg hc, hxM] at this
    calc c * opNorm p q M ≤ opNorm p q (fun i j => c * M i j) * lpNorm p x := this
      _ ≤ opNorm p q (fun i j => c * M i j) := by
          nlinarith [opNorm_nonneg p q (fun i j => c * M i j), lpNorm_nonneg p x]

section Relation

variable [DecidableEq V] [DecidableEq W] (p q : ENNReal) (G : SimpleGraph V) [DecidableRel G.Adj]
  (H : SimpleGraph W) [DecidableRel H.Adj]

/-- For a coupling `Q*` and `n = |V| = |W|`: `B_{p→q}(G, H, n Q*) = n^κ B_{p→q}(G, H, Q*)`. -/
lemma Bmat_smul {n : ℝ} (hn : 0 < n) {Q : V → W → ℝ} (hQ : ∀ v w, 0 ≤ Q v w) :
    Bmat p q G H (fun v w => n * Q v w) = fun a b => n ^ kappa p q * Bmat p q G H Q a b := by
  funext a b
  simp only [Bmat, kappa]
  rw [powZ_mul_left hn (hQ _ _), powZ_mul_left hn (hQ _ _),
    show q⁻¹.toReal + 1 - p⁻¹.toReal = q⁻¹.toReal + (1 - p⁻¹.toReal) by ring,
    Real.rpow_add hn]
  ring

/-- `δ^OT_{p→q}(G, H) = n^{-κ} d^OT_{p→q}(G, H)` for graphs of the same order `n ≥ 1`: the
unnormalised `d^OT_{p→q}` (Section 2, p. 5, l. 184–187) and `δ^OT_{p→q}` (Eq. (2)) differ by the
factor `s(n) = n^κ` (p. 3, l. 88–90; Appendix B, p. 15, l. 513–514). The proof uses
`DS(V, W) = n DS*(V, W)` (Appendix A, p. 14, l. 494–495) and the homogeneity of `B_{p→q}`
(`Bmat_smul`) and of the operator norm (`opNorm_smul_of_nonneg`). -/
theorem deltaOTPQ_eq_dOT (hp : 1 ≤ p) (hq : 1 ≤ q) (hcard : Fintype.card V = Fintype.card W)
    [Nonempty V] :
    deltaOTPQ p q G H = (Fintype.card V : ℝ) ^ (-kappa p q) * dOT p q G H := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hnW : (Fintype.card W : ℝ) = n := by rw [hn, hcard]
  have hk : n ^ (-kappa p q) * n ^ kappa p q = 1 := by
    rw [← Real.rpow_add hn0, neg_add_cancel, Real.rpow_zero]
  -- couplings ↔ doubly stochastic matrices via `Q ↦ n Q`
  have toDS : ∀ Q : V → W → ℝ, IsCoupling Q → IsDS (fun v w => n * Q v w) := fun Q hQ =>
    { nonneg := fun v w => mul_nonneg hn0.le (hQ.nonneg v w)
      row_sum := fun v => by rw [← Finset.mul_sum, hQ.row_sum, ← hn]; field_simp
      col_sum := fun w => by rw [← Finset.mul_sum, hQ.col_sum, hnW]; field_simp }
  have toC : ∀ Q : V → W → ℝ, IsDS Q → IsCoupling (fun v w => Q v w / n) := fun Q hQ =>
    { nonneg := fun v w => div_nonneg (hQ.nonneg v w) hn0.le
      row_sum := fun v => by rw [← Finset.sum_div, hQ.row_sum]
      col_sum := fun w => by rw [← Finset.sum_div, hQ.col_sum, hnW] }
  have hval : ∀ Q : V → W → ℝ, (∀ v w, 0 ≤ Q v w) →
      opNorm p q (Bmat p q G H (fun v w => n * Q v w)) =
        n ^ kappa p q * opNorm p q (Bmat p q G H Q) := fun Q hQ => by
    rw [Bmat_smul p q G H hn0 hQ, opNorm_smul_of_nonneg hp hq (by positivity)]
  have hbdd1 : BddBelow (Set.range fun Q : {Q : V → W → ℝ // IsCoupling Q} =>
      opNorm p q (Bmat p q G H Q.1)) := ⟨0, by rintro _ ⟨Q, rfl⟩; exact opNorm_nonneg _ _ _⟩
  have hbdd2 : BddBelow (Set.range fun Q : {Q : V → W → ℝ // IsDS Q} =>
      opNorm p q (Bmat p q G H Q.1)) := ⟨0, by rintro _ ⟨Q, rfl⟩; exact opNorm_nonneg _ _ _⟩
  obtain ⟨e⟩ : Nonempty (V ≃ W) := ⟨Fintype.equivOfCardEq hcard⟩
  have hne2 : Nonempty {Q : V → W → ℝ // IsDS Q} := ⟨⟨permMat e, permMat_isDS e⟩⟩
  have hne1 : Nonempty {Q : V → W → ℝ // IsCoupling Q} :=
    ⟨⟨fun v w => permMat e v w / n, toC _ (permMat_isDS e)⟩⟩
  unfold deltaOTPQ dOT
  apply le_antisymm
  · -- `δ^OT ≤ n^{-κ} ‖B(Q)‖` for every `Q ∈ DS`
    rw [Real.mul_iInf_of_nonneg (by positivity)]
    refine le_ciInf fun Q => ?_
    have h1 := ciInf_le hbdd1 ⟨fun v w => Q.1 v w / n, toC _ Q.2⟩
    have h2 := hval (fun v w => Q.1 v w / n) (fun v w => div_nonneg (Q.2.nonneg v w) hn0.le)
    have h3 : (fun v w => n * (Q.1 v w / n)) = Q.1 := by
      funext v w; field_simp
    rw [h3] at h2
    refine h1.trans (le_of_eq ?_)
    rw [h2, ← mul_assoc, hk, one_mul]
  · refine le_ciInf fun Q => ?_
    have h1 := ciInf_le hbdd2 ⟨fun v w => n * Q.1 v w, toDS _ Q.2⟩
    rw [hval _ Q.2.nonneg] at h1
    calc n ^ (-kappa p q) * (⨅ Q : {Q : V → W → ℝ // IsDS Q}, opNorm p q (Bmat p q G H Q.1))
        ≤ n ^ (-kappa p q) * (n ^ kappa p q * opNorm p q (Bmat p q G H Q.1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = opNorm p q (Bmat p q G H Q.1) := by rw [← mul_assoc, hk, one_mul]

end Relation

end GsimOT
