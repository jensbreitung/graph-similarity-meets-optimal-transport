/-
# Tools for Theorem 14: the spectral norm `‖·‖_2 = ‖·‖_{2→2}` of real matrices

Paper, App. F.2 (proof of Theorem 14, pp. 46–50).

We relate the repository's operator norm `opNorm 2 2` to Mathlib's `L2` operator norm on
matrices (scoped instance `Matrix.Norms.L2Operator`), which comes with submultiplicativity and
invariance under transposition. We then collect the elementary facts used in the proof of
Theorem 14:

* `sum_sq_mulVec_le`, `l2_norm_le_of_sum_sq`: the defining inequality `‖Mx‖₂ ≤ ‖M‖₂ ‖x‖₂`, in
  squared form, and its converse;
* `opNorm_two_two_eq`: `‖M‖_{2→2} = ‖M‖₂`;
* `l2_norm_le_frobenius`: `‖M‖₂ ≤ ‖M‖_F` (p. 47, l. 1452);
* `l2_norm_le_one_of_stochastic`: `‖R‖₂ ≤ 1` for nonnegative `R` with row and column sums at most
  one (in particular for doubly stochastic and permutation matrices; p. 47, l. 1485–1486);
* `l2_norm_transpose`, `l2_norm_submatrix`: invariance under transposition and reindexing;
* `sum_weighted_sq_sub`: the variance identity used for "expanding the square" in the proof of
  Lemma 51 (p. 48, l. 1508–1509).
-/
import GsimOT.Common.OperatorNorm

open Finset Matrix
open scoped Matrix.Norms.L2Operator

namespace GsimOT

section L2

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Z]

omit [DecidableEq X] in
/-- `‖x‖₂² = ∑ᵢ xᵢ²` for the Euclidean norm. -/
lemma euclidean_norm_sq (x : X → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ X)‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]

omit [DecidableEq X] in
lemma euclidean_norm_eq (x : X → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ X)‖ = Real.sqrt (∑ i, x i ^ 2) := by
  rw [← euclidean_norm_sq, Real.sqrt_sq (norm_nonneg _)]

omit [DecidableEq X] in
/-- `‖M x‖₂ ≤ ‖M‖₂ ‖x‖₂`. -/
lemma norm_mulVec_le_l2 (M : Matrix X Y ℝ) (x : Y → ℝ) :
    ‖(WithLp.toLp 2 (M *ᵥ x) : EuclideanSpace ℝ X)‖ ≤
      ‖M‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ Y)‖ :=
  M.l2_opNorm_mulVec (WithLp.toLp 2 x)

/-- `‖M x‖₂² ≤ ‖M‖₂² ‖x‖₂²`, written with sums of squares. -/
lemma sum_sq_mulVec_le (M : Matrix X Y ℝ) (x : Y → ℝ) :
    ∑ i, (M *ᵥ x) i ^ 2 ≤ ‖M‖ ^ 2 * ∑ j, x j ^ 2 := by
  rw [← euclidean_norm_sq, ← euclidean_norm_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_mulVec_le_l2 M x) 2

/-- Converse: if `‖M x‖₂² ≤ C² ‖x‖₂²` for all `x`, then `‖M‖₂ ≤ C`. -/
lemma l2_norm_le_of_sum_sq (M : Matrix X Y ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : Y → ℝ, ∑ i, (M *ᵥ x) i ^ 2 ≤ C ^ 2 * ∑ j, x j ^ 2) : ‖M‖ ≤ C := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  have h1 := h (WithLp.ofLp x)
  have hx : ‖x‖ = ‖(WithLp.toLp 2 (WithLp.ofLp x) : EuclideanSpace ℝ Y)‖ := rfl
  have hy : ‖((toEuclideanLin (𝕜 := ℝ) (m := X) (n := Y)).trans
      LinearMap.toContinuousLinearMap M) x‖ =
      ‖(WithLp.toLp 2 (M *ᵥ WithLp.ofLp x) : EuclideanSpace ℝ X)‖ := rfl
  rw [hy, hx]
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
    euclidean_norm_sq, euclidean_norm_sq]
  exact h1

/-- `‖M‖_{2→2} = ‖M‖₂`: the repository's operator norm agrees with Mathlib's `L2` operator norm. -/
lemma opNorm_two_two_eq (M : Matrix X Y ℝ) : opNorm 2 2 M = ‖M‖ := by
  apply le_antisymm
  · refine opNorm_le_of_bound (by norm_num) (by norm_num) M (norm_nonneg _) fun x hx => ?_
    have := norm_mulVec_le_l2 M x
    unfold lpNorm at hx ⊢
    exact this.trans (mul_le_of_le_one_right (norm_nonneg _) hx)
  · refine l2_norm_le_of_sum_sq M (opNorm_nonneg _ _ _) fun x => ?_
    have h := lpNorm_mulVec_le (p := 2) (q := 2) (by norm_num) (by norm_num) M x
    unfold lpNorm at h
    rw [← euclidean_norm_sq, ← euclidean_norm_sq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The spectral norm is bounded by the Frobenius norm: `‖M‖₂ ≤ (∑ᵢⱼ Mᵢⱼ²)^{1/2}`. -/
lemma l2_norm_le_frobenius (M : Matrix X Y ℝ) :
    ‖M‖ ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) := by
  refine l2_norm_le_of_sum_sq M (Real.sqrt_nonneg _) fun x => ?_
  rw [Real.sq_sqrt (by positivity), sum_mul]
  exact sum_le_sum fun i _ => sum_mul_sq_le_sq_mul_sq _ _ _

/-- Weighted Cauchy–Schwarz (Jensen): `(∑ wⱼ xⱼ)² ≤ (∑ wⱼ) (∑ wⱼ xⱼ²)` for `w ≥ 0`. -/
lemma sq_sum_mul_le {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (hw : ∀ j, 0 ≤ w j) :
    (∑ j ∈ s, w j * x j) ^ 2 ≤ (∑ j ∈ s, w j) * ∑ j ∈ s, w j * x j ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq s (fun j => Real.sqrt (w j))
    (fun j => Real.sqrt (w j) * x j)
  have e1 : ∀ j, Real.sqrt (w j) * (Real.sqrt (w j) * x j) = w j * x j := fun j => by
    rw [← mul_assoc, Real.mul_self_sqrt (hw j)]
  have e2 : ∀ j, Real.sqrt (w j) ^ 2 = w j := fun j => Real.sq_sqrt (hw j)
  have e3 : ∀ j, (Real.sqrt (w j) * x j) ^ 2 = w j * x j ^ 2 := fun j => by
    rw [mul_pow, e2]
  simpa only [e1, e2, e3] using h

/-- `‖R‖₂ ≤ 1` for a nonnegative matrix with row and column sums at most one (p. 47,
l. 1485–1486: `‖R‖₂ ≤ 1` for `R ∈ DS(n)`). -/
lemma l2_norm_le_one_of_stochastic (R : Matrix X Y ℝ) (h0 : ∀ i j, 0 ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ 1) (hcol : ∀ j, ∑ i, R i j ≤ 1) : ‖R‖ ≤ 1 := by
  refine l2_norm_le_of_sum_sq R zero_le_one fun x => ?_
  calc ∑ i, (R *ᵥ x) i ^ 2 ≤ ∑ i, ∑ j, R i j * x j ^ 2 := sum_le_sum fun i _ => by
        refine (sq_sum_mul_le univ (R i) x (h0 i)).trans ?_
        exact mul_le_of_le_one_left (sum_nonneg fun j _ => mul_nonneg (h0 i j) (sq_nonneg _))
          (hrow i)
    _ = ∑ j, (∑ i, R i j) * x j ^ 2 := by rw [sum_comm]; simp [sum_mul]
    _ ≤ ∑ j, x j ^ 2 := sum_le_sum fun j _ => mul_le_of_le_one_left (sq_nonneg _) (hcol j)
    _ = 1 ^ 2 * ∑ j, x j ^ 2 := by ring

/-- `‖Mᵀ‖₂ = ‖M‖₂`. -/
lemma l2_norm_transpose (M : Matrix X Y ℝ) : ‖Mᵀ‖ = ‖M‖ := by
  rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]

lemma l2_norm_submatrix_le {X' Y' : Type*} [Fintype X'] [Fintype Y'] [DecidableEq X']
    [DecidableEq Y'] (M : Matrix X Y ℝ) (e : X' ≃ X) (f : Y' ≃ Y) :
    ‖M.submatrix e f‖ ≤ ‖M‖ := by
  refine l2_norm_le_of_sum_sq _ (norm_nonneg _) fun x => ?_
  have h := sum_sq_mulVec_le M (fun j => x (f.symm j))
  have h1 : ∀ i, (M.submatrix e f *ᵥ x) i = (M *ᵥ fun j => x (f.symm j)) (e i) := fun i => by
    simp only [mulVec, dotProduct, submatrix_apply]
    exact (Equiv.sum_comp f (fun j => M (e i) j * x (f.symm j))).symm.trans (by simp) |>.symm
  rw [show ∑ i, (M.submatrix e f *ᵥ x) i ^ 2 = ∑ i, (M *ᵥ fun j => x (f.symm j)) i ^ 2 by
      simp only [h1]; exact Equiv.sum_comp e (fun i => (M *ᵥ fun j => x (f.symm j)) i ^ 2),
    show ∑ j, x j ^ 2 = ∑ j, x (f.symm j) ^ 2 from
      (Equiv.sum_comp f.symm (fun j => x j ^ 2)).symm]
  exact h

/-- The spectral norm is invariant under reindexing rows and columns by bijections. -/
lemma l2_norm_submatrix {X' Y' : Type*} [Fintype X'] [Fintype Y'] [DecidableEq X']
    [DecidableEq Y'] (M : Matrix X Y ℝ) (e : X' ≃ X) (f : Y' ≃ Y) :
    ‖M.submatrix e f‖ = ‖M‖ := by
  refine le_antisymm (l2_norm_submatrix_le M e f) ?_
  have := l2_norm_submatrix_le (M.submatrix e f) e.symm f.symm
  simpa using this

end L2

/-- **Variance identity.** For weights `q` with `∑ qᵢ = 1` and mean `m = ∑ qᵢ xᵢ`,
`∑ qᵢ (xᵢ - c)² = ∑ qᵢ (xᵢ - m)² + (m - c)²`. With `c = 0` this is the expansion
`∑ᵢ Qᵢⱼ (Fᵢⱼ - mⱼ)² = ∑ᵢ Qᵢⱼ F²ᵢⱼ - m²ⱼ` in the proof of Lemma 51 (p. 48, l. 1508–1509). -/
lemma sum_weighted_sq_sub {ι : Type*} (s : Finset ι) (q x : ι → ℝ) (hq : ∑ i ∈ s, q i = 1)
    (c : ℝ) :
    ∑ i ∈ s, q i * (x i - c) ^ 2 =
      ∑ i ∈ s, q i * (x i - ∑ j ∈ s, q j * x j) ^ 2 + (∑ j ∈ s, q j * x j - c) ^ 2 := by
  have key : ∀ d : ℝ, ∑ i ∈ s, q i * (x i - d) ^ 2 =
      ∑ i ∈ s, q i * x i ^ 2 - 2 * d * ∑ i ∈ s, q i * x i + d ^ 2 * ∑ i ∈ s, q i := by
    intro d
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [key, key, hq]
  ring

end GsimOT
