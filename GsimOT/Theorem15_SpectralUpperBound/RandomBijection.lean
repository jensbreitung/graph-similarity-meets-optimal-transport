/-
# Theorem 14, matrix part: rounding an optimal fractional alignment to a permutation

Paper, App. F.2 (pp. 47–50): Eq. (40), Eq. (41), Lemmas 50, 51 (with Eq. (42)) and 52,
and the matrix part of the proof of Theorem 14 (spectral truncation, Eq. (43), chain (a)).

Throughout, `A : Matrix V V ℝ`, `B : Matrix W W ℝ` (the paper's `A′, B′`) and `Q ∈ DS(V, W)`.
Matrices act on vectors by ordinary matrix multiplication and `‖·‖` is the spectral norm
`‖·‖₂ = ‖·‖_{2→2}` (Mathlib's `L2` operator norm, see `Tools.lean`).

* `discKernel A B Q` is the matrix with entries `√Q(a) (A_{a₁b₁} - B_{a₂b₂}) √Q(b)`, i.e.
  `B_{2→2}(G, H, Q)` for `A = A_G`, `B = A_H`. Substituting `f ↦ √Q f` in Eq. (40) shows
  `‖discKernel A B Q‖ = n γ_Q(A, B)`; we work with this unnormalised quantity throughout
  (`eq40_le` is the bilinear bound behind Eq. (40)).
* `lemma50`: `‖QᵀAQ - B‖₂ ≤ n γ_Q(A, B)`.
* `eq42`, `lemma51`: **Lemma 51** (local agreement),
  `∑ᵢⱼ Qᵢⱼ (xᵢ - (Qᵀx)ⱼ)² ≤ n² γ_Q² ‖y‖²` for `x = Ay`.
* `lemma52`: **Lemma 52**, `E ‖(I - R)x‖² = ∑ᵢⱼ Qᵢⱼ (xᵢ - (Qᵀx)ⱼ)²` for the random permutation
  `P` of a Birkhoff decomposition of `Q` and `R = PQᵀ`.
* `eq41`, `eq28`, `eq43`: Eq. (41), Eq. (28) for `A′_t`, Eq. (43).
* `exists_bij_norm_le'`: the main estimate `‖A - PBPᵀ‖₂ ≤ nγ_Q + 2s + 2 nγ_Q ‖A‖_F / s` for
  every threshold `s > 0` of the spectral truncation (in the paper `s = nt`, `‖A′‖_F = nh`);
  `exists_bij_norm_le` is the same bound for `PᵀAP - B`.
-/
import GsimOT.Theorem15_SpectralUpperBound.Tools
import GsimOT.Common.BirkhoffDecomposition

open Finset Matrix
open scoped Matrix.Norms.L2Operator

namespace GsimOT

namespace Theorem15

set_option linter.unusedSectionVars false

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-! ### Euclidean norms -/

lemma lpNorm_two_eq' {X : Type*} [Fintype X] (x : X → ℝ) :
    lpNorm 2 x = Real.sqrt (∑ i, x i ^ 2) := by
  rw [lpNorm, EuclideanSpace.norm_eq]
  simp

lemma conjExponent_two' : ENNReal.conjExponent 2 = 2 := by
  rw [ENNReal.conjExponent, show (2 : ENNReal) = 1 + 1 from one_add_one_eq_two.symm,
    ENNReal.add_sub_cancel_left ENNReal.one_ne_top, inv_one]

/-! ### The discrepancy kernel and Eq. (40) -/

/-- The matrix `B_{2→2}` for general matrices `A, B`: entries `√Q(a) (A_{a₁b₁} - B_{a₂b₂}) √Q(b)`.
Its spectral norm is `n γ_Q(A, B)` (Eq. (40), substituting `√Q f` for `f`). -/
noncomputable def discKernel (A : Matrix V V ℝ) (B : Matrix W W ℝ) (Q : Matrix V W ℝ) :
    Matrix (V × W) (V × W) ℝ :=
  fun a b => Real.sqrt (Q a.1 a.2) * (A a.1 b.1 - B a.2 b.2) * Real.sqrt (Q b.1 b.2)

variable (A : Matrix V V ℝ) (B : Matrix W W ℝ) {Q : Matrix V W ℝ}

/-- Applying the kernel to a lifted function `b ↦ √Q(b) f(b)`. -/
lemma discKernel_mulVec_lift (hQ : ∀ v w, 0 ≤ Q v w) (f : V → W → ℝ) (a : V × W) :
    (discKernel A B Q *ᵥ fun b => Real.sqrt (Q b.1 b.2) * f b.1 b.2) a =
      Real.sqrt (Q a.1 a.2) * ∑ v', ∑ w', Q v' w' * (A a.1 v' - B a.2 w') * f v' w' := by
  simp only [mulVec, dotProduct, discKernel]
  rw [Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun v' _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun w' _ => ?_
  have := Real.mul_self_sqrt (hQ v' w')
  calc _ = Real.sqrt (Q a.1 a.2) * ((Real.sqrt (Q v' w') * Real.sqrt (Q v' w')) *
        (A a.1 v' - B a.2 w') * f v' w') := by ring
    _ = _ := by rw [this]

lemma sum_sq_sqrt_mul (hQ : ∀ v w, 0 ≤ Q v w) (c : V × W → ℝ) :
    ∑ a : V × W, (Real.sqrt (Q a.1 a.2) * c a) ^ 2 = ∑ v, ∑ w, Q v w * c (v, w) ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun v _ => sum_congr rfl fun w _ => ?_
  rw [mul_pow, Real.sq_sqrt (hQ v w)]

/-- Lifting via the first coordinate is norm-preserving (the rows of `Q` sum to one). -/
lemma sum_Q_mul_fst (hQ : IsDS Q) (g : V → ℝ) : ∑ v, ∑ w, Q v w * g v = ∑ v, g v :=
  sum_congr rfl fun v _ => by rw [← sum_mul, hQ.row_sum, one_mul]

/-- Lifting via the second coordinate is norm-preserving (the columns of `Q` sum to one). -/
lemma sum_Q_mul_snd (hQ : IsDS Q) (g : W → ℝ) : ∑ v, ∑ w, Q v w * g w = ∑ w, g w := by
  rw [sum_comm]
  exact sum_congr rfl fun w _ => by rw [← sum_mul, hQ.col_sum, one_mul]

/-- **Eq. (40), the bilinear bound.** For all `f, g : V × W → ℝ`,
`|∑ f(i,j) Qᵢⱼ Q_{kℓ} (A_{ik} - B_{jℓ}) g(k,ℓ)| ≤ ‖discKernel A B Q‖ · ‖f‖ · ‖g‖`, with the
`Q`-weighted norms `‖f‖² = ∑ Qᵢⱼ f(i,j)²`. In the paper's normalisation
(`‖discKernel A B Q‖ = nγ_Q`, `‖f‖ = √n ‖f‖_Q`) the right-hand side is `n² γ_Q ‖f‖_Q ‖g‖_Q`.
The sum is `⟨√Q f, K (√Q g)⟩`, so this is Cauchy–Schwarz and the definition of the spectral
norm. -/
lemma eq40_le (hQ : IsDS Q) (f g : V → W → ℝ) :
    |∑ i, ∑ j, f i j * Q i j * ∑ k, ∑ l, Q k l * (A i k - B j l) * g k l| ≤
      ‖discKernel A B Q‖ * (Real.sqrt (∑ i, ∑ j, Q i j * f i j ^ 2) *
        Real.sqrt (∑ k, ∑ l, Q k l * g k l ^ 2)) := by
  set u : V × W → ℝ := fun a => Real.sqrt (Q a.1 a.2) * f a.1 a.2 with hu_def
  set v : V × W → ℝ := fun b => Real.sqrt (Q b.1 b.2) * g b.1 b.2 with hv_def
  have hS : ∑ i, ∑ j, f i j * Q i j * ∑ k, ∑ l, Q k l * (A i k - B j l) * g k l =
      ∑ a, u a * (discKernel A B Q *ᵥ v) a := by
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [hv_def, discKernel_mulVec_lift A B hQ.nonneg g (i, j)]
    have := Real.mul_self_sqrt (hQ.nonneg i j)
    simp only [hu_def]
    calc _ = f i j * (Real.sqrt (Q i j) * Real.sqrt (Q i j)) *
          ∑ k, ∑ l, Q k l * (A i k - B j l) * g k l := by rw [this]
      _ = _ := by ring
  have hu : ∑ a, u a ^ 2 = ∑ i, ∑ j, Q i j * f i j ^ 2 :=
    sum_sq_sqrt_mul hQ.nonneg (fun a => f a.1 a.2)
  have hv : ∑ b, v b ^ 2 = ∑ k, ∑ l, Q k l * g k l ^ 2 :=
    sum_sq_sqrt_mul hQ.nonneg (fun b => g b.1 b.2)
  have hcs := sum_mul_sq_le_sq_mul_sq univ u (discKernel A B Q *ᵥ v)
  have hK := sum_sq_mulVec_le (discKernel A B Q) v
  rw [hS, ← hu, ← hv]
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  calc _ ≤ (∑ a, u a ^ 2) * ∑ a, (discKernel A B Q *ᵥ v) a ^ 2 := hcs
    _ ≤ (∑ a, u a ^ 2) * (‖discKernel A B Q‖ ^ 2 * ∑ b, v b ^ 2) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
    _ = _ := by ring

lemma transpose_mulVec_apply (x : V → ℝ) (w : W) : (Qᵀ *ᵥ x) w = ∑ v, Q v w * x v := by
  simp [mulVec, dotProduct]

lemma inner_sum_fst (hQ : IsDS Q) (g : V → ℝ) (v : V) (w : W) :
    ∑ v', ∑ w', Q v' w' * (A v v' - B w w') * g v' = (A *ᵥ g) v - (B *ᵥ (Qᵀ *ᵥ g)) w := by
  have h1 : ∑ v', ∑ w', Q v' w' * A v v' * g v' = (A *ᵥ g) v := by
    simp only [mulVec, dotProduct]
    refine sum_congr rfl fun v' _ => ?_
    rw [← sum_mul, ← sum_mul, hQ.row_sum, one_mul]
  have h2 : ∑ v', ∑ w', Q v' w' * B w w' * g v' = (B *ᵥ (Qᵀ *ᵥ g)) w := by
    simp only [mulVec, dotProduct, transpose_apply]
    rw [sum_comm]
    refine sum_congr rfl fun w' _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun v' _ => by ring
  rw [← h1, ← h2, ← sum_sub_distrib]
  refine sum_congr rfl fun v' _ => ?_
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun w' _ => by ring

lemma inner_sum_snd (hQ : IsDS Q) (g : W → ℝ) (v : V) (w : W) :
    ∑ v', ∑ w', Q v' w' * (A v v' - B w w') * g w' = (A *ᵥ (Q *ᵥ g)) v - (B *ᵥ g) w := by
  have h1 : ∑ v', ∑ w', Q v' w' * A v v' * g w' = (A *ᵥ (Q *ᵥ g)) v := by
    simp only [mulVec, dotProduct]
    refine sum_congr rfl fun v' _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun w' _ => by ring
  have h2 : ∑ v', ∑ w', Q v' w' * B w w' * g w' = (B *ᵥ g) w := by
    simp only [mulVec, dotProduct]
    rw [sum_comm]
    refine sum_congr rfl fun w' _ => ?_
    rw [← sum_mul, ← sum_mul, hQ.col_sum, one_mul]
  rw [← h1, ← h2, ← sum_sub_distrib]
  refine sum_congr rfl fun v' _ => ?_
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun w' _ => by ring

/-! ### Lemma 50 -/

/-- **Lemma 50.** `‖QᵀAQ - B‖₂ ≤ n γ_Q(A, B)`. As in the paper: by Lemma 19 the spectral norm is
attained by a bilinear form `yᵀ(QᵀAQ - B)x` with unit vectors `x, y`; testing Eq. (40) with
`f(i, j) = y_j`, `g(k, ℓ) = x_ℓ` (the paper's `√n x_j`, `√n y_ℓ` before normalisation) gives
exactly this bilinear form, since the columns of `Q` sum to one, and these lifts have norm `≤ 1`. -/
theorem lemma50 (hQ : IsDS Q) : ‖Qᵀ * A * Q - B‖ ≤ ‖discKernel A B Q‖ := by
  rw [← opNorm_two_two_eq]
  obtain ⟨x, y, hx, hy, heq⟩ := exists_abs_dotProduct_mulVec_eq_opNorm (p := 2) (q := 2)
    (by norm_num) (by norm_num) (Qᵀ * A * Q - B)
  rw [conjExponent_two'] at hy
  rw [lpNorm_two_eq'] at hx hy
  have hform : y ⬝ᵥ ((Qᵀ * A * Q - B) *ᵥ x) =
      ∑ i, ∑ j, y j * Q i j * ∑ k, ∑ l, Q k l * (A i k - B j l) * x l := by
    simp only [inner_sum_snd A B hQ x]
    rw [sum_comm]
    simp only [dotProduct]
    refine sum_congr rfl fun j _ => ?_
    have hw : ((Qᵀ * A * Q - B) *ᵥ x) j = ∑ i, Q i j * (A *ᵥ (Q *ᵥ x)) i - (B *ᵥ x) j := by
      rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, Pi.sub_apply, transpose_mulVec_apply]
    have e : ∑ i, y j * Q i j * ((A *ᵥ (Q *ᵥ x)) i - (B *ᵥ x) j) =
        y j * ∑ i, Q i j * (A *ᵥ (Q *ᵥ x)) i - y j * (B *ᵥ x) j * ∑ i, Q i j := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [hw, e, hQ.col_sum, mul_one, mul_sub]
  have h := eq40_le A B hQ (fun _ j => y j) (fun _ l => x l)
  rw [sum_Q_mul_snd hQ (fun j => y j ^ 2), sum_Q_mul_snd hQ (fun l => x l ^ 2)] at h
  rw [← heq, hform]
  refine h.trans ?_
  have hn := norm_nonneg (discKernel A B Q)
  calc ‖discKernel A B Q‖ * (Real.sqrt (∑ j, y j ^ 2) * Real.sqrt (∑ l, x l ^ 2))
      ≤ ‖discKernel A B Q‖ * (1 * 1) := by
        gcongr
    _ = _ := by ring

/-- `‖QᵀAQ - B‖₂ ≤ n γ_Q`, the statement of `lemma50`. -/
lemma norm_QtAQ_sub_le (hQ : IsDS Q) : ‖Qᵀ * A * Q - B‖ ≤ ‖discKernel A B Q‖ :=
  lemma50 A B hQ

/-! ### Lemma 51 (local agreement) and Eq. (42) -/

/-- The function `F_{ij} = ∑_{k,ℓ} Q_{kℓ} (A_{ik} - B_{jℓ}) y_k` of the proof of Lemma 51. -/
noncomputable def Fmat (Q : Matrix V W ℝ) (y : V → ℝ) (i : V) (j : W) : ℝ :=
  ∑ k, ∑ l, Q k l * (A i k - B j l) * y k

/-- `F_{ij} = x_i - r_j` with `x = Ay`, `r = BQᵀy` (the rows of `Q` sum to one). -/
lemma Fmat_eq (hQ : IsDS Q) (y : V → ℝ) (i : V) (j : W) :
    Fmat A B Q y i j = (A *ᵥ y) i - (B *ᵥ (Qᵀ *ᵥ y)) j :=
  inner_sum_fst A B hQ y i j

/-- **Eq. (42).** `∑ᵢⱼ Qᵢⱼ F²ᵢⱼ ≤ n² γ_Q² ‖y‖²`. As in the paper: `S² = ∑ Qᵢⱼ F²ᵢⱼ` is the
expression of Eq. (40) for `f = F` and `g(k, ℓ) = y_k`, so `S² ≤ nγ_Q · S · ‖y‖`
(`eq40_le`; the rows of `Q` sum to one), and the case `S = 0` is trivial. -/
lemma eq42 (hQ : IsDS Q) (y : V → ℝ) :
    ∑ i, ∑ j, Q i j * Fmat A B Q y i j ^ 2 ≤ ‖discKernel A B Q‖ ^ 2 * ∑ k, y k ^ 2 := by
  set T := ∑ i, ∑ j, Q i j * Fmat A B Q y i j ^ 2 with hT
  have hT0 : 0 ≤ T := sum_nonneg fun i _ => sum_nonneg fun j _ =>
    mul_nonneg (hQ.nonneg i j) (sq_nonneg _)
  have h := eq40_le A B hQ (Fmat A B Q y) (fun k _ => y k)
  rw [sum_Q_mul_fst hQ (fun k => y k ^ 2)] at h
  have hTeq : ∑ i, ∑ j, Fmat A B Q y i j * Q i j *
      ∑ k, ∑ l, Q k l * (A i k - B j l) * y k = T := by
    rw [hT]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [← Fmat]; ring
  rw [hTeq, abs_of_nonneg hT0, ← hT] at h
  -- `S² ≤ c S` with `S = √T`, `c = nγ_Q ‖y‖`
  set S := Real.sqrt T
  set c := ‖discKernel A B Q‖ * Real.sqrt (∑ k, y k ^ 2)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := by positivity
  have hSS : S ^ 2 = T := Real.sq_sqrt hT0
  have h' : S ^ 2 ≤ c * S := by rw [hSS]; linarith
  have hSc : S ≤ c := by
    rcases hS0.eq_or_lt with h0 | h0
    · rw [← h0]; exact hc0
    · nlinarith
  calc T = S ^ 2 := hSS.symm
    _ ≤ c ^ 2 := pow_le_pow_left₀ hS0 hSc 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity)]

/-- **Lemma 51 (local agreement).** For `x = Ay`,
`∑ᵢⱼ Qᵢⱼ (xᵢ - (Qᵀx)ⱼ)² ≤ n² γ_Q² ‖y‖²`. As in the paper: `(Qᵀx)ⱼ = rⱼ + mⱼ` with
`mⱼ = ∑ᵢ Qᵢⱼ Fᵢⱼ`, so `xᵢ - (Qᵀx)ⱼ = Fᵢⱼ - mⱼ`; expanding the square (the columns of `Q` sum to
one) gives `∑ᵢⱼ Qᵢⱼ (Fᵢⱼ - mⱼ)² = ∑ᵢⱼ Qᵢⱼ F²ᵢⱼ - ∑ⱼ m²ⱼ`, and Eq. (42) concludes. -/
theorem lemma51 (hQ : IsDS Q) (y : V → ℝ) :
    ∑ i, ∑ j, Q i j * ((A *ᵥ y) i - (Qᵀ *ᵥ (A *ᵥ y)) j) ^ 2 ≤
      ‖discKernel A B Q‖ ^ 2 * ∑ k, y k ^ 2 := by
  refine le_trans ?_ (eq42 A B hQ y)
  rw [sum_comm, sum_comm (f := fun i j => Q i j * Fmat A B Q y i j ^ 2)]
  refine sum_le_sum fun j _ => ?_
  set m := ∑ i, Q i j * Fmat A B Q y i j with hm
  -- `x_i - (Qᵀx)_j = F_ij - m_j`
  have hQx : (Qᵀ *ᵥ (A *ᵥ y)) j = (B *ᵥ (Qᵀ *ᵥ y)) j + m := by
    rw [transpose_mulVec_apply, hm]
    have : ∀ i, Q i j * (A *ᵥ y) i = Q i j * (B *ᵥ (Qᵀ *ᵥ y)) j + Q i j * Fmat A B Q y i j :=
      fun i => by rw [Fmat_eq A B hQ]; ring
    simp only [this, sum_add_distrib, ← sum_mul, hQ.col_sum, one_mul]
  have hdiff : ∀ i, (A *ᵥ y) i - (Qᵀ *ᵥ (A *ᵥ y)) j = Fmat A B Q y i j - m := fun i => by
    rw [hQx, Fmat_eq A B hQ]; ring
  simp only [hdiff]
  -- expanding the square: `∑ᵢ Qᵢⱼ (Fᵢⱼ - mⱼ)² = ∑ᵢ Qᵢⱼ F²ᵢⱼ - m²ⱼ`
  have hvar := sum_weighted_sq_sub univ (fun i => Q i j) (fun i => Fmat A B Q y i j)
    (hQ.col_sum j) 0
  simp only [sub_zero] at hvar
  rw [← hm] at hvar
  nlinarith [sq_nonneg m]

/-! ### Permutation matrices and `R = PQᵀ` -/

/-- The permutation matrix `P_π` as a matrix. -/
def pmat (π : V ≃ W) : Matrix V W ℝ := fun v w => if π v = w then 1 else 0

lemma pmat_mulVec (π : V ≃ W) (x : W → ℝ) (v : V) : (pmat π *ᵥ x) v = x (π v) := by
  simp [pmat, mulVec, dotProduct]

lemma pmat_apply_eq (π : V ≃ W) (v : V) (w : W) :
    pmat π v w = if v = π.symm w then 1 else 0 := by
  simp only [pmat, Equiv.eq_symm_apply]

lemma transpose_pmat_mul_pmat (π : V ≃ W) : (pmat π)ᵀ * pmat π = 1 := by
  ext w w'
  simp only [mul_apply, transpose_apply, pmat_apply_eq, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, ite_true, one_apply]
  by_cases h : w = w'
  · simp [h]
  · have : π.symm w' ≠ π.symm w := fun h' => h (π.symm.injective h').symm
    simp [h, this]

lemma transpose_pmat_mul_mul_pmat_apply (π : V ≃ W) (A : Matrix V V ℝ) (w w' : W) :
    ((pmat π)ᵀ * A * pmat π) w w' = A (π.symm w) (π.symm w') := by
  simp [mul_apply, transpose_apply, pmat_apply_eq]

lemma norm_pmat_le (π : V ≃ W) : ‖pmat π‖ ≤ 1 := by
  refine l2_norm_le_one_of_stochastic _ (fun v w => by unfold pmat; split_ifs <;> norm_num)
    (fun v => by simp [pmat]) (fun w => by simp [pmat_apply_eq])

lemma norm_transpose_pmat_le (π : V ≃ W) : ‖(pmat π)ᵀ‖ ≤ 1 := by
  rw [l2_norm_transpose]; exact norm_pmat_le π

lemma pmat_mul_transpose_apply (π : V ≃ W) (v v' : V) : (pmat π * Qᵀ) v v' = Q v' (π v) := by
  simp [mul_apply, pmat]

/-- `‖R‖₂ ≤ 1` for the doubly stochastic matrix `R = PQᵀ`. -/
lemma norm_pmat_mul_transpose_le (π : V ≃ W) (hQ : IsDS Q) : ‖pmat π * Qᵀ‖ ≤ 1 := by
  refine l2_norm_le_one_of_stochastic _ (fun v v' => ?_) (fun v => ?_) (fun v' => ?_)
  · rw [pmat_mul_transpose_apply]; exact hQ.nonneg _ _
  · simp only [pmat_mul_transpose_apply, hQ.col_sum, le_refl]
  · simp only [pmat_mul_transpose_apply]
    rw [Equiv.sum_comp π (fun w => Q v' w), hQ.row_sum]

lemma norm_mul3_le {X Y Z T : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype T]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq T]
    (M₁ : Matrix X Y ℝ) (M₂ : Matrix Y Z ℝ) (M₃ : Matrix Z T ℝ) (h₁ : ‖M₁‖ ≤ 1) (h₃ : ‖M₃‖ ≤ 1) :
    ‖M₁ * M₂ * M₃‖ ≤ ‖M₂‖ := by
  calc ‖M₁ * M₂ * M₃‖ ≤ ‖M₁ * M₂‖ * ‖M₃‖ := l2_opNorm_mul _ _
    _ ≤ ‖M₁ * M₂‖ := mul_le_of_le_one_right (norm_nonneg _) h₃
    _ ≤ ‖M₁‖ * ‖M₂‖ := l2_opNorm_mul _ _
    _ ≤ ‖M₂‖ := mul_le_of_le_one_left (norm_nonneg _) h₁

/-- `((I - R)x)ᵢ = xᵢ - (Qᵀx)_{π(i)}` for `R = PQᵀ`. -/
lemma one_sub_R_mulVec (π : V ≃ W) (x : V → ℝ) (v : V) :
    ((1 - pmat π * Qᵀ) *ᵥ x) v = x v - (Qᵀ *ᵥ x) (π v) := by
  rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, Pi.sub_apply, pmat_mulVec]

/-- **Eq. (41).** `A - PBPᵀ = (A - RARᵀ) + P(QᵀAQ - B)Pᵀ` for `R = PQᵀ` (pure algebra). -/
lemma eq41 (π : V ≃ W) :
    A - pmat π * B * (pmat π)ᵀ = (A - (pmat π * Qᵀ) * A * (pmat π * Qᵀ)ᵀ) +
      pmat π * (Qᵀ * A * Q - B) * (pmat π)ᵀ := by
  rw [transpose_mul, transpose_transpose]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- **Eq. (28)** for a symmetric matrix `X`: `X - RXRᵀ = EX + R(EX)ᵀ` with `E = I - R`. -/
lemma eq28 (R X : Matrix V V ℝ) (hX : Xᵀ = X) :
    X - R * X * Rᵀ = (1 - R) * X + R * ((1 - R) * X)ᵀ := by
  rw [transpose_mul, hX, transpose_sub, transpose_one]
  noncomm_ring

/-! ### The random permutation: Lemma 52 -/

/-- Linearity of expectation for the random permutation of a Birkhoff decomposition. If
`Q = ∑ᵢ λᵢ P_{πᵢ}` and `π` is the random bijection with `Pr(π = πᵢ) = λᵢ`, then
`Pr(π(v) = w) = Q_{vw}`, hence `E[∑ᵥ F(v, π(v))] = ∑_{v,w} Q_{vw} F(v, w)` for every `F`. -/
lemma sum_birkhoff_eq {ι : Type*} [Fintype ι] (wt : ι → ℝ) (π : ι → V ≃ W)
    (hQ : ∀ v w, Q v w = ∑ i, wt i * permMat (π i) v w) (F : V → W → ℝ) :
    ∑ i, wt i * ∑ v, F v (π i v) = ∑ v, ∑ w, Q v w * F v w := by
  have h1 : ∀ i, ∑ v, F v (π i v) = ∑ v, ∑ w, F v w * permMat (π i) v w := fun i =>
    (sum_mul_permMat _ _).symm
  simp_rw [h1, hQ, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun w _ => sum_congr rfl fun i _ => by ring

/-- **Lemma 52.** Let `P = P_π` be the random permutation matrix of a Birkhoff decomposition
`Q = ∑ᵢ λᵢ P_{πᵢ}` (`Pr(π = πᵢ) = λᵢ`, so `E[P] = Q`) and `R = PQᵀ`. Then for every `x`,
`E ‖(I - R)x‖₂² = ∑ᵢⱼ Qᵢⱼ (xᵢ - (Qᵀx)ⱼ)²`. As in the paper:
`((I - R)x)ᵢ = xᵢ - (Qᵀx)_{π(i)}`, `Pr(π(i) = j) = Qᵢⱼ`, and linearity of expectation. -/
theorem lemma52 {ι : Type*} [Fintype ι] (wt : ι → ℝ) (π : ι → V ≃ W)
    (hQ : ∀ v w, Q v w = ∑ i, wt i * permMat (π i) v w) (x : V → ℝ) :
    ∑ σ, wt σ * ∑ v, ((1 - pmat (π σ) * Qᵀ) *ᵥ x) v ^ 2 =
      ∑ v, ∑ w, Q v w * (x v - (Qᵀ *ᵥ x) w) ^ 2 := by
  simp only [one_sub_R_mulVec]
  exact sum_birkhoff_eq wt π hQ (fun v w => (x v - (Qᵀ *ᵥ x) w) ^ 2)

/-- Some outcome of a random variable is at most its expectation. -/
lemma exists_le_of_sum_mul_le {ι : Type*} [Fintype ι] (wt f : ι → ℝ) (h0 : ∀ i, 0 ≤ wt i)
    (h1 : ∑ i, wt i = 1) {c : ℝ} (h : ∑ i, wt i * f i ≤ c) : ∃ i, f i ≤ c := by
  by_contra hne
  push Not at hne
  obtain ⟨j, hj⟩ : ∃ j, 0 < wt j := by
    by_contra hpos
    push Not at hpos
    have : ∑ i, wt i ≤ 0 := sum_nonpos fun i _ => hpos i
    linarith
  have : c < ∑ i, wt i * f i := by
    calc c = ∑ i, wt i * c := by rw [← sum_mul, h1, one_mul]
      _ < ∑ i, wt i * f i := sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hne i).le (h0 i))
          ⟨j, mem_univ _, mul_lt_mul_of_pos_left (hne j) hj⟩
  linarith

/-! ### Spectral truncation (proof of Theorem 14, p. 49; compare Lemma 45) -/

section Spectral

variable {A} (hA : A.IsHermitian)

/-- The orthogonal matrix `U` whose columns `φ_r` form an orthonormal eigenbasis of `A` (the
paper's `Φ`, pp. 49–50, l. 1554–1555). -/
noncomputable abbrev eigU : Matrix V V ℝ := (hA.eigenvectorUnitary : Matrix V V ℝ)

/-- Spectral theorem `A = ∑_r λ_r φ_r φ_rᵀ = U diag(λ) Uᵀ`. -/
lemma eigU_spectral : A = eigU hA * diagonal hA.eigenvalues * (eigU hA)ᵀ := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]

lemma eigU_transpose_mul : (eigU hA)ᵀ * eigU hA = 1 := by
  have := (hA.eigenvectorUnitary).2
  rw [mem_unitaryGroup_iff'] at this
  simpa [star_eq_conjTranspose] using this

lemma eigU_mul_transpose : eigU hA * (eigU hA)ᵀ = 1 := by
  have := (hA.eigenvectorUnitary).2
  rw [mem_unitaryGroup_iff] at this
  simpa [star_eq_conjTranspose] using this

lemma norm_one_le : ‖(1 : Matrix V V ℝ)‖ ≤ 1 :=
  l2_norm_le_one_of_stochastic _ (fun i j => by rw [one_apply]; split_ifs <;> norm_num)
    (fun i => by simp [one_apply]) (fun j => by simp [one_apply])

lemma norm_eigU_le : ‖eigU hA‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (eigU hA)
  rw [conjTranspose_eq_transpose_of_trivial, eigU_transpose_mul] at h
  nlinarith [norm_nonneg (eigU hA), norm_one_le (V := V)]

lemma norm_eigU_transpose_le : ‖(eigU hA)ᵀ‖ ≤ 1 := by
  rw [l2_norm_transpose]; exact norm_eigU_le hA

/-- The eigenvectors are unit vectors. -/
lemma sum_sq_eigU_col (r : V) : ∑ i, eigU hA i r ^ 2 = 1 := by
  have := congrFun (congrFun (eigU_transpose_mul hA) r) r
  simpa [mul_apply, sq] using this

lemma mul_eigU_apply (X : Matrix V V ℝ) (v r : V) :
    (X * eigU hA) v r = (X *ᵥ fun i => eigU hA i r) v := by
  simp [mul_apply, mulVec, dotProduct]

/-- `‖K‖_F² = ∑_r ‖K φ_r‖₂²` for the orthonormal basis `(φ_r)` (p. 47, l. 1453; in the proof of
Eq. (43), p. 50, l. 1555–1556: `‖M‖_F² = ‖MΦ‖_F² = ∑_r ‖Mφ_r‖₂²`). -/
lemma frobenius_eq_sum_eigvec (K : Matrix V V ℝ) :
    ∑ i, ∑ j, K i j ^ 2 = ∑ r, ∑ i, (K *ᵥ fun k => eigU hA k r) i ^ 2 := by
  have hrow : ∀ i, ∑ r, (K * eigU hA) i r ^ 2 = ∑ j, K i j ^ 2 := fun i => by
    have h : (K * eigU hA) * (K * eigU hA)ᵀ = K * Kᵀ := by
      rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (eigU hA), eigU_mul_transpose,
        Matrix.one_mul]
    have := congrFun (congrFun h i) i
    rw [Matrix.mul_apply, Matrix.mul_apply] at this
    simpa only [transpose_apply, sq] using this
  simp only [← hrow, mul_eigU_apply]
  exact sum_comm

/-- `∑_r λ_r² = ‖A‖_F²`. -/
lemma sum_sq_entries_eq : ∑ i, ∑ k, A i k ^ 2 = ∑ r, hA.eigenvalues r ^ 2 := by
  have h1 : ∑ i, ∑ k, A i k ^ 2 = trace (A * Aᵀ) := by simp [trace, mul_apply, sq]
  have hUU := eigU_transpose_mul hA
  have h2 : A * Aᵀ = eigU hA * (diagonal hA.eigenvalues * diagonal hA.eigenvalues) *
      (eigU hA)ᵀ := by
    calc A * Aᵀ = (eigU hA * diagonal hA.eigenvalues * (eigU hA)ᵀ) *
          (eigU hA * diagonal hA.eigenvalues * (eigU hA)ᵀ)ᵀ := by rw [← eigU_spectral hA]
      _ = _ := ?_
    simp only [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (eigU hA)ᵀ (eigU hA), hUU, Matrix.one_mul]
  rw [h1, h2, trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, diagonal_mul_diagonal,
    trace_diagonal]
  simp [sq]

/-- The indicator of `I_t = {r : |λ_r| > s}` (in the paper `s = nt`). -/
noncomputable def ind (s : ℝ) (r : V) : ℝ := if s < |hA.eigenvalues r| then 1 else 0

lemma ind_nonneg (s : ℝ) (r : V) : 0 ≤ ind hA s r := by
  simp only [ind]; split_ifs <;> norm_num

lemma ind_sq (s : ℝ) (r : V) : ind hA s r ^ 2 = ind hA s r := by
  simp only [ind]; split_ifs <;> norm_num

/-- The spectral truncation `A_t = ∑_{r ∈ I_t} λ_r φ_r φ_rᵀ`. -/
noncomputable def truncHigh (s : ℝ) : Matrix V V ℝ :=
  eigU hA * diagonal (fun r => hA.eigenvalues r * ind hA s r) * (eigU hA)ᵀ

/-- The remainder `A - A_t = ∑_{r ∉ I_t} λ_r φ_r φ_rᵀ`. -/
noncomputable def truncLow (s : ℝ) : Matrix V V ℝ :=
  eigU hA * diagonal (fun r => hA.eigenvalues r * (1 - ind hA s r)) * (eigU hA)ᵀ

lemma eq_truncLow_add_truncHigh (s : ℝ) : A = truncLow hA s + truncHigh hA s := by
  conv_lhs => rw [eigU_spectral hA]
  rw [truncLow, truncHigh, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
  congr 3
  funext r
  ring

/-- `‖A - A_t‖₂ ≤ s`: all eigenvalues of `A - A_t` lie in `[-s, s]`. -/
lemma norm_truncLow_le {s : ℝ} (hs : 0 ≤ s) : ‖truncLow hA s‖ ≤ s := by
  refine (norm_mul3_le _ _ _ (norm_eigU_le hA) (norm_eigU_transpose_le hA)).trans ?_
  rw [l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg hs).2 fun r => ?_
  simp only [ind, Real.norm_eq_abs]
  split_ifs with h
  · simp [hs]
  · simpa using not_lt.1 h

lemma truncHigh_transpose (s : ℝ) : (truncHigh hA s)ᵀ = truncHigh hA s := by
  simp only [truncHigh, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]

/-- `A_t = A U diag(1_{I_t}) Uᵀ`, since `A φ_r = λ_r φ_r`. -/
lemma truncHigh_eq (s : ℝ) :
    truncHigh hA s = A * eigU hA * diagonal (ind hA s) * (eigU hA)ᵀ := by
  have hAU : A * eigU hA = eigU hA * diagonal hA.eigenvalues := by
    calc A * eigU hA = (eigU hA * diagonal hA.eigenvalues * (eigU hA)ᵀ) * eigU hA := by
          rw [← eigU_spectral hA]
      _ = _ := by rw [Matrix.mul_assoc _ (eigU hA)ᵀ, eigU_transpose_mul, Matrix.mul_one]
  rw [hAU, Matrix.mul_assoc (eigU hA) (diagonal _), diagonal_mul_diagonal]
  rfl

/-- `A_t φ_r = A φ_r` for `r ∈ I_t` and `A_t φ_r = 0` otherwise. -/
lemma truncHigh_mulVec_eigvec (s : ℝ) (r v : V) :
    (truncHigh hA s *ᵥ fun i => eigU hA i r) v = ind hA s r * (A *ᵥ fun i => eigU hA i r) v := by
  rw [← mul_eigU_apply, truncHigh_eq, Matrix.mul_assoc _ (eigU hA)ᵀ, eigU_transpose_mul,
    Matrix.mul_one, mul_diagonal, mul_eigU_apply, mul_comm]

/-- `|I_t| s² ≤ ∑_r λ_r² = ‖A‖_F²`, i.e. `|I_t| ≤ h²/t²` in the paper's normalisation. -/
lemma sq_mul_card_le {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * ∑ r, ind hA s r ≤ ∑ i, ∑ k, A i k ^ 2 := by
  rw [sum_sq_entries_eq hA, mul_sum]
  refine sum_le_sum fun r _ => ?_
  simp only [ind]
  split_ifs with h
  · rw [mul_one, ← sq_abs (hA.eigenvalues r)]
    exact pow_le_pow_left₀ hs h.le 2
  · simp [sq_nonneg]

/-! ### The error of the random permutation on the eigenvectors: Eq. (43) -/

/-- `∑_{r ∈ I_t} ‖(I - R) A φ_r‖₂²` for `R = P_π Qᵀ`. -/
noncomputable def errBij (Q : Matrix V W ℝ) (s : ℝ) (π : V ≃ W) : ℝ :=
  ∑ r, ind hA s r * ∑ v, ((1 - pmat π * Qᵀ) *ᵥ (A *ᵥ fun i => eigU hA i r)) v ^ 2

/-- `‖(I - R) A_t‖_F² = ∑_{r ∈ I_t} ‖(I - R) A φ_r‖₂²`: the Frobenius norm in the eigenbasis,
using `A_t φ_r = A φ_r` for `r ∈ I_t` and `A_t φ_r = 0` otherwise (the equality in Eq. (43)). -/
lemma frobenius_one_sub_R_truncHigh (π : V ≃ W) (s : ℝ) :
    ∑ i, ∑ j, ((1 - pmat π * Qᵀ) * truncHigh hA s : Matrix V V ℝ) i j ^ 2 = errBij hA Q s π := by
  rw [frobenius_eq_sum_eigvec hA, errBij]
  refine sum_congr rfl fun r _ => ?_
  have hv : (((1 - pmat π * Qᵀ) * truncHigh hA s : Matrix V V ℝ) *ᵥ fun k => eigU hA k r) =
      ind hA s r • ((1 - pmat π * Qᵀ) *ᵥ (A *ᵥ fun i => eigU hA i r)) := by
    rw [← mulVec_mulVec, ← mulVec_smul]
    congr 1
    funext v
    rw [truncHigh_mulVec_eigvec, Pi.smul_apply, smul_eq_mul]
  rw [hv, mul_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_pow, ind_sq]

/-- **Eq. (43).** For the random permutation `P` of a Birkhoff decomposition of `Q`,
`E ‖EA_t‖₂² ≤ E ‖EA_t‖_F² = ∑_{r ∈ I_t} E ‖EAφ_r‖₂² ≤ (nγ_Q)² |I_t|`, with `E = I - R`, by
`‖·‖₂ ≤ ‖·‖_F`, the Frobenius norm in the eigenbasis, linearity of expectation, and Lemmas 52
and 51 (with `x = Aφ_r`, `y = φ_r`, `‖φ_r‖₂ = 1`). The last step of Eq. (43),
`|I_t| ≤ h²/t²`, is `sq_mul_card_le`. -/
theorem eq43 (hQ : IsDS Q) {ι : Type*} [Fintype ι] (wt : ι → ℝ) (π : ι → V ≃ W)
    (h0 : ∀ i, 0 ≤ wt i) (hQd : ∀ v w, Q v w = ∑ i, wt i * permMat (π i) v w) (s : ℝ) :
    ∑ σ, wt σ * ‖(1 - pmat (π σ) * Qᵀ) * truncHigh hA s‖ ^ 2 ≤
      ‖discKernel A B Q‖ ^ 2 * ∑ r, ind hA s r := by
  calc ∑ σ, wt σ * ‖(1 - pmat (π σ) * Qᵀ) * truncHigh hA s‖ ^ 2
      ≤ ∑ σ, wt σ * ∑ i, ∑ j, ((1 - pmat (π σ) * Qᵀ) * truncHigh hA s : Matrix V V ℝ) i j ^ 2 :=
        sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (by
          have h := l2_norm_le_frobenius ((1 - pmat (π σ) * Qᵀ) * truncHigh hA s)
          calc _ ≤ Real.sqrt (∑ i, ∑ j, ((1 - pmat (π σ) * Qᵀ) * truncHigh hA s : Matrix V V ℝ) i j ^ 2) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) h 2
            _ = _ := Real.sq_sqrt (by positivity)) (h0 σ)
    _ = ∑ r, ind hA s r * ∑ σ, wt σ *
          ∑ v, ((1 - pmat (π σ) * Qᵀ) *ᵥ (A *ᵥ fun i => eigU hA i r)) v ^ 2 := by
        simp only [frobenius_one_sub_R_truncHigh, errBij, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun r _ => sum_congr rfl fun σ _ => sum_congr rfl fun v _ => ?_
        ring
    _ = ∑ r, ind hA s r * ∑ v, ∑ w, Q v w * ((A *ᵥ fun i => eigU hA i r) v -
          (Qᵀ *ᵥ (A *ᵥ fun i => eigU hA i r)) w) ^ 2 := by
        simp only [lemma52 wt π hQd]
    _ ≤ ∑ r, ind hA s r * ‖discKernel A B Q‖ ^ 2 := by
        refine sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (ind_nonneg hA s r)
        have h51 := lemma51 A B hQ (fun i => eigU hA i r)
        rwa [sum_sq_eigU_col, mul_one] at h51
    _ = _ := by rw [mul_comm, sum_mul]

/-- Taking the square root in Eq. (43): some permutation `P` of the Birkhoff decomposition of `Q`
satisfies `‖EA_t‖₂ ≤ nγ_Q ‖A‖_F / s` (the paper's `nγ_Q h / t`). -/
lemma exists_one_sub_R_truncHigh_le (hQ : IsDS Q) (hcard : Fintype.card V = Fintype.card W)
    {s : ℝ} (hs : 0 < s) :
    ∃ π : V ≃ W, ‖(1 - pmat π * Qᵀ) * truncHigh hA s‖ ≤
      ‖discKernel A B Q‖ * Real.sqrt (∑ i, ∑ k, A i k ^ 2) / s := by
  obtain ⟨wt, π, h0, h1, hQd⟩ := exists_birkhoff_decomposition hQ hcard
  have h43 := eq43 B hA hQ wt π h0 hQd s
  obtain ⟨σ, hσ⟩ := exists_le_of_sum_mul_le wt _ h0 h1 h43
  refine ⟨π σ, ?_⟩
  have hC := norm_nonneg (discKernel A B Q)
  have hcnt := sq_mul_card_le hA hs.le
  have hN : 0 ≤ ∑ r, ind hA s r := sum_nonneg fun r _ => ind_nonneg hA s r
  rw [le_div_iff₀ hs]
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  calc ‖(1 - pmat (π σ) * Qᵀ) * truncHigh hA s‖ ^ 2 * s ^ 2
      ≤ ‖discKernel A B Q‖ ^ 2 * ∑ r, ind hA s r * s ^ 2 := by
        rw [← sum_mul, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hσ (sq_nonneg _)
    _ ≤ ‖discKernel A B Q‖ ^ 2 * ∑ i, ∑ k, A i k ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [← sum_mul, mul_comm]; exact hcnt

include hA in
/-- **Main estimate (proof of Theorem 14, pp. 49–50).** For `Q ∈ DS(V, W)` and every threshold
`s > 0`, some permutation `P = P_π` (from a Birkhoff decomposition of `Q`) satisfies
`‖A - PBPᵀ‖₂ ≤ C + 2s + 2 C ‖A‖_F / s` with `C = ‖B_{2→2}(Q)‖₂ = n γ_Q`. In the paper's
normalisation (`s = nt`, `‖A′‖_F = nh`) this is `γ_P ≤ γ_Q + 2t + 2 γ_Q h / t` (p. 50, l. 1572).
As in the paper: `‖EA_t‖₂ ≤ C ‖A‖_F / s` by Eq. (43); the chain (a) (p. 50, l. 1563–1570) splits
`A = (A - A_t) + A_t` and applies Eq. (28) to `A_t`, giving `‖A - RARᵀ‖₂ ≤ 2s + 2C‖A‖_F/s`; and
Eq. (41) together with Lemma 50 and the invariance of `‖·‖₂` under conjugation with `P`
concludes. -/
theorem exists_bij_norm_le' (hQ : IsDS Q) (hcard : Fintype.card V = Fintype.card W) {s : ℝ}
    (hs : 0 < s) :
    ∃ π : V ≃ W, ‖A - pmat π * B * (pmat π)ᵀ‖ ≤ ‖discKernel A B Q‖ + 2 * s +
      2 * ‖discKernel A B Q‖ * Real.sqrt (∑ i, ∑ k, A i k ^ 2) / s := by
  obtain ⟨π, hπ⟩ := exists_one_sub_R_truncHigh_le B hA hQ hcard hs
  refine ⟨π, ?_⟩
  set R := pmat π * Qᵀ with hRdef
  set F := Real.sqrt (∑ i, ∑ k, A i k ^ 2)
  have hR : ‖R‖ ≤ 1 := norm_pmat_mul_transpose_le π hQ
  have hRt : ‖Rᵀ‖ ≤ 1 := by rw [l2_norm_transpose]; exact hR
  have hE := norm_truncLow_le hA hs.le
  -- the chain (a)
  have hsplit : A - R * A * Rᵀ = (truncLow hA s - R * truncLow hA s * Rᵀ) +
      (truncHigh hA s - R * truncHigh hA s * Rᵀ) := by
    conv_lhs => rw [eq_truncLow_add_truncHigh hA s]
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  have h28 := eq28 R (truncHigh hA s) (truncHigh_transpose hA s)
  have ha : ‖truncHigh hA s - R * truncHigh hA s * Rᵀ‖ ≤
      2 * ‖(1 - R) * truncHigh hA s‖ := by
    rw [h28]
    refine (norm_add_le _ _).trans ?_
    have : ‖R * ((1 - R) * truncHigh hA s)ᵀ‖ ≤ ‖(1 - R) * truncHigh hA s‖ := by
      refine (l2_opNorm_mul _ _).trans ?_
      rw [l2_norm_transpose]
      exact mul_le_of_le_one_left (norm_nonneg _) hR
    linarith
  have hlow : ‖truncLow hA s - R * truncLow hA s * Rᵀ‖ ≤ 2 * s := by
    refine (norm_sub_le _ _).trans ?_
    have := norm_mul3_le _ (truncLow hA s) _ hR hRt
    linarith
  have hchain : ‖A - R * A * Rᵀ‖ ≤ 2 * s + 2 * (‖discKernel A B Q‖ * F / s) := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    generalize ‖discKernel A B Q‖ * F / s = X at hπ ⊢
    linarith
  -- Eq. (41) and Lemma 50
  rw [eq41 A B (Q := Q) π]
  refine (norm_add_le _ _).trans ?_
  have h50 := lemma50 A B hQ
  have hconj := norm_mul3_le (pmat π) (Qᵀ * A * Q - B) (pmat π)ᵀ (norm_pmat_le π)
    (norm_transpose_pmat_le π)
  have e : 2 * ‖discKernel A B Q‖ * F / s = 2 * (‖discKernel A B Q‖ * F / s) := by ring
  rw [e]
  generalize ‖discKernel A B Q‖ * F / s = X at hchain ⊢
  linarith

include hA in
/-- The main estimate for `PᵀAP - B = Pᵀ(A - PBPᵀ)P` (the form `A^π - B` used for `d₂`). -/
theorem exists_bij_norm_le (hQ : IsDS Q) (hcard : Fintype.card V = Fintype.card W) {s : ℝ}
    (hs : 0 < s) :
    ∃ π : V ≃ W, ‖(pmat π)ᵀ * A * pmat π - B‖ ≤ ‖discKernel A B Q‖ + 2 * s +
      2 * ‖discKernel A B Q‖ * Real.sqrt (∑ i, ∑ k, A i k ^ 2) / s := by
  obtain ⟨π, hπ⟩ := exists_bij_norm_le' B hA hQ hcard hs
  refine ⟨π, le_trans ?_ hπ⟩
  have hPP := transpose_pmat_mul_pmat π
  have e : (pmat π)ᵀ * A * pmat π - B = (pmat π)ᵀ * (A - pmat π * B * (pmat π)ᵀ) * pmat π := by
    have e2 : (pmat π)ᵀ * (pmat π * B * (pmat π)ᵀ) * pmat π = B := by
      calc _ = ((pmat π)ᵀ * pmat π) * B * ((pmat π)ᵀ * pmat π) := by simp only [Matrix.mul_assoc]
        _ = B := by rw [hPP, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, e2]
  rw [e]
  exact norm_mul3_le _ _ _ (norm_transpose_pmat_le π) (norm_pmat_le π)

end Spectral

/-! ### Aligned matrices and the symmetric version -/

/-- `A^π - B ∈ ℝ^{W×W}` with `A^π(π v, π v') = A(v, v')`; for adjacency matrices this is
`alignedDiff`. -/
def aligned (π : V ≃ W) : Matrix W W ℝ := fun w w' => A (π.symm w) (π.symm w') - B w w'

lemma aligned_eq (π : V ≃ W) : aligned A B π = (pmat π)ᵀ * A * pmat π - B := by
  ext w w'
  rw [Matrix.sub_apply, transpose_pmat_mul_mul_pmat_apply]
  rfl

/-- The main estimate in terms of `A^π - B`, with the Frobenius norm of `A`. -/
theorem exists_aligned_le (hA : A.IsHermitian) (hQ : IsDS Q)
    (hcard : Fintype.card V = Fintype.card W) {s : ℝ} (hs : 0 < s) :
    ∃ π : V ≃ W, ‖aligned A B π‖ ≤ ‖discKernel A B Q‖ + 2 * s +
      2 * ‖discKernel A B Q‖ * Real.sqrt (∑ i, ∑ k, A i k ^ 2) / s := by
  obtain ⟨π, hπ⟩ := exists_bij_norm_le B hA hQ hcard hs
  exact ⟨π, by rw [aligned_eq]; exact hπ⟩

/-- Exchanging the roles of the two sides: `B_{2→2}` for `(B, A, Qᵀ)` is, up to sign and
reindexing, `B_{2→2}` for `(A, B, Q)`. -/
lemma norm_discKernel_swap :
    ‖discKernel B A Qᵀ‖ = ‖discKernel A B Q‖ := by
  have : discKernel B A Qᵀ =
      -(discKernel A B Q).submatrix (Equiv.prodComm W V) (Equiv.prodComm W V) := by
    ext a b
    rw [Matrix.neg_apply, submatrix_apply]
    simp only [discKernel, transpose_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    ring
  rw [this, norm_neg, l2_norm_submatrix]

lemma isDS_transpose (hQ : IsDS Q) : IsDS Qᵀ where
  nonneg w v := hQ.nonneg v w
  row_sum w := hQ.col_sum w
  col_sum v := hQ.row_sum v

/-- The main estimate with the Frobenius norm of `B` (the case `h = √(p_H(1 - p_H))`, which the
paper reduces to the other one "by symmetry"). -/
theorem exists_aligned_le' (hB : B.IsHermitian) (hQ : IsDS Q)
    (hcard : Fintype.card V = Fintype.card W) {s : ℝ} (hs : 0 < s) :
    ∃ π : V ≃ W, ‖aligned A B π‖ ≤ ‖discKernel A B Q‖ + 2 * s +
      2 * ‖discKernel A B Q‖ * Real.sqrt (∑ i, ∑ k, B i k ^ 2) / s := by
  obtain ⟨σ, hσ⟩ := exists_aligned_le B A hB (isDS_transpose hQ) hcard.symm hs
  rw [norm_discKernel_swap] at hσ
  refine ⟨σ.symm, ?_⟩
  have : aligned A B σ.symm = -(aligned B A σ).submatrix σ σ := by
    ext w w'
    simp [aligned]
  rw [this, norm_neg, l2_norm_submatrix]
  exact hσ

/-- Choice of the threshold (end of the proof of Theorem 14, p. 50, l. 1573–1575): if
`X ≤ C + 2t + 2CF/t` for all `t > 0`, then `X ≤ C + 4√(CF)` (take `t = √(CF)` if `CF > 0`, and
let `t → 0` otherwise). -/
lemma le_of_forall_threshold {X C F : ℝ} (hC : 0 ≤ C) (hF : 0 ≤ F)
    (h : ∀ s, 0 < s → X ≤ C + 2 * s + 2 * C * F / s) : X ≤ C + 4 * Real.sqrt (C * F) := by
  rcases (mul_nonneg hC hF).eq_or_lt with hCF | hCF
  · have hX : X ≤ C := by
      by_contra hX
      push Not at hX
      have := h ((X - C) / 4) (by linarith)
      rw [mul_assoc 2 C F, ← hCF, mul_zero, zero_div, add_zero] at this
      linarith
    have := Real.sqrt_nonneg (C * F)
    linarith
  · have hs := Real.sqrt_pos.2 hCF
    have := h _ hs
    have e : 2 * C * F / Real.sqrt (C * F) = 2 * Real.sqrt (C * F) := by
      rw [div_eq_iff hs.ne']
      linear_combination -2 * Real.mul_self_sqrt (mul_nonneg hC hF)
    rw [e] at this
    linarith

end Theorem15

end GsimOT
