/-
# Lemmas 40, 41, 45, Eqs. (31)–(37) and Corollary 46 (App. E.2.2, pp. 36–41)

Lemma 40 (Lifted Kernels, p. 36, l. 1141–1143), Lemma 41 (Close Support Functions, p. 37,
l. 1158–1161), Lemma 45 (p. 39, l. 1218–1220; proof pp. 39–40, l. 1221–1245), the zonotopes and
Eqs. (32)–(37) (pp. 40–41, l. 1246–1272) and Corollary 46 (p. 41, l. 1273–1274).

Structure of the proof (following the paper):
* Spectral theorem for `A`, `B` (`spectral_entry`, `parseval_row`) and the spectral truncation
  `specTrunc` keeping the eigenvalues of absolute value `> tN`. We work with the standard inner
  product instead of `L2(n)`, so the paper's eigenvalues of the averaging operator are `λ_r / N`
  and its eigenfunctions are `√N e_r`.
* `opBound_sub_specTrunc`: `‖A - A_t‖_{L2(n)} ≤ t` (in the averaged normalisation).
* Eq. (22) (bilinear forms of `[0,1]`-valued functions): `abs_bilin_le_cutNorm`;
  **Lemma 40**: `lemma41_2_fst`, `lemma41_2_snd`; **Eq. (31)**: `eq28`.
* The vectors `z_ij` (`specVec`, called `v` in Lean), the operator `T_t = diagOp specDiag`,
  `‖z_ij‖ ≤ √2` (`norm_specVec_le`), `‖T_t‖ ≤ 1/t` (`abs_specDiag_le`, `norm_diagOp_le`) and
  `⟨z_ij, T_t z_kl⟩ = (A_t)_ik - (B_t)_jl` (`diagForm_specVec`, `inner_diagOp`).
  **Lemma 45** (Eq. (30)): `lemma45`.
* Zonotopes `Z_R = zonLin v R '' cube` (Eq. (32)) and their support function `hSupp`
  (**Eq. (33)**: `supportFn_zonotope`); **Eq. (36)**: `eq36`; **Eq. (37)**: `eq37`.
* **Lemma 41**: `lemma41`, by the paper's support-function argument (`lemma41_step`: maximise over
  `u` first via `h_Z(T u')`, then over `u'` via `h_{Z'}(T* u)` with the adjoint `T*`).
* **Corollary 46**: `corollary46`.
-/
import GsimOT.Theorem13_CutUpperBound.Definitions
open Finset

namespace GsimOT

section Spectral
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.IsHermitian)

/-- Eigenvector equation, coordinatewise: `λ_r e_r(i) = (A e_r)(i)`. -/
lemma eig_coord (r i : ι) :
    hM.eigenvalues r * hM.eigenvectorBasis r i = ∑ k, M i k * hM.eigenvectorBasis r k := by
  have := congrFun (hM.mulVec_eigenvectorBasis r) i
  simpa [Matrix.mulVec, dotProduct] using this.symm

/-- `⟨e_r, A_i⟩ = λ_r e_r(i)` for the row `A_i`. -/
lemma inner_row_eig (r i : ι) :
    inner ℝ (hM.eigenvectorBasis r) (WithLp.toLp 2 (M i)) =
      hM.eigenvalues r * hM.eigenvectorBasis r i := by
  rw [eig_coord, PiLp.inner_apply]
  simp

/-- Spectral theorem, entrywise: `A_ik = ∑_r λ_r e_r(i) e_r(k)`. -/
lemma spectral_entry (i k : ι) :
    M i k = ∑ r, hM.eigenvalues r * hM.eigenvectorBasis r i * hM.eigenvectorBasis r k := by
  have h := congrArg (fun x : EuclideanSpace ℝ ι => x k)
    ((hM.eigenvectorBasis).sum_repr' (WithLp.toLp 2 (M i)))
  simp only [inner_row_eig, WithLp.ofLp_sum] at h
  rw [← h]
  simp

/-- Parseval for the rows: `∑_r (λ_r e_r(i))² = ∑_k A_ik²`. -/
lemma parseval_row (i : ι) :
    ∑ r, (hM.eigenvalues r * hM.eigenvectorBasis r i) ^ 2 = ∑ k, M i k ^ 2 := by
  have h := (hM.eigenvectorBasis).sum_inner_mul_inner (WithLp.toLp 2 (M i)) (WithLp.toLp 2 (M i))
  have h2 : ∀ r, inner ℝ (WithLp.toLp 2 (M i)) (hM.eigenvectorBasis r) =
      hM.eigenvalues r * hM.eigenvectorBasis r i := fun r => by
    rw [real_inner_comm]; exact inner_row_eig hM r i
  simp only [inner_row_eig, h2, ← sq] at h
  rw [h, PiLp.inner_apply]
  simp [sq]

/-- Spectral truncation `M_c`: keep the eigenvalues with `|λ_r| > c`. -/
noncomputable def specTrunc (c : ℝ) : Matrix ι ι ℝ := fun i k =>
  ∑ r, if c < |hM.eigenvalues r| then
    hM.eigenvalues r * hM.eigenvectorBasis r i * hM.eigenvectorBasis r k else 0

end Spectral

/-- Operator-norm bound `|⟨f, K g⟩| ≤ c ‖f‖ ‖g‖`, in the (weaker) AM-GM form. -/
def OpBound {ι : Type*} [Fintype ι] (K : Matrix ι ι ℝ) (c : ℝ) : Prop :=
  ∀ f g : ι → ℝ, |∑ i, ∑ k, f i * K i k * g k| ≤ c * ((∑ i, f i ^ 2) + ∑ i, g i ^ 2) / 2

lemma OpBound.neg {ι : Type*} [Fintype ι] {K : Matrix ι ι ℝ} {c : ℝ} (h : OpBound K c) :
    OpBound (fun i k => -K i k) c := fun f g => by
  have := h f g
  simpa [Finset.sum_neg_distrib] using this

/-- Diagonal bilinear forms: `|∑ d_p x_p y_p| ≤ c ‖x‖ ‖y‖` if `|d_p| ≤ c`. -/
lemma abs_sum_diag_le {ι : Type*} [Fintype ι] (d : ι → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hd : ∀ p, |d p| ≤ c) (x y : EuclideanSpace ℝ ι) :
    |∑ p, d p * x p * y p| ≤ c * (‖x‖ * ‖y‖) := by
  calc |∑ p, d p * x p * y p| ≤ ∑ p, |d p * x p * y p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, c * (|x p| * |y p|) := Finset.sum_le_sum fun p _ => by
        rw [abs_mul, abs_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_right (hd p) (by positivity)
    _ = c * ∑ p, |x p| * |y p| := by rw [Finset.mul_sum]
    _ ≤ c * (√(∑ p, |x p| ^ 2) * √(∑ p, |y p| ^ 2)) := by
        gcongr
        exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = c * (‖x‖ * ‖y‖) := by simp [EuclideanSpace.norm_eq]

section Spectral
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.IsHermitian)

/-- The remainder `M - M_c` has operator norm at most `c`. -/
lemma opBound_sub_specTrunc {c : ℝ} (hc : 0 ≤ c) :
    OpBound (fun i k => M i k - specTrunc hM c i k) c := by
  intro f g
  let e := hM.eigenvectorBasis
  let d : ι → ℝ := fun r => if c < |hM.eigenvalues r| then 0 else hM.eigenvalues r
  have hd : ∀ r, |d r| ≤ c := fun r => by
    simp only [d]; split_ifs with h
    · simpa using hc
    · exact not_lt.mp h
  have hsum : ∑ i, ∑ k, f i * (M i k - specTrunc hM c i k) * g k =
      ∑ r, d r * (e.repr (WithLp.toLp 2 f)) r * (e.repr (WithLp.toLp 2 g)) r := by
    simp only [OrthonormalBasis.repr_apply_apply, PiLp.inner_apply]
    have hMk : ∀ i k, M i k - specTrunc hM c i k = ∑ r, d r * e r i * e r k := fun i k => by
      rw [spectral_entry hM i k, specTrunc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [d, e]; split_ifs <;> ring
    simp only [hMk, Finset.mul_sum, Finset.sum_mul, RCLike.inner_apply, conj_trivial]
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hsum]
  refine (abs_sum_diag_le d hc hd _ _).trans ?_
  simp only [LinearIsometryEquiv.norm_map]
  have h1 : ‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ ^ 2 = ∑ i, f i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  have h2 : ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖ ^ 2 = ∑ i, g i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  rw [← h1, ← h2]
  nlinarith [two_mul_le_add_sq ‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖
    ‖(WithLp.toLp 2 g : EuclideanSpace ℝ ι)‖]

end Spectral

section CutNormFacts
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Triangle inequality for the cut norm (three summands). -/
lemma cutNorm_le_of_eq_add3 {X Y K L : Matrix ι κ ℝ}
    (h : ∀ x y, X x y = Y x y + K x y + L x y) :
    cutNorm X ≤ cutNorm Y + cutNorm K + cutNorm L := by
  refine cutNorm_le _ fun S T => ?_
  have : ∑ i ∈ S, ∑ j ∈ T, X i j = (∑ i ∈ S, ∑ j ∈ T, Y i j) + (∑ i ∈ S, ∑ j ∈ T, K i j) +
      ∑ i ∈ S, ∑ j ∈ T, L i j := by
    simp only [h, Finset.sum_add_distrib]
  rw [this]
  calc _ ≤ |∑ i ∈ S, ∑ j ∈ T, Y i j| + |∑ i ∈ S, ∑ j ∈ T, K i j| +
        |∑ i ∈ S, ∑ j ∈ T, L i j| := abs_add_three _ _ _
    _ ≤ _ := by gcongr <;> exact le_cutNorm _ _ _

omit [DecidableEq ι] in
/-- A linear form with coefficients in `[0, 1]` is dominated by a subset sum. -/
lemma exists_finset_abs_sum_le (f c : ι → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    ∃ S : Finset ι, |∑ i, f i * c i| ≤ |∑ i ∈ S, c i| := by
  by_cases h : 0 ≤ ∑ i, f i * c i
  · refine ⟨Finset.univ.filter fun i => 0 < c i, ?_⟩
    rw [abs_of_nonneg h]
    refine le_trans ?_ (le_abs_self _)
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hf i
    split_ifs with hc
    · nlinarith
    · nlinarith
  · refine ⟨Finset.univ.filter fun i => c i < 0, ?_⟩
    push Not at h
    rw [abs_of_neg h]
    refine le_trans ?_ (neg_le_abs _)
    rw [Finset.sum_filter, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hf i
    split_ifs with hc
    · nlinarith
    · nlinarith

/-- **Eq. (22)** (unweighted form): bilinear forms of `[0, 1]`-valued functions are bounded
by the cut norm. -/
lemma abs_bilin_le_cutNorm (K : Matrix ι κ ℝ) (f : ι → ℝ) (g : κ → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ y, 0 ≤ g y ∧ g y ≤ 1) :
    |∑ x, ∑ y, f x * K x y * g y| ≤ cutNorm K := by
  obtain ⟨S, hS⟩ := exists_finset_abs_sum_le f (fun x => ∑ y, K x y * g y) hf
  obtain ⟨T, hT⟩ := exists_finset_abs_sum_le g (fun y => ∑ x ∈ S, K x y) hg
  calc |∑ x, ∑ y, f x * K x y * g y| = |∑ x, f x * ∑ y, K x y * g y| := by
        simp [Finset.mul_sum, mul_assoc]
    _ ≤ |∑ x ∈ S, ∑ y, K x y * g y| := hS
    _ = |∑ y, g y * ∑ x ∈ S, K x y| := by
        rw [Finset.sum_comm]; simp [Finset.mul_sum, mul_comm]
    _ ≤ |∑ y ∈ T, ∑ x ∈ S, K x y| := hT
    _ = |∑ x ∈ S, ∑ y ∈ T, K x y| := by rw [Finset.sum_comm]
    _ ≤ cutNorm K := le_cutNorm K S T

/-- A cut value as a bilinear form with indicator functions. -/
lemma cut_sum_eq_bilin (K : Matrix ι κ ℝ) (S : Finset ι) (T : Finset κ) :
    ∑ x ∈ S, ∑ y ∈ T, K x y =
      ∑ x, ∑ y, (if x ∈ S then 1 else 0) * K x y * (if y ∈ T then 1 else 0) := by
  simp [ite_mul, mul_ite, Finset.sum_ite_mem]

end CutNormFacts

/-- Marginal weights of a subset are small in `ℓ²`: if `F ≥ 0` has row sums `≤ 1` and total mass
`≤ N`, then `N ∑_a (∑_b F a b / N)² ≤ 1`. -/
lemma weight_sq_le {α β : Type*} [Fintype α] [Fintype β] (F : α → β → ℝ) {N : ℝ}
    (hN : 0 ≤ N) (hF : ∀ a b, 0 ≤ F a b) (hrow : ∀ a, ∑ b, F a b ≤ 1)
    (htot : ∑ a, ∑ b, F a b ≤ N) :
    N * ∑ a, ((∑ b, F a b) / N) ^ 2 ≤ 1 := by
  rcases hN.eq_or_lt with h | h
  · simp [← h]
  have h1 : ∀ a, N * ((∑ b, F a b) / N) ^ 2 ≤ (∑ b, F a b) / N := fun a => by
    have h0 : 0 ≤ ∑ b, F a b := Finset.sum_nonneg fun b _ => hF a b
    rw [div_pow, ← mul_div_assoc, sq, mul_comm N]
    rw [div_le_div_iff₀ (by positivity) h]
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hrow a) h0) (sq_nonneg N)
    nlinarith
  calc N * ∑ a, ((∑ b, F a b) / N) ^ 2 = ∑ a, N * ((∑ b, F a b) / N) ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ a, (∑ b, F a b) / N := Finset.sum_le_sum fun a _ => h1 a
    _ = (∑ a, ∑ b, F a b) / N := (Finset.sum_div _ _ _).symm
    _ ≤ 1 := by rw [div_le_one h]; exact htot

section Weighted
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- **Lemma 40** (Lifted kernels), first coordinate: if `|⟨f, K g⟩| ≤ t ‖f‖ ‖g‖`, the kernel
`K⁽¹⁾((i,j),(k,l)) = K i k` has weighted cut norm `‖K⁽¹⁾‖_{□,μ_R} ≤ t`. -/
lemma lemma41_2_fst {R : V → W → ℝ} (hR : IsDS R) {K : Matrix V V ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hK : OpBound K (t * Fintype.card V)) :
    cutNorm (fun x y : V × W => (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
      K x.1 y.1) ≤ t := by
  refine cutNorm_le _ fun S T => ?_
  have hN : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  let f : V → ℝ := fun i => (∑ j, if (i, j) ∈ S then R i j else 0) / Fintype.card V
  let g : V → ℝ := fun i => (∑ j, if (i, j) ∈ T then R i j else 0) / Fintype.card V
  have hw : ∀ U : Finset (V × W), (Fintype.card V : ℝ) *
      ∑ i, ((∑ j, if (i, j) ∈ U then R i j else 0) / Fintype.card V) ^ 2 ≤ 1 := fun U =>
    weight_sq_le _ hN (fun i j => by split_ifs <;> simp [hR.nonneg])
      (fun i => (Finset.sum_le_sum fun j _ => by split_ifs <;> simp [hR.nonneg]).trans
        (hR.row_sum i).le)
      ((Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
        split_ifs <;> simp [hR.nonneg]).trans hR.sum_sum.le)
  have hsum : ∑ x ∈ S, ∑ y ∈ T, (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
      K x.1 y.1 = ∑ i, ∑ k, f i * K i k * g k := by
    refine (cut_sum_eq_bilin (fun x y : V × W => (R x.1 x.2 / Fintype.card V) *
      (R y.1 y.2 / Fintype.card V) * K x.1 y.1) S T).trans ?_
    simp only [f, g, Fintype.sum_prod_type, Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [hsum]
  refine (hK f g).trans ?_
  have h1 := hw S
  have h2 := hw T
  nlinarith

/-- **Lemma 40** (Lifted kernels), second coordinate: if `|⟨f, K g⟩| ≤ t ‖f‖ ‖g‖`, the kernel
`K⁽²⁾((i,j),(k,l)) = K j l` has weighted cut norm `‖K⁽²⁾‖_{□,μ_R} ≤ t`. -/
lemma lemma41_2_snd {R : V → W → ℝ} (hR : IsDS R) {K : Matrix W W ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hK : OpBound K (t * Fintype.card V)) :
    cutNorm (fun x y : V × W => (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
      K x.2 y.2) ≤ t := by
  refine cutNorm_le _ fun S T => ?_
  have hN : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  let f : W → ℝ := fun j => (∑ i, if (i, j) ∈ S then R i j else 0) / Fintype.card V
  let g : W → ℝ := fun j => (∑ i, if (i, j) ∈ T then R i j else 0) / Fintype.card V
  have hw : ∀ U : Finset (V × W), (Fintype.card V : ℝ) *
      ∑ j, ((∑ i, if (i, j) ∈ U then R i j else 0) / Fintype.card V) ^ 2 ≤ 1 := fun U =>
    weight_sq_le (fun j i => if (i, j) ∈ U then R i j else 0) hN
      (fun j i => by split_ifs <;> simp [hR.nonneg])
      (fun j => (Finset.sum_le_sum fun i _ => by split_ifs <;> simp [hR.nonneg]).trans
        (hR.col_sum j).le)
      (by
        have h1 : ∑ j, ∑ i, (if (i, j) ∈ U then R i j else 0) ≤ ∑ j, ∑ i, R i j :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => by
            split_ifs <;> simp [hR.nonneg]
        rw [Finset.sum_comm (f := fun j i => R i j), hR.sum_sum] at h1
        exact h1)
  have hsum : ∑ x ∈ S, ∑ y ∈ T, (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
      K x.2 y.2 = ∑ j, ∑ l, f j * K j l * g l := by
    refine (cut_sum_eq_bilin (fun x y : V × W => (R x.1 x.2 / Fintype.card V) *
      (R y.1 y.2 / Fintype.card V) * K x.2 y.2) S T).trans ?_
    simp only [f, g, Fintype.sum_prod_type, Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm, Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  rw [hsum]
  refine (hK f g).trans ?_
  have h1 := hw S
  have h2 := hw T
  nlinarith

/-- **Eq. (31)**: spectral truncation changes `ζ_R` by at most `2t`. -/
lemma eq28 {R : V → W → ℝ} (hR : IsDS R) {A At : Matrix V V ℝ} {B Bt : Matrix W W ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hA : OpBound (fun i k => A i k - At i k) (t * Fintype.card V))
    (hB : OpBound (fun j l => B j l - Bt j l) (t * Fintype.card V)) :
    epsR A B R ≤ epsR At Bt R + 2 * t ∧ epsR At Bt R ≤ epsR A B R + 2 * t := by
  have h1 := lemma41_2_fst (W := W) hR ht hA
  have h1' := lemma41_2_fst (W := W) hR ht hA.neg
  have h2 := lemma41_2_snd hR ht hB
  have h2' := lemma41_2_snd hR ht hB.neg
  beta_reduce at h1 h1' h2 h2'
  unfold epsR
  constructor
  · have := cutNorm_le_of_eq_add3
      (X := fun x y : V × W => (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
        (A x.1 y.1 - B x.2 y.2))
      (Y := fun x y : V × W => (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
        (At x.1 y.1 - Bt x.2 y.2))
      (K := fun x y : V × W => (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
        (A x.1 y.1 - At x.1 y.1))
      (L := fun x y : V × W => (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
        -(B x.2 y.2 - Bt x.2 y.2)) (fun x y => by ring)
    linarith
  · have := cutNorm_le_of_eq_add3
      (Y := fun x y : V × W => (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
        (A x.1 y.1 - B x.2 y.2))
      (X := fun x y : V × W => (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
        (At x.1 y.1 - Bt x.2 y.2))
      (K := fun x y : V × W => (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
        -(A x.1 y.1 - At x.1 y.1))
      (L := fun x y : V × W => (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
        (B x.2 y.2 - Bt x.2 y.2)) (fun x y => by ring)
    linarith

end Weighted

section Zonotope
variable {V W : Type*} [Fintype V] [Fintype W]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear map `a ↦ u_a = (1/n) ∑_{i,j} R_ij a_ij v_ij`, whose image of the cube
`[0,1]^{V×W}` is the zonotope `Z_R` (Eq. (32)). -/
noncomputable def zonLin (v : V → W → E) (R : V → W → ℝ) : (V → W → ℝ) →ₗ[ℝ] E where
  toFun a := ∑ i, ∑ j, (R i j * a i j / Fintype.card V) • v i j
  map_add' a b := by
    simp only [Pi.add_apply, mul_add, add_div, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1; ring

/-- The cube `[0,1]^{V×W}`. -/
def cube : Set (V → W → ℝ) := Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc 0 1

omit [Fintype V] [Fintype W] in
lemma mem_cube {a : V → W → ℝ} : a ∈ (cube : Set (V → W → ℝ)) ↔ ∀ i j, 0 ≤ a i j ∧ a i j ≤ 1 := by
  simp only [cube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]

lemma convex_zonotope (v : V → W → E) (R : V → W → ℝ) : Convex ℝ (zonLin v R '' cube) :=
  (convex_pi fun _ _ => convex_pi fun _ _ => convex_Icc 0 1).linear_image _

lemma isCompact_zonotope (v : V → W → E) (R : V → W → ℝ) : IsCompact (zonLin v R '' cube) :=
  (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).image
    (LinearMap.continuous_of_finiteDimensional _)

lemma inner_zonLin (v : V → W → E) (R a : V → W → ℝ) (z : E) :
    inner ℝ z (zonLin v R a) =
      ∑ i, ∑ j, R i j * a i j / Fintype.card V * inner ℝ z (v i j) := by
  simp [zonLin, inner_sum, inner_smul_right]

/-- Points of `Z_R` satisfy `⟨z, u⟩ ≤ h_R(z)`. -/
lemma inner_zonLin_le_hSupp (v : V → W → E) {R a : V → W → ℝ} (hR : ∀ i j, 0 ≤ R i j)
    (ha : a ∈ (cube : Set (V → W → ℝ))) (z : E) :
    inner ℝ z (zonLin v R a) ≤ hSupp v R z := by
  rw [inner_zonLin, hSupp, Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun j _ => ?_
  have ha' := mem_cube.mp ha i j
  rw [div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hx := le_max_left (inner ℝ z (v i j)) 0
  have hx0 := le_max_right (inner ℝ z (v i j)) 0
  have : a i j * inner ℝ z (v i j) ≤ max (inner ℝ z (v i j)) 0 := by
    rcases le_total 0 (inner ℝ z (v i j)) with h | h <;> nlinarith
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left this (hR i j)

/-- The support function `h_R` is attained on `Z_R` (by `a_ij = 1[⟨z, v_ij⟩ > 0]`). -/
lemma exists_inner_zonLin_eq_hSupp (v : V → W → E) (R : V → W → ℝ) (z : E) :
    ∃ a ∈ (cube : Set (V → W → ℝ)), inner ℝ z (zonLin v R a) = hSupp v R z := by
  refine ⟨fun i j => if 0 < inner ℝ z (v i j) then 1 else 0, mem_cube.mpr fun i j => ?_, ?_⟩
  · split_ifs <;> norm_num
  rw [inner_zonLin, hSupp, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [max_eq_left h.le]; ring
  · rw [max_eq_right (not_lt.mp h)]; ring

/-- `Z_R` lies in the ball of radius `M` if `‖v_ij‖ ≤ M`. -/
lemma norm_zonLin_le [DecidableEq V] [DecidableEq W] (v : V → W → E) {R a : V → W → ℝ} (hR : IsDS R)
    (ha : a ∈ (cube : Set (V → W → ℝ))) {M : ℝ} (hM : 0 ≤ M) (hv : ∀ i j, ‖v i j‖ ≤ M) :
    ‖zonLin v R a‖ ≤ M := by
  have hN : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  calc ‖zonLin v R a‖ ≤ ∑ i, ‖∑ j, (R i j * a i j / Fintype.card V) • v i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖(R i j * a i j / Fintype.card V) • v i j‖ :=
        Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, R i j / Fintype.card V * M := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have ha' := mem_cube.mp ha i j
        have hRij := hR.nonneg i j
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hRij ha'.1) hN)]
        have : R i j * a i j / Fintype.card V ≤ R i j / Fintype.card V := by
          gcongr; nlinarith
        exact mul_le_mul this (hv i j) (norm_nonneg _) (by positivity)
    _ = (∑ i, ∑ j, R i j) / Fintype.card V * M := by
        rw [Finset.sum_div, Finset.sum_mul]
        simp [Finset.sum_div, Finset.sum_mul]
    _ ≤ M := by
        rw [hR.sum_sum]
        exact mul_le_of_le_one_left hM (div_self_le_one _)

/-- On the unit ball, `0 ≤ h_R(z) ≤ (1/n) ∑ R_ij ‖v_ij‖`. -/
lemma hSupp_bounds (v : V → W → E) {R : V → W → ℝ} (hR : ∀ i j, 0 ≤ R i j) {z : E}
    (hz : ‖z‖ ≤ 1) :
    0 ≤ hSupp v R z ∧
      hSupp v R z ≤ (∑ i, ∑ j, R i j * ‖v i j‖) / Fintype.card V := by
  have hN : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hR i j) (le_max_right _ _)) hN
  · refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hR i j)) hN
    refine max_le ?_ (norm_nonneg _)
    calc inner ℝ z (v i j) ≤ ‖z‖ * ‖v i j‖ := real_inner_le_norm _ _
      _ ≤ 1 * ‖v i j‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ = ‖v i j‖ := one_mul _

lemma bddAbove_rhoSupp (v : V → W → E) {R R' : V → W → ℝ} (hR : ∀ i j, 0 ≤ R i j)
    (hR' : ∀ i j, 0 ≤ R' i j) :
    BddAbove (Set.range fun z : Metric.closedBall (0 : E) 1 =>
      |hSupp v R z.1 - hSupp v R' z.1|) := by
  refine ⟨(∑ i, ∑ j, R i j * ‖v i j‖) / Fintype.card V +
    (∑ i, ∑ j, R' i j * ‖v i j‖) / Fintype.card V, ?_⟩
  rintro _ ⟨z, rfl⟩
  have hz : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
  have h1 := hSupp_bounds v hR hz
  have h2 := hSupp_bounds v hR' hz
  rw [abs_le]; constructor <;> linarith

lemma le_rhoSupp (v : V → W → E) {R R' : V → W → ℝ} (hR : ∀ i j, 0 ≤ R i j)
    (hR' : ∀ i j, 0 ≤ R' i j) {z : E} (hz : ‖z‖ ≤ 1) :
    |hSupp v R z - hSupp v R' z| ≤ rhoSupp v R R' :=
  le_ciSup (f := fun z : Metric.closedBall (0 : E) 1 => |hSupp v R z.1 - hSupp v R' z.1|)
    (bddAbove_rhoSupp v hR hR') ⟨z, mem_closedBall_zero_iff.mpr hz⟩


end Zonotope

/-! ### Support functions and Lemma 41 -/

section SupportFunction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support function `h_Z(w) = max_{u ∈ Z} ⟨w, u⟩` of a set `Z ⊆ H` (p. 37, l. 1156). -/
noncomputable def supportFn (Z : Set E) (w : E) : ℝ := sSup ((fun u => inner ℝ w u) '' Z)

/-- The maximum `max_{u, u' ∈ Z} |⟨u, T u'⟩|` of the bilinear form of `T` on `Z`. -/
noncomputable def bilMax (Z : Set E) (T : E →L[ℝ] E) : ℝ :=
  sSup ((fun p : E × E => |inner ℝ p.1 (T p.2)|) '' (Z ×ˢ Z))

variable {Z Z' : Set E}

lemma isCompact_image_inner (hZ : IsCompact Z) (w : E) :
    IsCompact ((fun u => inner ℝ w u) '' Z) :=
  hZ.image (continuous_const.inner continuous_id)

lemma le_supportFn (hZ : IsCompact Z) (w : E) {u : E} (hu : u ∈ Z) :
    inner ℝ w u ≤ supportFn Z w :=
  le_csSup (isCompact_image_inner hZ w).bddAbove ⟨u, hu, rfl⟩

/-- For compact non-empty `Z`, the maximum defining `h_Z(w)` is attained. -/
lemma exists_eq_supportFn (hZ : IsCompact Z) (hne : Z.Nonempty) (w : E) :
    ∃ u ∈ Z, inner ℝ w u = supportFn Z w := by
  obtain ⟨u, hu, h⟩ := (isCompact_image_inner hZ w).sSup_mem (hne.image _)
  exact ⟨u, hu, h⟩

/-- Support functions are positively homogeneous. -/
lemma supportFn_smul (hZ : IsCompact Z) (hne : Z.Nonempty) {c : ℝ} (hc : 0 ≤ c) (w : E) :
    supportFn Z (c • w) = c * supportFn Z w := by
  obtain ⟨u, hu, hu'⟩ := exists_eq_supportFn hZ hne (c • w)
  obtain ⟨u₀, hu₀, hu₀'⟩ := exists_eq_supportFn hZ hne w
  refine le_antisymm ?_ ?_
  · rw [← hu', real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (le_supportFn hZ w hu) hc
  · rw [← hu₀', ← real_inner_smul_left]
    exact le_supportFn hZ _ hu₀

/-- First step of the proof of Lemma 41: `|h_Z(w) - h_{Z'}(w)| ≤ η ‖w‖` for all `w ∈ H`. -/
lemma abs_supportFn_sub_le (hZ : IsCompact Z) (hne : Z.Nonempty) (hZ' : IsCompact Z')
    (hne' : Z'.Nonempty) {η : ℝ}
    (hη : ∀ w : E, ‖w‖ ≤ 1 → |supportFn Z w - supportFn Z' w| ≤ η) (x : E) :
    |supportFn Z x - supportFn Z' x| ≤ η * ‖x‖ := by
  have hx : x = ‖x‖ • (‖x‖⁻¹ • x) := by
    rcases eq_or_ne x 0 with rfl | h
    · simp
    · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]
  have hw : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne x 0 with rfl | h
    · simp
    · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]
  conv_lhs => rw [hx]
  rw [supportFn_smul hZ hne (norm_nonneg x), supportFn_smul hZ' hne' (norm_nonneg x), ← mul_sub,
    abs_mul, abs_norm, mul_comm η]
  exact mul_le_mul_of_nonneg_left (hη _ hw) (norm_nonneg x)

lemma isCompact_image_bil (hZ : IsCompact Z) (T : E →L[ℝ] E) :
    IsCompact ((fun p : E × E => |inner ℝ p.1 (T p.2)|) '' (Z ×ˢ Z)) :=
  (hZ.prod hZ).image (continuous_fst.inner (T.continuous.comp continuous_snd)).abs

lemma le_bilMax (hZ : IsCompact Z) (T : E →L[ℝ] E) {u u' : E} (hu : u ∈ Z) (hu' : u' ∈ Z) :
    |inner ℝ u (T u')| ≤ bilMax Z T :=
  le_csSup (isCompact_image_bil hZ T).bddAbove ⟨(u, u'), ⟨hu, hu'⟩, rfl⟩

lemma bilMax_le (hne : Z.Nonempty) (T : E →L[ℝ] E) {c : ℝ}
    (h : ∀ u ∈ Z, ∀ u' ∈ Z, |inner ℝ u (T u')| ≤ c) : bilMax Z T ≤ c :=
  csSup_le ((hne.prod hne).image _) (by rintro _ ⟨p, ⟨h1, h2⟩, rfl⟩; exact h _ h1 _ h2)

variable [CompleteSpace E]

/-- The two steps of the proof of Lemma 41, for single points: with
`m_T(Y, Y') = max_{u ∈ Y, u' ∈ Y'} ⟨u, T u'⟩`, the paper shows
`m_T(Z, Z) ≤ m_T(Z', Z) + M η τ` (maximising over `u` first, `m_T(Y, Z) = max_{u' ∈ Z} h_Y(T u')`) and
`m_T(Z', Z) ≤ m_T(Z', Z') + M η τ` (maximising over `u'` first,
`m_T(Z', Y') = max_{u ∈ Z'} h_{Y'}(T* u)` with the adjoint `T*`). -/
lemma lemma41_step (hZ : IsCompact Z) (hZ' : IsCompact Z') (hne : Z.Nonempty)
    (hne' : Z'.Nonempty) {M η τ : ℝ} (hMZ : ∀ u ∈ Z, ‖u‖ ≤ M) (hMZ' : ∀ u ∈ Z', ‖u‖ ≤ M)
    (hη : ∀ w : E, ‖w‖ ≤ 1 → |supportFn Z w - supportFn Z' w| ≤ η)
    (T : E →L[ℝ] E) (hT : ‖T‖ ≤ τ) {u u' : E} (hu : u ∈ Z) (hu' : u' ∈ Z) :
    ∃ v ∈ Z', ∃ v' ∈ Z', inner ℝ u (T u') ≤ inner ℝ v (T v') + 2 * M * η * τ := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 0 (by simp))
  have hhom := abs_supportFn_sub_le hZ hne hZ' hne' hη
  have hτ0 : 0 ≤ τ := (norm_nonneg _).trans hT
  -- `‖T x‖, ‖T* x‖ ≤ τ M` on the ball of radius `M`
  have hTx : ∀ (S : E →L[ℝ] E), ‖S‖ ≤ τ → ∀ x : E, ‖x‖ ≤ M → ‖S x‖ ≤ τ * M := fun S hS x hx =>
    (S.le_opNorm x).trans (mul_le_mul hS hx (norm_nonneg _) hτ0)
  have hT' : ‖ContinuousLinearMap.adjoint T‖ ≤ τ := by
    rw [LinearIsometryEquiv.norm_map]; exact hT
  -- step 1: `⟨u, T u'⟩ ≤ h_Z(T u') ≤ h_{Z'}(T u') + M η τ = ⟨v, T u'⟩ + M η τ`
  obtain ⟨v, hv, hv'⟩ := exists_eq_supportFn hZ' hne' (T u')
  have h1 : inner ℝ u (T u') ≤ inner ℝ v (T u') + η * (τ * M) := by
    have a := le_supportFn hZ (T u') hu
    have b := (abs_le.mp (hhom (T u'))).2
    have c := mul_le_mul_of_nonneg_left (hTx T hT u' (hMZ u' hu')) hη0
    rw [real_inner_comm u (T u')] at a
    rw [real_inner_comm v (T u')] at hv'
    linarith
  -- step 2: `⟨v, T u'⟩ = ⟨T* v, u'⟩ ≤ h_Z(T* v) ≤ h_{Z'}(T* v) + M η τ = ⟨v, T v'⟩ + M η τ`
  obtain ⟨v', hv'', hv'''⟩ := exists_eq_supportFn hZ' hne' (ContinuousLinearMap.adjoint T v)
  have h2 : inner ℝ v (T u') ≤ inner ℝ v (T v') + η * (τ * M) := by
    have a := le_supportFn hZ (ContinuousLinearMap.adjoint T v) hu'
    have b := (abs_le.mp (hhom (ContinuousLinearMap.adjoint T v))).2
    have c := mul_le_mul_of_nonneg_left
      (hTx (ContinuousLinearMap.adjoint T) hT' v (hMZ' v hv)) hη0
    rw [ContinuousLinearMap.adjoint_inner_left] at a hv'''
    linarith
  refine ⟨v, hv, v', hv'', ?_⟩
  have : η * (τ * M) + η * (τ * M) = 2 * M * η * τ := by ring
  linarith

/-- Lemma 41 for single points, with absolute values (apply `lemma41_step` to `T` and `-T`). -/
lemma abs_inner_le_bilMax_add (hZ : IsCompact Z) (hZ' : IsCompact Z') (hne : Z.Nonempty)
    (hne' : Z'.Nonempty) {M η τ : ℝ} (hMZ : ∀ u ∈ Z, ‖u‖ ≤ M) (hMZ' : ∀ u ∈ Z', ‖u‖ ≤ M)
    (hη : ∀ w : E, ‖w‖ ≤ 1 → |supportFn Z w - supportFn Z' w| ≤ η)
    (T : E →L[ℝ] E) (hT : ‖T‖ ≤ τ) {u u' : E} (hu : u ∈ Z) (hu' : u' ∈ Z) :
    |inner ℝ u (T u')| ≤ bilMax Z' T + 2 * M * η * τ := by
  obtain ⟨v, hv, v', hv', h⟩ := lemma41_step hZ hZ' hne hne' hMZ hMZ' hη T hT hu hu'
  obtain ⟨w, hw, w', hw', h'⟩ := lemma41_step (τ := τ) hZ hZ' hne hne' hMZ hMZ' hη (-T)
    (by rw [norm_neg]; exact hT) hu hu'
  have e1 := le_bilMax hZ' T hv hv'
  have e2 := le_bilMax hZ' T hw hw'
  have hneg : ∀ x y : E, inner ℝ x ((-T) y) = -inner ℝ x (T y) := fun x y => by
    simp [inner_neg_right]
  rw [hneg, hneg] at h'
  rw [abs_le] at e1 e2 ⊢
  constructor <;> linarith

/-- **Lemma 41** (Close support functions). Let `Z, Z' ⊆ H` be non-empty compact sets in the ball of
radius `M` with `|h_Z(w) - h_{Z'}(w)| ≤ η` for all `w ∈ B_H`, and let `‖T‖ ≤ τ`. Then
`|max_{u,u' ∈ Z} |⟨u, T u'⟩| - max_{u,u' ∈ Z'} |⟨u, T u'⟩|| ≤ 2 M η τ`.
(The Lean statement does not assume `Z, Z'` convex, so it is a more general form of Lemma 41.) -/
theorem lemma41 (hZ : IsCompact Z) (hZ' : IsCompact Z') (hne : Z.Nonempty) (hne' : Z'.Nonempty)
    {M η τ : ℝ} (hMZ : ∀ u ∈ Z, ‖u‖ ≤ M) (hMZ' : ∀ u ∈ Z', ‖u‖ ≤ M)
    (hη : ∀ w : E, ‖w‖ ≤ 1 → |supportFn Z w - supportFn Z' w| ≤ η)
    (T : E →L[ℝ] E) (hT : ‖T‖ ≤ τ) :
    |bilMax Z T - bilMax Z' T| ≤ 2 * M * η * τ := by
  have hη' : ∀ w : E, ‖w‖ ≤ 1 → |supportFn Z' w - supportFn Z w| ≤ η := fun w hw => by
    rw [abs_sub_comm]; exact hη w hw
  rw [abs_sub_le_iff]
  constructor
  · have := bilMax_le hne T fun u hu u' hu' =>
      abs_inner_le_bilMax_add hZ hZ' hne hne' hMZ hMZ' hη T hT hu hu'
    linarith
  · have := bilMax_le hne' T fun u hu u' hu' =>
      abs_inner_le_bilMax_add hZ' hZ hne' hne hMZ' hMZ hη' T hT hu hu'
    linarith

end SupportFunction

/-! ### Zonotopes: Eqs. (33), (36) -/

section ZonotopeSupport
variable {V W : Type*} [Fintype V] [Fintype W]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma zonotope_nonempty (v : V → W → E) (R : V → W → ℝ) : (zonLin v R '' cube).Nonempty :=
  ⟨_, 0, mem_cube.mpr fun _ _ => ⟨le_rfl, zero_le_one⟩, rfl⟩

/-- **Eq. (33)**: the support function of the zonotope `Z_R` is `h_R(w) = (1/n) ∑ R_ij ⟨w, v_ij⟩_+`. -/
lemma supportFn_zonotope (v : V → W → E) {R : V → W → ℝ} (hR : ∀ i j, 0 ≤ R i j) (w : E) :
    supportFn (zonLin v R '' cube) w = hSupp v R w := by
  refine le_antisymm (csSup_le ((zonotope_nonempty v R).image _) ?_) ?_
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact inner_zonLin_le_hSupp v hR ha w
  · obtain ⟨a, ha, h⟩ := exists_inner_zonLin_eq_hSupp v R w
    rw [← h]
    exact le_supportFn (isCompact_zonotope v R) w ⟨a, ha, rfl⟩

/-- The kernel `μ_R(x) μ_R(y) ⟨v_x, T v_y⟩` on `Ω_R = V × W` whose weighted cut norm is the maximum in
Eqs. (30) and (36). -/
noncomputable def zonKernel (v : V → W → E) (T : E →L[ℝ] E) (R : V → W → ℝ) :
    Matrix (V × W) (V × W) ℝ := fun x y =>
  (R x.1 x.2 / Fintype.card V) * (R y.1 y.2 / Fintype.card V) *
    inner ℝ (v x.1 x.2) (T (v y.1 y.2))

/-- Bilinear expansion behind Eq. (36):
`⟨u_a, T u_{a'}⟩ = ∑_{x, y ∈ Ω_R} a(x) μ_R(x) μ_R(y) ⟨v_x, T v_y⟩ a'(y)`. -/
lemma eq36_expand (v : V → W → E) (T : E →L[ℝ] E) (R a a' : V → W → ℝ) :
    inner ℝ (zonLin v R a) (T (zonLin v R a')) =
      ∑ x : V × W, ∑ y : V × W, a x.1 x.2 * zonKernel v T R x y * a' y.1 y.2 := by
  conv_rhs => rw [Finset.sum_comm]
  simp only [zonLin, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, zonKernel, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **Eq. (36)**: `max_{u, u' ∈ Z_R} |⟨u, T u'⟩|` is the weighted cut norm of `⟨v_x, T v_y⟩`. The
maximum over the zonotope is attained at indicator vectors `a = 1_S`, `a' = 1_T`. -/
lemma eq36 (v : V → W → E) (T : E →L[ℝ] E) (R : V → W → ℝ) :
    bilMax (zonLin v R '' cube) T = cutNorm (zonKernel v T R) := by
  classical
  refine le_antisymm (bilMax_le (zonotope_nonempty v R) T ?_) ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    rw [eq36_expand]
    exact abs_bilin_le_cutNorm (zonKernel v T R) (fun x => a x.1 x.2) (fun y => a' y.1 y.2)
      (fun x => mem_cube.mp ha x.1 x.2) (fun y => mem_cube.mp ha' y.1 y.2)
  · obtain ⟨S, S', hS⟩ := exists_eq_cutNorm (zonKernel v T R)
    let a : V → W → ℝ := fun i j => if (i, j) ∈ S then 1 else 0
    let a' : V → W → ℝ := fun i j => if (i, j) ∈ S' then 1 else 0
    have ha : a ∈ (cube : Set (V → W → ℝ)) := mem_cube.mpr fun i j => by
      simp only [a]; split_ifs <;> norm_num
    have ha' : a' ∈ (cube : Set (V → W → ℝ)) := mem_cube.mpr fun i j => by
      simp only [a']; split_ifs <;> norm_num
    have h := le_bilMax (isCompact_zonotope v R) T ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
    rw [eq36_expand] at h
    rw [← hS, cut_sum_eq_bilin]
    exact h

end ZonotopeSupport


/-- The diagonal bilinear form `β_d(x, y) = ∑_p d_p x_p y_p` on `EuclideanSpace ℝ ι`, i.e.
`β_d(x, y) = ⟨x, T y⟩` for the diagonal operator `T = diag(d)`. -/
noncomputable def diagForm {ι : Type*} [Fintype ι] (d : ι → ℝ) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ p, d p * x p * y p)
    (fun x x' y => by simp [add_mul, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring)
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring)

lemma diagForm_apply {ι : Type*} [Fintype ι] (d : ι → ℝ) (x y : EuclideanSpace ℝ ι) :
    diagForm d x y = ∑ p, d p * x p * y p := rfl

lemma aux_cancel {lam x y N : ℝ} (hl : lam ≠ 0) (hN : 0 < N) :
    N / lam * (lam * x / √N) * (lam * y / √N) = lam * x * y := by
  have hs : √N * √N = N := Real.mul_self_sqrt hN.le
  have hs0 : √N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  field_simp
  rw [sq, hs]; ring

section Construction
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {A : Matrix V V ℝ} {B : Matrix W W ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)

/-- The vectors `v_ij = ((λ_r φ_r(i))_{r ∈ I_A}, (ν_s ψ_s(j))_{s ∈ I_B})` of Lemma 45 (the paper's `z_ij`), written
with orthonormal eigenvectors `e_r` for the standard inner product (`φ_r = √N e_r`,
`λ_r^{paper} = λ_r / N`), embedded into `EuclideanSpace ℝ (V ⊕ W)` by zero padding. -/
noncomputable def specVec (c N : ℝ) (i : V) (j : W) : EuclideanSpace ℝ (V ⊕ W) :=
  WithLp.toLp 2 (Sum.elim
    (fun r => if c < |hA.eigenvalues r| then
      hA.eigenvalues r * hA.eigenvectorBasis r i / √N else 0)
    (fun s => if c < |hB.eigenvalues s| then
      hB.eigenvalues s * hB.eigenvectorBasis s j / √N else 0))

/-- The diagonal of the operator `T_t = diag((λ_r⁻¹)_{r ∈ I_A}, (-ν_s⁻¹)_{s ∈ I_B})`. -/
noncomputable def specDiag (c N : ℝ) : V ⊕ W → ℝ := Sum.elim
  (fun r => if c < |hA.eigenvalues r| then N / hA.eigenvalues r else 0)
  (fun s => if c < |hB.eigenvalues s| then -(N / hB.eigenvalues s) else 0)

/-- `⟨v_ij, T_t v_kl⟩ = (A_t)_ik - (B_t)_jl`. -/
lemma diagForm_specVec {c N : ℝ} (hc : 0 ≤ c) (hN : 0 < N) (i : V) (j : W) (k : V) (l : W) :
    diagForm (specDiag hA hB c N) (specVec hA hB c N i j) (specVec hA hB c N k l) =
      specTrunc hA c i k - specTrunc hB c j l := by
  rw [diagForm_apply, Fintype.sum_sum_type, sub_eq_add_neg, specTrunc, specTrunc,
    ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun r _ => ?_
    simp only [specDiag, specVec, Sum.elim_inl, PiLp.toLp_apply]
    split_ifs with h
    · exact aux_cancel (abs_pos.mp (hc.trans_lt h)) hN
    · simp
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp only [specDiag, specVec, Sum.elim_inr, PiLp.toLp_apply]
    split_ifs with h
    · rw [neg_mul, neg_mul, aux_cancel (abs_pos.mp (hc.trans_lt h)) hN]
    · simp

/-- `‖T_t‖ ≤ 1/t`: the diagonal entries are bounded by `1/t`. -/
lemma abs_specDiag_le {t N : ℝ} (ht : 0 < t) (hN : 0 ≤ N) (p : V ⊕ W) :
    |specDiag hA hB (t * N) N p| ≤ 1 / t := by
  have key : ∀ lam : ℝ, t * N < |lam| → |N / lam| ≤ 1 / t := fun lam h => by
    have hl : 0 < |lam| := (mul_nonneg ht.le hN).trans_lt h
    rw [abs_div, abs_of_nonneg hN, div_le_div_iff₀ hl ht]
    linarith
  rcases p with r | s
  · simp only [specDiag, Sum.elim_inl]
    split_ifs with h
    · exact key _ h
    · simp [ht.le]
  · simp only [specDiag, Sum.elim_inr]
    split_ifs with h
    · rw [abs_neg]; exact key _ h
    · simp [ht.le]

lemma sq_ite_le {p : Prop} [Decidable p] (x N : ℝ) (hN : 0 ≤ N) :
    (if p then x / √N else 0) ^ 2 ≤ x ^ 2 / N := by
  split_ifs
  · rw [div_pow, Real.sq_sqrt hN]
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity

/-- `‖v_ij‖ ≤ √2`, by Parseval's identity for the rows of `A` and `B`. -/
lemma norm_specVec_le (hA01 : ∀ i k, 0 ≤ A i k ∧ A i k ≤ 1)
    (hB01 : ∀ j l, 0 ≤ B j l ∧ B j l ≤ 1) (hcard : Fintype.card V = Fintype.card W)
    (c : ℝ) (i : V) (j : W) :
    ‖specVec hA hB c (Fintype.card V) i j‖ ≤ √2 := by
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)
  have hrowA : ∑ k, A i k ^ 2 ≤ Fintype.card V := by
    calc ∑ k, A i k ^ 2 ≤ ∑ _k : V, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
          have := hA01 i k; nlinarith
      _ = Fintype.card V := by simp
  have hrowB : ∑ l, B j l ^ 2 ≤ Fintype.card V := by
    calc ∑ l, B j l ^ 2 ≤ ∑ _l : W, (1 : ℝ) := Finset.sum_le_sum fun l _ => by
          have := hB01 j l; nlinarith
      _ = Fintype.card V := by simp [hcard]
  have hsq : ‖specVec hA hB c (Fintype.card V) i j‖ ^ 2 ≤ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
    simp only [specVec, PiLp.toLp_apply, Sum.elim_inl, Sum.elim_inr]
    have h1 : ∑ r, (if c < |hA.eigenvalues r| then
        hA.eigenvalues r * hA.eigenvectorBasis r i / √(Fintype.card V) else 0) ^ 2 ≤ 1 := by
      calc _ ≤ ∑ r, (hA.eigenvalues r * hA.eigenvectorBasis r i) ^ 2 / Fintype.card V :=
            Finset.sum_le_sum fun r _ => sq_ite_le _ _ hN.le
        _ = (∑ k, A i k ^ 2) / Fintype.card V := by rw [← Finset.sum_div, parseval_row]
        _ ≤ 1 := by rw [div_le_one hN]; exact hrowA
    have h2 : ∑ s, (if c < |hB.eigenvalues s| then
        hB.eigenvalues s * hB.eigenvectorBasis s j / √(Fintype.card V) else 0) ^ 2 ≤ 1 := by
      calc _ ≤ ∑ s, (hB.eigenvalues s * hB.eigenvectorBasis s j) ^ 2 / Fintype.card V :=
            Finset.sum_le_sum fun s _ => sq_ite_le _ _ hN.le
        _ = (∑ l, B j l ^ 2) / Fintype.card V := by rw [← Finset.sum_div, parseval_row]
        _ ≤ 1 := by rw [div_le_one hN]; exact hrowB
    linarith
  exact Real.le_sqrt_of_sq_le hsq

end Construction

/-- The diagonal operator `T = diag(d)` on `EuclideanSpace ℝ ι`. -/
noncomputable def diagOp {ι : Type*} [Fintype ι] (d : ι → ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun p => d p * x p)
      map_add' := fun x y => by ext p; simp [mul_add]
      map_smul' := fun c x => by ext p; simp; ring }

lemma diagOp_apply {ι : Type*} [Fintype ι] (d : ι → ℝ) (x : EuclideanSpace ℝ ι) (p : ι) :
    diagOp d x p = d p * x p := rfl

/-- `⟨x, diag(d) y⟩ = ∑_p d_p x_p y_p`. -/
lemma inner_diagOp {ι : Type*} [Fintype ι] (d : ι → ℝ) (x y : EuclideanSpace ℝ ι) :
    inner ℝ x (diagOp d y) = diagForm d x y := by
  rw [diagForm_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [diagOp_apply, real_inner_eq_re_inner, RCLike.inner_apply]
  simp only [conj_trivial, RCLike.re_to_real]
  ring

/-- `‖diag(d)‖ ≤ c` if `|d_p| ≤ c` for all `p`. -/
lemma norm_diagOp_le {ι : Type*} [Fintype ι] (d : ι → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hd : ∀ p, |d p| ≤ c) : ‖diagOp d‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun y => ?_
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [diagOp_apply, mul_pow]
  have : d p ^ 2 ≤ c ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hd p) 2
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- **Lemma 45** (Spectral approximation, Eq. (30)). For every `t > 0` there are vectors `v_ij`
(the paper's `z_ij`) with `‖v_ij‖ ≤ √2` and an operator `T_t` with `‖T_t‖ ≤ 1/t` such that every
`Q ∈ DS(V, W)` satisfies `|ζ_Q - max_{S,T} |∑_{(i,j) ∈ S} ∑_{(k,l) ∈ T} μ_Q μ_Q ⟨v_ij, T_t v_kl⟩|| ≤ 2t`.
Here `H = ℝ^{V ⊕ W}` (dimension `2n`; the paper uses `ℝ^{I_A ⊕ I_B}`, the extra coordinates of the
vectors are zero), `ζ_Q = epsR A B Q`, and the maximum is the weighted cut norm of `zonKernel`. -/
theorem lemma45 (A : Matrix V V ℝ) (B : Matrix W W ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (hA01 : ∀ i k, 0 ≤ A i k ∧ A i k ≤ 1) (hB01 : ∀ j l, 0 ≤ B j l ∧ B j l ≤ 1)
    (hcard : Fintype.card V = Fintype.card W) {t : ℝ} (ht : 0 < t) :
    ∃ (v : V → W → EuclideanSpace ℝ (V ⊕ W))
      (T : EuclideanSpace ℝ (V ⊕ W) →L[ℝ] EuclideanSpace ℝ (V ⊕ W)),
      (∀ i j, ‖v i j‖ ≤ √2) ∧ ‖T‖ ≤ 1 / t ∧
      ∀ Q : V → W → ℝ, IsDS Q → |epsR A B Q - cutNorm (zonKernel v T Q)| ≤ 2 * t := by
  have hAh : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hA
  have hBh : B.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hB
  have hN0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hc : 0 ≤ t * Fintype.card V := mul_nonneg ht.le hN0
  refine ⟨specVec hAh hBh (t * Fintype.card V) (Fintype.card V),
    diagOp (specDiag hAh hBh (t * Fintype.card V) (Fintype.card V)),
    norm_specVec_le hAh hBh hA01 hB01 hcard (t * Fintype.card V),
    norm_diagOp_le _ (by positivity) (abs_specDiag_le hAh hBh ht hN0), fun Q hQ => ?_⟩
  -- `⟨v_ij, T_t v_kl⟩ = (A_t)_ik - (B_t)_jl`, so the maximum in Eq. (30) is `ζ_Q(A_t, B_t)`
  have hK : cutNorm (zonKernel (specVec hAh hBh (t * Fintype.card V) (Fintype.card V))
      (diagOp (specDiag hAh hBh (t * Fintype.card V) (Fintype.card V))) Q) =
      epsR (specTrunc hAh (t * Fintype.card V)) (specTrunc hBh (t * Fintype.card V)) Q := by
    unfold epsR
    congr 1
    funext x y
    simp only [zonKernel, inner_diagOp]
    rw [diagForm_specVec hAh hBh hc (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨x.1⟩))]
  -- Eq. (31)
  obtain ⟨h1, h2⟩ := eq28 hQ ht.le (opBound_sub_specTrunc hAh hc) (opBound_sub_specTrunc hBh hc)
  rw [hK, abs_le]
  constructor <;> linarith

section Corollary46
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq V] [DecidableEq W] in
/-- **Eq. (37)**: from Eqs. (30) and (36), `|ζ_Q - max_{u, u' ∈ Z_Q} |⟨u, T_t u'⟩|| ≤ 2t`. -/
lemma eq37 {A : Matrix V V ℝ} {B : Matrix W W ℝ} {t : ℝ} {v : V → W → E} {T : E →L[ℝ] E}
    (h30 : ∀ Q : V → W → ℝ, IsDS Q → |epsR A B Q - cutNorm (zonKernel v T Q)| ≤ 2 * t)
    {Q : V → W → ℝ} (hQ : IsDS Q) : |epsR A B Q - bilMax (zonLin v Q '' cube) T| ≤ 2 * t := by
  rw [eq36]; exact h30 Q hQ

variable [CompleteSpace E]

/-- **Corollary 46.** Fix `t > 0` and vectors `v_ij`, `‖v_ij‖ ≤ M = √2`, and an operator `T_t`,
`‖T_t‖ ≤ 1/t`, as in Lemma 45 (Eq. (30)). Then every `P, Q ∈ DS(V, W)` satisfy
`ζ_P ≤ ζ_Q + 4t + (2√2/t) ρ(P, Q)`. -/
theorem corollary46 {A : Matrix V V ℝ} {B : Matrix W W ℝ} {t : ℝ}
    (v : V → W → E) (T : E →L[ℝ] E) (hv : ∀ i j, ‖v i j‖ ≤ √2) (hT : ‖T‖ ≤ 1 / t)
    (h30 : ∀ Q : V → W → ℝ, IsDS Q → |epsR A B Q - cutNorm (zonKernel v T Q)| ≤ 2 * t)
    {P Q : V → W → ℝ} (hP : IsDS P) (hQ : IsDS Q) :
    epsR A B P ≤ epsR A B Q + 4 * t + 2 * √2 / t * rhoSupp v P Q := by
  have hs2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
  -- Lemma 41 with `M = √2`, `η = ρ(P, Q)`, `τ = 1/t`
  have h41 := lemma41 (isCompact_zonotope v P) (isCompact_zonotope v Q) (zonotope_nonempty v P)
    (zonotope_nonempty v Q) (M := √2) (η := rhoSupp v P Q)
    (by rintro _ ⟨a, ha, rfl⟩; exact norm_zonLin_le v hP ha hs2 hv)
    (by rintro _ ⟨a, ha, rfl⟩; exact norm_zonLin_le v hQ ha hs2 hv)
    (fun w hw => by
      rw [supportFn_zonotope v hP.nonneg, supportFn_zonotope v hQ.nonneg]
      exact le_rhoSupp v hP.nonneg hQ.nonneg hw) T hT
  -- Eq. (37) for `P` and `Q`
  have hP37 := eq37 h30 hP
  have hQ37 := eq37 h30 hQ
  have hring : 2 * √2 * rhoSupp v P Q * (1 / t) = 2 * √2 / t * rhoSupp v P Q := by ring
  rw [abs_le] at h41 hP37 hQ37
  linarith [h41.2, hP37.2, hQ37.1]

end Corollary46

end GsimOT
