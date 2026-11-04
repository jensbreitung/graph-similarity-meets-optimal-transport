/-
# Theorem 38: multiplicative rounding via thin matchings (Appendix E.2.1)

Appendix E.2.1 (pp. 32–35): Theorem 38 (p. 34, l. 1074–1075; proof pp. 34–35, l. 1076–1109) with
Lemmas 36 and 37.

* `lemma36`   : Lemma 36, the level-set argument, using thinness Eq. (23).
* `lemma37`   : Lemma 37 (Local Agreement), with Eq. (24) as an intermediate step.
* `abs_sum_mul_le_of_cut` : Eq. (25), in the one-dimensional form used in the proof.
* `epsR_permMat_le`, `eq27_left`, `normEA_le`, `cut_R_EAt_le`, `eq28_cut`, `eq27_right` : the steps
  of the proof of Theorem 38 (`ζ_P` as a cut norm, the two bounds of Eq. (27), Eq. (28)).
* `eq26` : Eq. (26), `ζ_P ≤ (1 + 4α) ζ_Q` for every `α`-thin `P`.
* `theorem38` : Theorem 38, the existence of such a `P` via Theorem 35 [HOG26].

The paper's `ζ_Q` (Eq. (21)) is `epsR A B Q`.
-/
import GsimOT.Theorem11_CutUpperBound.Definitions

open Finset MeasureTheory

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-! ### Elementary cut-norm facts -/

/-- **Eq. (25)**, one-dimensional form (p. 34, l. 1066–1072): if all subset sums of `h` are
bounded by `c` in absolute value, then so is `∑ₖ r(k) h(k)` for every `r : ι → [0, 1]`. With
`r = Rᵀ 1_X` this gives `‖R K‖_□ ≤ ‖K‖_□` for `R ∈ DS(n)`. -/
lemma abs_sum_mul_le_of_cut {ι : Type*} [Fintype ι] (r h : ι → ℝ) {c : ℝ}
    (hr : ∀ k, 0 ≤ r k ∧ r k ≤ 1) (hc : ∀ K : Finset ι, |∑ k ∈ K, h k| ≤ c) :
    |∑ k, r k * h k| ≤ c := by
  have hup : ∑ k, r k * h k ≤ ∑ k ∈ univ.filter (fun k => 0 < h k), h k := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun k _ => ?_
    obtain ⟨h0, h1⟩ := hr k
    split_ifs with hk
    · nlinarith
    · push Not at hk; nlinarith
  have hlo : ∑ k ∈ univ.filter (fun k => h k < 0), h k ≤ ∑ k, r k * h k := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun k _ => ?_
    obtain ⟨h0, h1⟩ := hr k
    split_ifs with hk
    · nlinarith
    · push Not at hk; nlinarith
  rw [abs_le]
  constructor
  · have := (abs_le.1 (hc (univ.filter fun k => h k < 0))).1; linarith
  · have := (abs_le.1 (hc (univ.filter fun k => 0 < h k))).2; linarith

/-- A mean-zero function sums to at most half its `ℓ¹` norm over any subset (proof of
Theorem 38, p. 35, l. 1101–1103). -/
lemma abs_sum_le_half_of_sum_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∑ i, f i = 0) (S : Finset ι) : |∑ i ∈ S, f i| ≤ (∑ i, |f i|) / 2 := by
  have h1 : ∑ i ∈ S, f i + ∑ i ∈ Sᶜ, f i = 0 := by rw [Finset.sum_add_sum_compl]; exact hf
  have h2 : ∑ i ∈ S, |f i| + ∑ i ∈ Sᶜ, |f i| = ∑ i, |f i| := Finset.sum_add_sum_compl _ _
  have h3 := Finset.abs_sum_le_sum_abs f S
  have h4 := Finset.abs_sum_le_sum_abs f Sᶜ
  have h5 : |∑ i ∈ Sᶜ, f i| = |∑ i ∈ S, f i| := by
    rw [show ∑ i ∈ Sᶜ, f i = -∑ i ∈ S, f i by linarith, abs_neg]
  linarith

/-- Testing the kernel `D_{A,B}` (weighted by `Q ⊗ Q`) on a cut `(S, T)` gives at most
`n² ζ_Q` (definition of `ζ_Q`, Eq. (21), p. 32). -/
lemma abs_cut_le_epsR (A : Matrix V V ℝ) (B : Matrix W W ℝ) (Q : V → W → ℝ)
    (hn : (Fintype.card V : ℝ) ≠ 0) (S T : Finset (V × W)) :
    |∑ x ∈ S, ∑ y ∈ T, Q x.1 x.2 * Q y.1 y.2 * (A x.1 y.1 - B x.2 y.2)| ≤
      (Fintype.card V : ℝ) ^ 2 * epsR A B Q := by
  have h := le_cutNorm (fun x y : V × W => (Q x.1 x.2 / Fintype.card V) *
    (Q y.1 y.2 / Fintype.card V) * (A x.1 y.1 - B x.2 y.2)) S T
  have he : ∑ x ∈ S, ∑ y ∈ T, Q x.1 x.2 * Q y.1 y.2 * (A x.1 y.1 - B x.2 y.2) =
      (Fintype.card V : ℝ) ^ 2 * ∑ x ∈ S, ∑ y ∈ T, (Q x.1 x.2 / Fintype.card V) *
        (Q y.1 y.2 / Fintype.card V) * (A x.1 y.1 - B x.2 y.2) := by
    rw [mul_sum]; refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]; refine sum_congr rfl fun y _ => ?_
    field_simp
  rw [he, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-! ### Lemma 36 -/

/-- The level-set function `s ↦ |1[x > s] - 1[y > s]|`, i.e. the indicator of
`[min x y, max x y)`. -/
noncomputable def levelInd (x y : ℝ) : ℝ → ℝ := Set.indicator (Set.Ico (min x y) (max x y)) 1

lemma levelInd_apply (x y s : ℝ) :
    levelInd x y s = if ¬ ((s < x) ↔ (s < y)) then 1 else 0 := by
  unfold levelInd
  rw [Set.indicator_apply]
  simp only [Set.mem_Ico, lt_max_iff, Pi.one_apply, ← not_lt]
  by_cases hx : s < x <;> by_cases hy : s < y <;> simp [hx, hy]

lemma integrable_levelInd (x y : ℝ) : Integrable (levelInd x y) := by
  unfold levelInd
  exact (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const measure_Ico_lt_top.ne)

/-- `|x - y| = ∫ |1[x > s] - 1[y > s]| ds`. -/
lemma integral_levelInd (x y : ℝ) : ∫ s, levelInd x y s = |x - y| := by
  unfold levelInd
  rw [integral_indicator measurableSet_Ico]
  simp [Measure.real, Real.volume_Ico, max_sub_min_eq_abs, abs_sub_comm]

/-- **Lemma 36** (p. 33, l. 1026–1028). If `π` is `a`-thin w.r.t. `Q` (Eq. (23)), then for
all `x, y`, `∑ᵢ |xᵢ - y_{π(i)}| ≤ a ∑_{i,j} Q_{ij} |xᵢ - yⱼ|`. As in the paper: Eq. (23) for the
level sets `X_s, Y_s` (`hpt`), then integration over `s`. -/
theorem lemma36 {Q : V → W → ℝ} {π : V ≃ W} {a : ℝ} (hthin : IsThin a Q π)
    (x : V → ℝ) (y : W → ℝ) :
    ∑ v, |x v - y (π v)| ≤ a * ∑ v, ∑ w, Q v w * |x v - y w| := by
  have hpt : ∀ s, ∑ v, levelInd (x v) (y (π v)) s ≤
      a * ∑ v, ∑ w, Q v w * levelInd (x v) (y w) s := by
    intro s
    have h := hthin (univ.filter fun v => s < x v) (univ.filter fun w => s < y w)
    simp only [mem_filter, mem_univ, true_and] at h
    rw [Finset.natCast_card_filter] at h
    simpa [levelInd_apply, mul_ite] using h
  calc ∑ v, |x v - y (π v)| = ∫ s, ∑ v, levelInd (x v) (y (π v)) s := by
        rw [integral_finsetSum _ (fun v _ => integrable_levelInd _ _)]
        simp [integral_levelInd]
    _ ≤ ∫ s, a * ∑ v, ∑ w, Q v w * levelInd (x v) (y w) s := by
        refine integral_mono ?_ ?_ hpt
        · exact integrable_finsetSum _ fun v _ => integrable_levelInd _ _
        · exact (integrable_finsetSum _ fun v _ => integrable_finsetSum _ fun w _ =>
            (integrable_levelInd _ _).const_mul _).const_mul _
    _ = a * ∑ v, ∑ w, Q v w * |x v - y w| := by
        rw [integral_const_mul, integral_finsetSum _ (fun v _ => integrable_finsetSum _
          fun w _ => (integrable_levelInd _ _).const_mul _)]
        congr 1; refine sum_congr rfl fun v _ => ?_
        rw [integral_finsetSum _ (fun w _ => (integrable_levelInd _ _).const_mul _)]
        refine sum_congr rfl fun w _ => ?_
        rw [integral_const_mul, integral_levelInd]

/-! ### Lemma 37 -/

/-- **Lemma 37** (Local Agreement, p. 33, l. 1038–1039; proof pp. 33–34) for `y = 1_T`, the only
case used (p. 35, l. 1099): with `x = A 1_T`, i.e. `x_i = ∑_{k ∈ T} A_{ik}`, and
`(Qᵀx)_j = ∑_k Q_{kj} x_k`, `∑_{i,j} Q_{ij} |x_i - (Qᵀx)_j| ≤ 4 n² ζ_Q`. The proof follows the
paper: Eq. (24) (`hQF`, via `S₊`, `S₋`), then the triangle inequality and the column sums. -/
theorem lemma37 (A : Matrix V V ℝ) (B : Matrix W W ℝ) {Q : V → W → ℝ} (hQ : IsDS Q)
    (hn : (Fintype.card V : ℝ) ≠ 0) (T : Finset V) :
    ∑ i, ∑ j, Q i j * |(∑ k ∈ T, A i k) - ∑ k', Q k' j * ∑ k ∈ T, A k' k| ≤
      4 * ((Fintype.card V : ℝ) ^ 2 * epsR A B Q) := by
  -- `F(i, j) = ∑_{(k, ℓ) ∈ T × W} Q_{kℓ} (A_{ik} - B_{jℓ}) = x_i - r_j` with `r = BQᵀ1_T`.
  have hF : ∀ i j, ∑ y ∈ T ×ˢ (univ : Finset W), Q y.1 y.2 * (A i y.1 - B j y.2) =
      (∑ k ∈ T, A i k) - ∑ y ∈ T ×ˢ (univ : Finset W), Q y.1 y.2 * B j y.2 := by
    intro i j
    simp_rw [mul_sub, sum_sub_distrib]
    congr 1
    rw [sum_product]
    refine sum_congr rfl fun k _ => ?_
    dsimp only
    rw [← sum_mul, hQ.row_sum, one_mul]
  -- Eq. (24): `n⁻² ∑ Q_{ij} |F_{ij}| ≤ 2 ζ_Q`, via the positive and negative parts.
  have hQF : ∑ i, ∑ j, Q i j * |∑ y ∈ T ×ˢ (univ : Finset W),
      Q y.1 y.2 * (A i y.1 - B j y.2)| ≤ 2 * ((Fintype.card V : ℝ) ^ 2 * epsR A B Q) := by
    have hsplit : ∀ U : Finset (V × W), ∑ x ∈ U, Q x.1 x.2 *
        ∑ y ∈ T ×ˢ (univ : Finset W), Q y.1 y.2 * (A x.1 y.1 - B x.2 y.2) =
        ∑ x ∈ U, ∑ y ∈ T ×ˢ (univ : Finset W), Q x.1 x.2 * Q y.1 y.2 *
          (A x.1 y.1 - B x.2 y.2) := by
      intro U
      refine sum_congr rfl fun x _ => ?_
      rw [mul_sum]; refine sum_congr rfl fun y _ => ?_; ring
    have hp := abs_cut_le_epsR A B Q hn (univ.filter fun x : V × W =>
      0 < ∑ y ∈ T ×ˢ (univ : Finset W), Q y.1 y.2 * (A x.1 y.1 - B x.2 y.2)) (T ×ˢ univ)
    have hm := abs_cut_le_epsR A B Q hn (univ.filter fun x : V × W =>
      ∑ y ∈ T ×ˢ (univ : Finset W), Q y.1 y.2 * (A x.1 y.1 - B x.2 y.2) < 0) (T ×ˢ univ)
    rw [← hsplit] at hp hm
    have heq : ∑ i, ∑ j, Q i j * |∑ y ∈ T ×ˢ (univ : Finset W),
        Q y.1 y.2 * (A i y.1 - B j y.2)| =
        (∑ x ∈ univ.filter fun x : V × W =>
          0 < ∑ y ∈ T ×ˢ (univ : Finset W), Q y.1 y.2 * (A x.1 y.1 - B x.2 y.2),
          Q x.1 x.2 * ∑ y ∈ T ×ˢ (univ : Finset W), Q y.1 y.2 * (A x.1 y.1 - B x.2 y.2)) -
        (∑ x ∈ univ.filter fun x : V × W =>
          ∑ y ∈ T ×ˢ (univ : Finset W), Q y.1 y.2 * (A x.1 y.1 - B x.2 y.2) < 0,
          Q x.1 x.2 * ∑ y ∈ T ×ˢ (univ : Finset W), Q y.1 y.2 * (A x.1 y.1 - B x.2 y.2)) := by
      rw [sum_filter, sum_filter, ← sum_sub_distrib, ← Fintype.sum_prod_type']
      refine sum_congr rfl fun x _ => ?_
      rcases lt_trichotomy (∑ y ∈ T ×ˢ (univ : Finset W),
        Q y.1 y.2 * (A x.1 y.1 - B x.2 y.2)) 0 with h | h | h
      · rw [abs_of_neg h, ite_eq_right (not_lt.2 h.le), ite_eq_left h]; ring
      · rw [h]; simp
      · rw [abs_of_pos h, ite_eq_left h, ite_eq_right (not_lt.2 h.le)]; ring
    rw [heq]
    have := (abs_le.1 hp).2
    have := (abs_le.1 hm).1
    linarith
  -- `x_i - (Qᵀx)_j = F_{ij} - ∑_{i'} Q_{i'j} F_{i'j}`, then the triangle inequality.
  have hdiff : ∀ i j, (∑ k ∈ T, A i k) - ∑ k', Q k' j * ∑ k ∈ T, A k' k =
      (∑ y ∈ T ×ˢ (univ : Finset W), Q y.1 y.2 * (A i y.1 - B j y.2)) -
        ∑ k', Q k' j * ∑ y ∈ T ×ˢ (univ : Finset W), Q y.1 y.2 * (A k' y.1 - B j y.2) := by
    intro i j
    simp_rw [hF, mul_sub, sum_sub_distrib, ← sum_mul, hQ.col_sum, one_mul]
    ring
  calc ∑ i, ∑ j, Q i j * |(∑ k ∈ T, A i k) - ∑ k', Q k' j * ∑ k ∈ T, A k' k|
      ≤ ∑ i, ∑ j, (Q i j * |∑ y ∈ T ×ˢ (univ : Finset W), Q y.1 y.2 * (A i y.1 - B j y.2)| +
          Q i j * ∑ k', Q k' j * |∑ y ∈ T ×ˢ (univ : Finset W),
            Q y.1 y.2 * (A k' y.1 - B j y.2)|) := by
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        rw [hdiff, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (hQ.nonneg i j)
        refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun k _ => ?_))
        rw [abs_mul, abs_of_nonneg (hQ.nonneg k j)]
    _ = 2 * ∑ i, ∑ j, Q i j * |∑ y ∈ T ×ˢ (univ : Finset W),
          Q y.1 y.2 * (A i y.1 - B j y.2)| := by
        simp_rw [sum_add_distrib]
        rw [two_mul]
        congr 1
        rw [sum_comm]
        simp_rw [← sum_mul, hQ.col_sum, one_mul]
        exact sum_comm
    _ ≤ 4 * ((Fintype.card V : ℝ) ^ 2 * epsR A B Q) := by linarith

/-! ### Theorem 38 -/

/-- Sums against the permutation matrix `P_π` over `S ⊆ V × W` collapse to sums over
`{v | (v, π v) ∈ S}`. -/
lemma sum_permMat_mul_atoms (π : V ≃ W) (S : Finset (V × W)) (h : V × W → ℝ) :
    ∑ x ∈ S, permMat π x.1 x.2 * h x =
      ∑ v ∈ univ.filter (fun v => (v, π v) ∈ S), h (v, π v) := by
  rw [sum_filter, ← Finset.univ_inter S, ← Finset.sum_ite_mem, Fintype.sum_prod_type]
  refine sum_congr rfl fun v _ => ?_
  rw [Finset.sum_eq_single (π v)]
  · simp [permMat]
  · intro w _ hw
    simp [permMat, Ne.symm hw]
  · simp

/-- `ζ_P` as a cut norm (proof of Theorem 38, p. 34, l. 1080–1084): for the permutation matrix,
`n² ζ_{P_π}` is the cut norm of `A - P B Pᵀ`, where `(P B Pᵀ)(v, v') = B(π v, π v')`. Only the
direction `≤` is needed. -/
lemma epsR_permMat_le (A : Matrix V V ℝ) (B : Matrix W W ℝ) (π : V ≃ W)
    (hn : (Fintype.card V : ℝ) ≠ 0) {c : ℝ}
    (h : ∀ S T : Finset V, |∑ v ∈ S, ∑ v' ∈ T, (A v v' - B (π v) (π v'))| ≤
      (Fintype.card V : ℝ) ^ 2 * c) :
    epsR A B (permMat π) ≤ c := by
  refine cutNorm_le _ fun S T => ?_
  have hpos : (0 : ℝ) < Fintype.card V := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hn)
  have e1 : ∑ x ∈ S, ∑ y ∈ T, (permMat π x.1 x.2 / Fintype.card V) *
      (permMat π y.1 y.2 / Fintype.card V) * (A x.1 y.1 - B x.2 y.2) =
      (∑ x ∈ S, permMat π x.1 x.2 * ∑ y ∈ T, permMat π y.1 y.2 * (A x.1 y.1 - B x.2 y.2)) /
        (Fintype.card V : ℝ) ^ 2 := by
    rw [sum_div]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum, sum_div]
    refine sum_congr rfl fun y _ => ?_
    field_simp
  rw [e1]
  simp only [sum_permMat_mul_atoms]
  rw [abs_div, abs_of_pos (pow_pos hpos 2), div_le_iff₀ (pow_pos hpos 2)]
  linarith [h (univ.filter (fun v => (v, π v) ∈ S)) (univ.filter (fun v => (v, π v) ∈ T))]

/-- **First bound of Eq. (27)** (proof of Theorem 38, p. 35, l. 1090–1095):
`n⁻² ‖QᵀAQ - B‖_□ ≤ ζ_Q`, with `(QᵀAQ)(j, ℓ) = ∑_{i,k} Q_{ij} Q_{kℓ} A_{ik}`. Since the columns of
`Q` sum to one, testing `QᵀAQ - B` on `X × Y` is testing the kernel of Eq. (21) on
`S = [n] × X`, `T = [n] × Y`. -/
lemma eq27_left (A : Matrix V V ℝ) (B : Matrix W W ℝ) {Q : V → W → ℝ} (hQ : IsDS Q)
    (hn : (Fintype.card V : ℝ) ≠ 0) (X Y : Finset W) :
    |∑ j ∈ X, ∑ l ∈ Y, ((∑ i, ∑ k, Q i j * Q k l * A i k) - B j l)| ≤
      (Fintype.card V : ℝ) ^ 2 * epsR A B Q := by
  have h := abs_cut_le_epsR A B Q hn (univ ×ˢ X) (univ ×ˢ Y)
  -- `∑_{i,k} Q_{ij} Q_{kℓ} B_{jℓ} = B_{jℓ}` (column sums)
  have hB : ∀ j l, ∑ i, ∑ k, Q i j * Q k l * B j l = B j l := by
    intro j l
    have : ∀ i, ∑ k, Q i j * Q k l * B j l = Q i j * B j l := fun i => by
      rw [show ∑ k, Q i j * Q k l * B j l = Q i j * B j l * ∑ k, Q k l by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring, hQ.col_sum, mul_one]
    rw [sum_congr rfl fun i _ => this i, ← sum_mul, hQ.col_sum, one_mul]
  have e : ∀ j l, (∑ i, ∑ k, Q i j * Q k l * A i k) - B j l =
      ∑ i, ∑ k, Q i j * Q k l * (A i k - B j l) := by
    intro j l
    simp_rw [mul_sub, sum_sub_distrib, hB]
  simp_rw [e]
  convert h using 2
  simp only [sum_product]
  conv_rhs => rw [Finset.sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => Finset.sum_comm

/-- `n⁻² ‖EA‖_□ ≤ 2α ζ_Q` with `E = I - R`, `R = P Qᵀ`, i.e.
`(EA)(v, v') = A(v, v') - ∑_k Q(k, π v) A(k, v')` (proof of Theorem 38, p. 35,
l. 1096–1105): Lemma 36 for `x = A 1_Y` and `Qᵀx`, then Lemma 37 with `y = 1_Y`, and the
mean-zero argument. -/
lemma normEA_le (A : Matrix V V ℝ) (B : Matrix W W ℝ) {Q : V → W → ℝ} (hQ : IsDS Q)
    (hn : (Fintype.card V : ℝ) ≠ 0) {π : V ≃ W} {a : ℝ} (ha : 0 ≤ a) (hthin : IsThin a Q π)
    (S T : Finset V) :
    |∑ v ∈ S, ∑ v' ∈ T, (A v v' - ∑ k, Q k (π v) * A k v')| ≤
      2 * a * ((Fintype.card V : ℝ) ^ 2 * epsR A B Q) := by
  have hcol : ∀ k, ∑ v, Q k (π v) = 1 := fun k => by
    rw [Equiv.sum_comp π (Q k)]; exact hQ.row_sum k
  -- `f_v = x_v - (Qᵀx)_{π v}` with `x = A 1_T`
  have hsw : ∀ v, ∑ v' ∈ T, (A v v' - ∑ k, Q k (π v) * A k v') =
      (∑ v' ∈ T, A v v') - ∑ k, Q k (π v) * ∑ v' ∈ T, A k v' := by
    intro v
    rw [sum_sub_distrib, Finset.sum_comm]
    simp only [mul_sum]
  rw [sum_congr rfl fun v _ => hsw v]
  -- `∑_v f_v = 0`, since the columns of `R` sum to one
  have h0 : ∑ v, ((∑ v' ∈ T, A v v') - ∑ k, Q k (π v) * ∑ v' ∈ T, A k v') = 0 := by
    rw [sum_sub_distrib, Finset.sum_comm (s := univ) (t := univ)]
    simp_rw [← sum_mul, hcol, one_mul, sub_self]
  refine (abs_sum_le_half_of_sum_eq_zero _ h0 S).trans ?_
  have h50 := lemma36 hthin (fun v => ∑ v' ∈ T, A v v')
    (fun w => ∑ k, Q k w * ∑ v' ∈ T, A k v')
  have h51 := mul_le_mul_of_nonneg_left (lemma37 A B hQ hn T) ha
  linarith

/-- **Eq. (25)** together with the invariance under transposition, for `K = EA`:
`‖R (EA)ᵀ‖_□ ≤ ‖EA‖_□ ≤ 2α n² ζ_Q` (end of the proof of Theorem 38, p. 35, l. 1107–1108). -/
lemma cut_R_EAt_le (A : Matrix V V ℝ) (B : Matrix W W ℝ) {Q : V → W → ℝ} (hQ : IsDS Q)
    (hn : (Fintype.card V : ℝ) ≠ 0) {π : V ≃ W} {a : ℝ} (ha : 0 ≤ a) (hthin : IsThin a Q π)
    (S T : Finset V) :
    |∑ v ∈ S, ∑ v' ∈ T, ∑ k, Q k (π v) * (A v' k - ∑ k', Q k' (π v') * A k' k)| ≤
      2 * a * ((Fintype.card V : ℝ) ^ 2 * epsR A B Q) := by
  have hcol : ∀ k, ∑ v, Q k (π v) = 1 := fun k => by
    rw [Equiv.sum_comp π (Q k)]; exact hQ.row_sum k
  have e : ∑ v ∈ S, ∑ v' ∈ T, ∑ k, Q k (π v) * (A v' k - ∑ k', Q k' (π v') * A k' k) =
      ∑ k, (∑ v ∈ S, Q k (π v)) * ∑ v' ∈ T, (A v' k - ∑ k', Q k' (π v') * A k' k) := by
    calc _ = ∑ v ∈ S, ∑ k, ∑ v' ∈ T, Q k (π v) * (A v' k - ∑ k', Q k' (π v') * A k' k) :=
          sum_congr rfl fun v _ => Finset.sum_comm
      _ = ∑ k, ∑ v ∈ S, ∑ v' ∈ T, Q k (π v) * (A v' k - ∑ k', Q k' (π v') * A k' k) :=
          Finset.sum_comm
      _ = _ := by
          refine sum_congr rfl fun k _ => ?_
          rw [sum_mul]
          refine sum_congr rfl fun v _ => ?_
          rw [mul_sum]
  rw [e]
  refine abs_sum_mul_le_of_cut _ _ (fun k => ⟨sum_nonneg fun v _ => hQ.nonneg _ _, ?_⟩)
    (fun K => ?_)
  · rw [← hcol k]
    exact sum_le_univ_sum_of_nonneg fun v => hQ.nonneg _ _
  · rw [Finset.sum_comm]
    exact normEA_le A B hQ hn ha hthin T K

omit [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- **Eq. (28)**: since `A` is symmetric, `A - R A Rᵀ = EA + R (EA)ᵀ` with `R = P Qᵀ`,
`E = I - R`; entrywise, `(R A Rᵀ)(v, v') = ∑_{k,k'} Q(k, π v) Q(k', π v') A(k, k')`. -/
lemma eq28_cut (A : Matrix V V ℝ) (hA : A.IsSymm) (Q : V → W → ℝ) (π : V ≃ W) (v v' : V) :
    A v v' - ∑ k, ∑ k', Q k (π v) * Q k' (π v') * A k k' =
      (A v v' - ∑ k, Q k (π v) * A k v') +
        ∑ k, Q k (π v) * (A v' k - ∑ k', Q k' (π v') * A k' k) := by
  have e2 : ∑ k, Q k (π v) * (A v' k - ∑ k', Q k' (π v') * A k' k) =
      ∑ k, Q k (π v) * A k v' - ∑ k, ∑ k', Q k (π v) * Q k' (π v') * A k k' := by
    simp_rw [mul_sub, sum_sub_distrib, mul_sum]
    congr 1
    · exact sum_congr rfl fun k _ => by rw [hA.apply]
    · exact sum_congr rfl fun k _ => sum_congr rfl fun k' _ => by rw [hA.apply]; ring
  rw [e2]
  ring

/-- **Second bound of Eq. (27)**: `n⁻² ‖A - R A Rᵀ‖_□ ≤ 4α ζ_Q` (from Eq. (28), `normEA_le` and
`cut_R_EAt_le`). -/
lemma eq27_right (A : Matrix V V ℝ) (B : Matrix W W ℝ) (hA : A.IsSymm) {Q : V → W → ℝ}
    (hQ : IsDS Q) (hn : (Fintype.card V : ℝ) ≠ 0) {π : V ≃ W} {a : ℝ} (ha : 0 ≤ a)
    (hthin : IsThin a Q π) (S T : Finset V) :
    |∑ v ∈ S, ∑ v' ∈ T, (A v v' - ∑ k, ∑ k', Q k (π v) * Q k' (π v') * A k k')| ≤
      4 * a * ((Fintype.card V : ℝ) ^ 2 * epsR A B Q) := by
  rw [sum_congr rfl fun v _ => sum_congr rfl fun v' _ => eq28_cut A hA Q π v v']
  simp only [sum_add_distrib]
  have h1 := normEA_le A B hQ hn ha hthin S T
  have h2 := cut_R_EAt_le A B hQ hn ha hthin S T
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- **Eq. (26)** (proof of Theorem 38, p. 34, l. 1079): if `P = P_π` is `α`-thin w.r.t.
`Q ∈ DS(n)`, then `ζ_P ≤ (1 + 4α) ζ_Q`. As in the paper (p. 35, l. 1085–1090), split
`A - P B Pᵀ = (A - R A Rᵀ) + P (QᵀAQ - B) Pᵀ` with `R = P Qᵀ` and use the two bounds of Eq. (27)
(`eq27_right`, and `eq27_left` tested on `π(S) × π(T)`). Theorem 38 itself (the existence of such
a `P`) is `theorem38`. -/
theorem eq26 (A : Matrix V V ℝ) (B : Matrix W W ℝ) (hA : A.IsSymm) (_hB : B.IsSymm)
    (_hA01 : ∀ i k, 0 ≤ A i k ∧ A i k ≤ 1) (_hB01 : ∀ j l, 0 ≤ B j l ∧ B j l ≤ 1)
    (_hcard : Fintype.card V = Fintype.card W) {Q : V → W → ℝ} (hQ : IsDS Q) {π : V ≃ W}
    {a : ℝ} (ha : 0 ≤ a) (hthin : IsThin a Q π) :
    epsR A B (permMat π) ≤ (1 + 4 * a) * epsR A B Q := by
  by_cases hn : (Fintype.card V : ℝ) = 0
  · -- `V` is empty: both sides vanish.
    have hε : 0 ≤ epsR A B Q := cutNorm_nonneg _
    refine (cutNorm_le _ fun S T => ?_).trans (mul_nonneg (by linarith) hε)
    simp [hn]
  refine epsR_permMat_le A B π hn fun S T => ?_
  -- the split `A - P B Pᵀ = (A - R A Rᵀ) + P (QᵀAQ - B) Pᵀ`
  have hsplit : ∀ v v', A v v' - B (π v) (π v') =
      (A v v' - ∑ k, ∑ k', Q k (π v) * Q k' (π v') * A k k') +
        ((∑ k, ∑ k', Q k (π v) * Q k' (π v') * A k k') - B (π v) (π v')) :=
    fun v v' => by ring
  rw [sum_congr rfl fun v _ => sum_congr rfl fun v' _ => hsplit v v']
  simp only [sum_add_distrib]
  have h1 := eq27_right A B hA hQ hn ha hthin S T
  -- conjugation by `P`: test `QᵀAQ - B` on `π(S) × π(T)`
  have h2 := eq27_left A B hQ hn (S.map π.toEmbedding) (T.map π.toEmbedding)
  simp only [sum_map, Equiv.coe_toEmbedding] at h2
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- **Theorem 38** (p. 34, l. 1074–1075; assuming Theorem 35 [HOG26]). Let
`α = C_thin ln(2n) ln ln(4n)`, where
`C_thin` is the constant of Theorem 35. Then for every `Q ∈ DS(n)` there is a permutation matrix
`P = P_π` with `ζ_P ≤ (1 + 4α) ζ_Q`. Stated for symmetric `[0, 1]`-valued matrices `A`, `B`
(the adjacency matrices of `G`, `H`). -/
theorem theorem38 (hThin : ThinPermutationTheorem) :
    ∃ Cthin : ℝ, 0 < Cthin ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V]
      [DecidableEq W] (A : Matrix V V ℝ) (B : Matrix W W ℝ), A.IsSymm → B.IsSymm →
      (∀ i k, 0 ≤ A i k ∧ A i k ≤ 1) → (∀ j l, 0 ≤ B j l ∧ B j l ≤ 1) →
      Fintype.card V = Fintype.card W → ∀ Q : V → W → ℝ, IsDS Q →
      ∃ π : V ≃ W, epsR A B (permMat π) ≤
        (1 + 4 * (Cthin * Real.log (2 * Fintype.card V) *
          Real.log (Real.log (4 * Fintype.card V)))) * epsR A B Q := by
  obtain ⟨Cthin, hCthin, hT⟩ := hThin
  refine ⟨Cthin, hCthin, fun V W _ _ _ _ A B hA hB hA01 hB01 hcard Q hQ => ?_⟩
  obtain ⟨π, hπ⟩ := hT V W Q hQ hcard
  refine ⟨π, eq26 A B hA hB hA01 hB01 hcard hQ ?_ hπ⟩
  -- `α ≥ 0`: for `n = 0` the logarithms vanish, for `n ≥ 1` they are nonnegative.
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · simp [h0]
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hpos
  have h2 : 0 ≤ Real.log (2 * Fintype.card V) := Real.log_nonneg (by linarith)
  have h4 : 1 ≤ Real.log (4 * Fintype.card V) := by
    have : Real.log 4 ≤ Real.log (4 * Fintype.card V) :=
      Real.log_le_log (by norm_num) (by linarith)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hll : 0 ≤ Real.log (Real.log (4 * Fintype.card V)) := Real.log_nonneg h4
  have := hCthin.le
  positivity

end GsimOT
