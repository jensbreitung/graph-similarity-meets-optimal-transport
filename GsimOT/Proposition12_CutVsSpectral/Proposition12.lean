/-
# Proposition 12: cut distance and spectral distance bound each other

Paper, Section 3.4, Proposition 12 (p. 11, l. 385–386), and its proof at the beginning of
Appendix F (pp. 44–45, l. 1382–1397).

The proof goes through two matrix inequalities for `A ∈ ℝ^{ι×κ}` (`m = |ι|`, `n = |κ|`; p. 44,
l. 1384), applied to `A_G^π - A_H`, whose entries lie in `[-1, 1]` (l. 1385–1387):
* `cutNorm_le_sqrt_mul_opNorm_two` : `‖A‖_□ ≤ √(mn) ‖A‖_2` (Cauchy–Schwarz, as in the paper,
  l. 1391–1396);
* `opNorm_two_le_two_sqrt_cutNorm` : `‖A‖_2 ≤ 2 √(‖A‖_(∞) ‖A‖_□)` with
  `‖A‖_(∞) = max_{v,w} |A_vw|` (l. 1385) (Nikiforov [Nik09, Thm. 3], which the paper cites,
  p. 11, l. 387 and p. 45, l. 1397; here it is proved via the Schur test and
  `‖A‖_{∞→1} ≤ 4 ‖A‖_□`, see `infOneNorm_le_four_cutNorm`).
-/
import GsimOT.Common.CutNorm

open Finset Matrix

namespace GsimOT

section MatrixInequalities

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The entrywise maximum norm `‖A‖_(∞) = max_{i,j} |A i j|` (Appendix F, p. 44, l. 1385). -/
noncomputable def maxEntryNorm (A : Matrix ι κ ℝ) : ℝ := ⨆ ij : ι × κ, |A ij.1 ij.2|

omit [DecidableEq ι] [DecidableEq κ] in
lemma abs_le_maxEntryNorm (A : Matrix ι κ ℝ) (i : ι) (j : κ) : |A i j| ≤ maxEntryNorm A :=
  le_ciSup (f := fun ij : ι × κ => |A ij.1 ij.2|) (Set.finite_range _).bddAbove (i, j)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma maxEntryNorm_nonneg (A : Matrix ι κ ℝ) : 0 ≤ maxEntryNorm A :=
  Real.iSup_nonneg fun _ => abs_nonneg _

/-- The Euclidean norm as a square root of a sum of squares. -/
lemma lpNorm_two_eq_sqrt {α : Type*} [Fintype α] (x : α → ℝ) :
    lpNorm 2 x = Real.sqrt (∑ i, x i ^ 2) := by
  rw [lpNorm_eq_sum (by norm_num) (by norm_num), Real.sqrt_eq_rpow]
  simp [sq_abs]

lemma sum_sq_eq_lpNorm_two_sq {α : Type*} [Fintype α] (x : α → ℝ) :
    ∑ i, x i ^ 2 = lpNorm 2 x ^ 2 := by
  rw [lpNorm_two_eq_sqrt, Real.sq_sqrt (by positivity)]

/-- The indicator vector `1_U`. -/
private def ind {α : Type*} [DecidableEq α] (U : Finset α) (a : α) : ℝ := if a ∈ U then 1 else 0

private lemma sum_ind_ind (A : Matrix ι κ ℝ) (T : Finset ι) (S : Finset κ) :
    ∑ i, ∑ k, ind T i * ind S k * A i k = ∑ i ∈ T, ∑ k ∈ S, A i k := by
  calc ∑ i, ∑ k, ind T i * ind S k * A i k = ∑ i, if i ∈ T then ∑ k ∈ S, A i k else 0 :=
        Finset.sum_congr rfl fun i _ => by
          by_cases hi : i ∈ T <;> simp [ind, hi, Finset.sum_ite_mem]
    _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]

private lemma eq_ind_sub_ind {α : Type*} [Fintype α] [DecidableEq α] (u : α → ℝ)
    (hu : ∀ a, u a = 1 ∨ u a = -1) (a : α) :
    u a = ind (univ.filter fun b => u b = 1) a - ind (univ.filter fun b => u b = -1) a := by
  rcases hu a with h | h <;> simp [ind, h] <;> norm_num

/-- **`‖A‖_{∞→1} ≤ 4 ‖A‖_□`.** For all sign vectors `s ∈ {±1}^κ`, `t ∈ {±1}^ι`,
`tᵀ A s ≤ 4 ‖A‖_□` (split `s`, `t` into positive and negative parts: four cut values). -/
lemma infOneNorm_le_four_cutNorm (A : Matrix ι κ ℝ) (s : κ → ℝ) (t : ι → ℝ)
    (hs : ∀ k, s k = 1 ∨ s k = -1) (ht : ∀ i, t i = 1 ∨ t i = -1) :
    ∑ i, t i * ∑ k, A i k * s k ≤ 4 * cutNorm A := by
  have hexp : ∑ i, t i * ∑ k, A i k * s k =
      ∑ i, ∑ k, (ind (univ.filter fun b => t b = 1) i - ind (univ.filter fun b => t b = -1) i) *
        (ind (univ.filter fun b => s b = 1) k - ind (univ.filter fun b => s b = -1) k) * A i k := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← eq_ind_sub_ind t ht i, ← eq_ind_sub_ind s hs k]; ring
  have hsplit : ∀ (a b c d x : ℝ), (a - b) * (c - d) * x = a * c * x - a * d * x - b * c * x
      + b * d * x := fun _ _ _ _ _ => by ring
  rw [hexp]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_ind_ind]
  have h1 := le_cutNorm A (univ.filter fun b => t b = 1) (univ.filter fun b => s b = 1)
  have h2 := le_cutNorm A (univ.filter fun b => t b = 1) (univ.filter fun b => s b = -1)
  have h3 := le_cutNorm A (univ.filter fun b => t b = -1) (univ.filter fun b => s b = 1)
  have h4 := le_cutNorm A (univ.filter fun b => t b = -1) (univ.filter fun b => s b = -1)
  rw [abs_le] at h1 h2 h3 h4
  linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

/-- Row sums of `|AᵀA|` are at most `4 ‖A‖_(∞) ‖A‖_□`. -/
private lemma sum_abs_gram_le (A : Matrix ι κ ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i j, |A i j| ≤ M) (j : κ) :
    ∑ k, |∑ i, A i j * A i k| ≤ 4 * M * cutNorm A := by
  let s : κ → ℝ := fun k => if 0 ≤ ∑ i, A i j * A i k then 1 else -1
  let u : ι → ℝ := fun i => ∑ k, A i k * s k
  let t : ι → ℝ := fun i => if 0 ≤ u i then 1 else -1
  have hs : ∀ k, s k = 1 ∨ s k = -1 := fun k => by simp only [s]; split_ifs <;> simp
  have ht : ∀ i, t i = 1 ∨ t i = -1 := fun i => by simp only [t]; split_ifs <;> simp
  have hsabs : ∀ k, |∑ i, A i j * A i k| = s k * ∑ i, A i j * A i k := fun k => by
    simp only [s]; split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.1 h)]; ring
  have htabs : ∀ i, |u i| = t i * u i := fun i => by
    simp only [t]; split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.1 h)]; ring
  calc ∑ k, |∑ i, A i j * A i k| = ∑ i, A i j * u i := by
        simp only [hsabs, u, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ∑ i, M * |u i| := Finset.sum_le_sum fun i _ => by
        calc A i j * u i ≤ |A i j * u i| := le_abs_self _
          _ = |A i j| * |u i| := abs_mul _ _
          _ ≤ M * |u i| := mul_le_mul_of_nonneg_right (hM i j) (abs_nonneg _)
    _ = M * ∑ i, t i * ∑ k, A i k * s k := by
        rw [← Finset.mul_sum]; simp only [htabs, u]
    _ ≤ M * (4 * cutNorm A) :=
        mul_le_mul_of_nonneg_left (infOneNorm_le_four_cutNorm A s t hs ht) hM0
    _ = 4 * M * cutNorm A := by ring

/-- **First inequality of Proposition 12 (matrix form)** (p. 44, l. 1384; proof pp. 44–45,
l. 1391–1396). For `A ∈ ℝ^{ι×κ}`, `‖A‖_□ ≤ √(|ι| |κ|) ‖A‖_2` (Cauchy–Schwarz). -/
lemma cutNorm_le_sqrt_mul_opNorm_two (A : Matrix ι κ ℝ) :
    cutNorm A ≤ Real.sqrt (Fintype.card ι * Fintype.card κ) * opNorm 2 2 A := by
  refine cutNorm_le A fun S T => ?_
  let x : κ → ℝ := ind T
  have hAx : ∀ i, (A *ᵥ x) i = ∑ j ∈ T, A i j := fun i => by
    simp [x, ind, Matrix.mulVec, dotProduct, mul_ite, Finset.sum_ite_mem]
  have hx : lpNorm 2 x ≤ Real.sqrt (Fintype.card κ) := by
    rw [lpNorm_two_eq_sqrt]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ j, x j ^ 2 ≤ ∑ _j : κ, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => by simp only [x, ind]; split_ifs <;> norm_num
      _ = Fintype.card κ := by simp
  have hop := opNorm_nonneg 2 2 A
  have hL : lpNorm 2 (A *ᵥ x) ≤ opNorm 2 2 A * Real.sqrt (Fintype.card κ) :=
    (lpNorm_mulVec_le (by norm_num) (by norm_num) A x).trans
      (mul_le_mul_of_nonneg_left hx hop)
  have hsq : ∑ i, (A *ᵥ x) i ^ 2 ≤ (opNorm 2 2 A * Real.sqrt (Fintype.card κ)) ^ 2 := by
    rw [sum_sq_eq_lpNorm_two_sq]
    exact pow_le_pow_left₀ (lpNorm_nonneg _ _) hL 2
  have hS : (∑ i ∈ S, ∑ j ∈ T, A i j) ^ 2 ≤
      (Fintype.card ι : ℝ) * (opNorm 2 2 A * Real.sqrt (Fintype.card κ)) ^ 2 := by
    calc (∑ i ∈ S, ∑ j ∈ T, A i j) ^ 2 = (∑ i ∈ S, (A *ᵥ x) i) ^ 2 := by simp only [hAx]
      _ ≤ (S.card : ℝ) * ∑ i ∈ S, (A *ᵥ x) i ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (Fintype.card ι : ℝ) * ∑ i, (A *ᵥ x) i ^ 2 := by
          refine mul_le_mul (by exact_mod_cast Finset.card_le_univ S)
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
              fun i _ _ => sq_nonneg _) (by positivity) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by positivity)
  refine (Real.abs_le_sqrt hS).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
    Real.sqrt_mul (by positivity)]
  ring

/-- Version of Nikiforov's inequality with an arbitrary entrywise bound `M`:
if `|A i j| ≤ M` for all `i, j`, then `‖A‖_2 ≤ 2 √(M ‖A‖_□)`.  Proof: for `‖x‖_2 ≤ 1`,
`‖Ax‖² = xᵀ(AᵀA)x ≤ max_j ∑_k |(AᵀA)_{jk}|` (Schur test) and
`∑_k |(AᵀA)_{jk}| ≤ M ‖A‖_{∞→1} ≤ 4 M ‖A‖_□`. -/
lemma opNorm_two_le_two_sqrt_of_abs_le (A : Matrix ι κ ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i j, |A i j| ≤ M) :
    opNorm 2 2 A ≤ 2 * Real.sqrt (M * cutNorm A) := by
  have hc := cutNorm_nonneg A
  refine opNorm_le_of_bound (by norm_num) (by norm_num) A (by positivity) fun x hx => ?_
  have hx2 : ∑ j, x j ^ 2 ≤ 1 := by
    rw [sum_sq_eq_lpNorm_two_sq]; exact pow_le_one₀ (lpNorm_nonneg _ _) hx
  let B : κ → κ → ℝ := fun j k => ∑ i, A i j * A i k
  have hBsymm : ∀ j k, B j k = B k j := fun j k =>
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hR : ∀ j, ∑ k, |B j k| ≤ 4 * M * cutNorm A := sum_abs_gram_le A hM0 hM
  have hC : 0 ≤ 4 * M * cutNorm A := by positivity
  have hquad : ∑ i, (A *ᵥ x) i ^ 2 = ∑ j, ∑ k, B j k * x j * x k := by
    have e1 : ∀ i, (A *ᵥ x) i ^ 2 = ∑ j, ∑ k, A i j * x j * (A i k * x k) := fun i => by
      simp only [Matrix.mulVec, dotProduct]; rw [sq, Finset.sum_mul_sum]
    simp only [e1, B, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  have hpt : ∀ j k, B j k * x j * x k ≤ |B j k| * x j ^ 2 / 2 + |B j k| * x k ^ 2 / 2 :=
    fun j k => by
      have h1 : B j k * x j * x k ≤ |B j k| * |x j * x k| := by
        rw [← abs_mul, ← mul_assoc]; exact le_abs_self _
      have h2 : |x j * x k| ≤ (x j ^ 2 + x k ^ 2) / 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|x j| - |x k|), sq_abs (x j), sq_abs (x k)]
      nlinarith [abs_nonneg (B j k)]
  have hfirst : ∑ j, ∑ k, |B j k| * x j ^ 2 ≤ 4 * M * cutNorm A * ∑ j, x j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hR j) (sq_nonneg _)
  have hsecond : ∑ j, ∑ k, |B j k| * x k ^ 2 ≤ 4 * M * cutNorm A * ∑ j, x j ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [hBsymm _ (_ : κ)]
    exact hfirst
  have hsum : ∑ i, (A *ᵥ x) i ^ 2 ≤ 4 * (M * cutNorm A) := by
    rw [hquad]
    calc ∑ j, ∑ k, B j k * x j * x k
        ≤ ∑ j, ∑ k, (|B j k| * x j ^ 2 / 2 + |B j k| * x k ^ 2 / 2) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hpt j k
      _ = (∑ j, ∑ k, |B j k| * x j ^ 2) / 2 + (∑ j, ∑ k, |B j k| * x k ^ 2) / 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ 4 * M * cutNorm A * ∑ j, x j ^ 2 := by linarith
      _ ≤ 4 * M * cutNorm A * 1 := mul_le_mul_of_nonneg_left hx2 hC
      _ = 4 * (M * cutNorm A) := by ring
  rw [lpNorm_two_eq_sqrt]
  calc Real.sqrt (∑ i, (A *ᵥ x) i ^ 2) ≤ Real.sqrt (4 * (M * cutNorm A)) := Real.sqrt_le_sqrt hsum
    _ = 2 * Real.sqrt (M * cutNorm A) := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]

/-- **Nikiforov's inequality** ([Nik09, Theorem 3], used for the second inequality of
Proposition 12, p. 44, l. 1384 and p. 45, l. 1397): `‖A‖_2 ≤ 2 √(‖A‖_(∞) ‖A‖_□)`. -/
theorem opNorm_two_le_two_sqrt_cutNorm (A : Matrix ι κ ℝ) :
    opNorm 2 2 A ≤ 2 * Real.sqrt (maxEntryNorm A * cutNorm A) :=
  opNorm_two_le_two_sqrt_of_abs_le A (maxEntryNorm_nonneg A) (abs_le_maxEntryNorm A)

end MatrixInequalities

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- **Proposition 12** (p. 11, l. 385–386). For all graphs `G, H` of the same order,
`δ_□(G, H) ≤ δ_2(G, H) ≤ 2 √(δ_□(G, H))`. -/
theorem proposition12 (hcard : Fintype.card V = Fintype.card W) :
    deltaCut G H ≤ deltaPQ 2 2 G H ∧ deltaPQ 2 2 G H ≤ 2 * Real.sqrt (deltaCut G H) := by
  have hk : kappa 2 2 = 1 := by unfold kappa; ring
  have hδ2 : deltaPQ 2 2 G H = distPQ 2 2 G H / (Fintype.card V : ℝ) := by
    rw [deltaPQ, hk, Real.rpow_neg_one, inv_mul_eq_div]
  rw [hδ2, deltaCut]
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · simp [h0]
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast hpos
  have : Nonempty (V ≃ W) := ⟨Fintype.equivOfCardEq hcard⟩
  constructor
  · obtain ⟨π, hπ⟩ := exists_eq_ciInf_of_finite (f := fun π : V ≃ W =>
      opNorm 2 2 (alignedDiff G H π))
    have h1 : dCut G H ≤ cutNorm (alignedDiff G H π) :=
      ciInf_le (Set.finite_range _).bddBelow π
    have h2 := cutNorm_le_sqrt_mul_opNorm_two (alignedDiff G H π)
    rw [← hcard, Real.sqrt_mul_self hN.le] at h2
    have hd : distPQ 2 2 G H = opNorm 2 2 (alignedDiff G H π) := hπ.symm
    rw [hd, div_le_div_iff₀ (by positivity) hN]
    nlinarith
  · obtain ⟨π, hπ⟩ := exists_eq_ciInf_of_finite (f := fun π : V ≃ W =>
      cutNorm (alignedDiff G H π))
    have h1 : distPQ 2 2 G H ≤ opNorm 2 2 (alignedDiff G H π) :=
      ciInf_le (Set.finite_range _).bddBelow π
    have h2 := opNorm_two_le_two_sqrt_of_abs_le (alignedDiff G H π) zero_le_one
      fun w w' => abs_adj_sub_adj_le_one G H _ _ _ _
    have hd : dCut G H = cutNorm (alignedDiff G H π) := hπ.symm
    rw [one_mul, ← hd] at h2
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hN.le, div_le_iff₀ hN, mul_assoc,
      div_mul_cancel₀ _ hN.ne']
    linarith

end GsimOT
