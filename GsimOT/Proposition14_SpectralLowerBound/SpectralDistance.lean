/-
# `d_2(G_r, H_r) = √r`

Paper, App. F.1 (p. 45, l. 1412–1416, the paragraph before Lemma 49).

* Lower bound: every bijection `π` matches the all-zeros row of the isolated vertex `u` of `G_r`
  with the row of `π(u)` in `H_r`, which has at least `r` ones since `H_r` has minimum degree `r`;
  the spectral norm is at least the Euclidean norm of every row.
* Upper bound: for the identity, `A_{G_r} - A_{H_r}` is minus the adjacency matrix of the star
  with centre `u` and the `r` clocks as leaves, whose spectral norm is `√r`.

The file also contains the elementary facts on `ℓ²` norms used throughout this folder.
-/
import GsimOT.Proposition14_SpectralLowerBound.Construction

open Finset Matrix

namespace GsimOT.Prop14

/-! ## Euclidean norms and spectral norms -/

section Norms

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma lpNorm_two (x : ι → ℝ) : lpNorm 2 x = Real.sqrt (∑ i, x i ^ 2) := by
  rw [lpNorm, EuclideanSpace.norm_eq]
  simp

lemma conjExponent_two : ENNReal.conjExponent 2 = 2 := by
  rw [ENNReal.conjExponent, show (2 : ENNReal) = 1 + 1 from one_add_one_eq_two.symm,
    ENNReal.add_sub_cancel_left ENNReal.one_ne_top, inv_one]

/-- `‖M‖_{2→2} ≤ C` as soon as `‖Mx‖² ≤ C² ‖x‖²` for all `x`. -/
lemma opNorm22_le (M : Matrix ι κ ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : κ → ℝ, ∑ i, (M *ᵥ x) i ^ 2 ≤ C ^ 2 * ∑ j, x j ^ 2) : opNorm 2 2 M ≤ C := by
  refine opNorm_le_of_bound (by norm_num) (by norm_num) M hC fun x hx => ?_
  rw [lpNorm_two] at hx ⊢
  calc Real.sqrt (∑ i, (M *ᵥ x) i ^ 2) ≤ Real.sqrt (C ^ 2 * ∑ j, x j ^ 2) :=
        Real.sqrt_le_sqrt (h x)
    _ = C * Real.sqrt (∑ j, x j ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hx hC
    _ = C := mul_one C

/-- The spectral norm of a matrix is at least the Euclidean norm of each of its rows. -/
lemma sqrt_row_le_opNorm22 (M : Matrix ι κ ℝ) (i : ι) :
    Real.sqrt (∑ j, M i j ^ 2) ≤ opNorm 2 2 M := by
  set s := Real.sqrt (∑ j, M i j ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  rcases hs0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact opNorm_nonneg _ _ _
  have hss : s ^ 2 = ∑ j, M i j ^ 2 := Real.sq_sqrt (by positivity)
  have hx : lpNorm 2 (fun j => M i j / s) = 1 := by
    rw [lpNorm_two]
    simp only [div_pow]
    rw [← Finset.sum_div, ← hss, div_self (by positivity), Real.sqrt_one]
  have hMx : (M *ᵥ fun j => M i j / s) i = s := by
    simp only [mulVec, dotProduct]
    rw [show (∑ j, M i j * (M i j / s)) = (∑ j, M i j ^ 2) / s by
      rw [Finset.sum_div]; congr 1; funext j; ring]
    rw [← hss]; field_simp
  calc s = |(M *ᵥ fun j => M i j / s) i| := by rw [hMx, abs_of_pos hpos]
    _ ≤ lpNorm 2 (M *ᵥ fun j => M i j / s) := abs_le_lpNorm (by norm_num) _ _
    _ ≤ opNorm 2 2 M * lpNorm 2 (fun j => M i j / s) :=
        lpNorm_mulVec_le (by norm_num) (by norm_num) _ _
    _ = opNorm 2 2 M := by rw [hx, mul_one]

end Norms

/-! ## The lower bound `d_2 ≥ √r` -/

lemma sqrt_le_opNorm_alignedDiff (r : ℕ) (π : Vtx r ≃ Vtx r) :
    Real.sqrt r ≤ opNorm 2 2 (alignedDiff (Gr r) (Hr r) π) := by
  refine le_trans ?_ (sqrt_row_le_opNorm22 _ (π (.inl none)))
  apply Real.sqrt_le_sqrt
  have hrow : ∀ w, alignedDiff (Gr r) (Hr r) π (π (.inl none)) w ^ 2 =
      adj (Hr r) (π (.inl none)) w := by
    intro w
    simp only [alignedDiff, Equiv.symm_apply_apply, adj_Gr_u, zero_sub, neg_sq]
    rcases adj_eq_zero_or_one (Hr r) (π (.inl none)) w with h | h <;> rw [h] <;> norm_num
  simp only [hrow, sum_adj_eq_deg]
  exact_mod_cast le_deg_Hr r _

/-! ## The upper bound `d_2 ≤ √r` (identity alignment) -/

/-- `A_{G_r} - A_{H_r}` applied to a vector: only `u` and the clocks see a nonzero value. -/
lemma diff_mulVec (r : ℕ) (x : Vtx r → ℝ) (w : Vtx r) :
    (alignedDiff (Gr r) (Hr r) (Equiv.refl _) *ᵥ x) w =
      match w with
      | .inl none => -∑ j, x (.inr (.inl j))
      | .inr (.inl _) => -x (.inl none)
      | _ => 0 := by
  simp only [mulVec, dotProduct, alignedDiff, Equiv.refl_symm, Equiv.refl_apply]
  rcases w with (_ | ⟨i, k⟩) | j | ⟨i, t⟩
  · simp [Fintype.sum_sum_type]
  · simp [Fintype.sum_sum_type, cmR_some_eq]
  · simp [Fintype.sum_sum_type, Fintype.sum_option, cmR_some_eq]
  · simp [Fintype.sum_sum_type, cmR_some_eq]

lemma opNorm_diff_refl_le (r : ℕ) :
    opNorm 2 2 (alignedDiff (Gr r) (Hr r) (Equiv.refl _)) ≤ Real.sqrt r := by
  refine opNorm22_le _ (Real.sqrt_nonneg _) fun x => ?_
  rw [Real.sq_sqrt (Nat.cast_nonneg r)]
  simp only [diff_mulVec]
  simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type, neg_sq,
    zero_pow two_ne_zero, Finset.sum_const_zero, add_zero, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin r)))
    (f := fun j => x (.inr (.inl j)))
  simp only [card_univ, Fintype.card_fin] at hcs
  have h1 : 0 ≤ ∑ i : Fin (2 * r), ∑ k : Fin (r + 1), x (.inl (some (i, k))) ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∑ i : Fin (2 * r), ∑ t : Fin r, x (.inr (.inr (i, t))) ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have h3 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith

/-- `d_2(G_r, H_r) = √r`. -/
theorem distPQ_eq (r : ℕ) : distPQ 2 2 (Gr r) (Hr r) = Real.sqrt r := by
  apply le_antisymm
  · exact (ciInf_le ⟨0, by rintro _ ⟨π, rfl⟩; exact opNorm_nonneg _ _ _⟩ (Equiv.refl _)).trans
      (opNorm_diff_refl_le r)
  · exact le_ciInf (sqrt_le_opNorm_alignedDiff r)

end GsimOT.Prop14
