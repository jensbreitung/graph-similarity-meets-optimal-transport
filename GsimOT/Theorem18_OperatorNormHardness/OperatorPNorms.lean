import GsimOT.Common.MatrixNorms

/-!
# Operator `p`-norms

Tools for the operator `p`-norms `‖·‖_p = ‖·‖_{p→p}` of Lemma 53, Corollary 54 and Theorem 17.

* `bExp p = b(p) = max(1/p, 1 - 1/p)` (with `b(∞) = 1`, p. 12, l. 431);
* `rpow_sum_mul_le`: Jensen's inequality for weights of total mass at most `1`;
* `opNorm_le_one_of_sum_abs_le_one`: if all absolute row and column sums of `M` are at most
  `1`, then `‖M‖_p ≤ 1` (Schur test);
* `rpow_bExp_mul_le_opNorm`: Corollary 54 for symmetric matrices.

We write `s = p⁻¹.toReal` for `1/p`; then `s = 1/p.toReal` if `p < ∞` and `s = 0` if `p = ∞`.
-/

open Finset Matrix WithLp
open scoped ENNReal

namespace GsimOT.Hardness

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- `b(p) = max(1/p, 1 - 1/p)`, with `b(∞) = 1`. -/
noncomputable def bExp (p : ℝ≥0∞) : ℝ := max p⁻¹.toReal (1 - p⁻¹.toReal)

/-- Jensen's inequality for weights of total mass at most `1`. -/
lemma rpow_sum_mul_le {ι : Type*} (s : Finset ι) (a y : ι → ℝ) (ha : ∀ j ∈ s, 0 ≤ a j)
    (hsum : ∑ j ∈ s, a j ≤ 1) (hy : ∀ j ∈ s, 0 ≤ y j) {r : ℝ} (hr : 1 ≤ r) :
    (∑ j ∈ s, a j * y j) ^ r ≤ ∑ j ∈ s, a j * y j ^ r := by
  set α := ∑ j ∈ s, a j
  have hr0 : 0 < r := by linarith
  rcases (sum_nonneg ha).eq_or_lt with hα | hα
  · have h0 : ∀ j ∈ s, a j = 0 := (sum_eq_zero_iff_of_nonneg ha).mp hα.symm
    rw [sum_eq_zero fun j hj ↦ by rw [h0 j hj, zero_mul],
      sum_eq_zero fun j hj ↦ by rw [h0 j hj, zero_mul], Real.zero_rpow hr0.ne']
  · have hαne : α ≠ 0 := hα.ne'
    have hJ := Real.rpow_arith_mean_le_arith_mean_rpow (s := s) (fun j ↦ a j / α) y
      (fun j hj ↦ div_nonneg (ha j hj) hα.le) (by rw [← sum_div, div_self hα.ne']) hy hr
    have h1 : ∑ j ∈ s, a j * y j = α * ∑ j ∈ s, a j / α * y j := by
      rw [mul_sum]
      exact sum_congr rfl fun j _ ↦ by field_simp [hαne]
    have h2 : ∑ j ∈ s, a j * y j ^ r = α * ∑ j ∈ s, a j / α * y j ^ r := by
      rw [mul_sum]
      exact sum_congr rfl fun j _ ↦ by field_simp [hαne]
    have hX : 0 ≤ ∑ j ∈ s, a j / α * y j :=
      sum_nonneg fun j hj ↦ mul_nonneg (div_nonneg (ha j hj) hα.le) (hy j hj)
    have hY : 0 ≤ ∑ j ∈ s, a j / α * y j ^ r :=
      sum_nonneg fun j hj ↦ mul_nonneg (div_nonneg (ha j hj) hα.le) (by have := hy j hj; positivity)
    have hαr : α ^ r ≤ α := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hα hsum hr
    rw [h1, h2, Real.mul_rpow hα.le hX]
    calc α ^ r * (∑ j ∈ s, a j / α * y j) ^ r ≤ α ^ r * ∑ j ∈ s, a j / α * y j ^ r := by
          gcongr
      _ ≤ α * ∑ j ∈ s, a j / α * y j ^ r := by gcongr

section Norms

variable {p : ℝ≥0∞} [hp1 : Fact (1 ≤ p)]

include hp1 in
lemma one_le_toReal (hp : p ≠ ∞) : 1 ≤ p.toReal := by
  simpa using ENNReal.toReal_mono hp hp1.out

include hp1 in
lemma toReal_pos' (hp : p ≠ ∞) : 0 < p.toReal := lt_of_lt_of_le one_pos (one_le_toReal hp)

omit hp1 in
lemma toReal_inv_eq (p : ℝ≥0∞) : p⁻¹.toReal = 1 / p.toReal := by
  rw [ENNReal.toReal_inv, one_div]

include hp1 in
lemma toReal_inv_le_one : p⁻¹.toReal ≤ 1 := by
  by_cases hp : p = ∞
  · simp [hp]
  · rw [toReal_inv_eq p]
    exact (div_le_one (toReal_pos' hp)).mpr (one_le_toReal hp)

lemma abs_le_norm_toLp (x : X → ℝ) (i : X) : |x i| ≤ ‖toLp p x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (toLp p x) i

lemma norm_toLp_eq (hp : p ≠ ∞) (x : X → ℝ) :
    ‖toLp p x‖ = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal) := by
  rw [PiLp.norm_eq_sum (toReal_pos' hp)]
  simp [Real.norm_eq_abs]

/-- Comparing `ℓ^p` norms through their `p`-th power sums (for `p < ∞`). -/
lemma norm_toLp_le_norm_toLp (hp : p ≠ ∞) {x : X → ℝ} {y : Y → ℝ}
    (h : ∑ i, |x i| ^ p.toReal ≤ ∑ j, |y j| ^ p.toReal) : ‖toLp p x‖ ≤ ‖toLp p y‖ := by
  rw [norm_toLp_eq hp, norm_toLp_eq hp]
  have := toReal_pos' hp
  exact Real.rpow_le_rpow (sum_nonneg fun _ _ ↦ by positivity) h (by positivity)

lemma norm_toLp_top_le {x : X → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, |x i| ≤ C) :
    ‖toLp ∞ x‖ ≤ C := by
  rw [PiLp.norm_eq_ciSup]
  rcases isEmpty_or_nonempty X with hX | hX
  · simp [hC]
  · exact ciSup_le fun i ↦ by simpa [Real.norm_eq_abs] using h i

/-- **Schur test**: if all absolute row and column sums of `M` are at most `1`, then
`‖M‖_p ≤ 1`. -/
lemma opNorm_le_one_of_sum_abs_le_one [DecidableEq Y] {M : Matrix X Y ℝ}
    (hrow : ∀ i, ∑ j, |M i j| ≤ 1) (hcol : ∀ j, ∑ i, |M i j| ≤ 1) : opNorm p p M ≤ 1 := by
  refine opNorm_le_of_forall zero_le_one fun x ↦ ?_
  rw [one_mul]
  have habs (i : X) : |(M *ᵥ x) i| ≤ ∑ j, |M i j| * |x j| :=
    (abs_sum_le_sum_abs _ _).trans (le_of_eq (by simp [abs_mul]))
  by_cases hp : p = ∞
  · subst hp
    refine norm_toLp_top_le (norm_nonneg _) fun i ↦ ?_
    calc |(M *ᵥ x) i| ≤ ∑ j, |M i j| * |x j| := habs i
      _ ≤ ∑ j, |M i j| * ‖toLp ∞ x‖ := by
          gcongr with j
          exact abs_le_norm_toLp x j
      _ = (∑ j, |M i j|) * ‖toLp ∞ x‖ := by rw [sum_mul]
      _ ≤ 1 * ‖toLp ∞ x‖ := by gcongr; exact hrow i
      _ = ‖toLp ∞ x‖ := one_mul _
  · have hr := one_le_toReal hp
    have hr0 := toReal_pos' hp
    refine norm_toLp_le_norm_toLp hp ?_
    have key (i : X) : |(M *ᵥ x) i| ^ p.toReal ≤ ∑ j, |M i j| * |x j| ^ p.toReal :=
      (Real.rpow_le_rpow (abs_nonneg _) (habs i) hr0.le).trans
        (rpow_sum_mul_le univ _ _ (fun j _ ↦ abs_nonneg _) (hrow i) (fun j _ ↦ abs_nonneg _) hr)
    calc ∑ i, |(M *ᵥ x) i| ^ p.toReal ≤ ∑ i, ∑ j, |M i j| * |x j| ^ p.toReal :=
          sum_le_sum fun i _ ↦ key i
      _ = ∑ j, (∑ i, |M i j|) * |x j| ^ p.toReal := by
          rw [sum_comm]
          simp [sum_mul]
      _ ≤ ∑ j, 1 * |x j| ^ p.toReal := by
          gcongr with j
          exact hcol j
      _ = ∑ j, |x j| ^ p.toReal := by simp

/-- Test vector `e_v`: every column has `ℓ^p` norm at most `‖A‖_p`. -/
lemma norm_col_le_opNorm [DecidableEq X] (A : Matrix X X ℝ) (v : X) :
    ‖toLp p fun i ↦ A i v‖ ≤ opNorm p p A := by
  have h := norm_mulVec_le_opNorm (p := p) (q := p) A (Pi.single v 1)
  have h1 : ‖toLp p (Pi.single v (1 : ℝ) : X → ℝ)‖ = 1 := by
    rw [PiLp.toLp_single, PiLp.norm_single, norm_one]
  rw [h1, mul_one, Matrix.mulVec_single_one] at h
  exact h

/-- **Corollary 54** for symmetric matrices: if column `v` of the symmetric matrix `A` has `#K`
entries of absolute value at least `ε`, then `#K ^ b(p) · ε ≤ ‖A‖_p`. The two test vectors are
`e_v` (giving `#K ^ (1/p) ε`) and a signed indicator of `K` (giving `#K ^ (1 - 1/p) ε`). -/
lemma rpow_bExp_mul_le_opNorm [DecidableEq X] {A : Matrix X X ℝ} (hA : A.IsSymm) {v : X}
    {K : Finset X} {ε : ℝ} (hε : 0 ≤ ε) (hK : ∀ i ∈ K, ε ≤ |A i v|) :
    ((#K : ℕ) : ℝ) ^ bExp p * ε ≤ opNorm p p A := by
  set s := p⁻¹.toReal
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hs1 : s ≤ 1 := toReal_inv_le_one
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · have hb : 0 < bExp p := lt_of_lt_of_le (by norm_num) (show (1 / 2 : ℝ) ≤ bExp p by
      unfold bExp; rcases le_total s (1 / 2) with h | h
      · exact le_max_of_le_right (by linarith)
      · exact le_max_of_le_left h)
    simp [hK0, Real.zero_rpow hb.ne', opNorm_nonneg]
  rcases hε.eq_or_lt with hε0 | hεpos
  · simp [← hε0, opNorm_nonneg]
  set k : ℝ := ((#K : ℕ) : ℝ)
  have hk1 : 1 ≤ k := Nat.one_le_cast.mpr hKne.card_pos
  have hk0 : 0 < k := by linarith
  -- first test vector: `e_v`
  have hfirst : k ^ s * ε ≤ opNorm p p A := by
    refine le_trans ?_ (norm_col_le_opNorm A v)
    by_cases hp : p = ∞
    · obtain ⟨i, hi⟩ := hKne
      have hs : s = 0 := by simp [s, hp]
      rw [hs, Real.rpow_zero, one_mul]
      exact (hK i hi).trans (abs_le_norm_toLp (fun i ↦ A i v) i)
    · have hr0 := toReal_pos' hp
      rw [norm_toLp_eq hp]
      have hsr : s = 1 / p.toReal := toReal_inv_eq p
      calc k ^ s * ε = (k * ε ^ p.toReal) ^ (1 / p.toReal) := by
            rw [Real.mul_rpow hk0.le (by positivity), ← Real.rpow_mul hε, hsr]
            field_simp
            rw [Real.rpow_one]
        _ ≤ (∑ i, |A i v| ^ p.toReal) ^ (1 / p.toReal) := by
            gcongr
            calc k * ε ^ p.toReal = ∑ _i ∈ K, ε ^ p.toReal := by simp [k]
              _ ≤ ∑ i ∈ K, |A i v| ^ p.toReal := sum_le_sum fun i hi ↦ by gcongr; exact hK i hi
              _ ≤ ∑ i, |A i v| ^ p.toReal :=
                  sum_le_sum_of_subset_of_nonneg (subset_univ K) fun _ _ _ ↦ by positivity
  -- second test vector: the signed indicator `x` of `K`
  have hsecond : k ^ (1 - s) * ε ≤ opNorm p p A := by
    set x : X → ℝ := fun i ↦ if i ∈ K then (if 0 ≤ A v i then 1 else -1) else 0
    have hxabs (i : X) : |x i| = if i ∈ K then 1 else 0 := by
      simp only [x]; split_ifs <;> simp
    have hAx : k * ε ≤ |(A *ᵥ x) v| := by
      have : (A *ᵥ x) v = ∑ i ∈ K, |A v i| := by
        simp only [Matrix.mulVec, dotProduct, x, mul_ite, mul_one, mul_neg, mul_zero]
        rw [← sum_filter_add_sum_filter_not univ (· ∈ K)]
        simp only [filter_mem_eq_inter, univ_inter]
        rw [sum_eq_zero (s := filter (· ∉ K) univ) fun i hi ↦ by simp [(mem_filter.mp hi).2],
          add_zero]
        refine sum_congr rfl fun i hi ↦ ?_
        simp only [hi, ite_true]
        split_ifs with h
        · exact (abs_of_nonneg h).symm
        · exact (abs_of_neg (not_le.mp h)).symm
      rw [this, abs_of_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _)]
      calc k * ε = ∑ _i ∈ K, ε := by simp [k]
        _ ≤ ∑ i ∈ K, |A v i| := sum_le_sum fun i hi ↦ by rw [hA.apply i v]; exact hK i hi
    have hxnorm : ‖toLp p x‖ = k ^ s := by
      by_cases hp : p = ∞
      · have hs : s = 0 := by simp [s, hp]
        rw [hs, Real.rpow_zero]
        subst hp
        apply le_antisymm
        · exact norm_toLp_top_le zero_le_one fun i ↦ by rw [hxabs]; split_ifs <;> norm_num
        · obtain ⟨i, hi⟩ := hKne
          calc (1 : ℝ) = |x i| := by rw [hxabs, ite_eq_left hi]
            _ ≤ _ := abs_le_norm_toLp x i
      · have hsr : s = 1 / p.toReal := toReal_inv_eq p
        rw [norm_toLp_eq hp, hsr]
        congr 1
        have hr0 := toReal_pos' hp
        have hterm (i : X) :
            (if i ∈ K then (1 : ℝ) else 0) ^ p.toReal = if i ∈ K then 1 else 0 := by
          split_ifs <;> simp [Real.zero_rpow hr0.ne']
        simp only [hxabs, hterm, sum_boole]
        simp [k]
    have h := norm_mulVec_le_opNorm (p := p) (q := p) A x
    rw [hxnorm] at h
    have h2 := (hAx.trans (abs_le_norm_toLp (A *ᵥ x) v)).trans h
    have hks : 0 < k ^ s := Real.rpow_pos_of_pos hk0 s
    calc k ^ (1 - s) * ε = k * ε / k ^ s := by
          rw [Real.rpow_sub hk0, Real.rpow_one]; ring
      _ ≤ opNorm p p A * k ^ s / k ^ s := by gcongr
      _ = opNorm p p A := by field_simp
  unfold bExp
  rcases le_total s (1 - s) with h | h
  · rw [max_eq_right h]; exact hsecond
  · rw [max_eq_left h]; exact hfirst

end Norms

end GsimOT.Hardness
