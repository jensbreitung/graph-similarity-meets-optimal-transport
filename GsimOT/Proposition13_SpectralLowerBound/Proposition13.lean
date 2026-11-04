/-
# Proposition 13 and Theorem 3 (4)

Paper, Section 3.4 (Proposition 13, p. 11, l. 389–390, and the remark after it, l. 391–393),
Theorem 3 (4) (p. 4, l. 127) and Appendix F.1 (proof of Proposition 13, p. 46, l. 1447–1448).

* `proposition13`: Proposition 13, `n = 4r² + 3r + 1`, `d_2(G_r, H_r) = √r` and
  `1/(2√2) ≤ d^OT_2(G_r, H_r) ≤ 1`.
* `proposition13_explicit`: Proposition 13 together with the bound `r/√n ≤ d^OT_2(G_r, H_r)` of Lemma 49,
  i.e. `1/(2√2) ≤ r/√n ≤ d^OT_2(G_r, H_r) ≤ 1`.
* `theorem3_item4`: Theorem 3 (4), `δ_2(G_r, H_r) ≥ √r · δ^OT_2(G_r, H_r)`.
* `no_power_bound`: the remark after Proposition 13: since `δ_2(G_r, H_r) = Θ(n^{-3/4})` and
  `δ^OT_2(G_r, H_r) = Θ(n^{-1})`, there is no uniform bound `δ_2 ≤ C (δ^OT_2)^α` for any `α > 3/4`.
-/
import GsimOT.Proposition13_SpectralLowerBound.Lemma49

open Finset

namespace GsimOT.Prop13

/-- **Proposition 13 with the bound of Lemma 49.** For every `r ≥ 1` the graphs `G_r, H_r` on
`n = 4r² + 3r + 1` vertices satisfy `d_2(G_r, H_r) = √r` and
`1/(2√2) ≤ r/√n ≤ d^OT_2(G_r, H_r) ≤ 1`. As in the proof (p. 46, l. 1447–1448): Lemma 49,
`d_2(G_r, H_r) = √r`, and `r/√n ≥ 1/(2√2)` since `8r² ≥ n`. -/
theorem proposition13_explicit (r : ℕ) (hr : 1 ≤ r) :
    Fintype.card (Vtx r) = 4 * r ^ 2 + 3 * r + 1 ∧
      distPQ 2 2 (Gr r) (Hr r) = Real.sqrt r ∧
      1 / (2 * Real.sqrt 2) ≤ r / Real.sqrt (4 * r ^ 2 + 3 * r + 1) ∧
      r / Real.sqrt (4 * r ^ 2 + 3 * r + 1) ≤ dOT 2 2 (Gr r) (Hr r) ∧
      dOT 2 2 (Gr r) (Hr r) ≤ 1 := by
  refine ⟨card_Vtx r, distPQ_eq r, ?_, lemma49 r hr⟩
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hn : (0 : ℝ) < 4 * r ^ 2 + 3 * r + 1 := by positivity
  rw [div_le_div_iff₀ (by positivity) (Real.sqrt_pos.2 hn), one_mul]
  -- `√n ≤ 2√2 r` since `n ≤ 8r²`
  have h8 : (4 * r ^ 2 + 3 * r + 1 : ℝ) ≤ (2 * Real.sqrt 2 * r) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith
  calc Real.sqrt (4 * r ^ 2 + 3 * r + 1) ≤ Real.sqrt ((2 * Real.sqrt 2 * r) ^ 2) :=
        Real.sqrt_le_sqrt h8
    _ = r * (2 * Real.sqrt 2) := by rw [Real.sqrt_sq (by positivity)]; ring

/-- **Proposition 13** (p. 11, l. 389–390). For every `r ≥ 1` there are graphs `G_r, H_r` on
`n = 4r² + 3r + 1 = Θ(r²)` vertices with `d_2(G_r, H_r) = √r` and
`1/(2√2) ≤ d^OT_2(G_r, H_r) ≤ 1`. -/
theorem proposition13 (r : ℕ) (hr : 1 ≤ r) :
    Fintype.card (Vtx r) = 4 * r ^ 2 + 3 * r + 1 ∧
      distPQ 2 2 (Gr r) (Hr r) = Real.sqrt r ∧
      1 / (2 * Real.sqrt 2) ≤ dOT 2 2 (Gr r) (Hr r) ∧ dOT 2 2 (Gr r) (Hr r) ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := proposition13_explicit r hr
  exact ⟨h1, h2, h3.trans h4, h5⟩

/-! ## Normalised distances -/

lemma kappa_two : kappa 2 2 = 1 := by simp [kappa]

instance (r : ℕ) : Nonempty (Vtx r) := ⟨.inl none⟩

/-- `δ_2(G_r, H_r) = √r / n`. -/
lemma deltaPQ_eq (r : ℕ) :
    deltaPQ 2 2 (Gr r) (Hr r) = Real.sqrt r / (4 * r ^ 2 + 3 * r + 1) := by
  rw [deltaPQ, distPQ_eq, kappa_two, card_Vtx, Real.rpow_neg_one]
  push_cast
  ring

/-- `0 ≤ δ^OT_2(G_r, H_r) ≤ 1/n`. -/
lemma deltaOTPQ_bounds (r : ℕ) (hr : 1 ≤ r) :
    0 ≤ deltaOTPQ 2 2 (Gr r) (Hr r) ∧
      deltaOTPQ 2 2 (Gr r) (Hr r) ≤ 1 / (4 * r ^ 2 + 3 * r + 1) := by
  rw [deltaOTPQ_eq_dOT 2 2 (Gr r) (Hr r) (by norm_num) (by norm_num) rfl, kappa_two, card_Vtx,
    Real.rpow_neg_one]
  push_cast
  have hn : (0 : ℝ) < 4 * r ^ 2 + 3 * r + 1 := by positivity
  have h0 : 0 ≤ dOT 2 2 (Gr r) (Hr r) := le_trans (by positivity) (lemma49 r hr).1
  have h1 := (lemma49 r hr).2
  refine ⟨by positivity, ?_⟩
  rw [one_div]
  exact mul_le_of_le_one_right (by positivity) h1

/-- **Theorem 3 (4)** (p. 4, l. 127). For every `r ≥ 1`, `δ_2(G_r, H_r) ≥ √r · δ^OT_2(G_r, H_r)`. -/
theorem theorem3_item4 (r : ℕ) (hr : 1 ≤ r) :
    Real.sqrt r * deltaOTPQ 2 2 (Gr r) (Hr r) ≤ deltaPQ 2 2 (Gr r) (Hr r) := by
  rw [deltaPQ_eq]
  calc Real.sqrt r * deltaOTPQ 2 2 (Gr r) (Hr r)
      ≤ Real.sqrt r * (1 / (4 * r ^ 2 + 3 * r + 1)) :=
        mul_le_mul_of_nonneg_left (deltaOTPQ_bounds r hr).2 (Real.sqrt_nonneg _)
    _ = Real.sqrt r / (4 * r ^ 2 + 3 * r + 1) := by ring

/-- **Remark after Proposition 13** (p. 11, l. 391–393). There is no uniform bound
`δ_2 ≤ C (δ^OT_2)^α` with `α > 3/4`: for every `C` some `G_r, H_r` violate it. -/
theorem no_power_bound {α : ℝ} (hα : 3 / 4 < α) (C : ℝ) :
    ∃ r : ℕ, 1 ≤ r ∧ C * deltaOTPQ 2 2 (Gr r) (Hr r) ^ α < deltaPQ 2 2 (Gr r) (Hr r) := by
  rcases le_or_gt C 0 with hC | hC
  · refine ⟨1, le_rfl, ?_⟩
    rw [deltaPQ_eq]
    have h0 := Real.rpow_nonneg (deltaOTPQ_bounds 1 le_rfl).1 α
    have : (0 : ℝ) < Real.sqrt ((1 : ℕ) : ℝ) / (4 * ((1 : ℕ) : ℝ) ^ 2 + 3 * ((1 : ℕ) : ℝ) + 1) := by
      norm_num
    nlinarith
  -- reduce to an exponent `a ∈ (3/4, 1]`
  obtain ⟨a, haα, ha1, ha⟩ : ∃ a : ℝ, a ≤ α ∧ a ≤ 1 ∧ 3 / 4 < a :=
    ⟨min α 1, min_le_left _ _, min_le_right _ _, lt_min hα (by norm_num)⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = 2 * a - 3 / 2 := ⟨_, rfl⟩
  have hβ : 0 < β := by rw [hβdef]; linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = C * (8 : ℝ) ^ (1 - a) := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max K 1 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hMdef]; exact le_trans zero_le_one (le_max_right _ _)
  refine ⟨⌈M ^ β⁻¹⌉₊ + 1, by omega, ?_⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, r = ⌈M ^ β⁻¹⌉₊ + 1 := ⟨_, rfl⟩
  rw [← hrdef]
  have hr1 : 1 ≤ r := by omega
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrpos : (0 : ℝ) < r := by linarith
  -- `K < r^β`
  have hKr : K < (r : ℝ) ^ β := by
    have hlt : M ^ β⁻¹ < r := by
      rw [hrdef]; push_cast
      linarith [Nat.le_ceil (M ^ β⁻¹)]
    calc K ≤ M := by rw [hMdef]; exact le_max_left _ _
      _ = (M ^ β⁻¹) ^ β := (Real.rpow_inv_rpow hM0 hβ.ne').symm
      _ < (r : ℝ) ^ β := Real.rpow_lt_rpow (Real.rpow_nonneg hM0 _) hlt hβ
  rw [deltaPQ_eq]
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = 4 * (r : ℝ) ^ 2 + 3 * r + 1 := ⟨_, rfl⟩
  rw [← hNdef]
  have hN1 : 1 ≤ N := by rw [hNdef]; nlinarith [sq_nonneg (r : ℝ)]
  have hNpos : 0 < N := by linarith
  have hN8 : N ≤ 8 * (r : ℝ) ^ 2 := by rw [hNdef]; nlinarith
  obtain ⟨h0, h1⟩ := deltaOTPQ_bounds r hr1
  rw [← hNdef] at h1
  have hd1 : deltaOTPQ 2 2 (Gr r) (Hr r) ≤ 1 :=
    h1.trans (by rw [div_le_one hNpos]; exact hN1)
  -- `(δ^OT)^α ≤ (1/N)^a = N^{1-a} / N`
  have hstep1 : deltaOTPQ 2 2 (Gr r) (Hr r) ^ α ≤ N ^ (1 - a) / N := by
    calc deltaOTPQ 2 2 (Gr r) (Hr r) ^ α ≤ deltaOTPQ 2 2 (Gr r) (Hr r) ^ a :=
          Real.rpow_le_rpow_of_exponent_ge' h0 hd1 (by linarith) haα
      _ ≤ (1 / N) ^ a := Real.rpow_le_rpow h0 h1 (by linarith)
      _ = N ^ (1 - a) / N := by
          rw [Real.div_rpow zero_le_one hNpos.le, Real.one_rpow, Real.rpow_sub hNpos,
            Real.rpow_one]
          field_simp
  -- `N^{1-a} ≤ 8^{1-a} r^{2(1-a)}`
  have hstep2 : N ^ (1 - a) ≤ (8 : ℝ) ^ (1 - a) * (r : ℝ) ^ (2 * (1 - a)) := by
    calc N ^ (1 - a) ≤ (8 * (r : ℝ) ^ 2) ^ (1 - a) :=
          Real.rpow_le_rpow hNpos.le hN8 (by linarith)
      _ = (8 : ℝ) ^ (1 - a) * (r : ℝ) ^ (2 * (1 - a)) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_mul hrpos.le]
          norm_cast
  -- `r^β r^{2(1-a)} = √r`
  have hstep3 : (r : ℝ) ^ β * (r : ℝ) ^ (2 * (1 - a)) = Real.sqrt r := by
    rw [← Real.rpow_add hrpos, Real.sqrt_eq_rpow, hβdef]
    congr 1; ring
  have hpos : 0 < (r : ℝ) ^ (2 * (1 - a)) := Real.rpow_pos_of_pos hrpos _
  calc C * deltaOTPQ 2 2 (Gr r) (Hr r) ^ α ≤ C * (N ^ (1 - a) / N) :=
        mul_le_mul_of_nonneg_left hstep1 hC.le
    _ ≤ C * ((8 : ℝ) ^ (1 - a) * (r : ℝ) ^ (2 * (1 - a)) / N) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hstep2 hNpos.le) hC.le
    _ = K * (r : ℝ) ^ (2 * (1 - a)) / N := by rw [hKdef]; ring
    _ < (r : ℝ) ^ β * (r : ℝ) ^ (2 * (1 - a)) / N := by
        apply div_lt_div_of_pos_right _ hNpos
        exact mul_lt_mul_of_pos_right hKr hpos
    _ = Real.sqrt r / N := by rw [hstep3]

end GsimOT.Prop13
