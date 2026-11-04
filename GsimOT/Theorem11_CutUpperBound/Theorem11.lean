/-
# Theorem 11: the cut distance is bounded by its optimal transport relaxation

Paper: Theorem 11 (p. 10, l. 333–337), Theorem 2 (cut part, p. 3, l. 118–120), and the proof in
Appendix E.2.3 (p. 44, l. 1362–1379).

* Graph facts: `costCut_permMat` (`C_□(P_π) = ‖A_G^π - A_H‖_□`), `costCut_le_sq`, attainment of
  `d^OT_□` (`exists_costCut_eq_dOTCut`, via compactness of `DS(V, W)`), the lower bound
  `deltaOTCut_le_deltaCut`, and `deltaCut_le_zero_of_card_eq_one` (the case `n = 1`; Appendix E.2
  assumes `n ≥ 2`, p. 32, l. 1003).
* Numerics of E.2.3: `one_lt_log_four_mul_log_log_eight`, `dn_mul_log_two_le`, `error_term_le`,
  `log_fourteen_lt_three`, `main_numeric`, `power_numeric`, `power_numeric_lt_one`.
* `eq39`: Eq. (39) with `C₁ = 1 + 4 C_thin`, from Theorem 38.
* `theorem11`: Theorem 11; `theorem11_power_lt_one`: the power bound for every `α < 1`
  (`theorem11_power`: the special case `0 < α < 1`); `theorem2_cut_of_thin`: the cut part of
  Theorem 2.
-/
import GsimOT.Theorem11_CutUpperBound.Theorem39_AdditiveRounding
import GsimOT.Theorem11_CutUpperBound.Theorem38_ThinRounding
import GsimOT.Theorem11_CutUpperBound.ContractionPrinciple

open Finset

namespace GsimOT

/-- `d_n ln 2 ≤ 3 ln n` for `n ≥ 2` (proof of Theorem 11, E.2.3, p. 44, l. 1373:
`d_n ≤ 2 log n + 1 ≤ 3 log n = (3 / ln 2) ln n`, `log` binary). -/
lemma dn_mul_log_two_le {n : ℕ} (hn : 2 ≤ n) :
    (dn n : ℝ) * Real.log 2 ≤ 3 * Real.log n := by
  have hx : 1 < n ^ 2 := by nlinarith
  have h := Nat.pow_pred_clog_lt_self (b := 2) one_lt_two hx
  have hpos : (0 : ℝ) < 2 ^ (Nat.clog 2 (n ^ 2)).pred := by positivity
  have hR : ((2 : ℝ) ^ (Nat.clog 2 (n ^ 2)).pred) < (n : ℝ) ^ 2 := by exact_mod_cast h
  have hlog := Real.log_lt_log hpos hR
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  have hle : (dn n : ℝ) ≤ ((Nat.clog 2 (n ^ 2)).pred : ℝ) + 1 := by
    unfold dn
    have : Nat.clog 2 (n ^ 2) ≤ (Nat.clog 2 (n ^ 2)).pred + 1 := by
      rw [Nat.pred_eq_sub_one]; omega
    exact_mod_cast this
  have hl2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- `ln z ≤ z / e` for `z > 0`. -/
lemma log_le_div_exp_one {z : ℝ} (hz : 0 < z) : Real.log z ≤ z / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hz (Real.exp_pos 1))
  rw [Real.log_div hz.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

/-- The error term of Theorem 39 in the case `n > ε⁻¹²` of the proof of Theorem 11 (E.2.3,
p. 44, l. 1372–1376): `36 √(d_n) n^{-1/6} ≤ 112 ε`. The paper substitutes `n = ε⁻¹²` into the
decreasing function `x ↦ x^{-1/6} √(ln x)` and uses `ε √(ln(1/ε)) ≤ (2e)^{-1/2}`; here
`m = n^{1/6} > ε⁻²` and `ln m ≤ m/e` (the same inequality) give the same constant without the
monotonicity. -/
lemma error_term_le {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn2 : 2 ≤ n) (hn : (1 / ε) ^ 12 < n) :
    36 * Real.sqrt (dn n) * (n : ℝ) ^ (-(1 / 6 : ℝ)) ≤ 112 * ε := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hm : 0 < (n : ℝ) ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hnpos _
  have hm6 : ((n : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  have hneg : (n : ℝ) ^ (-(1 / 6 : ℝ)) = ((n : ℝ) ^ (1 / 6 : ℝ))⁻¹ := Real.rpow_neg hnpos.le _
  rw [hneg]
  generalize (n : ℝ) ^ (1 / 6 : ℝ) = m at hm hm6
  have hmε : (1 / ε) ^ 2 < m := by
    refine lt_of_pow_lt_pow_left₀ 6 hm.le ?_
    rw [hm6, ← pow_mul]; exact hn
  have hmε' : 1 < ε ^ 2 * m := by
    rw [div_pow, one_pow, div_lt_iff₀ (by positivity)] at hmε; linarith
  have hlogn : Real.log n = 6 * Real.log m := by rw [← hm6, Real.log_pow]; norm_num
  have hlogm := log_le_div_exp_one hm
  have hd := dn_mul_log_two_le hn2
  have he := Real.exp_one_gt_d9
  have hl2 := Real.log_two_gt_d9
  have hl2pos : 0 < Real.log 2 := by linarith
  -- `d_n ≤ 18 m / (e ln 2)`
  have hd' : (dn n : ℝ) * (Real.log 2 * Real.exp 1) ≤ 18 * m := by
    have : Real.log m * Real.exp 1 ≤ m := by rwa [le_div_iff₀ (Real.exp_pos 1)] at hlogm
    nlinarith
  have hsq : (dn n : ℝ) ≤ (112 / 36 * ε * m) ^ 2 := by
    have hc : 18 * m ≤ (112 / 36 * ε * m) ^ 2 * (Real.log 2 * Real.exp 1) := by
      have h1 : m ≤ ε ^ 2 * m * m := by nlinarith
      have h2 : 1.88 ≤ Real.log 2 * Real.exp 1 := by nlinarith
      have h3 : (112 / 36 * ε * m) ^ 2 = (112 / 36) ^ 2 * (ε ^ 2 * m * m) := by ring
      rw [h3]
      have : 0 ≤ ε ^ 2 * m * m := by positivity
      nlinarith
    have hpos : 0 < Real.log 2 * Real.exp 1 := by positivity
    exact le_of_mul_le_mul_right (hd'.trans hc) hpos
  have hsqrt : Real.sqrt (dn n) ≤ 112 / 36 * ε * m := by
    rw [Real.sqrt_le_left (by positivity)]
    exact hsq
  rw [mul_inv_le_iff₀ hm]
  nlinarith

/-- `ln 14 < 3`, used in the case `n ≤ ε⁻¹²` of the proof of Theorem 11 (E.2.3, p. 44,
l. 1369–1371). -/
lemma log_fourteen_lt_three : Real.log 14 < 3 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have he := Real.exp_one_gt_d9
  rw [h]; nlinarith

/-- The numerical core of the proof of Theorem 11 (E.2.3, p. 44, l. 1363–1376). Let `ε = ζ_Q`
for an optimal `Q`, `δ = δ_□(G, H)` and `n ≥ 2`. Given `δ ≤ 1`, Eq. (39) and the bound of
Theorem 39, we get `δ ≤ C ε ln(e/ε) ln(e ln(e/ε))` with `C = max{2, 39 C₁, 113}`: the cases
`ε = 0`, `ε ≥ 1/2`, `n ≤ ε⁻¹²` and `n > ε⁻¹²` of the paper. -/
lemma main_numeric {C1 ε δ : ℝ} {n : ℕ} (hC1 : 0 < C1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hδ1 : δ ≤ 1) (hn2 : 2 ≤ n)
    (h33 : δ ≤ C1 * Real.log (2 * n) * Real.log (Real.log (4 * n)) * ε)
    (h45 : δ ≤ ε + 36 * Real.sqrt (dn n) * (n : ℝ) ^ (-(1 / 6 : ℝ))) :
    δ ≤ max (max 2 (39 * C1)) 113 * ε * Real.log (Real.exp 1 / ε) *
      Real.log (Real.exp 1 * Real.log (Real.exp 1 / ε)) := by
  have he := Real.exp_one_gt_d9
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  -- case `ε = 0`
  rcases hε0.eq_or_lt with h0 | hεpos
  · subst h0
    have hl : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
    have hl4 : 0 ≤ Real.log (Real.log (4 * n)) := by
      apply Real.log_nonneg
      have : Real.log 4 ≤ Real.log (4 * n) := Real.log_le_log (by norm_num) (by linarith)
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    simpa using h33
  -- `L = ln(e/ε) = 1 + ln(1/ε) ≥ 1` and `ln(e L) = 1 + ln L ≥ 1`
  have hL : Real.log (Real.exp 1 / ε) = 1 + Real.log (1 / ε) := by
    rw [div_eq_mul_one_div, Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  have hinv : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg (by rw [le_div_iff₀ hεpos]; linarith)
  rw [hL]
  have hL1 : 1 ≤ 1 + Real.log (1 / ε) := by linarith
  have hM : Real.log (Real.exp 1 * (1 + Real.log (1 / ε))) =
      1 + Real.log (1 + Real.log (1 / ε)) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  rw [hM]
  have hlogL : 0 ≤ Real.log (1 + Real.log (1 / ε)) := Real.log_nonneg hL1
  have hC2 : 2 ≤ max (max 2 (39 * C1)) 113 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC39 : 39 * C1 ≤ max (max 2 (39 * C1)) 113 :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hC113 : 113 ≤ max (max 2 (39 * C1)) 113 := le_max_right _ _
  generalize max (max 2 (39 * C1)) 113 = C at hC2 hC39 hC113
  have hprod : 1 ≤ (1 + Real.log (1 / ε)) * (1 + Real.log (1 + Real.log (1 / ε))) := by
    nlinarith
  -- case `ε ≥ 1/2`
  by_cases hhalf : 1 / 2 ≤ ε
  · calc δ ≤ 1 := hδ1
      _ ≤ C * ε * 1 := by nlinarith
      _ ≤ C * ε * ((1 + Real.log (1 / ε)) * (1 + Real.log (1 + Real.log (1 / ε)))) := by
          gcongr
      _ = _ := by ring
  push Not at hhalf
  have hinvε : 2 < 1 / ε := by rw [lt_div_iff₀ hεpos]; linarith
  by_cases hsmall : (n : ℝ) ≤ (1 / ε) ^ 12
  · -- case `n ≤ ε⁻¹²`
    have hlogn : Real.log n ≤ 12 * Real.log (1 / ε) := by
      have := Real.log_le_log (by linarith) hsmall
      rwa [Real.log_pow] at this
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hnR
    have h2n : Real.log (2 * n) ≤ 13 * (1 + Real.log (1 / ε)) := by
      rw [Real.log_mul (by norm_num) (by linarith)]; linarith
    have h2n0 : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h4n : Real.log (4 * n) ≤ 14 * (1 + Real.log (1 / ε)) := by
      rw [Real.log_mul (by norm_num) (by linarith)]; linarith
    have h4n1 : 1 < Real.log (4 * n) := by
      rw [Real.log_mul (by norm_num) (by linarith)]; linarith
    have hll : Real.log (Real.log (4 * n)) ≤ 3 * (1 + Real.log (1 + Real.log (1 / ε))) := by
      have := Real.log_le_log (by linarith) h4n
      rw [Real.log_mul (x := 14) (by norm_num) (by linarith)] at this
      have := log_fourteen_lt_three
      linarith
    have hll0 : 0 ≤ Real.log (Real.log (4 * n)) := Real.log_nonneg h4n1.le
    calc δ ≤ C1 * Real.log (2 * n) * Real.log (Real.log (4 * n)) * ε := h33
      _ ≤ C1 * (13 * (1 + Real.log (1 / ε))) * (3 * (1 + Real.log (1 + Real.log (1 / ε)))) *
          ε := by gcongr
      _ = 39 * C1 * ε * (1 + Real.log (1 / ε)) * (1 + Real.log (1 + Real.log (1 / ε))) := by
          ring
      _ ≤ C * ε * (1 + Real.log (1 / ε)) * (1 + Real.log (1 + Real.log (1 / ε))) := by
          gcongr
  · -- case `n > ε⁻¹²`
    push Not at hsmall
    have herr := error_term_le hεpos hn2 hsmall
    calc δ ≤ ε + 36 * Real.sqrt (dn n) * (n : ℝ) ^ (-(1 / 6 : ℝ)) := h45
      _ ≤ 113 * ε * 1 := by linarith
      _ ≤ C * ε * ((1 + Real.log (1 / ε)) * (1 + Real.log (1 + Real.log (1 / ε)))) := by
          gcongr
      _ = _ := by ring

/-- The power bound (end of E.2.3, p. 44, l. 1377): for `0 ≤ f ≤ 1` and `0 < α < 1`,
`f ln(e/f) ln(e ln(e/f)) ≤ (1 + 2/(1-α))² f^α`, i.e. `f^{1-α} ln(e/f) ln(e ln(e/f))` is bounded on
`(0, 1]`. -/
lemma power_numeric {f α : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hα0 : 0 < α) (hα1 : α < 1) :
    f * Real.log (Real.exp 1 / f) * Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) ≤
      (1 + 2 / (1 - α)) ^ 2 * f ^ α := by
  rcases hf0.eq_or_lt with h0 | hf
  · subst h0; simp [Real.zero_rpow hα0.ne']
  have hL : Real.log (Real.exp 1 / f) = 1 + Real.log (1 / f) := by
    rw [div_eq_mul_one_div, Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  have hinv : 0 ≤ Real.log (1 / f) :=
    Real.log_nonneg (by rw [le_div_iff₀ hf]; linarith)
  rw [hL]
  have hL1 : 1 ≤ 1 + Real.log (1 / f) := by linarith
  have hM : Real.log (Real.exp 1 * (1 + Real.log (1 / f))) ≤ 1 + Real.log (1 / f) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + Real.log (1 / f))
    linarith
  have hβ : 0 < (1 - α) / 2 := by linarith
  have hlog := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 1 / f) hβ
  have hu : (1 / f) ^ ((1 - α) / 2) = f ^ (-((1 - α) / 2)) := by
    rw [one_div, Real.inv_rpow hf.le, Real.rpow_neg hf.le]
  rw [hu] at hlog
  have hu1 : 1 ≤ f ^ (-((1 - α) / 2)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hf hf1 (by linarith)
  have hdiv : f ^ (-((1 - α) / 2)) / ((1 - α) / 2) = 2 / (1 - α) * f ^ (-((1 - α) / 2)) := by
    field_simp
  rw [hdiv] at hlog
  have hK : 0 ≤ 2 / (1 - α) := by apply div_nonneg <;> linarith
  have hLu : 1 + Real.log (1 / f) ≤ (1 + 2 / (1 - α)) * f ^ (-((1 - α) / 2)) := by nlinarith
  have hfα : f * (f ^ (-((1 - α) / 2)) * f ^ (-((1 - α) / 2))) = f ^ α := by
    rw [← Real.rpow_add hf, ← Real.rpow_one_add' hf.le (by
      have : 1 + (-((1 - α) / 2) + -((1 - α) / 2)) = α := by ring
      rw [this]; exact hα0.ne')]
    congr 1; ring
  have hM0 : 0 ≤ Real.log (Real.exp 1 * (1 + Real.log (1 / f))) := by
    apply Real.log_nonneg; nlinarith [Real.add_one_le_exp (1 : ℝ)]
  calc f * (1 + Real.log (1 / f)) * Real.log (Real.exp 1 * (1 + Real.log (1 / f)))
      ≤ f * (1 + Real.log (1 / f)) * (1 + Real.log (1 / f)) := by gcongr
    _ ≤ f * ((1 + 2 / (1 - α)) * f ^ (-((1 - α) / 2))) *
          ((1 + 2 / (1 - α)) * f ^ (-((1 - α) / 2))) := by gcongr
    _ = (1 + 2 / (1 - α)) ^ 2 * (f * (f ^ (-((1 - α) / 2)) * f ^ (-((1 - α) / 2)))) := by ring
    _ = _ := by rw [hfα]

/-- The power bound for every `α < 1` (end of E.2.3, p. 44, l. 1377): for `α ≤ 1/2` use the case
`α = 1/2` of `power_numeric` and `f^{1/2} ≤ f^α` on `[0, 1]`. -/
lemma power_numeric_lt_one {f α : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hα1 : α < 1) :
    f * Real.log (Real.exp 1 / f) * Real.log (Real.exp 1 * Real.log (Real.exp 1 / f)) ≤
      (1 + 2 / (1 - max α (1 / 2))) ^ 2 * f ^ α := by
  rcases le_or_gt α (1 / 2) with hα | hα
  · rw [max_eq_right hα]
    have h := power_numeric hf0 hf1 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rcases hf0.eq_or_lt with h0 | hf
    · subst h0
      rw [Real.zero_rpow (by norm_num)]
      exact Real.rpow_nonneg le_rfl _
    · exact Real.rpow_le_rpow_of_exponent_ge hf hf1 hα
  · rw [max_eq_left hα.le]
    exact power_numeric hf0 hf1 (by linarith) hα1

/-- `ln 4 · ln ln 8 > 1` (proof of Theorem 11, E.2.3, p. 44, l. 1364), via
`ln ln 8 = ln 2 + ln(3 ln 2 / 2) ≥ ln 2 + 1 - 2/(3 ln 2)`. -/
lemma one_lt_log_four_mul_log_log_eight : 1 < Real.log 4 * Real.log (Real.log 8) := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hpos : 0 < 3 * Real.log 2 / 2 := by positivity
  have hsplit : Real.log (3 * Real.log 2) = Real.log 2 + Real.log (3 * Real.log 2 / 2) := by
    rw [← Real.log_mul (by norm_num) hpos.ne']; congr 1; ring
  -- `ln x ≥ 1 - 1/x`
  have hlow : 1 - 2 / (3 * Real.log 2) ≤ Real.log (3 * Real.log 2 / 2) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
    rw [Real.log_inv, inv_div] at h
    linarith
  have hq : 2 / (3 * Real.log 2) ≤ 0.9619 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  rw [h4, h8, hsplit]
  nlinarith

/-- `ln(2n) ln ln(4n) ≥ ln 4 · ln ln 8 > 1` for `n ≥ 2` (E.2.3, p. 44, l. 1364–1365). -/
lemma one_le_log_mul_log_log {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ Real.log (2 * n) * Real.log (Real.log (4 * n)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hA : Real.log 4 ≤ Real.log (2 * n) := Real.log_le_log (by norm_num) (by linarith)
  have h8 : Real.log 8 ≤ Real.log (4 * n) := Real.log_le_log (by norm_num) (by linarith)
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hB : Real.log (Real.log 8) ≤ Real.log (Real.log (4 * n)) := Real.log_le_log hl8 h8
  have h := one_lt_log_four_mul_log_log_eight
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hll8 : 0 < Real.log (Real.log 8) := by
    by_contra hc; push Not at hc; nlinarith
  nlinarith [mul_le_mul hA hB hll8.le (by linarith)]

/-- The right-hand side of Theorem 11 is nonnegative for `0 ≤ ε ≤ 1`. -/
lemma rhs_nonneg {C ε : ℝ} (hC : 0 ≤ C) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    0 ≤ C * ε * Real.log (Real.exp 1 / ε) * Real.log (Real.exp 1 * Real.log (Real.exp 1 / ε)) := by
  rcases hε0.eq_or_lt with h0 | hε
  · subst h0; simp
  have he : 1 ≤ Real.exp 1 / ε := by
    rw [le_div_iff₀ hε]; have := Real.add_one_le_exp (1 : ℝ); linarith
  have hL : 0 ≤ Real.log (Real.exp 1 / ε) := Real.log_nonneg he
  have hL1 : 1 ≤ Real.log (Real.exp 1 / ε) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    rw [le_div_iff₀ hε]
    calc Real.exp 1 * ε ≤ Real.exp 1 * 1 := by gcongr
      _ = Real.exp 1 := mul_one _
  have hM : 0 ≤ Real.log (Real.exp 1 * Real.log (Real.exp 1 / ε)) := by
    apply Real.log_nonneg
    have := Real.add_one_le_exp (1 : ℝ)
    nlinarith
  positivity

section GraphLemmas

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]

lemma sum_finset_prod_eq {s : Finset (V × W)} (g : V × W → ℝ) :
    ∑ x ∈ s, g x = ∑ v, ∑ w, if (v, w) ∈ s then g (v, w) else 0 := by
  rw [← Fintype.sum_prod_type' (f := fun v w => if (v, w) ∈ s then g (v, w) else 0)]
  simp

lemma sum_finset_filter_eq (π : V ≃ W) {s : Finset (V × W)} (g : W → ℝ) :
    ∑ w ∈ univ.filter (fun w => (π.symm w, w) ∈ s), g w =
      ∑ v, if (v, π v) ∈ s then g (π v) else 0 := by
  rw [Finset.sum_filter, ← Equiv.sum_comp π]
  simp

/-- The block sums of `B(G, H, P_π)` are block sums of `A_G^π - A_H`: the nonzero rows and columns
of `B(G, H, P_π)` (indexed by the pairs `(v, π v)`) form a copy of `A_G^π - A_H`. -/
lemma sum_cutMat_permMat (π : V ≃ W) (S T : Finset (V × W)) :
    ∑ x ∈ S, ∑ y ∈ T, B G H (permMat π) x y =
      ∑ w ∈ univ.filter (fun w => (π.symm w, w) ∈ S),
        ∑ w' ∈ univ.filter (fun w' => (π.symm w', w') ∈ T), alignedDiff G H π w w' := by
  rw [sum_finset_filter_eq π]
  simp_rw [sum_finset_filter_eq π, sum_finset_prod_eq (s := T), sum_finset_prod_eq (s := S)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_eq_single (π v) (fun w _ hw => by simp [B, permMat, Ne.symm hw])
    (by simp)]
  split_ifs with hS
  · refine Finset.sum_congr rfl fun v' _ => ?_
    rw [Finset.sum_eq_single (π v') (fun w _ hw => by simp [B, permMat, Ne.symm hw])
      (by simp)]
    split_ifs <;> simp [B, permMat, alignedDiff, disc]
  · rfl

/-- `C_□(P_π) = ‖A_G^π - A_H‖_□`. -/
lemma costCut_permMat (π : V ≃ W) : costCut G H (permMat π) = cutNorm (alignedDiff G H π) := by
  apply le_antisymm
  · exact cutNorm_le _ fun S T => by rw [sum_cutMat_permMat]; exact le_cutNorm _ _ _
  · refine cutNorm_le _ fun S T => ?_
    have h := sum_cutMat_permMat G H π (univ ×ˢ S) (univ ×ˢ T)
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.filter_mem_eq_inter,
      Finset.univ_inter] at h
    rw [← h]
    exact le_cutNorm _ _ _

/-- `C_□(Q) ≤ n²` for `Q ∈ DS(V, W)`. -/
lemma costCut_le_sq {Q : V → W → ℝ} (hQ : IsDS Q) :
    costCut G H Q ≤ (Fintype.card V : ℝ) ^ 2 := by
  refine cutNorm_le _ fun S T => ?_
  have htot : ∑ x : V × W, Q x.1 x.2 = Fintype.card V := by
    rw [Fintype.sum_prod_type]; exact hQ.sum_sum
  calc |∑ x ∈ S, ∑ y ∈ T, B G H Q x y| ≤ ∑ x ∈ S, |∑ y ∈ T, B G H Q x y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ S, ∑ y ∈ T, Q x.1 x.2 * Q y.1 y.2 := by
        refine Finset.sum_le_sum fun x _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun y _ => ?_
        simp only [B, abs_mul, abs_of_nonneg (hQ.nonneg _ _)]
        have := abs_adj_sub_adj_le_one G H x.1 y.1 x.2 y.2
        have h1 := hQ.nonneg x.1 x.2
        have h2 := hQ.nonneg y.1 y.2
        unfold disc
        nlinarith [mul_nonneg h1 h2]
    _ ≤ ∑ x : V × W, ∑ y : V × W, Q x.1 x.2 * Q y.1 y.2 := by
        refine (Finset.sum_le_sum fun x _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ T) fun y _ _ => mul_nonneg (hQ.nonneg _ _) (hQ.nonneg _ _)).trans ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun x _ _ =>
          Finset.sum_nonneg fun y _ => mul_nonneg (hQ.nonneg _ _) (hQ.nonneg _ _)
    _ = (Fintype.card V : ℝ) ^ 2 := by
        rw [← Finset.sum_mul_sum, htot, sq]

/-- The set `DS(V, W)` is compact. -/
lemma isCompact_DS : IsCompact {Q : V → W → ℝ | IsDS Q} := by
  have hset : {Q : V → W → ℝ | IsDS Q} =
      ((⋂ v, ⋂ w, {Q : V → W → ℝ | 0 ≤ Q v w}) ∩ ⋂ v, {Q : V → W → ℝ | ∑ w, Q v w = 1}) ∩
        ⋂ w, {Q : V → W → ℝ | ∑ v, Q v w = 1} := by
    ext Q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨⟨h.nonneg, h.row_sum⟩, h.col_sum⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  have hclosed : IsClosed {Q : V → W → ℝ | IsDS Q} := by
    rw [hset]
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · exact isClosed_iInter fun v => isClosed_iInter fun w =>
        isClosed_le continuous_const (by fun_prop)
    · exact isClosed_iInter fun v => isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_iInter fun w => isClosed_eq (by fun_prop) continuous_const
  refine (isCompact_Icc (a := (0 : V → W → ℝ)) (b := 1)).of_isClosed_subset hclosed ?_
  intro Q hQ
  exact ⟨fun v w => hQ.nonneg v w, fun v w => hQ.le_one v w⟩

omit [DecidableEq V] [DecidableEq W] in
/-- `Q ↦ C_□(Q)` is continuous (a finite maximum of polynomials). -/
lemma continuous_costCut : Continuous fun Q : V → W → ℝ => costCut G H Q := by
  have h : (fun Q : V → W → ℝ => costCut G H Q) = fun Q =>
      (Finset.univ : Finset (Finset (V × W) × Finset (V × W))).sup' Finset.univ_nonempty
        (fun ST => |∑ x ∈ ST.1, ∑ y ∈ ST.2, B G H Q x y|) := by
    funext Q
    rw [Finset.sup'_univ_eq_ciSup]; rfl
  rw [h]
  refine Continuous.finset_sup'_apply _ fun ST _ => ?_
  unfold B
  fun_prop

/-- The infimum defining `d^OT_□` is attained (`DS(V, W)` is compact and `C_□` continuous). -/
lemma exists_costCut_eq_dOTCut (hcard : Fintype.card V = Fintype.card W) :
    ∃ Q, IsDS Q ∧ costCut G H Q = dOTCut G H := by
  obtain ⟨π⟩ := nonempty_equiv_of_card_eq hcard
  have hne : {Q : V → W → ℝ | IsDS Q}.Nonempty := ⟨permMat π, permMat_isDS π⟩
  obtain ⟨Q, hQ, hmin⟩ :=
    (isCompact_DS (V := V) (W := W)).exists_isMinOn hne (continuous_costCut G H).continuousOn
  refine ⟨Q, hQ, le_antisymm ?_ ?_⟩
  · have : Nonempty {Q : V → W → ℝ // IsDS Q} := ⟨⟨Q, hQ⟩⟩
    exact le_ciInf fun Q' => hmin Q'.2
  · exact ciInf_le (f := fun Q : {Q : V → W → ℝ // IsDS Q} => costCut G H Q.1)
      ⟨0, by rintro _ ⟨Q, rfl⟩; exact cutNorm_nonneg _⟩ ⟨Q, hQ⟩


lemma epsR_nonneg (Q : V → W → ℝ) : 0 ≤ epsR (adjMat G) (adjMat H) Q := cutNorm_nonneg _

/-- `ζ_Q ≤ 1` for `Q ∈ DS(V, W)`. -/
lemma epsR_le_one {Q : V → W → ℝ} (hQ : IsDS Q) : epsR (adjMat G) (adjMat H) Q ≤ 1 := by
  rw [epsR_adjMat]
  rcases (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ _).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [div_le_one (by positivity)]; exact costCut_le_sq G H hQ

/-- `δ_□(G, H) ≤ ζ_{P_π}` for every bijection `π`. -/
lemma deltaCut_le_epsR_permMat (π : V ≃ W) :
    deltaCut G H ≤ epsR (adjMat G) (adjMat H) (permMat π) := by
  rw [epsR_adjMat, costCut_permMat, deltaCut]
  gcongr
  exact ciInf_le ⟨0, by rintro _ ⟨σ, rfl⟩; exact cutNorm_nonneg _⟩ π

/-- `δ^OT_□(G, H) ≤ ζ_Q` for every `Q ∈ DS(V, W)`. -/
lemma deltaOTCut_le_epsR {Q : V → W → ℝ} (hQ : IsDS Q) :
    deltaOTCut G H ≤ epsR (adjMat G) (adjMat H) Q := by
  rw [epsR_adjMat, deltaOTCut]
  gcongr
  exact ciInf_le (f := fun Q : {Q : V → W → ℝ // IsDS Q} => costCut G H Q.1)
      ⟨0, by rintro _ ⟨Q, rfl⟩; exact cutNorm_nonneg _⟩ ⟨Q, hQ⟩

/-- The lower bound of Theorem 11: `δ^OT_□ ≤ δ_□`, since permutation matrices are doubly
stochastic (p. 44, l. 1363). -/
lemma deltaOTCut_le_deltaCut (hcard : Fintype.card V = Fintype.card W) :
    deltaOTCut G H ≤ deltaCut G H := by
  have := nonempty_equiv_of_card_eq hcard
  rw [deltaOTCut, deltaCut]
  gcongr
  refine le_ciInf fun π => ?_
  rw [← costCut_permMat]
  exact ciInf_le (f := fun Q : {Q : V → W → ℝ // IsDS Q} => costCut G H Q.1)
      ⟨0, by rintro _ ⟨Q, rfl⟩; exact cutNorm_nonneg _⟩ ⟨permMat π, permMat_isDS π⟩

lemma adjMat_isSymm : (adjMat G).IsSymm := by
  ext v v'; simp [adjMat, Matrix.transpose_apply, adj_symm G v' v]

lemma adjMat_mem_Icc (v v' : V) : 0 ≤ adjMat G v v' ∧ adjMat G v v' ≤ 1 :=
  ⟨adj_nonneg G v v', adj_le_one G v v'⟩

/-- For `n = 1` both graphs are a single vertex without loops, so `δ_□(G, H) = 0` (Appendix E.2
assumes `n ≥ 2`, p. 32, l. 1003). -/
lemma deltaCut_le_zero_of_card_eq_one (hV : Fintype.card V = 1)
    (hcard : Fintype.card V = Fintype.card W) : deltaCut G H ≤ 0 := by
  obtain ⟨π⟩ := nonempty_equiv_of_card_eq hcard
  have hW : Subsingleton W := Fintype.card_le_one_iff_subsingleton.1 (by omega)
  have h0 : cutNorm (alignedDiff G H π) ≤ 0 := by
    refine cutNorm_le _ fun S T => ?_
    have : ∀ w w' : W, alignedDiff G H π w w' = 0 := fun w w' => by
      rw [Subsingleton.elim w' w]; simp [alignedDiff, adj_self]
    simp [this]
  have h := deltaCut_le_epsR_permMat G H π
  rw [epsR_adjMat, costCut_permMat] at h
  exact h.trans (div_nonpos_of_nonpos_of_nonneg h0 (by positivity))

end GraphLemmas

/-- **Eq. (39)** in the proof of Theorem 11 (E.2.3, p. 44, l. 1363–1366): by Theorem 38, with
`C₁ = 1 + 4 C_thin`, `δ_□(G, H) ≤ C₁ ln(2n) ln ln(4n) ζ_Q` for every `Q ∈ DS(n)` and `n ≥ 2`
(using `ln(2n) ln ln(4n) ≥ ln 4 · ln ln 8 > 1`). -/
lemma eq39 (hThin : ThinPermutationTheorem) :
    ∃ Cthin : ℝ, 0 < Cthin ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V]
      [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
      [DecidableRel H.Adj], Fintype.card V = Fintype.card W → 2 ≤ Fintype.card V →
      ∀ Q : V → W → ℝ, IsDS Q →
      deltaCut G H ≤ (1 + 4 * Cthin) * Real.log (2 * Fintype.card V) *
        Real.log (Real.log (4 * Fintype.card V)) * epsR (adjMat G) (adjMat H) Q := by
  obtain ⟨Cthin, hCthin, hT⟩ := theorem38 hThin
  refine ⟨Cthin, hCthin, fun V W _ _ _ _ G _ H _ hcard hn2 Q hQ => ?_⟩
  obtain ⟨π, hπ⟩ := hT V W (adjMat G) (adjMat H) (adjMat_isSymm G) (adjMat_isSymm H)
    (adjMat_mem_Icc G) (adjMat_mem_Icc H) hcard Q hQ
  have hK := one_le_log_mul_log_log hn2
  have hε := epsR_nonneg G H Q
  have hfac : 1 + 4 * (Cthin * Real.log (2 * Fintype.card V) *
      Real.log (Real.log (4 * Fintype.card V))) ≤
      (1 + 4 * Cthin) * Real.log (2 * Fintype.card V) *
        Real.log (Real.log (4 * Fintype.card V)) := by nlinarith
  calc deltaCut G H ≤ epsR (adjMat G) (adjMat H) (permMat π) := deltaCut_le_epsR_permMat G H π
    _ ≤ _ := hπ
    _ ≤ _ := mul_le_mul_of_nonneg_right hfac hε

/-- **Theorem 11** (p. 10, l. 333–337; assuming Theorem 35 [HOG26] and the contraction principle,
Lemma 43 [LT91]). There is a universal constant `C > 0` such that for all graphs `G, H` of the
same order, `δ^OT_□ ≤ δ_□(G, H) ≤ C δ^OT_□ ln(e/δ^OT_□) ln(e ln(e/δ^OT_□))`
(the right-hand side is `0` if `δ^OT_□ = 0`, which holds automatically in Lean). As in the paper
(p. 44, l. 1376), `C = max{2, 39 C₁, 113}` with `C₁ = 1 + 4 C_thin`. -/
theorem theorem11 (hThin : ThinPermutationTheorem) (hCP : ContractionPrinciple) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card V = Fintype.card W →
      deltaOTCut G H ≤ deltaCut G H ∧
      deltaCut G H ≤ C * deltaOTCut G H * Real.log (Real.exp 1 / deltaOTCut G H) *
        Real.log (Real.exp 1 * Real.log (Real.exp 1 / deltaOTCut G H)) := by
  obtain ⟨Cthin, hCthin, h39⟩ := eq39 hThin
  have hC1 : 0 < 1 + 4 * Cthin := by linarith
  refine ⟨max (max 2 (39 * (1 + 4 * Cthin))) 113, by positivity, ?_⟩
  intro V W _ _ _ _ G _ H _ hcard
  refine ⟨deltaOTCut_le_deltaCut G H hcard, ?_⟩
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
  · simp [deltaCut, deltaOTCut, hn]
  obtain ⟨Q, hQ, hQopt⟩ := exists_costCut_eq_dOTCut G H hcard
  have hf : deltaOTCut G H = epsR (adjMat G) (adjMat H) Q := by
    rw [epsR_adjMat, hQopt, deltaOTCut]
  obtain ⟨π⟩ := nonempty_equiv_of_card_eq hcard
  rw [hf]
  rcases Nat.lt_or_ge (Fintype.card V) 2 with h1 | hn2
  · -- `n = 1`: `δ_□ = 0`
    exact (deltaCut_le_zero_of_card_eq_one G H (by omega) hcard).trans
      (rhs_nonneg (by positivity) (epsR_nonneg G H Q) (epsR_le_one G H hQ))
  obtain ⟨σ, hσ⟩ := theorem39 hCP (adjMat G) (adjMat H) (adjMat_isSymm G) (adjMat_isSymm H)
    (adjMat_mem_Icc G) (adjMat_mem_Icc H) hcard hn2 hQ
  exact main_numeric hC1 (epsR_nonneg G H Q) (epsR_le_one G H hQ)
    ((deltaCut_le_epsR_permMat G H π).trans (epsR_le_one G H (permMat_isDS π))) hn2
    (h39 V W G H hcard hn2 Q hQ) ((deltaCut_le_epsR_permMat G H σ).trans hσ)

/-- **Theorem 11 (power bound) for every `α < 1`** (end of E.2.3, p. 44, l. 1377–1379): there is
`C_α > 0` with `δ_□(G, H) ≤ C_α δ^OT_□(G, H)^α` for all graphs of the same order. With
`α = 1 - ε` this is the consequence `δ_□ = O((δ^OT_□)^{1-ε})` stated in Theorem 11 (p. 10,
l. 336–337). -/
theorem theorem11_power_lt_one (hThin : ThinPermutationTheorem) (hCP : ContractionPrinciple)
    {α : ℝ} (hα1 : α < 1) :
    ∃ Cα : ℝ, 0 < Cα ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card V = Fintype.card W →
      deltaCut G H ≤ Cα * deltaOTCut G H ^ α := by
  obtain ⟨C, hC, h13⟩ := theorem11 hThin hCP
  have hK : 0 < 1 + 2 / (1 - max α (1 / 2)) := by
    have : 0 ≤ 2 / (1 - max α (1 / 2)) :=
      div_nonneg (by norm_num) (by have := max_lt hα1 (by norm_num : (1 / 2 : ℝ) < 1); linarith)
    linarith
  refine ⟨C * (1 + 2 / (1 - max α (1 / 2))) ^ 2, by positivity, ?_⟩
  intro V W _ _ _ _ G _ H _ hcard
  obtain ⟨π⟩ := nonempty_equiv_of_card_eq hcard
  have hf1 : deltaOTCut G H ≤ 1 :=
    (deltaOTCut_le_epsR G H (permMat_isDS π)).trans (epsR_le_one G H (permMat_isDS π))
  have hf0 : 0 ≤ deltaOTCut G H := by
    unfold deltaOTCut dOTCut
    exact div_nonneg (Real.iInf_nonneg fun Q => cutNorm_nonneg _) (by positivity)
  have hp := power_numeric_lt_one hf0 hf1 hα1
  calc deltaCut G H ≤ C * deltaOTCut G H * Real.log (Real.exp 1 / deltaOTCut G H) *
        Real.log (Real.exp 1 * Real.log (Real.exp 1 / deltaOTCut G H)) := (h13 V W G H hcard).2
    _ = C * (deltaOTCut G H * Real.log (Real.exp 1 / deltaOTCut G H) *
        Real.log (Real.exp 1 * Real.log (Real.exp 1 / deltaOTCut G H))) := by ring
    _ ≤ C * ((1 + 2 / (1 - max α (1 / 2))) ^ 2 * deltaOTCut G H ^ α) := by gcongr
    _ = _ := by ring

/-- **Theorem 11 (power bound)** for `0 < α < 1`: the special case `0 < α < 1` of
`theorem11_power_lt_one`. -/
theorem theorem11_power (hThin : ThinPermutationTheorem) (hCP : ContractionPrinciple) {α : ℝ}
    (_hα0 : 0 < α) (hα1 : α < 1) :
    ∃ Cα : ℝ, 0 < Cα ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card V = Fintype.card W →
      deltaCut G H ≤ Cα * deltaOTCut G H ^ α :=
  theorem11_power_lt_one hThin hCP hα1

/-! ### Final form: only the cited Theorem 35 [HOG26] is assumed

The contraction principle (Lemma 43, [LT91, Thm. 4.12]) is proved in `ContractionPrinciple.lean`,
so the hypothesis `ContractionPrinciple` can be discharged. -/

/-- **Theorem 11** (assuming only Theorem 35 [HOG26]). -/
theorem theorem11_of_thin (hThin : ThinPermutationTheorem) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card V = Fintype.card W →
      deltaOTCut G H ≤ deltaCut G H ∧
      deltaCut G H ≤ C * deltaOTCut G H * Real.log (Real.exp 1 / deltaOTCut G H) *
        Real.log (Real.exp 1 * Real.log (Real.exp 1 / deltaOTCut G H)) :=
  theorem11 hThin contractionPrinciple

/-- **Theorem 11, power bound for every `α < 1`** (assuming only Theorem 35 [HOG26]). -/
theorem theorem11_power_lt_one_of_thin (hThin : ThinPermutationTheorem) {α : ℝ} (hα1 : α < 1) :
    ∃ Cα : ℝ, 0 < Cα ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card V = Fintype.card W →
      deltaCut G H ≤ Cα * deltaOTCut G H ^ α :=
  theorem11_power_lt_one hThin contractionPrinciple hα1

/-- **Theorem 11, power bound** for `0 < α < 1` (assuming only Theorem 35 [HOG26]); see
`theorem11_power_lt_one_of_thin` for every `α < 1`. -/
theorem theorem11_power_of_thin (hThin : ThinPermutationTheorem) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ Cα : ℝ, 0 < Cα ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card V = Fintype.card W →
      deltaCut G H ≤ Cα * deltaOTCut G H ^ α :=
  theorem11_power hThin contractionPrinciple hα0 hα1

/-- **Theorem 2, cut part** (p. 3, l. 118–120; assuming only Theorem 35 [HOG26]): for every `ε > 0`
there is `C_ε > 0` with `δ_□ ≤ C_ε (δ^OT_□)^{1-ε}` for all graphs of the same order. -/
theorem theorem2_cut_of_thin (hThin : ThinPermutationTheorem) {ε : ℝ} (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card V = Fintype.card W →
      deltaCut G H ≤ Cε * deltaOTCut G H ^ (1 - ε) :=
  theorem11_power_lt_one_of_thin hThin (by linarith)

end GsimOT
