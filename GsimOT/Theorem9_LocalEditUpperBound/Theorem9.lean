/-
# Theorem 9: upper bound for the local edit distance

Theorem 9 is the `δ₁` part of Theorem 2 (p. 3, l. 118–121).

Paper, Section 3.2, Theorem 9 (p. 9, l. 297–299): For all graphs `G, H` of the same order,
`δ₁(G, H) ≤ 15 · √(δ₁^OT(G, H) · ln(4 / δ₁^OT(G, H)))`,
where the right-hand side is defined as `0` if `δ₁^OT(G, H) = 0`.

The proof (Appendix D.2, p. 30, l. 936–947) is formalised assuming Lemma 30 (`CVZRounding`), the
cited dependent-rounding theorem of Chekuri, Vondrák and Zenklusen.

Formalisation notes.
* In Lean, `Real.log 0 = 0` and `4 / 0 = 0`, so the expression `f * log (4 / f)` is `0` for
  `f = 0`; the convention of the paper is therefore built in.
* We first prove the bound for *every* `Q ∈ DS(V, W)` with `f := C₁(Q)/n` (`theorem9_of_isDS`);
  the paper applies the same argument to an optimal `Q`.  Since we define `d₁^OT` as an infimum,
  the final statement follows by continuity of `f ↦ 15 √(f ln(4/f))` (`theorem9`).
* The final numerical estimate follows the paper (p. 30, l. 945–947):
  `b/√(fh) ≤ 4√(f/h) + 2√2/√h + 4√5 ≤ (4 + 2√2)/√(ln 4) + 4√5 < 15` (`final_estimate`).
* The remark after Theorem 9 (p. 9, l. 320), that Theorem 9 yields `δ₁ ≤ C_α (δ₁^OT)^α` for
  every `α < 1/2`, is `theorem9_power`.
-/
import GsimOT.Theorem9_LocalEditUpperBound.Proposition32_Rounding

open Finset

namespace GsimOT

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- The trivial bound `d₁(G, H) ≤ n`. -/
lemma dOne_le_card (hcard : Fintype.card V = Fintype.card W) : dOne G H ≤ Fintype.card V := by
  let π : V ≃ W := Fintype.equivOfCardEq hcard
  refine (dOne_le π).trans ?_
  exact costOne_le_card (permMat_isDS π)

/-- `x ↦ ln(4x)/x` is decreasing for `x ≥ 1`: `ln(4y)/y ≤ ln(4x)/x` for `1 ≤ x ≤ y`. -/
lemma log_four_mul_div_antitone {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    Real.log (4 * y) / y ≤ Real.log (4 * x) / x := by
  have he : Real.exp 1 ≤ 4 := by
    have := Real.exp_one_lt_d9; linarith
  have h := Real.log_div_self_antitoneOn (show 4 * x ∈ Set.Ici (Real.exp 1) by
      simp only [Set.mem_Ici]; linarith)
    (show 4 * y ∈ Set.Ici (Real.exp 1) by simp only [Set.mem_Ici]; linarith)
    (by linarith)
  simp only at h
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
  rw [div_le_div_iff₀ hy0 hx0]
  nlinarith

/-- The final numerical estimate of the proof of Theorem 9 (as in the paper):
for `0 < f ≤ 1` and `h := ln(4/f)`, `4f + 2√2 √f + 4√5 √(f h) ≤ 15 √(f h)`. -/
lemma final_estimate {f : ℝ} (hf0 : 0 < f) (hf1 : f ≤ 1) :
    4 * f + 2 * Real.sqrt 2 * Real.sqrt f +
        4 * Real.sqrt 5 * Real.sqrt (f * Real.log (4 / f)) ≤
      15 * Real.sqrt (f * Real.log (4 / f)) := by
  set h := Real.log (4 / f) with hh
  -- `h ≥ ln 4 > 1.3689`
  have hln4 : (1.3689 : ℝ) ≤ h := by
    have h4 : Real.log 4 ≤ h := Real.log_le_log (by norm_num) (by
      rw [le_div_iff₀ hf0]; linarith)
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hh0 : 0 ≤ h := by linarith
  set a := Real.sqrt f with ha
  set r := Real.sqrt h with hr
  have ha0 : 0 < a := Real.sqrt_pos.2 hf0
  have ha1 : a ≤ 1 := Real.sqrt_le_one.mpr hf1 |>.trans_eq' rfl
  have hfa : f = a * a := (Real.mul_self_sqrt hf0.le).symm
  have hfh : Real.sqrt (f * h) = a * r := Real.sqrt_mul hf0.le h
  have hr1 : (1.17 : ℝ) ≤ r := by
    rw [hr]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hs2 : Real.sqrt 2 ≤ 1.415 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs5 : Real.sqrt 5 ≤ 2.237 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [hfh, hfa]
  -- `4a² + 2√2 a ≤ (15 - 4√5) a r` since `4a + 2√2 ≤ 6.83 < 7.08 ≤ (15 - 4√5) r`
  have key : 4 * a + 2 * Real.sqrt 2 ≤ (15 - 4 * Real.sqrt 5) * r := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key ha0.le]

/-- **Theorem 9, for an arbitrary fractional alignment.**  For every `Q ∈ DS(V, W)`, with
`f := C₁(Q)/n`, we have `δ₁(G, H) ≤ 15 √(f ln(4/f))`. -/
theorem theorem9_of_isDS (hCVZ : CVZRounding) (hcard : Fintype.card V = Fintype.card W)
    {Q : V → W → ℝ} (hQ : IsDS Q) :
    deltaOne G H ≤ 15 * Real.sqrt (costOne G H Q / Fintype.card V *
      Real.log (4 / (costOne G H Q / Fintype.card V))) := by
  set n := Fintype.card V with hn
  set L := costOne G H Q with hLdef
  have hL : ∀ v w, Q v w ≠ 0 → localCost G H Q v w ≤ L := fun v w h => localCost_le_costOne h
  have hrhs : 0 ≤ 15 * Real.sqrt (L / n * Real.log (4 / (L / n))) := by positivity
  -- If `L < 1`, then `G ≅ H` by Lemma 29, so `δ₁ = 0`.
  by_cases hL1 : L < 1
  · have := lemma29_dOne_eq_zero hcard hQ hL1
    simp only [deltaOne, this, zero_div]
    exact hrhs
  push Not at hL1
  -- Hence `1 ≤ L ≤ n`.
  have hLn : L ≤ n := costOne_le_card hQ
  have hn1 : (1 : ℝ) ≤ n := hL1.trans hLn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨σ, hσ⟩ := exists_bij_subset_supp hQ hcard
  -- the block length `ℓ := ⌈√(n/(2L))⌉`
  set s := Real.sqrt (n / (2 * L)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hss : s * s = n / (2 * L) := Real.mul_self_sqrt (by positivity)
  set ℓ := ⌈s⌉₊ with hℓ
  have hℓs : s ≤ ℓ := Nat.le_ceil s
  have hℓs1 : (ℓ : ℝ) < s + 1 := Nat.ceil_lt_add_one hs0.le
  have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [h] at hℓs; simp at hℓs; linarith)
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
  -- `n/ℓ + 2ℓL ≤ 4Ls + 2L`
  have hnl : (n : ℝ) / ℓ + 2 * ℓ * L ≤ 4 * L * s + 2 * L := by
    have h1 : (n : ℝ) / ℓ ≤ 2 * L * s := by
      rw [div_le_iff₀ hℓpos]
      have : (n : ℝ) = 2 * L * (s * s) := by rw [hss]; field_simp
      rw [this]; nlinarith
    nlinarith
  -- `γ* := √(5 ln(4n)/n)`
  have hlog4n : 0 < Real.log (4 * n) := Real.log_pos (by linarith)
  set γs := Real.sqrt (5 * Real.log (4 * n) / n) with hγs
  have hγs0 : 0 < γs := Real.sqrt_pos.2 (by positivity)
  have hγsq : γs * γs = 5 * Real.log (4 * n) / n := Real.mul_self_sqrt (by positivity)
  -- Eq. (20) (p. 30, l. 940): `d₁ ≤ 4L + 4Ls + 4nγ*` (with `4Ls = 2√(2nL)` and
  -- `4nγ* = 4√(5n ln(4n))`)
  have h23 : dOne G H ≤ 4 * L + 4 * L * s + 4 * n * γs := by
    by_cases hγ : γs ≤ 1 / 2
    · have h38 := proposition32 hCVZ hQ hL hσ hL0 hγs0 hγ ℓ hℓ1
      have h10 : 10 * Real.log (4 * n) / γs = 2 * n * γs := by
        rw [div_eq_iff hγs0.ne']
        have : 10 * Real.log (4 * n) = 2 * n * (γs * γs) := by rw [hγsq]; field_simp; norm_num
        rw [this]; ring
      rw [h10] at h38
      linarith
    · push Not at hγ
      have := dOne_le_card (G := G) (H := H) hcard
      nlinarith [hs0, hL0]
  -- normalise: `b ≤ 4f + 2√2 √f + 4√5 √(f ln(4/f))`
  set f := L / n with hf
  have hf0 : 0 < f := by positivity
  have hf1 : f ≤ 1 := by rw [div_le_one hn0]; exact hLn
  -- `ln(4n)/n ≤ f ln(4/f)` since `n ≥ 1/f ≥ 1`
  have hlogf : Real.log (4 * n) / n ≤ f * Real.log (4 / f) := by
    have h1f : 1 ≤ 1 / f := by rw [le_div_iff₀ hf0]; linarith
    have hfn : 1 / f ≤ n := by
      rw [div_le_iff₀ hf0, hf, mul_div_cancel₀ _ hn0.ne']; exact hL1
    have := log_four_mul_div_antitone h1f hfn
    rw [show 4 * (1 / f) = 4 / f by ring, div_div_eq_mul_div, div_one] at this
    linarith
  have hb : deltaOne G H ≤ 4 * f + 2 * Real.sqrt 2 * Real.sqrt f +
      4 * Real.sqrt 5 * Real.sqrt (f * Real.log (4 / f)) := by
    unfold deltaOne
    rw [div_le_iff₀ hn0]
    refine h23.trans ?_
    -- term by term
    have t1 : 4 * L = 4 * f * n := by rw [hf]; field_simp
    have t2 : 4 * L * s ≤ 2 * Real.sqrt 2 * Real.sqrt f * n := by
      -- `(4Ls)² = 8nL = (2√2 √f n)²`
      have hlhs : 0 ≤ 4 * L * s := by positivity
      have hrhs' : 0 ≤ 2 * Real.sqrt 2 * Real.sqrt f * n := by positivity
      have e1 : (4 * L * s) ^ 2 = 8 * n * L := by
        have : (4 * L * s) ^ 2 = 16 * L ^ 2 * (s * s) := by ring
        rw [this, hss]; field_simp; ring
      have e2 : (2 * Real.sqrt 2 * Real.sqrt f * n) ^ 2 = 8 * f * n * n := by
        have : (2 * Real.sqrt 2 * Real.sqrt f * n) ^ 2 =
            4 * (Real.sqrt 2) ^ 2 * (Real.sqrt f) ^ 2 * n ^ 2 := by ring
        rw [this, Real.sq_sqrt (by norm_num), Real.sq_sqrt hf0.le]; ring
      have e3 : 8 * f * n * n = 8 * n * L := by rw [hf]; field_simp
      exact (pow_le_pow_iff_left₀ hlhs hrhs' two_ne_zero).1 (by rw [e1, e2, e3])
    have t3 : 4 * n * γs ≤ 4 * Real.sqrt 5 * Real.sqrt (f * Real.log (4 / f)) * n := by
      have : γs ≤ Real.sqrt 5 * Real.sqrt (f * Real.log (4 / f)) := by
        rw [← Real.sqrt_mul (by norm_num), hγs]
        apply Real.sqrt_le_sqrt
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hlogf (by norm_num)
      nlinarith
    nlinarith
  exact hb.trans (final_estimate hf0 hf1)

/-- **Theorem 9.** For all graphs `G, H` of the same order (assuming Lemma 30),
`δ₁(G, H) ≤ 15 · √(δ₁^OT(G, H) · ln(4 / δ₁^OT(G, H)))`. -/
theorem theorem9 (hCVZ : CVZRounding) (hcard : Fintype.card V = Fintype.card W) :
    deltaOne G H ≤
      15 * Real.sqrt (deltaOTOne G H * Real.log (4 / deltaOTOne G H)) := by
  have := nonempty_equiv_of_card_eq hcard
  set n := Fintype.card V with hn
  set g : ℝ → ℝ := fun x => 15 * Real.sqrt (x * Real.log (4 / x)) with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  -- isomorphic case: `d₁^OT < 1`
  by_cases hD : dOTOne G H < 1
  · obtain ⟨Q, hQ, hQ1⟩ := exists_lt_of_dOTOne_lt hD
    have := lemma29_dOne_eq_zero hcard hQ hQ1
    simp only [deltaOne, this, zero_div]
    exact hg0 _
  push Not at hD
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · simp only [deltaOne, ← hn, hn0, Nat.cast_zero, div_zero]; exact hg0 _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  set f₀ := deltaOTOne G H with hf₀
  have hf₀pos : 0 < f₀ := by rw [hf₀, deltaOTOne]; positivity
  -- continuity of `g` at `f₀ > 0`
  have hcont : ContinuousAt g f₀ := by
    have h4 : ContinuousAt (fun x : ℝ => 4 / x) f₀ :=
      continuousAt_const.div continuousAt_id hf₀pos.ne'
    have hlog : ContinuousAt (fun x : ℝ => Real.log (4 / x)) f₀ :=
      (Real.continuousAt_log (by positivity)).comp h4
    exact ((continuousAt_id.mul hlog).sqrt).const_mul 15
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨η, hη, hηg⟩ := Metric.continuousAt_iff.1 hcont ε hε
  -- a fractional alignment that is `η n`-close to optimal
  obtain ⟨Q, hQ, hQlt⟩ := exists_lt_of_dOTOne_lt (G := G) (H := H)
    (show dOTOne G H < dOTOne G H + η * n by nlinarith)
  have hQge := dOTOne_le (G := G) (H := H) hQ
  have hclose : dist (costOne G H Q / n) f₀ < η := by
    rw [Real.dist_eq, hf₀, deltaOTOne, ← sub_div, abs_div, abs_of_pos hnR,
      abs_of_nonneg (by linarith), div_lt_iff₀ hnR]
    linarith
  have h1 := theorem9_of_isDS (G := G) (H := H) hCVZ hcard hQ
  have h2 := hηg hclose
  rw [Real.dist_eq] at h2
  have h3 := (abs_lt.1 h2).2
  change deltaOne G H ≤ g (costOne G H Q / n) at h1
  linarith

/-! ### The remark after Theorem 9: power bounds -/

/-- `√(f ln(4/f)) ≤ √(4^ε/ε) · f^α` for `f ≥ 0`, `α < 1/2`, `ε := 1 - 2α`. -/
lemma sqrt_mul_log_le_rpow {α : ℝ} (hα : α < 1 / 2) {f : ℝ} (hf : 0 ≤ f) :
    Real.sqrt (f * Real.log (4 / f)) ≤
      Real.sqrt ((4 : ℝ) ^ (1 - 2 * α) / (1 - 2 * α)) * f ^ α := by
  set ε := 1 - 2 * α with hε
  have hε0 : 0 < ε := by linarith
  rcases hf.eq_or_lt with rfl | hf0
  · simp only [zero_mul, Real.sqrt_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg le_rfl _)
  have hlog := Real.log_le_rpow_div (x := 4 / f) (by positivity) hε0
  -- `f ln(4/f) ≤ (4^ε/ε) f^(2α)`
  have h1 : f * Real.log (4 / f) ≤ (4 : ℝ) ^ ε / ε * (f ^ α) ^ 2 := by
    have e1 : (4 / f) ^ ε = (4 : ℝ) ^ ε / f ^ ε := Real.div_rpow (by norm_num) hf0.le ε
    have e2 : (f ^ α) ^ 2 = f / f ^ ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hf0.le]
      have : f / f ^ ε = f ^ (1 - ε) := by rw [Real.rpow_sub hf0 1 ε, Real.rpow_one]
      rw [this]; congr 1; push_cast; rw [hε]; ring
    calc f * Real.log (4 / f) ≤ f * ((4 / f) ^ ε / ε) :=
          mul_le_mul_of_nonneg_left hlog hf0.le
      _ = (4 : ℝ) ^ ε / ε * (f / f ^ ε) := by rw [e1]; ring
      _ = (4 : ℝ) ^ ε / ε * (f ^ α) ^ 2 := by rw [e2]
  calc Real.sqrt (f * Real.log (4 / f)) ≤ Real.sqrt ((4 : ℝ) ^ ε / ε * (f ^ α) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = Real.sqrt ((4 : ℝ) ^ ε / ε) * f ^ α := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **Remark after Theorem 9** (p. 9, l. 320): Theorem 9 yields a uniform bound
`δ₁ ≤ C_α · (δ₁^OT)^α` for every `α < 1/2` (assuming Lemma 30), with
`C_α := 15 √(4^ε/ε)`, `ε := 1 - 2α`. -/
theorem theorem9_power (hCVZ : CVZRounding) {α : ℝ} (hα : α < 1 / 2) :
    ∃ C : ℝ, ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card V = Fintype.card W → deltaOne G H ≤ C * deltaOTOne G H ^ α := by
  refine ⟨15 * Real.sqrt ((4 : ℝ) ^ (1 - 2 * α) / (1 - 2 * α)), ?_⟩
  intro V W _ _ _ _ G _ H _ hcard
  have hf : 0 ≤ deltaOTOne G H := by
    unfold deltaOTOne; exact div_nonneg dOTOne_nonneg (Nat.cast_nonneg _)
  calc deltaOne G H ≤ 15 * Real.sqrt (deltaOTOne G H * Real.log (4 / deltaOTOne G H)) :=
        theorem9 hCVZ hcard
    _ ≤ 15 * (Real.sqrt ((4 : ℝ) ^ (1 - 2 * α) / (1 - 2 * α)) * deltaOTOne G H ^ α) := by
        gcongr; exact sqrt_mul_log_le_rpow hα hf
    _ = _ := by ring

end GsimOT
