/-
# Proposition 8: no linear bound for the local edit distance

Paper, Section 3.2, Proposition 8 (p. 7, l. 262–263): For every even `r ≥ 2`, there are graphs
`G_r, H_r` on `Θ(r³)` vertices such that `d₁(G_r, H_r) = r` and `d₁^OT(G_r, H_r) = 1`.

The construction is in Appendix D.1 (pp. 25–26). We moreover give the exact order
`|V(G_r)| = 5r³ + 10r² - r + 4`; `proposition8` states `r³ ≤ |V(G_r)| ≤ 19 r³`.

Proof (paper, pp. 27–28, l. 860–863).  By Lemma 27, `d₁^OT(G_r, H_r) = 1`.  The bijection `σ₁`
fixes all markers and all vertices of `K`, so by the second item of Lemma 22 its local costs can be
computed in `(G⁰_r, H⁰_r)` as in the proof of Lemma 27, yielding `d₁(G_r, H_r) = r` by Lemma 28
and since `L_{σ₁}(b₁, b₁) = r`.  Finally `|G⁰_r| = Θ(r³)` and Lemma 22 only adds `O(r³)` vertices.

(For the upper bound `d₁ ≤ r` we show `C₁(σ₁) ≤ r`, i.e. *all* local costs of `σ₁` are at most
`r`.)

The file also contains Theorem 3 (2) and the two consequences for `G_r, H_r` stated in the text:
no bound `δ₁ ≤ c · δ₁^OT` (after Proposition 8, p. 9, l. 295) and no bound `δ₁ ≤ C · (δ₁^OT)^α`
with `α > 2/3` (after Theorem 9, p. 9, l. 318–320).
-/
import GsimOT.Proposition8_LocalEditLowerBound.Lemma28_BijectionCost
import GsimOT.Common.Lemma29_Integrality

open Finset

namespace GsimOT.Prop8

variable {r : ℕ}

/-- **Lemma 28 (as stated in the paper).** `d₁(G_r, H_r) ≥ r`. -/
theorem lemma28_dOne (hr : 2 ≤ r) (hev : Even r) : (r : ℝ) ≤ dOne (Gr r) (Hr r) :=
  le_dOne fun π => lemma28 hr hev π

/-- `d₁(G_r, H_r) = r`. -/
theorem dOne_Gr_Hr (hr : 2 ≤ r) (hev : Even r) : dOne (Gr r) (Hr r) = r := by
  apply le_antisymm
  · exact (dOne_le (sigmaExt ⟨0, by omega⟩)).trans (costOneBij_sigmaExt_le hr hev _)
  · exact lemma28_dOne hr hev

/-- **Lemma 27.** `d₁^OT(G_r, H_r) = 1`.  The upper bound is the fractional alignment `Q_r`; the
lower bound is Lemma 29 since `G_r ≇ H_r` (which follows from Lemma 28). -/
theorem lemma27 (hr : 2 ≤ r) (hev : Even r) : dOTOne (Gr r) (Hr r) = 1 := by
  apply le_antisymm
  · exact (dOTOne_le (QrExt_isDS (by omega))).trans (costOne_Qr_le_one hr hev)
  · refine lemma29_one_le_dOTOne rfl ?_
    rw [dOne_Gr_Hr hr hev]
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    positivity

/-- **Proposition 8.** For every even `r ≥ 2` the graphs `G_r, H_r` satisfy
`d₁(G_r, H_r) = r` and `d₁^OT(G_r, H_r) = 1`, and have `Θ(r³)` vertices. -/
theorem proposition8 (hr : 2 ≤ r) (hev : Even r) :
    dOne (Gr r) (Hr r) = r ∧ dOTOne (Gr r) (Hr r) = 1 ∧
      r ^ 3 ≤ Fintype.card (Vr r) ∧ Fintype.card (Vr r) ≤ 19 * r ^ 3 :=
  ⟨dOne_Gr_Hr hr hev, lemma27 hr hev, (card_Vr_bounds (by omega)).1,
    (card_Vr_bounds (by omega)).2⟩

/-- **Theorem 3 (2)** (Section 1, p. 4, l. 125; it follows from Proposition 8). For every even
`r ≥ 2` the graphs `G_r, H_r` satisfy `δ₁(G_r, H_r) = r · δ₁^OT(G_r, H_r)`. -/
theorem theorem3_item2 (hr : 2 ≤ r) (hev : Even r) :
    deltaOne (Gr r) (Hr r) = r * deltaOTOne (Gr r) (Hr r) := by
  unfold deltaOne deltaOTOne
  rw [dOne_Gr_Hr hr hev, lemma27 hr hev]
  ring

/-- Consequence stated after Proposition 8 (p. 9, l. 295, before Theorem 9): there is no bound of
the form `δ₁ ≤ c · δ₁^OT`. -/
theorem no_linear_bound (c : ℝ) : ∃ (r : ℕ), 2 ≤ r ∧ Even r ∧
    ¬ (deltaOne (Gr r) (Hr r) ≤ c * deltaOTOne (Gr r) (Hr r)) := by
  obtain ⟨k, hk⟩ := exists_nat_gt c
  refine ⟨2 * (k + 1), by omega, ⟨k + 1, by ring⟩, ?_⟩
  set r := 2 * (k + 1)
  have hr : 2 ≤ r := by omega
  have hev : Even r := ⟨k + 1, by ring⟩
  unfold deltaOne deltaOTOne
  rw [dOne_Gr_Hr hr hev, lemma27 hr hev]
  have hn : (0 : ℝ) < Fintype.card (Vr r) := by
    have := (card_Vr_bounds (r := r) (by omega)).1
    have : 0 < Fintype.card (Vr r) := lt_of_lt_of_le (by positivity) this
    exact_mod_cast this
  rw [mul_one_div, div_le_div_iff_of_pos_right hn, not_le]
  have : (c : ℝ) < r := by
    calc c < k := hk
      _ ≤ r := by simp only [r]; push_cast; linarith
  exact this

/-- **Remark after Theorem 9** (p. 9, l. 318–320): for the graphs `G_r, H_r` there is no uniform
bound of the form `δ₁ ≤ C · (δ₁^OT)^α` with `α > 2/3`.  Indeed `δ₁ = r/n`, `δ₁^OT = 1/n` and
`n ≤ 19 r³`. -/
theorem no_power_bound (C α : ℝ) (hα : 2 / 3 < α) : ∃ r : ℕ, 2 ≤ r ∧ Even r ∧
    ¬ (deltaOne (Gr r) (Hr r) ≤ C * deltaOTOne (Gr r) (Hr r) ^ α) := by
  have hβ : 0 < 3 * α - 2 := by linarith
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hβ).eventually_gt_atTop (19 * C))
  obtain ⟨k, hk⟩ := exists_nat_ge a
  refine ⟨2 * (k + 1), by omega, ⟨k + 1, by ring⟩, ?_⟩
  set r := 2 * (k + 1) with hrdef
  have hr : 2 ≤ r := by omega
  have hev : Even r := ⟨k + 1, by ring⟩
  unfold deltaOne deltaOTOne
  rw [dOne_Gr_Hr hr hev, lemma27 hr hev]
  obtain ⟨h1, h2⟩ := card_Vr_bounds (r := r) (by omega)
  set n := Fintype.card (Vr r)
  have hr0 : (0 : ℝ) < r := by positivity
  have hnR1 : (r : ℝ) ^ (3 : ℝ) ≤ n := by rw [Real.rpow_ofNat]; exact_mod_cast h1
  have hnR2 : (n : ℝ) ≤ 19 * (r : ℝ) ^ (3 : ℝ) := by rw [Real.rpow_ofNat]; exact_mod_cast h2
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnR1
  intro hle
  -- `r/n ≤ C (1/n)^α` gives `r ≤ C n^(1-α)`
  have key : (r : ℝ) ≤ C * (n : ℝ) ^ (1 - α) := by
    rw [one_div, Real.inv_rpow hn0.le, div_le_iff₀ hn0] at hle
    rw [Real.rpow_sub hn0, Real.rpow_one]
    calc (r : ℝ) ≤ C * ((n : ℝ) ^ α)⁻¹ * n := hle
      _ = C * ((n : ℝ) / (n : ℝ) ^ α) := by ring
  -- `n^(1-α) ≤ 19 r^(3(1-α))`
  have hpow : (n : ℝ) ^ (1 - α) ≤ 19 * (r : ℝ) ^ (3 * (1 - α)) := by
    rw [Real.rpow_mul hr0.le]
    rcases le_or_gt 0 (1 - α) with h | h
    · calc (n : ℝ) ^ (1 - α) ≤ (19 * (r : ℝ) ^ (3 : ℝ)) ^ (1 - α) :=
            Real.rpow_le_rpow hn0.le hnR2 h
        _ = (19 : ℝ) ^ (1 - α) * ((r : ℝ) ^ (3 : ℝ)) ^ (1 - α) :=
            Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 19 * ((r : ℝ) ^ (3 : ℝ)) ^ (1 - α) := by
            gcongr
            calc (19 : ℝ) ^ (1 - α) ≤ 19 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 19 := Real.rpow_one 19
    · calc (n : ℝ) ^ (1 - α) ≤ ((r : ℝ) ^ (3 : ℝ)) ^ (1 - α) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hnR1 h.le
        _ ≤ 19 * ((r : ℝ) ^ (3 : ℝ)) ^ (1 - α) := by
            have : 0 ≤ ((r : ℝ) ^ (3 : ℝ)) ^ (1 - α) := by positivity
            linarith
  have hq : 0 < (r : ℝ) ^ (3 * (1 - α)) := by positivity
  rcases le_or_gt C 0 with hC | hC
  · have : C * (n : ℝ) ^ (1 - α) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hC (by positivity)
    linarith
  · -- `r^(3α-2) = r / r^(3(1-α)) ≤ 19 C`, contradicting the choice of `r`
    have hrk : a ≤ (r : ℝ) := by
      calc a ≤ k := hk
        _ ≤ r := by rw [hrdef]; push_cast; linarith
    have hlt := ha r hrk
    have hβeq : (r : ℝ) ^ (3 * α - 2) = r / (r : ℝ) ^ (3 * (1 - α)) := by
      rw [show 3 * α - 2 = 1 - 3 * (1 - α) by ring, Real.rpow_sub hr0, Real.rpow_one]
    rw [hβeq, lt_div_iff₀ hq] at hlt
    have : (r : ℝ) ≤ 19 * C * (r : ℝ) ^ (3 * (1 - α)) := by
      calc (r : ℝ) ≤ C * (n : ℝ) ^ (1 - α) := key
        _ ≤ C * (19 * (r : ℝ) ^ (3 * (1 - α))) := by gcongr
        _ = 19 * C * (r : ℝ) ^ (3 * (1 - α)) := by ring
    linarith

end GsimOT.Prop8
