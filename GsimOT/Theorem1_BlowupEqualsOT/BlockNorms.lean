/-
# Norms of spread and averaged vectors

Paper, App. B (pp. 16–19): the norm computations for the test vectors `x̃, ỹ` (proof of Eq. (11),
p. 16, l. 538–553) and `x, y` (proof of Eq. (15), pp. 18–19, l. 604–620).

A *block map* `b : β → α` partitions the finite set `β` into the blocks `b⁻¹(a)`, `a ∈ α`, of
sizes `c(a) = |b⁻¹(a)|`.  In App. B, `α = V × W`, `β = W × [ℓm]` and the block of `(v, w)`
is `{w} × J(v, w)`.

* Spreading (proof of Eq. (11)): `z̃(j) := z(b j) / c(b j)^{1/r}` satisfies `‖z̃‖_r ≤ ‖z‖_r`.
* Averaging (proof of Eq. (15)): `z(a) := (∑_{j ∈ b⁻¹(a)} z̃(j)) / c(a)^{1-1/r}` satisfies
  `‖z‖_r ≤ ‖z̃‖_r` (by Hölder's inequality in the form of Eq. (5)).
-/
import GsimOT.Common.OperatorNorm

open Finset

namespace GsimOT

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

/-- The size `c(a) = |b⁻¹(a)|` of the block of `a`. -/
def blockCard (b : β → α) (a : α) : ℕ := #{j | b j = a}

/-- Comparison of ℓ^r norms (`r < ∞`) via the sums of `r`-th powers. -/
private lemma lpNorm_le_of_sum_rpow_le {ι κ : Type*} [Fintype ι] [Fintype κ] {r : ENNReal}
    (hr : 1 ≤ r) (hr' : r ≠ ⊤) (f : ι → ℝ) (g : κ → ℝ)
    (h : ∑ i, |f i| ^ r.toReal ≤ ∑ k, |g k| ^ r.toReal) : lpNorm r f ≤ lpNorm r g := by
  rw [lpNorm_eq_sum hr hr', lpNorm_eq_sum hr hr']
  have hp : 0 < r.toReal := ENNReal.toReal_pos (by positivity) hr'
  exact Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity) h (by positivity)

omit [Fintype α] in
private lemma blockCard_pos (b : β → α) (j : β) : 0 < blockCard b (b j) := by
  unfold blockCard
  exact Finset.card_pos.mpr ⟨j, by simp⟩

/-- **Spreading** (proof of Eq. (11)). -/
lemma lpNorm_spread_le {r : ENNReal} (hr : 1 ≤ r) (b : β → α) (z : α → ℝ) :
    lpNorm r (fun j => z (b j) / (blockCard b (b j) : ℝ) ^ r⁻¹.toReal) ≤ lpNorm r z := by
  by_cases hr' : r = ⊤
  · subst hr'
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, Real.rpow_zero, div_one]
    rw [lpNorm_top]
    exact Real.iSup_le (fun j => abs_le_lpNorm hr z (b j)) (lpNorm_nonneg _ _)
  · apply lpNorm_le_of_sum_rpow_le hr hr'
    have hp : 0 < r.toReal := ENNReal.toReal_pos (by positivity) hr'
    have hinv : r⁻¹.toReal = r.toReal⁻¹ := ENNReal.toReal_inv r
    have key : ∀ j, |z (b j) / (blockCard b (b j) : ℝ) ^ r⁻¹.toReal| ^ r.toReal =
        |z (b j)| ^ r.toReal / (blockCard b (b j) : ℝ) := by
      intro j
      have hc : (0 : ℝ) < blockCard b (b j) := by exact_mod_cast blockCard_pos b j
      rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hc _),
        Real.div_rpow (abs_nonneg _) (Real.rpow_nonneg hc.le _), ← Real.rpow_mul hc.le, hinv,
        inv_mul_cancel₀ hp.ne', Real.rpow_one]
    simp_rw [key]
    rw [← Finset.sum_fiberwise Finset.univ b]
    refine Finset.sum_le_sum fun a _ => ?_
    have hfib : ∀ j ∈ Finset.univ.filter (fun j => b j = a),
        |z (b j)| ^ r.toReal / (blockCard b (b j) : ℝ) =
          |z a| ^ r.toReal / (blockCard b a : ℝ) := by
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
    change ((blockCard b a : ℕ) : ℝ) * _ ≤ _
    rcases Nat.eq_zero_or_pos (blockCard b a) with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, zero_mul]; positivity
    · have : (0 : ℝ) < blockCard b a := by exact_mod_cast hpos
      rw [mul_div_cancel₀ _ this.ne']

/-- **Averaging** (proof of Eq. (15)). -/
lemma lpNorm_average_le {r : ENNReal} (hr : 1 ≤ r) (b : β → α) (z : β → ℝ) :
    lpNorm r (fun a => (∑ j ∈ univ.filter (fun j => b j = a), z j) /
      (blockCard b a : ℝ) ^ (1 - r⁻¹.toReal)) ≤ lpNorm r z := by
  by_cases hr' : r = ⊤
  · subst hr'
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, sub_zero, Real.rpow_one]
    rw [lpNorm_top]
    refine Real.iSup_le (fun a => ?_) (lpNorm_nonneg _ _)
    rcases Nat.eq_zero_or_pos (blockCard b a) with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, div_zero, abs_zero]; exact lpNorm_nonneg _ _
    · have hc : (0 : ℝ) < blockCard b a := by exact_mod_cast hpos
      rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]
      calc |∑ j ∈ univ.filter (fun j => b j = a), z j|
          ≤ ∑ j ∈ univ.filter (fun j => b j = a), |z j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ univ.filter (fun j => b j = a), lpNorm ⊤ z :=
            Finset.sum_le_sum fun j _ => abs_le_lpNorm hr z j
        _ = lpNorm ⊤ z * blockCard b a := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]; rfl
  · apply lpNorm_le_of_sum_rpow_le hr hr'
    have hp1 : 1 ≤ r.toReal := by
      have := ENNReal.toReal_mono hr' hr
      simpa using this
    have hp : 0 < r.toReal := by linarith
    have hinv : r⁻¹.toReal = r.toReal⁻¹ := ENNReal.toReal_inv r
    rw [← Finset.sum_fiberwise Finset.univ b (fun j => |z j| ^ r.toReal)]
    refine Finset.sum_le_sum fun a _ => ?_
    rcases Nat.eq_zero_or_pos (blockCard b a) with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, abs_div]
      have hS : univ.filter (fun j => b j = a) = ∅ := by
        unfold blockCard at h0; exact Finset.card_eq_zero.mp h0
      rw [hS]; simp [Real.zero_rpow hp.ne']
    · have hc : (0 : ℝ) < blockCard b a := by exact_mod_cast hpos
      rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hc _),
        Real.div_rpow (abs_nonneg _) (Real.rpow_nonneg hc.le _), ← Real.rpow_mul hc.le, hinv,
        sub_mul, inv_mul_cancel₀ hp.ne', one_mul, div_le_iff₀ (Real.rpow_pos_of_pos hc _)]
      calc |∑ j ∈ univ.filter (fun j => b j = a), z j| ^ r.toReal
          ≤ (∑ j ∈ univ.filter (fun j => b j = a), |z j|) ^ r.toReal :=
            Real.rpow_le_rpow (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) hp.le
        _ ≤ (#(univ.filter (fun j => b j = a)) : ℝ) ^ (r.toReal - 1) *
              ∑ j ∈ univ.filter (fun j => b j = a), |z j| ^ r.toReal :=
            Real.rpow_sum_le_const_mul_sum_rpow _ _ hp1
        _ = _ := by rw [mul_comm]; rfl

end GsimOT
