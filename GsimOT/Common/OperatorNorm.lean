/-
# ℓᵖ norms and operator `p → q` norms of matrices

Paper, App. A (Matrix Norms, p. 14, l. 474–486) and Lemma 19 (p. 14, l. 488–492).

For finite index types and `1 ≤ p, q ≤ ∞` we use
* `lpNorm p x` — the ℓᵖ norm of `x : ι → ℝ` (via Mathlib's `PiLp`);
* `opNorm p q A` — the operator norm `‖A‖_{p→q} = max_{‖x‖_p ≤ 1} ‖A x‖_q` of a matrix
  `A : Matrix ι κ ℝ` (acting on `x : κ → ℝ`);
* `ENNReal.conjExponent q` — the Hölder conjugate `q*` with `1/q + 1/q* = 1`.

Formalisation note.  The paper takes the maximum over the unit *sphere* `‖x‖_p = 1` (l. 479); we
take the supremum over the unit *ball* `‖x‖_p ≤ 1`.  Both agree by homogeneity whenever `κ` is
nonempty.  Lemma 19 is likewise stated with the unit balls of `‖·‖_p` and `‖·‖_{q*}`.
-/
import Mathlib

open Finset Matrix

namespace GsimOT

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The ℓᵖ norm of a real vector, `‖x‖_p` (`p ∈ [1, ∞]`). -/
noncomputable def lpNorm (p : ENNReal) (x : ι → ℝ) : ℝ := ‖WithLp.toLp p x‖

/-- The operator `p → q` norm `‖A‖_{p→q} := sup_{‖x‖_p ≤ 1} ‖A x‖_q`. -/
noncomputable def opNorm (p q : ENNReal) (A : Matrix ι κ ℝ) : ℝ :=
  sSup ((fun x => lpNorm q (A *ᵥ x)) '' {x : κ → ℝ | lpNorm p x ≤ 1})

/-! ### Exponents -/

lemma one_le_conjExponent {q : ENNReal} (hq : 1 ≤ q) : 1 ≤ ENNReal.conjExponent q := by
  have := (ENNReal.HolderConjugate.conjExponent hq).symm
  exact ENNReal.HolderConjugate.one_le _ q

/-- `1/q* = 1 - 1/q`. -/
lemma inv_conjExponent_toReal {q : ENNReal} (hq : 1 ≤ q) :
    (ENNReal.conjExponent q)⁻¹.toReal = 1 - q⁻¹.toReal := by
  have := ENNReal.HolderConjugate.conjExponent hq
  rw [← ENNReal.HolderConjugate.one_sub_inv q, ENNReal.toReal_sub_of_le
    (ENNReal.inv_le_one.2 hq) ENNReal.one_ne_top, ENNReal.toReal_one]

lemma inv_toReal_mem_Icc {q : ENNReal} (hq : 1 ≤ q) : q⁻¹.toReal ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (ENNReal.inv_le_one.2 hq)

/-! ### ℓᵖ norms -/

lemma lpNorm_nonneg (p : ENNReal) (x : ι → ℝ) : 0 ≤ lpNorm p x := by
  unfold lpNorm
  rcases p.trichotomy with rfl | rfl | hp
  · rw [PiLp.norm_eq_card]; positivity
  · rw [PiLp.norm_eq_ciSup]; exact Real.iSup_nonneg fun _ => norm_nonneg _
  · rw [PiLp.norm_eq_sum hp]; positivity

lemma lpNorm_eq_sum {p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤) (x : ι → ℝ) :
    lpNorm p x = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp'
  simp [lpNorm, PiLp.norm_eq_sum hp0]

lemma lpNorm_top (x : ι → ℝ) : lpNorm ⊤ x = ⨆ i, |x i| := by
  simp [lpNorm, PiLp.norm_eq_ciSup]

lemma lpNorm_zero (p : ENNReal) : lpNorm p (0 : ι → ℝ) = 0 := by
  unfold lpNorm
  rcases p.trichotomy with rfl | rfl | hp
  · simp [PiLp.norm_eq_card]
  · simp
  · simp [PiLp.norm_eq_sum hp, Real.zero_rpow hp.ne', Real.zero_rpow (inv_ne_zero hp.ne')]

lemma lpNorm_add_le {p : ENNReal} (hp : 1 ≤ p) (x y : ι → ℝ) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  simpa [lpNorm] using norm_add_le (WithLp.toLp p x) (WithLp.toLp p y)

lemma lpNorm_smul {p : ENNReal} (hp : 1 ≤ p) (c : ℝ) (x : ι → ℝ) :
    lpNorm p (c • x) = |c| * lpNorm p x := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  simp [lpNorm, WithLp.toLp_smul, norm_smul]

/-- Every coordinate is bounded by the norm. -/
lemma abs_le_lpNorm {p : ENNReal} (hp : 1 ≤ p) (x : ι → ℝ) (i : ι) : |x i| ≤ lpNorm p x := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  simpa [lpNorm] using PiLp.norm_apply_le (WithLp.toLp p x) i

/-- `‖x‖_q ≤ ‖x‖_1` and `‖x‖_∞ ≤ ‖x‖_p`, in the combined form `‖x‖_q ≤ ∑ |x i|`. -/
lemma lpNorm_le_sum_abs {p : ENNReal} (hp : 1 ≤ p) (x : ι → ℝ) : lpNorm p x ≤ ∑ i, |x i| := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  classical
  have hx : WithLp.toLp p x = ∑ i, PiLp.single p i (x i) := by
    ext j; simp [Pi.single_apply]
  rw [lpNorm, hx]
  refine (norm_sum_le _ _).trans_eq ?_
  simp

/-! ### Operator norms -/

/-- The matrix `A` as a continuous linear map `ℓᵖ(κ) → ℓ^q(ι)`. -/
private noncomputable def toCLM (p q : ENNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (A : Matrix ι κ ℝ) : PiLp p (fun _ : κ => ℝ) →L[ℝ] PiLp q (fun _ : ι => ℝ) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv q ℝ (ι → ℝ)).symm.toLinearMap ∘ₗ A.mulVecLin ∘ₗ
      (WithLp.linearEquiv p ℝ (κ → ℝ)).toLinearMap)

private lemma toCLM_apply (p q : ENNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (A : Matrix ι κ ℝ)
    (x : κ → ℝ) : toCLM p q A (WithLp.toLp p x) = WithLp.toLp q (A *ᵥ x) := rfl

/-- The unit ball of `ℓᵖ` is the image of `{x | ‖x‖_p ≤ 1}`. -/
private lemma closedBall_eq_image (p : ENNReal) [Fact (1 ≤ p)] :
    Metric.closedBall (0 : PiLp p (fun _ : κ => ℝ)) 1 =
      WithLp.toLp p '' {x : κ → ℝ | lpNorm p x ≤ 1} := by
  ext v
  simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_image, Set.mem_ofPred_eq, lpNorm]
  exact ⟨fun h => ⟨WithLp.ofLp v, by simpa using h, by simp⟩, by rintro ⟨x, hx, rfl⟩; exact hx⟩

/-- `opNorm` agrees with Mathlib's operator norm of `toCLM`. -/
private lemma opNorm_eq_norm_toCLM (p q : ENNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (A : Matrix ι κ ℝ) : opNorm p q A = ‖toCLM p q A‖ := by
  rw [← ContinuousLinearMap.sSup_unitClosedBall_eq_norm, closedBall_eq_image, Set.image_image]
  rfl

lemma opNorm_nonneg (p q : ENNReal) (A : Matrix ι κ ℝ) : 0 ≤ opNorm p q A := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, -, rfl⟩
  exact lpNorm_nonneg _ _

lemma lpNorm_mulVec_le {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) (A : Matrix ι κ ℝ)
    (x : κ → ℝ) : lpNorm q (A *ᵥ x) ≤ opNorm p q A * lpNorm p x := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  have : Fact (1 ≤ q) := ⟨hq⟩
  rw [opNorm_eq_norm_toCLM]
  simpa [lpNorm, toCLM_apply] using (toCLM p q A).le_opNorm (WithLp.toLp p x)

lemma opNorm_le_of_bound {p q : ENNReal} (_hp : 1 ≤ p) (_hq : 1 ≤ q) (A : Matrix ι κ ℝ) {C : ℝ}
    (_hC : 0 ≤ C) (h : ∀ x, lpNorm p x ≤ 1 → lpNorm q (A *ᵥ x) ≤ C) : opNorm p q A ≤ C := by
  refine csSup_le ⟨_, 0, by simp [lpNorm_zero], rfl⟩ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

/-- The supremum in the definition of `‖A‖_{p→q}` is attained. -/
lemma exists_lpNorm_mulVec_eq_opNorm {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (A : Matrix ι κ ℝ) : ∃ x, lpNorm p x ≤ 1 ∧ lpNorm q (A *ᵥ x) = opNorm p q A := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  have : Fact (1 ≤ q) := ⟨hq⟩
  obtain ⟨v, hv, hmax⟩ := (isCompact_closedBall (0 : PiLp p (fun _ : κ => ℝ)) 1).exists_isMaxOn
    (Metric.nonempty_closedBall.2 zero_le_one)
    (continuous_norm.comp (toCLM p q A).continuous).continuousOn
  refine ⟨WithLp.ofLp v, by simpa [lpNorm] using hv, ?_⟩
  rw [opNorm_eq_norm_toCLM, ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
  symm
  apply IsGreatest.csSup_eq
  refine ⟨⟨v, hv, rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hmax hw

/-- `‖A‖_{p→q} ≤ ∑_{i,j} |A i j|` (used for continuity). -/
lemma opNorm_le_sum_abs {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) (A : Matrix ι κ ℝ) :
    opNorm p q A ≤ ∑ i, ∑ j, |A i j| := by
  refine opNorm_le_of_bound hp hq A (by positivity) fun x hx => ?_
  refine (lpNorm_le_sum_abs hq _).trans (Finset.sum_le_sum fun i _ => ?_)
  calc |(A *ᵥ x) i| = |∑ j, A i j * x j| := rfl
    _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |A i j| := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) ((abs_le_lpNorm hp x j).trans hx)

/-- The triangle inequality for operator norms. -/
lemma opNorm_add_le {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) (A B : Matrix ι κ ℝ) :
    opNorm p q (A + B) ≤ opNorm p q A + opNorm p q B := by
  refine opNorm_le_of_bound hp hq _ (add_nonneg (opNorm_nonneg _ _ _) (opNorm_nonneg _ _ _))
    fun x hx => ?_
  rw [Matrix.add_mulVec]
  calc lpNorm q (A *ᵥ x + B *ᵥ x) ≤ lpNorm q (A *ᵥ x) + lpNorm q (B *ᵥ x) := lpNorm_add_le hq _ _
    _ ≤ opNorm p q A * lpNorm p x + opNorm p q B * lpNorm p x :=
        add_le_add (lpNorm_mulVec_le hp hq A x) (lpNorm_mulVec_le hp hq B x)
    _ ≤ opNorm p q A + opNorm p q B :=
        add_le_add (mul_le_of_le_one_right (opNorm_nonneg _ _ _) hx)
          (mul_le_of_le_one_right (opNorm_nonneg _ _ _) hx)

/-! ### Lemma 19: the bilinear characterisation -/

/-- `‖x‖_1 = ∑ |x i|`. -/
private lemma lpNorm_one (x : ι → ℝ) : lpNorm 1 x = ∑ i, |x i| := by
  simp [lpNorm_eq_sum le_rfl ENNReal.one_ne_top]

/-- **Hölder's inequality** `|y ⬝ᵥ z| ≤ ‖y‖_{q*} ‖z‖_q`. -/
private lemma abs_dotProduct_le_lpNorm_mul {q : ENNReal} (hq : 1 ≤ q) (y z : ι → ℝ) :
    |y ⬝ᵥ z| ≤ lpNorm (ENNReal.conjExponent q) y * lpNorm q z := by
  have hc := ENNReal.HolderConjugate.conjExponent hq
  have h1 : |y ⬝ᵥ z| ≤ ∑ i, |y i| * |z i| :=
    (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_mul])
  refine h1.trans ?_
  rcases eq_or_ne q ⊤ with rfl | hqt
  · rw [show ENNReal.conjExponent ⊤ = 1 by simp [ENNReal.conjExponent], lpNorm_one, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (abs_le_lpNorm le_top z i) (abs_nonneg _)
  rcases eq_or_ne q 1 with rfl | hq1
  · have : ENNReal.conjExponent 1 = ⊤ := by simp [ENNReal.conjExponent]
    rw [this, lpNorm_one, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (abs_le_lpNorm le_top y i) (abs_nonneg _)
  have hct : ENNReal.conjExponent q ≠ ⊤ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one _ q).2 hq1
  have hR : (ENNReal.conjExponent q).toReal.HolderConjugate q.toReal :=
    (ENNReal.HolderConjugate.toReal_of_ne_top hqt hct).symm
  rw [lpNorm_eq_sum (one_le_conjExponent hq) hct, lpNorm_eq_sum hq hqt]
  simpa using Real.inner_le_Lp_mul_Lq Finset.univ (fun i => |y i|) (fun i => |z i|) hR

/-- The sign vector `σ(z)_i = ±1` with `σ(z)_i * z_i = |z_i|`. -/
private noncomputable def sgn (z : ι → ℝ) : ι → ℝ := fun i => if 0 ≤ z i then 1 else -1

omit [Fintype ι] in
private lemma sgn_mul (z : ι → ℝ) (i : ι) : sgn z i * z i = |z i| := by
  unfold sgn; split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (not_le.1 h)]

omit [Fintype ι] in
private lemma abs_sgn (z : ι → ℝ) (i : ι) : |sgn z i| = 1 := by
  unfold sgn; split_ifs <;> simp

/-- **Duality of `ℓ^q` and `ℓ^{q*}`**: the Hölder bound is attained. -/
private lemma exists_dotProduct_eq_lpNorm {q : ENNReal} (hq : 1 ≤ q) (z : ι → ℝ) :
    ∃ y, lpNorm (ENNReal.conjExponent q) y ≤ 1 ∧ y ⬝ᵥ z = lpNorm q z := by
  classical
  have hc := ENNReal.HolderConjugate.conjExponent hq
  rcases eq_or_ne q ⊤ with rfl | hqt
  · rw [show ENNReal.conjExponent ⊤ = 1 by simp [ENNReal.conjExponent], lpNorm_top]
    cases isEmpty_or_nonempty ι
    · exact ⟨0, by simp [lpNorm_zero], by simp⟩
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => |z i|
    refine ⟨Pi.single i₀ (sgn z i₀), ?_, ?_⟩
    · rw [lpNorm_one, Finset.sum_eq_single i₀ (fun j _ hj => by simp [hj]) (by simp)]
      simp [abs_sgn]
    · rw [single_dotProduct, sgn_mul]
      exact le_antisymm (le_ciSup (f := fun i => |z i|) (Finite.bddAbove_range _) i₀) (ciSup_le hi₀)
  rcases eq_or_ne q 1 with rfl | hq1
  · have : ENNReal.conjExponent 1 = ⊤ := by simp [ENNReal.conjExponent]
    refine ⟨sgn z, ?_, ?_⟩
    · rw [this, lpNorm_top]
      exact Real.iSup_le (fun i => (abs_sgn z i).le) zero_le_one
    · simp [dotProduct, sgn_mul, lpNorm_one]
  have hct : ENNReal.conjExponent q ≠ ⊤ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one _ q).2 hq1
  have hR : q.toReal.HolderConjugate (ENNReal.conjExponent q).toReal :=
    ENNReal.HolderConjugate.toReal_of_ne_top hqt hct
  obtain ⟨g, hg, hfg⟩ :=
    (NNReal.isGreatest_Lp Finset.univ (fun i => (⟨|z i|, abs_nonneg _⟩ : NNReal)) hR).1
  simp only [Set.mem_ofPred_eq] at hg
  have hg' : ∑ i, ((g i : ℝ)) ^ (ENNReal.conjExponent q).toReal ≤ 1 := by
    exact_mod_cast hg
  have hfg' : ∑ i, |z i| * (g i : ℝ) = (∑ i, |z i| ^ q.toReal) ^ (1 / q.toReal) := by
    have := congrArg NNReal.toReal hfg
    push_cast at this
    exact this
  refine ⟨fun i => sgn z i * g i, ?_, ?_⟩
  · rw [lpNorm_eq_sum (one_le_conjExponent hq) hct]
    refine Real.rpow_le_one (by positivity) ?_ (by positivity)
    simpa [abs_mul, abs_sgn] using hg'
  · rw [lpNorm_eq_sum hq hqt, ← hfg']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_right_comm, sgn_mul, mul_comm]

/-- **Lemma 19 (≤).** `|yᵀ A x| ≤ ‖A‖_{p→q}` whenever `‖x‖_p ≤ 1` and `‖y‖_{q*} ≤ 1`
(Hölder's inequality). -/
lemma abs_dotProduct_mulVec_le_opNorm {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (A : Matrix ι κ ℝ) (x : κ → ℝ) (y : ι → ℝ) (hx : lpNorm p x ≤ 1)
    (hy : lpNorm (ENNReal.conjExponent q) y ≤ 1) : |y ⬝ᵥ (A *ᵥ x)| ≤ opNorm p q A := by
  calc |y ⬝ᵥ (A *ᵥ x)| ≤ lpNorm (ENNReal.conjExponent q) y * lpNorm q (A *ᵥ x) :=
        abs_dotProduct_le_lpNorm_mul hq y _
    _ ≤ 1 * (opNorm p q A * 1) := by
        gcongr
        · exact lpNorm_nonneg _ _
        · exact (lpNorm_mulVec_le hp hq A x).trans
            (mul_le_mul_of_nonneg_left hx (opNorm_nonneg _ _ _))
    _ = opNorm p q A := by ring

/-- **Lemma 19 (attained).** There are `x, y` with `‖x‖_p ≤ 1`, `‖y‖_{q*} ≤ 1` and
`|yᵀ A x| = ‖A‖_{p→q}` (duality of ℓ^q and ℓ^{q*}). -/
lemma exists_abs_dotProduct_mulVec_eq_opNorm {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (A : Matrix ι κ ℝ) :
    ∃ x y, lpNorm p x ≤ 1 ∧ lpNorm (ENNReal.conjExponent q) y ≤ 1 ∧
      |y ⬝ᵥ (A *ᵥ x)| = opNorm p q A := by
  obtain ⟨x, hx, hAx⟩ := exists_lpNorm_mulVec_eq_opNorm hp hq A
  obtain ⟨y, hy, hyz⟩ := exists_dotProduct_eq_lpNorm hq (A *ᵥ x)
  exact ⟨x, y, hx, hy, by rw [hyz, abs_of_nonneg (lpNorm_nonneg _ _), hAx]⟩

/-- **Lemma 19** (p. 14, l. 488–489). `‖A‖_{p→q} = max_{‖y‖_{q*} ≤ 1, ‖x‖_p ≤ 1} |yᵀ A x|`. -/
theorem lemma24 {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) (A : Matrix ι κ ℝ) :
    IsGreatest {t | ∃ x y, lpNorm p x ≤ 1 ∧ lpNorm (ENNReal.conjExponent q) y ≤ 1 ∧
      t = |y ⬝ᵥ (A *ᵥ x)|} (opNorm p q A) := by
  obtain ⟨x, y, hx, hy, h⟩ := exists_abs_dotProduct_mulVec_eq_opNorm hp hq A
  refine ⟨⟨x, y, hx, hy, h.symm⟩, ?_⟩
  rintro t ⟨x', y', hx', hy', rfl⟩
  exact abs_dotProduct_mulVec_le_opNorm hp hq A x' y' hx' hy'

end GsimOT
