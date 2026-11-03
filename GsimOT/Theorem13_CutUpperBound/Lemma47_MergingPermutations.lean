/-
# Lemma 47: merging two permutations (App. E.2.2, pp. 41–43)

Lemma 47 (Merging Two Permutations, p. 41, l. 1285–1287; proof pp. 41–43, l. 1288–1335). The
file also contains Lemma 42 (symmetrisation, p. 37, l. 1172–1174) and Lemma 44 (block Rademacher
estimate, p. 38, l. 1191–1193). Lemma 43 (Talagrand contraction lemma [LT91]) is the hypothesis
`hCP : ContractionPrinciple`, proved in `ContractionPrinciple.lean`.

* **Lemma 44** (`lemma44`): as in the paper, via uniformly random representatives `I_a ∈ B_a`
  (`sum_piFinset_comp`), Jensen, Lemma 43 and Eq. (29).
* **Lemma 42** (`lemma43`): independent `X_a ∼ Ber(θ_a)`, finite expectations (`bern`).
* Proof of Lemma 47: blocks with properties (i), (ii) (`exists_blocks`), Eq. (38)
  (`exists_good_choice`), repair of `T_X` (`exists_equiv_eq_off`); `lemma47_sharp` proves the
  bound `18 M n^{-1/3}` obtained at the end of the paper's proof (p. 43, l. 1334), `lemma47` the
  statement `20 M n^{-1/3}`.
-/
import GsimOT.Theorem13_CutUpperBound.Definitions

open Finset

set_option linter.unusedSectionVars false

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

namespace Lemma47

/-! ### Rademacher averages -/

/-- The Rademacher sign vector associated with `s : Fin b → Bool`. -/
def sgn {b : ℕ} (s : Fin b → Bool) : Fin b → ℝ := fun a => if s a then 1 else -1

lemma radAvg_eq {b : ℕ} (F : (Fin b → ℝ) → ℝ) :
    radAvg F = (∑ s : Fin b → Bool, F (sgn s)) / 2 ^ b := rfl

lemma radAvg_mono {b : ℕ} {F G : (Fin b → ℝ) → ℝ} (h : ∀ s, F (sgn s) ≤ G (sgn s)) :
    radAvg F ≤ radAvg G := by
  rw [radAvg_eq, radAvg_eq]
  gcongr with s
  exact h s

lemma radAvg_add {b : ℕ} (F G : (Fin b → ℝ) → ℝ) :
    radAvg (fun σ => F σ + G σ) = radAvg F + radAvg G := by
  rw [radAvg_eq, radAvg_eq, radAvg_eq, sum_add_distrib, add_div]

lemma radAvg_const_mul {b : ℕ} (c : ℝ) (F : (Fin b → ℝ) → ℝ) :
    radAvg (fun σ => c * F σ) = c * radAvg F := by
  rw [radAvg_eq, radAvg_eq, ← mul_sum, mul_div_assoc]

lemma radAvg_sum {b : ℕ} {κ : Type*} (t : Finset κ) (F : κ → (Fin b → ℝ) → ℝ) :
    radAvg (fun σ => ∑ k ∈ t, F k σ) = ∑ k ∈ t, radAvg (F k) := by
  simp only [radAvg_eq]
  rw [sum_comm, sum_div]

lemma card_bool_fun (b : ℕ) : (Fintype.card (Fin b → Bool) : ℝ) = 2 ^ b := by
  simp

lemma radAvg_const {b : ℕ} (c : ℝ) : radAvg (fun _ : Fin b → ℝ => c) = c := by
  rw [radAvg_eq, sum_const, card_univ, nsmul_eq_mul, card_bool_fun]
  field_simp

lemma sgn_sq {b : ℕ} (s : Fin b → Bool) (a : Fin b) : sgn s a * sgn s a = 1 := by
  unfold sgn; split_ifs <;> norm_num

/-- Orthogonality of Rademacher signs: `∑_s σ_a(s) σ_{a'}(s) = 2^b δ_{a a'}`. -/
lemma sum_sgn_mul_sgn {b : ℕ} (a a' : Fin b) :
    ∑ s : Fin b → Bool, sgn s a * sgn s a' = if a = a' then (2 : ℝ) ^ b else 0 := by
  split_ifs with h
  · subst h
    simp only [sgn_sq, sum_const, card_univ, nsmul_eq_mul, mul_one, card_bool_fun]
  · let fl : (Fin b → Bool) → (Fin b → Bool) := fun s => Function.update s a (!s a)
    have hinv : Function.Involutive fl := by
      intro s; simp [fl]
    have hneg : ∀ s, sgn (fl s) a * sgn (fl s) a' = -(sgn s a * sgn s a') := by
      intro s
      simp only [sgn, fl, Function.update_self, Function.update_of_ne (Ne.symm h)]
      cases s a <;> cases s a' <;> simp
    have := Equiv.sum_comp hinv.toPerm (fun s => sgn s a * sgn s a')
    simp only [Function.Involutive.coe_toPerm, hneg, sum_neg_distrib] at this
    linarith

/-- Rademacher averages of norms: `E_σ ‖∑_a σ_a x_a‖ ≤ (∑_a ‖x_a‖²)^{1/2}` (Cauchy–Schwarz and the
orthogonality of Rademacher signs, used in the proof of Lemma 44). -/
lemma radAvg_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {b : ℕ}
    (x : Fin b → E) : radAvg (fun σ => ‖∑ a, σ a • x a‖) ≤ √(∑ a, ‖x a‖ ^ 2) := by
  rw [radAvg_eq]
  have hN : (0 : ℝ) < 2 ^ b := by positivity
  have hsq : ∀ s : Fin b → Bool, ‖∑ a, sgn s a • x a‖ ^ 2 =
      ∑ a, ∑ a', sgn s a * sgn s a' * inner ℝ (x a) (x a') := by
    intro s
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine sum_congr rfl fun a _ => ?_
    rw [inner_sum]
    refine sum_congr rfl fun a' _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  have htot : ∑ s : Fin b → Bool, ‖∑ a, sgn s a • x a‖ ^ 2 = 2 ^ b * ∑ a, ‖x a‖ ^ 2 := by
    simp_rw [hsq]
    rw [sum_comm]
    simp_rw [sum_comm (s := (univ : Finset (Fin b → Bool))) (t := univ), ← sum_mul,
      sum_sgn_mul_sgn, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true, mul_sum,
      real_inner_self_eq_norm_sq]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin b → Bool)))
    (f := fun s => ‖∑ a, sgn s a • x a‖)
  rw [card_univ, htot] at hcs
  rw [card_bool_fun] at hcs
  apply Real.le_sqrt_of_sq_le
  rw [div_pow]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ### Suprema over the closed unit ball -/

section Ball

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The closed unit ball is nonempty. -/
lemma ball_nonempty : Nonempty (Metric.closedBall (0 : E) 1) := ⟨⟨0, by simp⟩⟩

attribute [local instance] ball_nonempty

lemma inner_abs_le (z : Metric.closedBall (0 : E) 1) (y : E) : |inner ℝ z.1 y| ≤ ‖y‖ := by
  have hz : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
  calc |inner ℝ z.1 y| ≤ ‖z.1‖ * ‖y‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * ‖y‖ := by gcongr
    _ = ‖y‖ := one_mul _

lemma abs_max_zero_le (t : ℝ) : |max t 0| ≤ |t| := by
  simpa using abs_max_sub_max_le_abs t 0 0

lemma phi_abs_le (z : Metric.closedBall (0 : E) 1) (y : E) : |max (inner ℝ z.1 y) 0| ≤ ‖y‖ :=
  (abs_max_zero_le _).trans (inner_abs_le z y)

/-- Since `s ↦ s_+` is `1`-Lipschitz, `|⟨z, y⟩_+ - ⟨z, y'⟩_+| ≤ ‖y - y'‖` on the unit ball. -/
lemma phi_sub_le (z : Metric.closedBall (0 : E) 1) (y y' : E) :
    |max (inner ℝ z.1 y) 0 - max (inner ℝ z.1 y') 0| ≤ ‖y - y'‖ :=
  (abs_max_sub_max_le_abs _ _ _).trans (by rw [← inner_sub_right]; exact inner_abs_le z _)

lemma le_ballSup {F : Metric.closedBall (0 : E) 1 → ℝ} {C : ℝ} (hC : ∀ z, F z ≤ C) (z) :
    F z ≤ ⨆ z, F z :=
  le_ciSup ⟨C, by rintro _ ⟨w, rfl⟩; exact hC w⟩ z

/-- `|∑_a c_a ⟨z, x_a⟩_+| ≤ ∑_a ‖x_a‖` for `|c_a| ≤ 1` and `z` in the unit ball. -/
lemma abs_sum_phi_le {κ : Type*} (t : Finset κ) (c : κ → ℝ) (hc : ∀ k, |c k| ≤ 1) (x : κ → E)
    (z : Metric.closedBall (0 : E) 1) :
    |∑ k ∈ t, c k * max (inner ℝ z.1 (x k)) 0| ≤ ∑ k ∈ t, ‖x k‖ := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  calc |c k| * |max (inner ℝ z.1 (x k)) 0| ≤ 1 * ‖x k‖ := by
        gcongr
        · exact hc k
        · exact phi_abs_le z _
    _ = ‖x k‖ := one_mul _

lemma abs_sgn {b : ℕ} (s : Fin b → Bool) (a : Fin b) : |sgn s a| = 1 := by
  unfold sgn; split_ifs <;> norm_num

/-- Suprema over `T = range f` are suprema over the parameter. -/
lemma iSup_range_eq {α β : Type*} (f : α → β) (G : β → ℝ) :
    ⨆ t : Set.range f, G t.1 = ⨆ z, G (f z) := by
  show sSup (Set.range _) = sSup (Set.range _)
  congr 1
  ext x
  simp

/-- A sum over a set with at most one element commutes with `y ↦ ⟨z, y⟩_+`. -/
lemma sum_phi_of_card_le_one {ι : Type*} (s : Finset ι) (hs : s.card ≤ 1) (z : E) (y : ι → E) :
    ∑ i ∈ s, max (inner ℝ z (y i)) 0 = max (inner ℝ z (∑ i ∈ s, y i)) 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with h | h
  · rw [card_eq_zero.mp h]; simp
  · obtain ⟨a, rfl⟩ := card_eq_one.mp h; simp

lemma norm_sq_sum_le_of_card_le_one {ι : Type*} (s : Finset ι) (hs : s.card ≤ 1) (y : ι → E)
    {M : ℝ} (hy : ∀ i, ‖y i‖ ≤ M) : ‖∑ i ∈ s, y i‖ ^ 2 ≤ M ^ 2 * s.card := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with h | h
  · rw [card_eq_zero.mp h]; simp
  · obtain ⟨a, rfl⟩ := card_eq_one.mp h
    simp only [sum_singleton, card_singleton, Nat.cast_one, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) (hy a) 2


/-! ### Lemma 44 (block Rademacher estimate) -/

/-- Averaging over a uniformly random representative `I_a ∈ B_a` (proof of Lemma 44): for the
product `𝓘 = ∏_a B_a` (as a `piFinset`), `∑_{I ∈ 𝓘} g(I_a) = (∏_{a' ≠ a} ℓ_{a'}) ∑_{i ∈ B_a} g(i)`. -/
lemma sum_piFinset_comp {b : ℕ} (B : Fin b → Finset V) (a : Fin b) (g : V → ℝ) :
    ∑ I ∈ Fintype.piFinset B, g (I a) =
      (∏ a' ∈ univ.erase a, ((B a').card : ℝ)) * ∑ i ∈ B a, g i := by
  rw [← sum_fiberwise_of_maps_to (s := Fintype.piFinset B) (t := B a) (g := fun I => I a)
    (fun I hI => Fintype.mem_piFinset.mp hI a), mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g i) (fun I hI => by rw [(mem_filter.mp hI).2]),
    sum_const, Fintype.card_filter_piFinset_eq_of_mem B a hi, nsmul_eq_mul]
  push_cast; ring

/-- **Lemma 44** (block Rademacher estimate, p. 38, l. 1191–1193). Let `B_1, …, B_b ⊆ V` be
non-empty, `ℓ_a = |B_a|`, and `‖u_i‖ ≤ M`. Then
`E_σ sup_{z ∈ B_H} |∑_a σ_a ∑_{i ∈ B_a} ⟨z, u_i⟩_+| ≤ 2 M (∑_a ℓ_a²)^{1/2}`.
(The Lean statement does not assume the blocks pairwise disjoint, so it is a more general form of
Lemma 44.)

Proof as in the paper: with independent uniformly random representatives `I_a ∈ B_a`,
`∑_{i ∈ B_a} ⟨z, u_i⟩_+ = E_{I_a} (ℓ_a ⟨z, u_{I_a}⟩)_+`; Jensen (`hstep1`), the contraction principle
(`hCP`, Lemma 43, for `s ↦ s_+`) for fixed `I` (`hstep2`), `sup_z |⟨z, g_σ⟩| ≤ ‖g_σ‖` and
`E_σ ‖g_σ‖ ≤ (E_σ ‖g_σ‖²)^{1/2} ≤ M (∑_a ℓ_a²)^{1/2}` (`hstep3`); `hstep2` and `hstep3` give
Eq. (29). -/
lemma lemma44 (hCP : ContractionPrinciple) {b : ℕ} (B : Fin b → Finset V)
    (hB : ∀ a, (B a).Nonempty) (u : V → E) {M : ℝ} (hM0 : 0 ≤ M) (hu : ∀ i, ‖u i‖ ≤ M) :
    radAvg (fun σ => ⨆ z : Metric.closedBall (0 : E) 1,
      |∑ a, σ a * ∑ i ∈ B a, max (inner ℝ z.1 (u i)) 0|) ≤
      2 * M * √(∑ a, ((B a).card : ℝ) ^ 2) := by
  let 𝓘 : Finset (Fin b → V) := Fintype.piFinset B
  let ℓ : Fin b → ℝ := fun a => ((B a).card : ℝ)
  have hℓ : ∀ a, 0 ≤ ℓ a := fun a => Nat.cast_nonneg _
  have hN : (#𝓘 : ℝ) = ∏ a, ℓ a := by
    simp only [𝓘, ℓ, Fintype.card_piFinset]; push_cast; rfl
  have hNpos : (0 : ℝ) < #𝓘 := by
    rw [hN]; exact prod_pos fun a _ => Nat.cast_pos.mpr (hB a).card_pos
  -- the vectors `ℓ_a u_{I_a}`
  let x : (Fin b → V) → Fin b → E := fun I a => ℓ a • u (I a)
  -- `∑_{i ∈ B_a} ⟨z, u_i⟩_+ = E_I (ℓ_a ⟨z, u_{I_a}⟩)_+`
  have hid : ∀ (σ : Fin b → ℝ) (z : E), ∑ a, σ a * ∑ i ∈ B a, max (inner ℝ z (u i)) 0 =
      (#𝓘 : ℝ)⁻¹ * ∑ I ∈ 𝓘, ∑ a, σ a * max (inner ℝ z (x I a)) 0 := by
    intro σ z
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    have h1 : ∀ I : Fin b → V, max (inner ℝ z (x I a)) 0 = ℓ a * max (inner ℝ z (u (I a))) 0 :=
      fun I => by
        simp only [x, real_inner_smul_right]
        rw [mul_max_of_nonneg _ _ (hℓ a), mul_zero]
    simp only [h1]
    rw [← mul_sum, ← mul_sum, sum_piFinset_comp B a (fun i => max (inner ℝ z (u i)) 0), hN,
      ← mul_prod_erase univ ℓ (mem_univ a)]
    have hne : (ℓ a * ∏ a' ∈ univ.erase a, ℓ a') ≠ 0 := by
      rw [mul_prod_erase univ ℓ (mem_univ a), ← hN]; exact hNpos.ne'
    have hP : (∏ a' ∈ univ.erase a, ((B a').card : ℝ)) = ∏ a' ∈ univ.erase a, ℓ a' := rfl
    rw [hP, show ∀ c S P : ℝ, σ a * (c * (P * S)) = (c * P) * (σ a * S) from fun _ _ _ => by ring,
      ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  -- step 1 (Jensen): move the expectation over `I` outside the supremum
  have hstep1 : ∀ s : Fin b → Bool,
      (⨆ z : Metric.closedBall (0 : E) 1, |∑ a, sgn s a * ∑ i ∈ B a, max (inner ℝ z.1 (u i)) 0|) ≤
      (#𝓘 : ℝ)⁻¹ * ∑ I ∈ 𝓘, ⨆ z : Metric.closedBall (0 : E) 1,
        |∑ a, sgn s a * max (inner ℝ z.1 (x I a)) 0| := by
    intro s
    refine ciSup_le fun z => ?_
    rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hNpos)]
    gcongr
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun I _ => ?_)
    exact le_ballSup (F := fun z : Metric.closedBall (0 : E) 1 =>
      |∑ a, sgn s a * max (inner ℝ z.1 (x I a)) 0|)
      (fun z => abs_sum_phi_le _ _ (fun a => (abs_sgn s a).le) _ z) z
  -- step 2: for fixed `I`, the contraction principle (Lemma 43)
  have hstep2 : ∀ I, radAvg (fun σ => ⨆ z : Metric.closedBall (0 : E) 1,
      |∑ a, σ a * max (inner ℝ z.1 (x I a)) 0|) ≤
      2 * radAvg (fun σ => ‖∑ a, σ a • x I a‖) := by
    intro I
    let f : Metric.closedBall (0 : E) 1 → (Fin b → ℝ) := fun z a => inner ℝ z.1 (x I a)
    have hT : Bornology.IsBounded (Set.range f) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨∑ a, ‖x I a‖, ?_⟩
      rintro _ ⟨z, rfl⟩
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
      rw [Real.norm_eq_abs]
      exact (inner_abs_le z _).trans
        (single_le_sum (f := fun a => ‖x I a‖) (fun _ _ => norm_nonneg _) (mem_univ a))
    have hlip : ∀ _ : Fin b, LipschitzWith 1 (fun s : ℝ => max s 0) := fun _ =>
      LipschitzWith.of_dist_le_mul fun p q => by
        simpa [Real.dist_eq] using abs_max_sub_max_le_abs p q 0
    have hcp := hCP b (Set.range f) hT (Set.range_nonempty f) (fun _ s => max s 0) hlip
      (fun _ => by simp)
    have e1 : (fun σ : Fin b → ℝ => ⨆ t : Set.range f, |∑ a, σ a * max (t.1 a) 0|) =
        fun σ => ⨆ z, |∑ a, σ a * max (f z a) 0| :=
      funext fun σ => iSup_range_eq f (fun t => |∑ a, σ a * max (t a) 0|)
    have e2 : (fun σ : Fin b → ℝ => ⨆ t : Set.range f, |∑ a, σ a * t.1 a|) =
        fun σ => ⨆ z, |∑ a, σ a * f z a| :=
      funext fun σ => iSup_range_eq f (fun t => |∑ a, σ a * t a|)
    rw [e1, e2] at hcp
    refine hcp.trans ?_
    gcongr
    refine radAvg_mono fun s => ciSup_le fun z => ?_
    simp only [f]
    have : ∑ a, sgn s a * inner ℝ z.1 (x I a) = inner ℝ z.1 (∑ a, sgn s a • x I a) := by
      rw [inner_sum]; simp_rw [real_inner_smul_right]
    rw [this]
    exact inner_abs_le z _
  -- step 3: `E_σ ‖g_σ‖ ≤ (∑_a ℓ_a² ‖u_{I_a}‖²)^{1/2} ≤ M (∑_a ℓ_a²)^{1/2}`
  have hstep3 : ∀ I, radAvg (fun σ => ‖∑ a, σ a • x I a‖) ≤ M * √(∑ a, ℓ a ^ 2) := by
    intro I
    refine (radAvg_norm_le _).trans ?_
    have h1 : ∑ a, ‖x I a‖ ^ 2 ≤ M ^ 2 * ∑ a, ℓ a ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun a _ => ?_
      simp only [x, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hℓ a), mul_pow]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hu _) 2) (sq_nonneg _)
    calc √(∑ a, ‖x I a‖ ^ 2) ≤ √(M ^ 2 * ∑ a, ℓ a ^ 2) := Real.sqrt_le_sqrt h1
      _ = M * √(∑ a, ℓ a ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM0]
  -- combine, and take the expectation over `I`
  calc _ ≤ radAvg (fun σ => (#𝓘 : ℝ)⁻¹ * ∑ I ∈ 𝓘, ⨆ z : Metric.closedBall (0 : E) 1,
        |∑ a, σ a * max (inner ℝ z.1 (x I a)) 0|) := radAvg_mono hstep1
    _ = (#𝓘 : ℝ)⁻¹ * ∑ I ∈ 𝓘, radAvg (fun σ => ⨆ z : Metric.closedBall (0 : E) 1,
        |∑ a, σ a * max (inner ℝ z.1 (x I a)) 0|) := by
        rw [radAvg_const_mul, radAvg_sum]
    _ ≤ (#𝓘 : ℝ)⁻¹ * ∑ _I ∈ 𝓘, 2 * (M * √(∑ a, ℓ a ^ 2)) := by
        gcongr with I _
        exact (hstep2 I).trans (by gcongr; exact hstep3 I)
    _ = 2 * M * √(∑ a, ((B a).card : ℝ) ^ 2) := by
        rw [sum_const, nsmul_eq_mul]
        field_simp
        rfl

end Ball

/-! ### Lemma 42 (symmetrisation) -/

section Symmetrisation

/-- The product Bernoulli(`θ_a`) weight of `X ∈ {0,1}^b` (encoded as `Fin b → Bool`). -/
def bern {b : ℕ} (θ : Fin b → ℝ) (X : Fin b → Bool) : ℝ := ∏ a, if X a then θ a else 1 - θ a

/-- The `{0,1}`-valued coordinates of `X`. -/
def ind {b : ℕ} (X : Fin b → Bool) (a : Fin b) : ℝ := if X a then 1 else 0

lemma bern_nonneg {b : ℕ} {θ : Fin b → ℝ} (hθ0 : ∀ a, 0 ≤ θ a) (hθ1 : ∀ a, θ a ≤ 1)
    (X : Fin b → Bool) :
    0 ≤ bern θ X :=
  prod_nonneg fun a _ => by split_ifs <;> linarith [hθ0 a, hθ1 a]

lemma sum_bern {b : ℕ} (θ : Fin b → ℝ) : ∑ X : Fin b → Bool, bern θ X = 1 := by
  unfold bern
  rw [← Fintype.prod_sum (fun (a : Fin b) (x : Bool) => if x then θ a else 1 - θ a)]
  simp

/-- The marginals of the product Bernoulli measure: `E X_a = θ_a`. -/
lemma sum_bern_ind {b : ℕ} (θ : Fin b → ℝ) (a : Fin b) :
    ∑ X : Fin b → Bool, bern θ X * ind X a = θ a := by
  have h : ∀ X : Fin b → Bool, bern θ X * ind X a = ∏ c, ((if X c then θ c else 1 - θ c) *
      (if c = a then (if X c then 1 else 0) else 1)) := by
    intro X
    rw [prod_mul_distrib, Fintype.prod_ite_eq']
    rfl
  simp_rw [h]
  rw [← Fintype.prod_sum (fun (c : Fin b) (x : Bool) => (if x then θ c else 1 - θ c) *
      (if c = a then (if x then 1 else 0) else 1))]
  rw [prod_eq_single a]
  · simp
  · intro c _ hc; simp [hc]
  · simp

lemma abs_ind_sub_le {b : ℕ} {θ : Fin b → ℝ} (hθ0 : ∀ a, 0 ≤ θ a) (hθ1 : ∀ a, θ a ≤ 1)
    (X : Fin b → Bool) (a : Fin b) : |ind X a - θ a| ≤ 1 := by
  unfold ind; rw [abs_le]; split_ifs <;> constructor <;> linarith [hθ0 a, hθ1 a]

lemma abs_ind_le {b : ℕ} (X : Fin b → Bool) (a : Fin b) : |ind X a| ≤ 1 := by
  unfold ind; split_ifs <;> simp

/-- The coordinatewise swap of `(X, X')` at the coordinates where `s` is `false`. -/
def swapAt {b : ℕ} (s : Fin b → Bool) (p : (Fin b → Bool) × (Fin b → Bool)) :
    (Fin b → Bool) × (Fin b → Bool) :=
  (fun a => if s a then p.1 a else p.2 a, fun a => if s a then p.2 a else p.1 a)

lemma swapAt_involutive {b : ℕ} (s : Fin b → Bool) : Function.Involutive (swapAt s) := by
  intro p
  ext a <;> simp only [swapAt] <;> split_ifs <;> rfl

lemma bern_swapAt {b : ℕ} (θ : Fin b → ℝ) (s : Fin b → Bool) (p : (Fin b → Bool) × (Fin b → Bool)) :
    bern θ (swapAt s p).1 * bern θ (swapAt s p).2 = bern θ p.1 * bern θ p.2 := by
  unfold bern
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun a _ => ?_
  simp only [swapAt]
  split_ifs <;> ring

lemma ind_swapAt {b : ℕ} (s : Fin b → Bool) (p : (Fin b → Bool) × (Fin b → Bool)) (a : Fin b) :
    ind (swapAt s p).1 a - ind (swapAt s p).2 a = sgn s a * (ind p.1 a - ind p.2 a) := by
  rcases p with ⟨X, X'⟩
  simp only [swapAt, sgn, ind]
  by_cases h : s a <;> by_cases h1 : X a <;> by_cases h2 : X' a <;> simp [h, h1, h2]

variable {Z : Type*} [Nonempty Z]

lemma le_sup_of_bd {F : Z → ℝ} {C : ℝ} (hC : ∀ z, F z ≤ C) (z : Z) : F z ≤ ⨆ z, F z :=
  le_ciSup ⟨C, by rintro _ ⟨w, rfl⟩; exact hC w⟩ z

/-- **Lemma 42** (symmetrisation, p. 37, l. 1172–1174), for independent `{0,1}`-valued
`X_1, …, X_b` with `E X_a = θ_a`
and bounded `d_a : Z → ℝ`:
`E_X sup_{z} |∑_a (X_a - θ_a) d_a(z)| ≤ 2 E_X E_σ sup_z |∑_a σ_a X_a d_a(z)|`.
Expectations are finite weighted sums (`bern`, `radAvg`). As in the paper, the proof uses an
independent copy `X'` of `X` (Jensen), the symmetry of `X_a - X'_a` (via the coordinate swap
`swapAt`) and the triangle inequality. -/
lemma lemma43 {b : ℕ} {θ : Fin b → ℝ} (hθ0 : ∀ a, 0 ≤ θ a) (hθ1 : ∀ a, θ a ≤ 1) (d : Fin b → Z → ℝ) {C : ℝ}
    (hd : ∀ a z, |d a z| ≤ C) :
    ∑ X : Fin b → Bool, bern θ X * ⨆ z, |∑ a, (ind X a - θ a) * d a z| ≤
      2 * ∑ X : Fin b → Bool, bern θ X *
        radAvg (fun σ => ⨆ z, |∑ a, σ a * ind X a * d a z|) := by
  have hbd : ∀ c : Fin b → ℝ, (∀ a, |c a| ≤ 1) → ∀ z, |∑ a, c a * d a z| ≤ ∑ _a : Fin b, C := by
    intro c hc z
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
    rw [abs_mul]
    calc |c a| * |d a z| ≤ 1 * C := mul_le_mul (hc a) (hd a z) (abs_nonneg _) zero_le_one
      _ = C := one_mul _
  let S : (Fin b → Bool) → (Fin b → Bool) → ℝ := fun X X' =>
    ⨆ z, |∑ a, (ind X a - ind X' a) * d a z|
  let Sσ : (Fin b → Bool) → (Fin b → Bool) → (Fin b → Bool) → ℝ := fun s X X' =>
    ⨆ z, |∑ a, sgn s a * (ind X a - ind X' a) * d a z|
  let R : (Fin b → Bool) → (Fin b → Bool) → ℝ := fun s X =>
    ⨆ z, |∑ a, sgn s a * ind X a * d a z|
  have hbern := bern_nonneg (b := b) hθ0 hθ1
  -- Jensen with an independent copy `X'`
  have hstep1 : ∀ X, ⨆ z, |∑ a, (ind X a - θ a) * d a z| ≤ ∑ X', bern θ X' * S X X' := by
    intro X
    refine ciSup_le fun z => ?_
    have hid : ∑ a, (ind X a - θ a) * d a z =
        ∑ X', bern θ X' * ∑ a, (ind X a - ind X' a) * d a z := by
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun a _ => ?_
      simp_rw [← mul_assoc, ← sum_mul, mul_sub, sum_sub_distrib, ← sum_mul, sum_bern,
        sum_bern_ind, one_mul]
    rw [hid]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun X' _ => ?_)
    rw [abs_mul, abs_of_nonneg (hbern X')]
    gcongr
    · exact hbern X'
    · exact le_sup_of_bd (F := fun z => |∑ a, (ind X a - ind X' a) * d a z|)
        (hbd _ (fun a => by unfold ind; split_ifs <;> norm_num)) z
  -- symmetry of `X - X'`
  have hstep2 : ∀ s, ∑ X, ∑ X', bern θ X * bern θ X' * S X X' =
      ∑ X, ∑ X', bern θ X * bern θ X' * Sσ s X X' := by
    intro s
    simp only [← Fintype.sum_prod_type']
    rw [← Equiv.sum_comp (swapAt_involutive s).toPerm]
    refine sum_congr rfl fun p _ => ?_
    simp only [Function.Involutive.coe_toPerm]
    rw [bern_swapAt]
    congr 1
    simp only [S, Sσ]
    simp_rw [ind_swapAt]
  -- triangle inequality
  have hstep3 : ∀ s X X', Sσ s X X' ≤ R s X + R s X' := by
    intro s X X'
    refine ciSup_le fun z => ?_
    have : ∑ a, sgn s a * (ind X a - ind X' a) * d a z =
        ∑ a, sgn s a * ind X a * d a z - ∑ a, sgn s a * ind X' a * d a z := by
      rw [← sum_sub_distrib]; congr 1; ext a; ring
    rw [this]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · exact le_sup_of_bd (F := fun z => |∑ a, sgn s a * ind X a * d a z|)
        (hbd _ (fun a => by rw [abs_mul, abs_sgn, one_mul]; exact abs_ind_le X a)) z
    · exact le_sup_of_bd (F := fun z => |∑ a, sgn s a * ind X' a * d a z|)
        (hbd _ (fun a => by rw [abs_mul, abs_sgn, one_mul]; exact abs_ind_le X' a)) z
  have hN : (0 : ℝ) < 2 ^ b := by positivity
  have hA : ∀ X : Fin b → Bool, radAvg (fun σ => ⨆ z, |∑ a, σ a * ind X a * d a z|) =
      (∑ s, R s X) / 2 ^ b := fun X => rfl
  calc ∑ X, bern θ X * ⨆ z, |∑ a, (ind X a - θ a) * d a z|
      ≤ ∑ X, bern θ X * ∑ X', bern θ X' * S X X' :=
        sum_le_sum fun X _ => mul_le_mul_of_nonneg_left (hstep1 X) (hbern X)
    _ = ∑ X, ∑ X', bern θ X * bern θ X' * S X X' := by
        simp_rw [mul_sum, mul_assoc]
    _ = (∑ s : Fin b → Bool, ∑ X, ∑ X', bern θ X * bern θ X' * Sσ s X X') / 2 ^ b := by
        simp_rw [← hstep2]
        rw [sum_const, card_univ, nsmul_eq_mul, card_bool_fun]
        field_simp
    _ ≤ (∑ s : Fin b → Bool, ∑ X, ∑ X', bern θ X * bern θ X' * (R s X + R s X')) / 2 ^ b := by
        gcongr with s _ X _ X' _
        · exact mul_nonneg (hbern X) (hbern X')
        · exact hstep3 s X X'
    _ = ∑ X, ∑ X', bern θ X * bern θ X' * ((∑ s, R s X) / 2 ^ b + (∑ s, R s X') / 2 ^ b) := by
        simp_rw [sum_div]
        rw [sum_comm]
        refine sum_congr rfl fun X _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun X' _ => ?_
        simp only [div_eq_mul_inv, ← sum_mul, ← mul_sum, sum_add_distrib]
        ring
    _ = 2 * ∑ X, bern θ X * radAvg (fun σ => ⨆ z, |∑ a, σ a * ind X a * d a z|) := by
        simp_rw [hA, mul_add, sum_add_distrib]
        have e1 : ∑ X : Fin b → Bool, ∑ X' : Fin b → Bool, bern θ X * bern θ X' * ((∑ s, R s X) / 2 ^ b) =
            ∑ X : Fin b → Bool, bern θ X * ((∑ s, R s X) / 2 ^ b) := by
          refine sum_congr rfl fun X _ => ?_
          rw [← sum_mul, ← mul_sum, sum_bern, mul_one]
        have e2 : ∑ X : Fin b → Bool, ∑ X' : Fin b → Bool, bern θ X * bern θ X' * ((∑ s, R s X') / 2 ^ b) =
            ∑ X' : Fin b → Bool, bern θ X' * ((∑ s, R s X') / 2 ^ b) := by
          rw [sum_comm]
          refine sum_congr rfl fun X' _ => ?_
          rw [← sum_mul, ← sum_mul, sum_bern, one_mul]
        rw [e1, e2]
        ring

end Symmetrisation

/-! ### The block partition along the cycles of `τ` (properties (i) and (ii)) -/

section Blocks

/-- `S ⊆ V` is `L`-separated along `τ`: no two distinct points of `S` are at distance
`1 ≤ p < L` along `τ`. -/
def Sep (τ : Equiv.Perm V) (L : ℕ) (S : Finset V) : Prop :=
  ∀ s ∈ S, ∀ p, 1 ≤ p → p < L → (τ ^ p) s ∈ S → (τ ^ p) s = s

lemma perm_pow_apply_succ (τ : Equiv.Perm V) (m : ℕ) (x : V) : (τ ^ m) (τ x) = (τ ^ (m + 1)) x := by
  rw [pow_succ, Equiv.Perm.mul_apply]

/-- A maximal `L`-separated set meets every orbit segment `i, τ i, …, τ^{2L-1} i`. -/
lemma exists_sep_cover (τ : Equiv.Perm V) (L : ℕ) (hL : 1 ≤ L) :
    ∃ S : Finset V, Sep τ L S ∧ ∀ i, ∃ k < 2 * L, (τ ^ k) i ∈ S := by
  classical
  obtain ⟨S, hS, hmax⟩ := exists_max_image (univ.powerset.filter (Sep τ L)) card
    ⟨∅, by simp [Sep]⟩
  simp only [mem_filter, mem_powerset, subset_univ, true_and] at hS hmax
  refine ⟨S, hS, fun i => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxdef⟩ : ∃ x, x = (τ ^ L) i := ⟨_, rfl⟩
  have hx : x ∉ S := hxdef ▸ hcon L (by omega)
  have hsep : Sep τ L (insert x S) := by
    intro s hs p hp1 hpL hps
    rw [mem_insert] at hs hps
    rcases hs with rfl | hs
    · rcases hps with h | h
      · exact h
      · exfalso
        apply hcon (p + L) (by omega)
        rwa [pow_add, Equiv.Perm.mul_apply, ← hxdef]
    · rcases hps with h | h
      · exfalso
        have : s = (τ ^ (L - p)) i := by
          apply (τ ^ p).injective
          rw [h, hxdef, ← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hpL.le]
        exact hcon (L - p) (by omega) (this ▸ hs)
      · exact hS s hs p hp1 hpL h
  have := hmax (insert x S) hsep
  rw [card_insert_of_notMem hx] at this
  omega

/-- The block partition of the proof of Lemma 47 (p. 42, l. 1303–1310). Blocks are segments
`i, τ i, τ² i, …` of the cycles of `τ`, labelled by `blk : V → V`; `pos i` is the position of `i`
counted backwards from the end of its block. Then
* (i) every block has fewer than `2L` elements (`pos i < 2L` and `(blk, pos)` is injective), and
* (ii) at most `n / L` elements `i` have `i` and `τ i` in different blocks.

(We obtain the segments from a maximal `L`-separated set of cut points rather than from the cycle
decomposition; any construction with (i) and (ii) suffices for the proof.) -/
lemma exists_blocks (τ : Equiv.Perm V) (L : ℕ) (hL : 1 ≤ L) :
    ∃ (blk : V → V) (pos : V → ℕ), (∀ i, pos i < 2 * L) ∧
      (∀ i j, blk i = blk j → pos i = pos j → i = j) ∧
      L * #{i | blk (τ i) ≠ blk i} ≤ Fintype.card V := by
  classical
  obtain ⟨S, hsep, hcov⟩ := exists_sep_cover τ L hL
  have hex : ∀ i, ∃ k, (τ ^ k) i ∈ S := fun i => (hcov i).imp fun k hk => hk.2
  let k : V → ℕ := fun i => Nat.find (hex i)
  have hk_spec : ∀ i, (τ ^ k i) i ∈ S := fun i => Nat.find_spec (hex i)
  have hk_min : ∀ i m, (τ ^ m) i ∈ S → k i ≤ m := fun i m h => Nat.find_min' (hex i) h
  have hk_lt : ∀ i, k i < 2 * L := fun i => by
    obtain ⟨m, hm, hmS⟩ := hcov i
    exact (hk_min i m hmS).trans_lt hm
  let blk : V → V := fun i => (τ ^ k i) i
  -- (a) outside `S`, `i` and `τ i` lie in the same block
  have ha : ∀ i, i ∉ S → blk (τ i) = blk i := by
    intro i hi
    have hk0 : k i ≠ 0 := by
      intro h0
      have := hk_spec i
      rw [h0, pow_zero, Equiv.Perm.one_apply] at this
      exact hi this
    have h1 : k (τ i) + 1 ≤ k i := by
      have : k (τ i) ≤ k i - 1 := hk_min (τ i) (k i - 1) (by
        rw [perm_pow_apply_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
        exact hk_spec i)
      omega
    have h2 : k i ≤ k (τ i) + 1 :=
      hk_min i _ (by rw [← perm_pow_apply_succ]; exact hk_spec (τ i))
    show (τ ^ k (τ i)) (τ i) = (τ ^ k i) i
    rw [perm_pow_apply_succ, show k (τ i) + 1 = k i by omega]
  -- (b) points of `S` are the last elements of their blocks
  have hb : ∀ s ∈ S, k s = 0 := fun s hs =>
    Nat.le_zero.mp (hk_min s 0 (by rwa [pow_zero, Equiv.Perm.one_apply]))
  have hb' : ∀ s ∈ S, blk s = s := fun s hs => by
    show (τ ^ k s) s = s
    rw [hb s hs, pow_zero, Equiv.Perm.one_apply]
  -- (c) short cycles form a single block
  have hc : ∀ s ∈ S, ∀ p, 1 ≤ p → p < L → (τ ^ p) s = s → blk (τ s) = s := by
    intro s hs p hp1 hpL hps
    have hq : k (τ s) ≤ p - 1 := hk_min (τ s) (p - 1) (by
      rw [perm_pow_apply_succ, Nat.sub_add_cancel hp1, hps]; exact hs)
    have hmem : (τ ^ (k (τ s) + 1)) s ∈ S := by
      rw [← perm_pow_apply_succ]; exact hk_spec (τ s)
    have := hsep s hs (k (τ s) + 1) (by omega) (by omega) hmem
    show (τ ^ k (τ s)) (τ s) = s
    rw [perm_pow_apply_succ, this]
  -- (d) a boundary point `s` is the last element of a block containing `(τ^j)⁻¹ s`, `j < L`
  have hd : ∀ s, blk (τ s) ≠ blk s → ∀ j < L,
      blk ((τ ^ j)⁻¹ s) = s ∧ k ((τ ^ j)⁻¹ s) = j := by
    intro s hbd j hj
    have hs : s ∈ S := by
      by_contra h; exact hbd (ha s h)
    have hjs : (τ ^ j) ((τ ^ j)⁻¹ s) = s := by simp
    have hkj : k ((τ ^ j)⁻¹ s) = j := by
      refine le_antisymm (hk_min _ j (by rw [hjs]; exact hs)) ?_
      by_contra hlt
      push Not at hlt
      obtain ⟨m, hm⟩ : ∃ m, m = k ((τ ^ j)⁻¹ s) := ⟨_, rfl⟩
      rw [← hm] at hlt
      have hm' : (τ ^ m) ((τ ^ j)⁻¹ s) ∈ S := hm ▸ hk_spec _
      have hshift : (τ ^ (j - m)) ((τ ^ m) ((τ ^ j)⁻¹ s)) = s := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hlt.le, hjs]
      have := hsep _ hm' (j - m) (by omega) (by omega) (by rw [hshift]; exact hs)
      rw [hshift] at this
      have hper : (τ ^ (j - m)) s = s := by
        conv_lhs => rw [this]
        exact hshift
      exact hbd ((hc s hs (j - m) (by omega) (by omega) hper).trans (hb' s hs).symm)
    refine ⟨?_, hkj⟩
    show (τ ^ k ((τ ^ j)⁻¹ s)) ((τ ^ j)⁻¹ s) = s
    rw [hkj, hjs]
  refine ⟨blk, k, hk_lt, ?_, ?_⟩
  · intro i j hij hk
    have : (τ ^ k i) i = (τ ^ k i) j := by
      have h' : (τ ^ k j) j = (τ ^ k i) j := by rw [hk]
      exact hij.trans h'
    exact (τ ^ k i).injective this
  · have := card_le_card_of_injOn (s := (univ.filter fun i => blk (τ i) ≠ blk i) ×ˢ range L)
      (t := (univ : Finset V)) (fun p => (τ ^ p.2)⁻¹ p.1) (fun _ _ => mem_univ _) (by
        rintro ⟨s, j⟩ hsj ⟨s', j'⟩ hsj' heq
        simp only [coe_product, Set.mem_prod, mem_coe, mem_filter, mem_univ, true_and,
          mem_range] at hsj hsj'
        have e1 := hd s hsj.1 j hsj.2
        have e2 := hd s' hsj'.1 j' hsj'.2
        simp only at heq
        rw [heq] at e1
        rw [Prod.mk.injEq]
        exact ⟨e1.1.symm.trans e2.1, e1.2.symm.trans e2.2⟩)
    rw [card_product, card_range, card_univ] at this
    rw [mul_comm]; exact this

end Blocks

/-! ### Repairing a map into a bijection -/

/-- A map `T : V → W` that is injective outside `S` agrees outside `S` with some bijection. -/
lemma exists_equiv_eq_off (T : V → W) (S : Finset V)
    (hT : ∀ i j, i ∉ S → j ∉ S → T i = T j → i = j)
    (hcard : Fintype.card V = Fintype.card W) : ∃ π : V ≃ W, ∀ i ∉ S, π i = T i := by
  classical
  let f : V ≃ W := Fintype.equivOfCardEq hcard
  let T' : {i // i ∉ S} → V := fun i => f.symm (T i.1)
  have hinj : Function.Injective T' := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    exact Subtype.ext (hT i j hi hj (f.symm.injective h))
  let e := Equiv.ofInjective T' hinj
  refine ⟨e.extendSubtype.trans f, fun i hi => ?_⟩
  rw [Equiv.trans_apply, Equiv.extendSubtype_apply_of_mem e i hi, Equiv.ofInjective_apply]
  simp [T']

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [local instance] ball_nonempty

/-- Regrouping a sum over the elements by blocks. -/
lemma sum_blk {b : ℕ} (blk : V → Fin b) (c : Fin b → ℝ) (f : V → ℝ) :
    ∑ a, c a * ∑ i ∈ univ.filter (fun i => blk i = a), f i = ∑ i, c (blk i) * f i := by
  simp_rw [mul_sum]
  rw [← sum_fiberwise univ blk (fun i => c (blk i) * f i)]
  refine sum_congr rfl fun a _ => sum_congr rfl fun i hi => ?_
  rw [(mem_filter.mp hi).2]

lemma ind_mul_phi {b : ℕ} (X : Fin b → Bool) (a : Fin b) (z y : E) :
    ind X a * max (inner ℝ z y) 0 = max (inner ℝ z (ind X a • y)) 0 := by
  unfold ind; split_ifs <;> simp

/-- The probabilistic part of the proof of Lemma 47, culminating in Eq. (38) (unnormalised): the
blocks are the fibres `B_a` of `blk : V → Fin b` (all non-empty); for independent `X_a ∼ Ber(θ)`,
Lemma 42 and two applications of Lemma 44 bound `E_X sup_z |∑_a (X_a - θ) d_a(z)|` by
`8 M (∑_a |B_a|²)^{1/2}`, so some `X` attains this bound. -/
lemma exists_good_choice (hCP : ContractionPrinciple) {b : ℕ} (blk : V → Fin b)
    (hsurj : ∀ a, ∃ i, blk i = a)
    (u0 u1 : V → E) {M : ℝ} (hM0 : 0 ≤ M) (hu0 : ∀ i, ‖u0 i‖ ≤ M) (hu1 : ∀ i, ‖u1 i‖ ≤ M)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ X : Fin b → Bool, ⨆ z : Metric.closedBall (0 : E) 1,
      |∑ i, (ind X (blk i) - θ) * (max (inner ℝ z.1 (u1 i)) 0 - max (inner ℝ z.1 (u0 i)) 0)| ≤
      8 * M * √(∑ a, (#(univ.filter fun i => blk i = a) : ℝ) ^ 2) := by
  let B : Fin b → Finset V := fun a => univ.filter fun i => blk i = a
  have hB : ∀ a, (B a).Nonempty := fun a => by
    obtain ⟨i, hi⟩ := hsurj a
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  let Λ : ℝ := √(∑ a, (#(B a) : ℝ) ^ 2)
  let d : Fin b → Metric.closedBall (0 : E) 1 → ℝ := fun a z =>
    ∑ i ∈ B a, (max (inner ℝ z.1 (u1 i)) 0 - max (inner ℝ z.1 (u0 i)) 0)
  have hdiff : ∀ (z : Metric.closedBall (0 : E) 1) i,
      |max (inner ℝ z.1 (u1 i)) 0 - max (inner ℝ z.1 (u0 i)) 0| ≤ 2 * M := fun z i =>
    (phi_sub_le z _ _).trans ((norm_sub_le _ _).trans (by linarith [hu0 i, hu1 i]))
  have hd : ∀ a z, |d a z| ≤ ∑ _i : V, 2 * M := by
    intro a z
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun i _ => hdiff z i).trans ?_
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by linarith)
  have hid : ∀ (c : Fin b → ℝ) z, ∑ a, c a * d a z = ∑ i, c (blk i) *
      (max (inner ℝ z.1 (u1 i)) 0 - max (inner ℝ z.1 (u0 i)) 0) := fun c z => sum_blk blk c _
  -- Lemma 42 (with `θ_a = θ` for all blocks)
  have h43 := lemma43 (θ := fun _ => θ) (fun _ => hθ0) (fun _ => hθ1) d hd
  -- Lemma 44, twice: to the vectors `X_a u_i` (`= 0` on the blocks with `X_a = 0`)
  have h44 : ∀ X : Fin b → Bool,
      radAvg (fun σ => ⨆ z, |∑ a, σ a * ind X a * d a z|) ≤ 4 * M * Λ := by
    intro X
    let y1 : V → E := fun i => ind X (blk i) • u1 i
    let y0 : V → E := fun i => ind X (blk i) • u0 i
    have hy : ∀ (u : V → E), (∀ i, ‖u i‖ ≤ M) → ∀ i, ‖ind X (blk i) • u i‖ ≤ M := by
      intro u hu i
      rw [norm_smul, Real.norm_eq_abs]
      calc |ind X (blk i)| * ‖u i‖ ≤ 1 * M := mul_le_mul (abs_ind_le X _) (hu i) (norm_nonneg _)
            zero_le_one
        _ = M := one_mul M
    have hsplit : ∀ (σ : Fin b → ℝ) (z : Metric.closedBall (0 : E) 1),
        ∑ a, σ a * ind X a * d a z = ∑ a, σ a * ∑ i ∈ B a, max (inner ℝ z.1 (y1 i)) 0 -
          ∑ a, σ a * ∑ i ∈ B a, max (inner ℝ z.1 (y0 i)) 0 := by
      intro σ z
      rw [hid (fun a => σ a * ind X a) z, sum_blk blk σ, sum_blk blk σ, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [y1, y0, ← ind_mul_phi]
      ring
    have hbd : ∀ (s : Fin b → Bool) (y : V → E) (z : Metric.closedBall (0 : E) 1),
        |∑ a, sgn s a * ∑ i ∈ B a, max (inner ℝ z.1 (y i)) 0| ≤ ∑ i, ‖y i‖ := by
      intro s y z
      rw [sum_blk blk (sgn s)]
      exact abs_sum_phi_le _ _ (fun i => (abs_sgn s (blk i)).le) _ z
    have hle : ∀ s : Fin b → Bool, (⨆ z, |∑ a, sgn s a * ind X a * d a z|) ≤
        (⨆ z : Metric.closedBall (0 : E) 1,
          |∑ a, sgn s a * ∑ i ∈ B a, max (inner ℝ z.1 (y1 i)) 0|) +
        (⨆ z : Metric.closedBall (0 : E) 1,
          |∑ a, sgn s a * ∑ i ∈ B a, max (inner ℝ z.1 (y0 i)) 0|) := by
      intro s
      refine ciSup_le fun z => ?_
      rw [hsplit]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · exact le_ballSup (F := fun z : Metric.closedBall (0 : E) 1 =>
          |∑ a, sgn s a * ∑ i ∈ B a, max (inner ℝ z.1 (y1 i)) 0|) (hbd s y1) z
      · exact le_ballSup (F := fun z : Metric.closedBall (0 : E) 1 =>
          |∑ a, sgn s a * ∑ i ∈ B a, max (inner ℝ z.1 (y0 i)) 0|) (hbd s y0) z
    refine (radAvg_mono (G := fun σ =>
      (⨆ z : Metric.closedBall (0 : E) 1, |∑ a, σ a * ∑ i ∈ B a, max (inner ℝ z.1 (y1 i)) 0|) +
      (⨆ z : Metric.closedBall (0 : E) 1, |∑ a, σ a * ∑ i ∈ B a, max (inner ℝ z.1 (y0 i)) 0|))
      hle).trans ?_
    rw [radAvg_add]
    have e1 := lemma44 hCP B hB y1 hM0 (hy u1 hu1)
    have e0 := lemma44 hCP B hB y0 hM0 (hy u0 hu0)
    linarith
  have hbern := bern_nonneg (b := b) (θ := fun _ => θ) (fun _ => hθ0) (fun _ => hθ1)
  have havg : ∑ X : Fin b → Bool, bern (fun _ => θ) X * ⨆ z, |∑ a, (ind X a - θ) * d a z| ≤
      8 * M * Λ := by
    refine h43.trans ?_
    calc 2 * ∑ X : Fin b → Bool, bern (fun _ => θ) X *
          radAvg (fun σ => ⨆ z, |∑ a, σ a * ind X a * d a z|)
        ≤ 2 * ∑ X : Fin b → Bool, bern (fun _ => θ) X * (4 * M * Λ) := by
          gcongr with X _
          · exact hbern X
          · exact h44 X
      _ = 8 * M * Λ := by rw [← sum_mul, sum_bern]; ring
  -- the probabilistic method: some `X` is at most the average
  by_contra hcon
  push Not at hcon
  have hpos' : 0 < ∑ X : Fin b → Bool, bern (fun _ => θ) X *
      ((⨆ z, |∑ a, (ind X a - θ) * d a z|) - 8 * M * Λ) := by
    have hX : ∀ X : Fin b → Bool, 8 * M * Λ < ⨆ z, |∑ a, (ind X a - θ) * d a z| := by
      intro X
      have := hcon X
      simp only [hid]
      exact this
    obtain ⟨X₀, hX₀⟩ : ∃ X₀ : Fin b → Bool, 0 < bern (fun _ => θ) X₀ := by
      by_contra h
      push Not at h
      have : ∑ X : Fin b → Bool, bern (fun _ => θ) X ≤ 0 := sum_nonpos fun X _ => h X
      rw [sum_bern] at this
      linarith
    exact sum_pos' (fun X _ => mul_nonneg (hbern X) (by linarith [hX X]))
      ⟨X₀, mem_univ _, mul_pos hX₀ (by linarith [hX X₀])⟩
  simp_rw [mul_sub, sum_sub_distrib, ← sum_mul, sum_bern, one_mul] at hpos'
  linarith


/-- `h_{P_π}(z) = (1/n) ∑_i ⟨z, v_{i, π i}⟩_+`. -/
lemma hSupp_permMat (v : V → W → E) (π : V ≃ W) (z : E) :
    hSupp v (permMat π) z = (∑ i, max (inner ℝ z (v i (π i))) 0) / Fintype.card V := by
  unfold hSupp
  congr 1
  rw [← sum_mul_permMat π (fun i j => max (inner ℝ z (v i j)) 0)]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_comm _ _

/-- Linearity of `R ↦ h_R`. -/
lemma hSupp_comb (v : V → W → E) (R₀ R₁ : V → W → ℝ) (θ : ℝ) (z : E) :
    hSupp v (fun i j => (1 - θ) * R₀ i j + θ * R₁ i j) z =
      (1 - θ) * hSupp v R₀ z + θ * hSupp v R₁ z := by
  unfold hSupp
  rw [mul_div_assoc', mul_div_assoc', ← add_div]
  congr 1
  simp_rw [add_mul, sum_add_distrib, mul_assoc, ← mul_sum]

end Main

end Lemma47

open Lemma47 in
/-- **Lemma 47** (Merging two permutations), with the constant `18 M` reached at the end of the
paper's proof (p. 43, l. 1333–1334, which ends with `≤ 18 M n^{-1/3}`): there is a permutation
`π` with `ρ(P_π, (1 - θ) P_{π₀} + θ P_{π₁}) ≤ 18 M n^{-1/3}`. -/
theorem lemma47_sharp (hCP : ContractionPrinciple) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : V → W → E) {M : ℝ} (hM : ∀ i j, ‖v i j‖ ≤ M)
    (hcard : Fintype.card V = Fintype.card W) (π₀ π₁ : V ≃ W) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    ∃ π : V ≃ W, rhoSupp v (permMat π) (fun i j => (1 - θ) * permMat π₀ i j + θ * permMat π₁ i j)
      ≤ 18 * M * (Fintype.card V : ℝ) ^ (-(1 / 3 : ℝ)) := by
  classical
  have := ball_nonempty (E := E)
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · -- the trivial case `n = 0`
    refine ⟨π₀, ?_⟩
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp h0
    have : rhoSupp v (permMat π₀)
        (fun i j => (1 - θ) * permMat π₀ i j + θ * permMat π₁ i j) = 0 := by
      unfold rhoSupp hSupp; simp
    rw [this, h0, Nat.cast_zero, Real.zero_rpow (by norm_num), mul_zero]
  obtain ⟨i₀⟩ : Nonempty V := Fintype.card_pos_iff.mp hpos
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM i₀ (π₀ i₀))
  -- w.l.o.g. `P₀ = I`, `P₁ = P_τ`: we work with `τ = π₀⁻¹ ∘ π₁`
  let τ : Equiv.Perm V := π₁.trans π₀.symm
  have hτ : ∀ i, π₀ (τ i) = π₁ i := fun i => by simp [τ]
  -- `L = ⌈n^{1/3}⌉`
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hpos
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (Fintype.card V : ℝ) ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  have ht3 : t ^ 3 = Fintype.card V := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have ht1 : 1 ≤ t := htdef ▸ Real.one_le_rpow hnR (by norm_num)
  have htneg : (Fintype.card V : ℝ) ^ (-(1 / 3 : ℝ)) = t⁻¹ := by
    rw [Real.rpow_neg (by positivity), htdef]
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = ⌈t⌉₊ := ⟨_, rfl⟩
  have hLt : t ≤ L := hLdef ▸ Nat.le_ceil t
  have hLt' : (L : ℝ) < t + 1 := hLdef ▸ Nat.ceil_lt_add_one (by linarith)
  have hL1 : 1 ≤ L := by exact_mod_cast (show (1 : ℝ) ≤ L by linarith)
  -- the blocks, with properties (i) and (ii)
  obtain ⟨blk0, pos, hpos2, hinj0, hbd⟩ := exists_blocks τ L hL1
  -- the blocks `B_1, …, B_b`, indexed by `Fin b`
  let lab : Finset V := univ.image blk0
  let e := lab.equivFin
  let blk : V → Fin lab.card := fun i => e ⟨blk0 i, mem_image_of_mem _ (mem_univ i)⟩
  have hblk : ∀ i j, blk i = blk j ↔ blk0 i = blk0 j := fun i j => by
    simp only [blk, e.injective.eq_iff, Subtype.mk.injEq]
  have hsurj : ∀ a, ∃ i, blk i = a := fun a => by
    obtain ⟨i, -, hi⟩ := mem_image.mp (e.symm a).2
    refine ⟨i, ?_⟩
    have : (⟨blk0 i, mem_image_of_mem _ (mem_univ i)⟩ : lab) = e.symm a := Subtype.ext hi
    simp only [blk, this, Equiv.apply_symm_apply]
  have hinj : ∀ i j, blk i = blk j → pos i = pos j → i = j := fun i j h hp =>
    hinj0 i j ((hblk i j).mp h) hp
  -- property (i): `∑_a |B_a|² ≤ 2 L n`
  have hsumsq : ∑ a, (#(univ.filter fun i => blk i = a) : ℝ) ^ 2 ≤
      ((2 * L : ℕ) : ℝ) * Fintype.card V := by
    have hcardB : ∀ a, #(univ.filter fun i => blk i = a) ≤ 2 * L := fun a => by
      have := card_le_card_of_injOn pos (s := univ.filter fun i => blk i = a) (t := range (2 * L))
        (fun i _ => mem_range.mpr (hpos2 i)) (fun i hi j hj h => hinj i j
          ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm) h)
      simpa using this
    calc ∑ a, (#(univ.filter fun i => blk i = a) : ℝ) ^ 2
        ≤ ∑ a, ((2 * L : ℕ) : ℝ) * #(univ.filter fun i => blk i = a) := by
          refine sum_le_sum fun a _ => ?_
          rw [sq]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardB a) (Nat.cast_nonneg _)
      _ = ((2 * L : ℕ) : ℝ) * Fintype.card V := by
          rw [← mul_sum, ← Nat.cast_sum, ← card_univ,
            ← card_eq_sum_card_fiberwise (f := blk) (fun i _ => mem_univ _)]
  -- Eq. (38): a good choice `X` of the blocks following `τ`
  obtain ⟨X, hX⟩ := exists_good_choice hCP blk hsurj (fun i => v i (π₀ i))
    (fun i => v i (π₁ i)) hM0 (fun i => hM _ _) (fun i => hM _ _) hθ0 hθ1
  let T : V → W := fun i => if X (blk i) then π₁ i else π₀ i
  -- repairing `T_X` into a bijection
  let Bd : Finset V := univ.filter (fun i => blk0 (τ i) ≠ blk0 i)
  have hTinj : ∀ i j, i ∉ Bd → j ∉ Bd → T i = T j → i = j := by
    intro i j hi hj h
    simp only [Bd, mem_filter, mem_univ, true_and, not_not] at hi hj
    simp only [T] at h
    by_cases hXi : X (blk i) <;> by_cases hXj : X (blk j) <;> simp only [hXi, hXj] at h
    · exact π₁.injective (by simpa using h)
    · exfalso
      have hj' : τ i = j := π₀.injective ((hτ i).trans (by simpa using h))
      have hb : blk j = blk i := (hblk j i).mpr (by rw [← hj', hi])
      rw [hb] at hXj; exact hXj hXi
    · exfalso
      have hi' : τ j = i := π₀.injective ((hτ j).trans (by simpa using h.symm))
      have hb : blk i = blk j := (hblk i j).mpr (by rw [← hi', hj])
      rw [hb] at hXi; exact hXi hXj
    · exact π₀.injective (by simpa using h)
  obtain ⟨π, hπ⟩ := exists_equiv_eq_off T Bd hTinj hcard
  refine ⟨π, ?_⟩
  have hrep : ∀ z : Metric.closedBall (0 : E) 1, |∑ i, max (inner ℝ z.1 (v i (π i))) 0 -
      ∑ i, max (inner ℝ z.1 (v i (T i))) 0| ≤ #Bd * (2 * M) := by
    intro z
    rw [← sum_sub_distrib, ← sum_subset (subset_univ Bd)
      (fun i _ hi => by rw [hπ i hi, sub_self])]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun i _ => (phi_sub_le z _ _).trans ((norm_sub_le _ _).trans
      (show ‖v i (π i)‖ + ‖v i (T i)‖ ≤ 2 * M by linarith [hM i (π i), hM i (T i)]))).trans ?_
    rw [sum_const, nsmul_eq_mul]
  have hT : ∀ z : Metric.closedBall (0 : E) 1, ∑ i, max (inner ℝ z.1 (v i (T i))) 0 -
      ((1 - θ) * ∑ i, max (inner ℝ z.1 (v i (π₀ i))) 0 +
        θ * ∑ i, max (inner ℝ z.1 (v i (π₁ i))) 0) =
      ∑ i, (ind X (blk i) - θ) *
        (max (inner ℝ z.1 (v i (π₁ i))) 0 - max (inner ℝ z.1 (v i (π₀ i))) 0) := by
    intro z
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [T, ind]
    split_ifs <;> ring
  have hbdd : ∀ z : Metric.closedBall (0 : E) 1, |∑ i, (ind X (blk i) - θ) *
      (max (inner ℝ z.1 (v i (π₁ i))) 0 - max (inner ℝ z.1 (v i (π₀ i))) 0)| ≤
      ∑ _i : V, 2 * M := by
    intro z
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    calc |ind X (blk i) - θ| * |max (inner ℝ z.1 (v i (π₁ i))) 0 -
          max (inner ℝ z.1 (v i (π₀ i))) 0| ≤ 1 * (2 * M) :=
          mul_le_mul (abs_ind_sub_le (θ := fun _ => θ) (fun _ => hθ0) (fun _ => hθ1) X _) ((phi_sub_le z _ _).trans
            ((norm_sub_le _ _).trans (by linarith [hM i (π₀ i), hM i (π₁ i)])))
            (abs_nonneg _) zero_le_one
      _ = 2 * M := one_mul _
  have hz := fun z => (le_ballSup (F := fun z : Metric.closedBall (0 : E) 1 =>
    |∑ i, (ind X (blk i) - θ) *
      (max (inner ℝ z.1 (v i (π₁ i))) 0 - max (inner ℝ z.1 (v i (π₀ i))) 0)|) hbdd z).trans hX
  -- numerics: `#Bd ≤ n^{2/3}` (property (ii)) and `√(2 L n) ≤ 2 n^{2/3}` (property (i))
  have ht0 : 0 < t := by linarith
  have hBd : (#Bd : ℝ) ≤ t ^ 2 := by
    have h1 : (L : ℝ) * #Bd ≤ t ^ 3 := by rw [ht3]; exact_mod_cast hbd
    have h2 : t * #Bd ≤ t * t ^ 2 := by nlinarith [(Nat.cast_nonneg (#Bd) : (0 : ℝ) ≤ #Bd)]
    exact le_of_mul_le_mul_left h2 ht0
  have hsq : √(∑ a, (#(univ.filter fun i => blk i = a) : ℝ) ^ 2) ≤ 2 * t ^ 2 := by
    refine (Real.sqrt_le_sqrt hsumsq).trans ?_
    rw [Real.sqrt_le_left (by positivity), ← ht3]
    push_cast
    nlinarith
  -- conclusion
  unfold rhoSupp
  refine ciSup_le fun z => ?_
  rw [hSupp_comb, hSupp_permMat, hSupp_permMat, hSupp_permMat, htneg]
  have hn0 : (0 : ℝ) < Fintype.card V := by linarith
  rw [show ∀ A B C : ℝ, A / Fintype.card V - ((1 - θ) * (B / Fintype.card V) +
      θ * (C / Fintype.card V)) = (A - ((1 - θ) * B + θ * C)) / Fintype.card V by
    intro A B C; field_simp, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
  have key := (abs_sub_le _ (∑ i, max (inner ℝ z.1 (v i (T i))) 0) _).trans
    (add_le_add (hrep z) ((hT z).symm ▸ hz z))
  refine key.trans ?_
  have : t⁻¹ * t ^ 3 = t ^ 2 := by field_simp
  calc (#Bd : ℝ) * (2 * M) + 8 * M * √(∑ a, (#(univ.filter fun i => blk i = a) : ℝ) ^ 2)
      ≤ t ^ 2 * (2 * M) + 8 * M * (2 * t ^ 2) := by gcongr
    _ = 18 * M * t⁻¹ * Fintype.card V := by rw [← ht3, mul_assoc _ t⁻¹, this]; ring

/-- **Lemma 47** (Merging two permutations), as stated in the paper (p. 41, l. 1285–1287): for
all permutation matrices `P₀ = P_{π₀}`, `P₁ = P_{π₁}` and `θ ∈ [0, 1]` there is a permutation
matrix `P` with `ρ(P, (1 - θ) P₀ + θ P₁) ≤ 20 M n^{-1/3}`. -/
theorem lemma47 (hCP : ContractionPrinciple) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : V → W → E) {M : ℝ} (hM : ∀ i j, ‖v i j‖ ≤ M)
    (hcard : Fintype.card V = Fintype.card W) (π₀ π₁ : V ≃ W) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    ∃ π : V ≃ W, rhoSupp v (permMat π) (fun i j => (1 - θ) * permMat π₀ i j + θ * permMat π₁ i j)
      ≤ 20 * M * (Fintype.card V : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨π, h⟩ := lemma47_sharp hCP v hM hcard π₀ π₁ hθ0 hθ1
  refine ⟨π, h.trans ?_⟩
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.zero_rpow (by norm_num)]; simp
  obtain ⟨i₀⟩ : Nonempty V := Fintype.card_pos_iff.mp hpos
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM i₀ (π₀ i₀))
  have hx : 0 ≤ (Fintype.card V : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith [mul_nonneg hM0 hx]

end GsimOT
