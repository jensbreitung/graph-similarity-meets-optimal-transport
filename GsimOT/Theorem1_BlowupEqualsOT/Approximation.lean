/-
# Approximating a coupling by couplings with denominator `N = ℓmn`

Paper, Appendix B, Eq. (13) and Claim 20 (pp. 17–18, l. 570–581): "let `ε > 0` and
`Q* ∈ DS*(V, W)` be a rational matrix such that
`‖B_{p→q}(G,H,Q*)‖ ≤ min_{Q*_0} ‖B_{p→q}(G,H,Q*_0)‖ + ε`."
The proof of Claim 20 takes a minimiser `Q*_0`, a sequence of rational couplings with the same
support converging to it ("the couplings in `DS*(V, W)` whose entries outside `S` are zero form a
rational polytope"), and continuity of `Q ↦ ‖B(Q)‖` on a fixed support.

This file provides the approximation step in a stronger form: every coupling `Q` can be
approximated, *for every sufficiently large `ℓ`*, by couplings `Q'` with `ℓmn · Q'` integral and
the same support as `Q` (`exists_integral_approx_close`), such that `‖B(Q')‖ ≤ ‖B(Q)‖ + ε`
(`exists_integral_approx`).  Instead of the rational polytope, the approximants are constructed
explicitly; Claim 20 itself is `claim20` in Claim20.lean.  Keeping the support is essential because
of the convention `0⁰ = 0` (for `p = 1` or `q = ∞` the map `Q ↦ B(Q)` is discontinuous at the
boundary of the support).

Proof.
1. (`liftM`, `liftM_mem_doublyStochastic`) Fix a bijection `f : W × [m] ≃ V × [n]`.  The lift
   `R((v,i), f(w,j)) = Q(v,w)` is a doubly stochastic `mn × mn` matrix; by Birkhoff–von Neumann
   (`exists_eq_sum_perm_of_mem_doublyStochastic`) `R = ∑_σ λ_σ P_σ`.
2. (`exists_round_weights`) For `ℓ` large, round `λ` to weights `λ'` with `ℓλ'_σ ∈ ℕ`,
   `λ'_σ > 0 ↔ λ_σ > 0` and `∑ |λ' - λ| ≤ δ/2` (floors `⌊ℓλ_σ⌋/ℓ`, remainder added to one
   `σ₀` with `λ_σ₀ > 0`).
3. (`avgM`) Put `Q' = avg(∑ λ'_σ P_σ)`, where `avg M (v,w) = (1/mn) ∑_{i,j} M((v,i), f(w,j))`.
   Then `Q'` is a coupling (`isCoupling_avgM`), `ℓmn Q'(v,w) = ∑_{i,j,σ} (ℓλ'_σ) P_σ(..) ∈ ℕ`,
   `Q = avg R = ∑ λ_σ avg(P_σ)` (`avgM_liftM`, `avgM_sum`), so `Q'` and `Q` have the same
   support and `|Q' - Q| ≤ ∑ |λ' - λ| < δ` entrywise (`avgM_mem_Icc`).
4. (`exists_delta_opNorm_Bmat`) On matrices with the same zero set as `Q`, every entry of
   `B(·)` is continuous at `Q` (`tendsto_powZ_apply`), and
   `‖B(Q')‖ ≤ ‖B(Q)‖ + ‖B(Q') - B(Q)‖ ≤ ‖B(Q)‖ + ∑ |B(Q') - B(Q)|`.
-/
import GsimOT.Theorem1_BlowupEqualsOT.Definitions

open Finset Filter Topology

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- `Q' ↦ powZ (Q' v w) a` is continuous at `Q` within the matrices with the same zero set. -/
lemma tendsto_powZ_apply (Q : V → W → ℝ) (v : V) (w : W) (a : ℝ) :
    Tendsto (fun Q' : V → W → ℝ => powZ (Q' v w) a)
      (𝓝[{Q' | ∀ v w, Q' v w = 0 ↔ Q v w = 0}] Q) (𝓝 (powZ (Q v w) a)) := by
  by_cases h : Q v w = 0
  · have : ∀ᶠ Q' in 𝓝[{Q' : V → W → ℝ | ∀ v w, Q' v w = 0 ↔ Q v w = 0}] Q,
        powZ (Q v w) a = powZ (Q' v w) a := by
      filter_upwards [self_mem_nhdsWithin] with Q' hQ'
      rw [(hQ' v w).2 h, h]
    exact tendsto_const_nhds.congr' this
  · have hc : ContinuousAt (fun Q' : V → W → ℝ => Q' v w ^ a) Q :=
      ((continuous_apply w).comp (continuous_apply v)).continuousAt.rpow_const (Or.inl h)
    have hev : ∀ᶠ Q' in 𝓝 Q, Q' v w ^ a = powZ (Q' v w) a := by
      have : ∀ᶠ Q' in 𝓝 Q, Q' v w ≠ 0 :=
        ((continuous_apply w).comp (continuous_apply v)).continuousAt.eventually_ne h
      filter_upwards [this] with Q' hQ'
      simp [powZ, hQ']
    have : Tendsto (fun Q' : V → W → ℝ => powZ (Q' v w) a) (𝓝 Q) (𝓝 (powZ (Q v w) a)) := by
      rw [show powZ (Q v w) a = Q v w ^ a by simp [powZ, h]]
      exact hc.tendsto.congr' hev
    exact this.mono_left nhdsWithin_le_nhds

omit [DecidableEq V] [DecidableEq W] in
/-- Continuity of `Q ↦ ‖B(Q)‖` from above, among matrices with the same zero set as `Q`. -/
lemma exists_delta_opNorm_Bmat {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) (Q : V → W → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ Q' : V → W → ℝ, (∀ v w, Q' v w = 0 ↔ Q v w = 0) →
      (∀ v w, |Q' v w - Q v w| < δ) →
      opNorm p q (Bmat p q G H Q') ≤ opNorm p q (Bmat p q G H Q) + ε := by
  have hT : Tendsto (fun Q' : V → W → ℝ => ∑ a, ∑ b,
      |Bmat p q G H Q' a b - Bmat p q G H Q a b|)
      (𝓝[{Q' | ∀ v w, Q' v w = 0 ↔ Q v w = 0}] Q) (𝓝 0) := by
    have := tendsto_finsetSum (univ : Finset (V × W)) fun a _ =>
      tendsto_finsetSum (univ : Finset (V × W)) fun b _ =>
      ((Tendsto.mul (Tendsto.mul (tendsto_powZ_apply Q a.1 a.2 q⁻¹.toReal)
        (tendsto_const_nhds (x := disc G H a.1 a.2 b.1 b.2)))
        (tendsto_powZ_apply Q b.1 b.2 (1 - p⁻¹.toReal))).sub_const (Bmat p q G H Q a b)).abs
    simpa [Bmat] using this
  have hev := (hT.eventually (gt_mem_nhds hε))
  rw [Filter.Eventually, mem_nhdsWithin] at hev
  obtain ⟨U, hU, hQU, hUsub⟩ := hev
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU Q hQU
  refine ⟨δ, hδ, fun Q' hsupp hclose => ?_⟩
  have hmem : Q' ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hδ]
    intro v
    rw [dist_pi_lt_iff hδ]
    intro w
    rw [Real.dist_eq]
    exact hclose v w
  have hlt := hUsub ⟨hmem, hsupp⟩
  simp only [Set.mem_ofPred_eq] at hlt
  have h1 := opNorm_add_le hp hq (Bmat p q G H Q) (Bmat p q G H Q' - Bmat p q G H Q)
  have h2 := opNorm_le_sum_abs hp hq (Bmat p q G H Q' - Bmat p q G H Q)
  simp only [add_sub_cancel, Matrix.sub_apply] at h1 h2
  linarith

/-- **Rounding convex weights to multiples of `1/ℓ`.**  For every sufficiently large `ℓ`, the
weights `w` can be replaced by weights `w'` with `ℓ w'` integral, the same positivity pattern,
and total deviation `∑ |w' - w| ≤ δ`. -/
lemma exists_round_weights {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L₀ : ℕ, ∀ ℓ ≥ L₀, ∃ w' : ι → ℝ, (∀ i, 0 ≤ w' i) ∧ ∑ i, w' i = 1 ∧
      (∀ i, 0 < w' i ↔ 0 < w i) ∧ (∀ i, ∃ c : ℕ, (ℓ : ℝ) * w' i = c) ∧
      ∑ i, |w' i - w i| ≤ δ := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, 0 < w i₀ := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have : ∑ i, w i ≤ 0 := sum_nonpos fun i _ => h i
    linarith
  refine ⟨max (univ.sup fun i => ⌈1 / w i⌉₊) (⌈2 * Fintype.card ι / δ⌉₊ + 1), fun ℓ hℓ => ?_⟩
  have hℓ1 : ∀ i, 0 < w i → 1 ≤ (ℓ : ℝ) * w i := by
    intro i hi
    have h1 : ⌈1 / w i⌉₊ ≤ ℓ :=
      le_trans (le_sup (f := fun i => ⌈1 / w i⌉₊) (mem_univ i)) (le_of_max_le_left hℓ)
    have h2 : 1 / w i ≤ ℓ := (Nat.le_ceil _).trans (by exact_mod_cast h1)
    rw [div_le_iff₀ hi] at h2
    exact h2
  have hℓ2 : (⌈2 * Fintype.card ι / δ⌉₊ + 1 : ℕ) ≤ ℓ := le_of_max_le_right hℓ
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (Nat.succ_pos _).trans_le hℓ2
  have hℓδ : 2 * Fintype.card ι / δ ≤ ℓ := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (Nat.le_succ _).trans hℓ2
  -- `g i = ⌊ℓ w i⌋ / ℓ`
  let g : ι → ℝ := fun i => (⌊(ℓ : ℝ) * w i⌋₊ : ℝ) / ℓ
  have hg0 : ∀ i, 0 ≤ g i := fun i => by positivity
  have hgle : ∀ i, g i ≤ w i := fun i => by
    rw [div_le_iff₀ hℓpos]
    calc (⌊(ℓ : ℝ) * w i⌋₊ : ℝ) ≤ ℓ * w i := Nat.floor_le (mul_nonneg hℓpos.le (hw0 i))
      _ = w i * ℓ := mul_comm _ _
  have hgerr : ∀ i, |g i - w i| ≤ 1 / ℓ := fun i => by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hgle i])]
    have := Nat.lt_floor_add_one ((ℓ : ℝ) * w i)
    have e : w i - g i = ((ℓ : ℝ) * w i - ⌊(ℓ : ℝ) * w i⌋₊) / ℓ := by
      rw [sub_div, mul_div_cancel_left₀ _ hℓpos.ne']
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hℓpos.le
  have hgsum : ∑ i, g i ≤ 1 := hw1 ▸ sum_le_sum fun i _ => hgle i
  have hgpos : ∀ i, 0 < g i ↔ 0 < w i := fun i => by
    constructor
    · intro h; exact h.trans_le (hgle i)
    · intro h
      have : (1 : ℝ) ≤ ⌊(ℓ : ℝ) * w i⌋₊ := by
        exact_mod_cast Nat.one_le_floor_iff _ |>.2 (hℓ1 i h)
      exact div_pos (by linarith) hℓpos
  refine ⟨fun i => g i + Pi.single (M := fun _ => ℝ) i₀ (1 - ∑ j, g j) i, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have : 0 ≤ Pi.single (M := fun _ => ℝ) i₀ (1 - ∑ j, g j) i := by
      by_cases h : i = i₀
      · subst h; simp; linarith
      · simp [h]
    linarith [hg0 i]
  · rw [sum_add_distrib]; simp
  · intro i
    by_cases h : i = i₀
    · subst h
      simp only [Pi.single_eq_same]
      constructor
      · intro _; exact hi₀
      · intro _; linarith [(hgpos i).2 hi₀]
    · simp [h, hgpos]
  · intro i
    have hfl : ∀ j, (ℓ : ℝ) * g j = ⌊(ℓ : ℝ) * w j⌋₊ := fun j =>
      mul_div_cancel₀ _ hℓpos.ne'
    by_cases h : i = i₀
    · subst h
      have hsum : ∑ j, ⌊(ℓ : ℝ) * w j⌋₊ ≤ ℓ := by
        have : ((∑ j, ⌊(ℓ : ℝ) * w j⌋₊ : ℕ) : ℝ) ≤ ℓ := by
          push_cast
          simp_rw [← hfl, ← mul_sum]
          nlinarith
        exact_mod_cast this
      refine ⟨⌊(ℓ : ℝ) * w i⌋₊ + (ℓ - ∑ j, ⌊(ℓ : ℝ) * w j⌋₊), ?_⟩
      simp only [Pi.single_eq_same]
      push_cast [Nat.cast_sub hsum]
      rw [mul_add, hfl, mul_sub, mul_sum]
      simp_rw [hfl]
      ring
    · exact ⟨⌊(ℓ : ℝ) * w i⌋₊, by simp [h, hfl]⟩
  · have hsplit : ∀ i, |g i + Pi.single (M := fun _ => ℝ) i₀ (1 - ∑ j, g j) i - w i| ≤
        |g i - w i| + |Pi.single (M := fun _ => ℝ) i₀ (1 - ∑ j, g j) i| := fun i => by
      rw [add_sub_right_comm]; exact abs_add_le _ _
    have hs2 : ∑ i, |Pi.single (M := fun _ => ℝ) i₀ (1 - ∑ j, g j) i| ≤ ∑ i, |g i - w i| := by
      have : ∑ i, |Pi.single (M := fun _ => ℝ) i₀ (1 - ∑ j, g j) i| = |1 - ∑ j, g j| := by
        rw [Fintype.sum_eq_single i₀ (fun i h => by simp [h])]; simp
      rw [this, ← hw1, ← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact sum_congr rfl fun i _ => abs_sub_comm _ _
    have hs1 : ∑ i, |g i - w i| ≤ Fintype.card ι * (1 / ℓ) := by
      have := sum_le_sum fun i (_ : i ∈ univ) => hgerr i
      simpa using this
    calc _ ≤ ∑ i, (|g i - w i| + |Pi.single (M := fun _ => ℝ) i₀ (1 - ∑ j, g j) i|) :=
          sum_le_sum fun i _ => hsplit i
      _ ≤ 2 * (Fintype.card ι * (1 / ℓ)) := by rw [sum_add_distrib]; linarith
      _ ≤ δ := by
          rw [div_le_iff₀ hδ] at hℓδ
          rw [← mul_assoc, mul_one_div, div_le_iff₀ hℓpos]
          linarith

/-! ### Lifting a coupling to a doubly stochastic matrix and averaging back -/

section Avg

variable (f : W × Fin (Fintype.card V) ≃ V × Fin (Fintype.card W))

/-- Averaging an `mn × mn` matrix (rows `V × [n]`, columns `W × [m]` via `f`) back to a
`V × W` matrix: `avgM M (v, w) = (1/(mn)) ∑_{i,j} M((v,i), f(w,j))`. -/
noncomputable def avgM (M : Matrix (V × Fin (Fintype.card W)) (V × Fin (Fintype.card W)) ℝ) :
    V → W → ℝ := fun v w =>
  (1 / ((Fintype.card V : ℝ) * Fintype.card W)) * ∑ i, ∑ j, M (v, i) (f (w, j))

/-- The lift `R((v,i), f(w,j)) = Q(v,w)` of `Q` to an `mn × mn` matrix. -/
def liftM (Q : V → W → ℝ) : Matrix (V × Fin (Fintype.card W)) (V × Fin (Fintype.card W)) ℝ :=
  fun x y => Q x.1 (f.symm y).1

omit [DecidableEq W] in
/-- The average of a doubly stochastic matrix is a coupling. -/
lemma isCoupling_avgM [Nonempty V] [Nonempty W]
    {M : Matrix (V × Fin (Fintype.card W)) (V × Fin (Fintype.card W)) ℝ}
    (hM : M ∈ doublyStochastic ℝ (V × Fin (Fintype.card W))) : IsCoupling (avgM f M) := by
  have hm : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  refine ⟨fun v w => ?_, fun v => ?_, fun w => ?_⟩
  · exact mul_nonneg (by positivity) (sum_nonneg fun i _ => sum_nonneg fun j _ => hM.1 _ _)
  · simp only [avgM]
    rw [← mul_sum, sum_comm]
    have : ∀ i, ∑ w, ∑ j, M (v, i) (f (w, j)) = 1 := by
      intro i
      rw [← Fintype.sum_prod_type' (f := fun w j => M (v, i) (f (w, j))),
        Equiv.sum_comp f (M (v, i))]
      exact sum_row_of_mem_doublyStochastic hM _
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
  · simp only [avgM]
    rw [← mul_sum, ← Fintype.sum_prod_type' (f := fun v i => ∑ j, M (v, i) (f (w, j))),
      sum_comm]
    simp only [sum_col_of_mem_doublyStochastic hM, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    field_simp

omit [DecidableEq V] [DecidableEq W] in
/-- Averaging is linear. -/
lemma avgM_sum {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (P : ι → Matrix (V × Fin (Fintype.card W)) (V × Fin (Fintype.card W)) ℝ) (v : V) (w : W) :
    avgM f (∑ σ, c σ • P σ) v w = ∑ σ, c σ * avgM f (P σ) v w := by
  simp only [avgM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_sum]
  calc _ = ∑ i, ∑ σ, ∑ j,
        1 / ((Fintype.card V : ℝ) * Fintype.card W) * (c σ * P σ (v, i) (f (w, j))) :=
        sum_congr rfl fun i _ => sum_comm
    _ = _ := sum_comm.trans (sum_congr rfl fun σ _ => sum_congr rfl fun i _ =>
        sum_congr rfl fun j _ => by ring)

omit [DecidableEq W] in
/-- The averages of a doubly stochastic matrix lie in `[0, 1]`. -/
lemma avgM_mem_Icc {M : Matrix (V × Fin (Fintype.card W)) (V × Fin (Fintype.card W)) ℝ}
    (hM : M ∈ doublyStochastic ℝ (V × Fin (Fintype.card W))) (v : V) (w : W) :
    0 ≤ avgM f M v w ∧ avgM f M v w ≤ 1 := by
  refine ⟨mul_nonneg (by positivity) (sum_nonneg fun i _ => sum_nonneg fun j _ => hM.1 _ _),
    ?_⟩
  have h : ∑ i : Fin (Fintype.card W), ∑ j : Fin (Fintype.card V), M (v, i) (f (w, j)) ≤
      ∑ i : Fin (Fintype.card W), ∑ j : Fin (Fintype.card V), (1 : ℝ) :=
    sum_le_sum fun i _ => sum_le_sum fun j _ => le_one_of_mem_doublyStochastic hM
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  simp only [avgM]
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card V)).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card W)).eq_or_lt with h1 | h1
  · rw [← h1]; simp
  rw [one_div_mul_eq_div, div_le_one (by positivity)]
  linarith [mul_comm (Fintype.card V : ℝ) (Fintype.card W)]

omit [DecidableEq W] in
/-- The lift of a coupling is doubly stochastic. -/
lemma liftM_mem_doublyStochastic [Nonempty V] [Nonempty W] {Q : V → W → ℝ}
    (hQ : IsCoupling Q) : liftM f Q ∈ doublyStochastic ℝ (V × Fin (Fintype.card W)) := by
  have hm : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun x y => hQ.nonneg _ _, fun x => ?_, fun y => ?_⟩
  · simp only [liftM]
    rw [Equiv.sum_comp f.symm (fun z => Q x.1 z.1), Fintype.sum_prod_type, sum_comm]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hQ.row_sum x.1]
    field_simp
  · simp only [liftM]
    rw [Fintype.sum_prod_type]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum, hQ.col_sum]
    field_simp

omit [DecidableEq V] [DecidableEq W] in
/-- Averaging the lift gives back `Q`. -/
lemma avgM_liftM (Q : V → W → ℝ) [Nonempty V] [Nonempty W] (v : V) (w : W) :
    avgM f (liftM f Q) v w = Q v w := by
  have hm : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  simp only [avgM, liftM, Equiv.symm_apply_apply, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

end Avg

/-- Entries of permutation matrices are natural numbers (`0` or `1`). -/
lemma permMatrix_apply_mem_rangeS {X : Type*} [Fintype X] [DecidableEq X] (σ : Equiv.Perm X)
    (x y : X) : σ.permMatrix ℝ x y ∈ (Nat.castRingHom ℝ).rangeS := by
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

omit [DecidableEq V] [DecidableEq W] in
/-- **Approximation by couplings with denominator `ℓmn` and the same support** (Steps 1–3 above;
in the proof of Claim 20, p. 17, l. 575–576: "there is a sequence of rational matrices
`Q*_k ∈ DS*(V, W)` with `supp(Q*_k) = S` and `Q*_k → Q*_0`"). For every `δ > 0` and every
sufficiently large `ℓ` there is a coupling `Q'` with `ℓmn · Q'` integral, the same zero set as `Q`
and `|Q' - Q| < δ`. -/
theorem exists_integral_approx_close [Nonempty V] [Nonempty W] {Q : V → W → ℝ}
    (hQ : IsCoupling Q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L₀ : ℕ, ∀ ℓ ≥ L₀, ∃ Q', IsCoupling Q' ∧
      (∀ v w, ∃ k : ℕ, ((Fintype.card V * (Fintype.card W * ℓ) : ℕ) : ℝ) * Q' v w = k) ∧
      (∀ v w, Q' v w = 0 ↔ Q v w = 0) ∧ (∀ v w, |Q' v w - Q v w| < δ) := by
  classical
  have hm : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  obtain ⟨f⟩ : Nonempty (W × Fin (Fintype.card V) ≃ V × Fin (Fintype.card W)) :=
    ⟨Fintype.equivOfCardEq (by simp [mul_comm])⟩
  obtain ⟨wt, hw0, hw1, hRsum⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic (liftM_mem_doublyStochastic f hQ)
  obtain ⟨L₀, hL⟩ := exists_round_weights wt hw0 hw1 (half_pos hδ)
  refine ⟨L₀, fun ℓ hℓ => ?_⟩
  obtain ⟨w', h0, h1, hpos, hint, herr⟩ := hL ℓ hℓ
  have hR' : ∑ σ, w' σ • σ.permMatrix ℝ ∈ doublyStochastic ℝ (V × Fin (Fintype.card W)) :=
    convex_doublyStochastic.sum_mem (fun σ _ => h0 σ) h1
      (fun σ _ => permMatrix_mem_doublyStochastic)
  have hQeq : ∀ v w, Q v w = ∑ σ, wt σ * avgM f (σ.permMatrix ℝ) v w := fun v w => by
    rw [← avgM_sum, hRsum, avgM_liftM]
  have hI := fun σ v w => avgM_mem_Icc f (permMatrix_mem_doublyStochastic (σ := σ)) v w
  refine ⟨avgM f (∑ σ, w' σ • σ.permMatrix ℝ), isCoupling_avgM f hR', fun v w => ?_, ?_⟩
  · -- integrality
    choose c hc using hint
    have hmem : ((Fintype.card V * (Fintype.card W * ℓ) : ℕ) : ℝ) *
        avgM f (∑ σ, w' σ • σ.permMatrix ℝ) v w ∈ (Nat.castRingHom ℝ).rangeS := by
      have : ((Fintype.card V * (Fintype.card W * ℓ) : ℕ) : ℝ) *
          avgM f (∑ σ, w' σ • σ.permMatrix ℝ) v w = ∑ i, ∑ j, ∑ σ,
            (c σ : ℝ) * σ.permMatrix ℝ (v, i) (f (w, j)) := by
        simp only [avgM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ← hc, mul_sum]
        push_cast
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun σ _ => ?_
        field_simp
      rw [this]
      exact sum_mem fun i _ => sum_mem fun j _ => sum_mem fun σ _ =>
        mul_mem ⟨c σ, rfl⟩ (permMatrix_apply_mem_rangeS σ _ _)
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, hk.symm⟩
  · refine ⟨fun v w => ?_, fun v w => ?_⟩
    · have hz : ∀ σ, w' σ = 0 ↔ wt σ = 0 := fun σ => by
        constructor
        · intro h; by_contra h'
          have := (hpos σ).2 (lt_of_le_of_ne (hw0 σ) (Ne.symm h')); linarith
        · intro h; by_contra h'
          have := (hpos σ).1 (lt_of_le_of_ne (h0 σ) (Ne.symm h')); linarith
      rw [avgM_sum, hQeq, sum_eq_zero_iff_of_nonneg (fun σ _ => mul_nonneg (h0 σ) (hI σ v w).1),
        sum_eq_zero_iff_of_nonneg (fun σ _ => mul_nonneg (hw0 σ) (hI σ v w).1)]
      simp only [mem_univ, true_implies, mul_eq_zero, hz]
    · rw [avgM_sum, hQeq, ← sum_sub_distrib]
      calc |∑ σ, (w' σ * avgM f (σ.permMatrix ℝ) v w - wt σ * avgM f (σ.permMatrix ℝ) v w)|
          ≤ ∑ σ, |w' σ * avgM f (σ.permMatrix ℝ) v w - wt σ * avgM f (σ.permMatrix ℝ) v w| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ σ, |w' σ - wt σ| := sum_le_sum fun σ _ => by
            rw [← sub_mul, abs_mul, abs_of_nonneg (hI σ v w).1]
            exact mul_le_of_le_one_right (abs_nonneg _) (hI σ v w).2
        _ < δ := by linarith

/-- **Approximation by couplings with denominator `ℓmn`** (the strengthened Claim 20 used by
`theorem1_tendsto`): for every `ε > 0` and every sufficiently large `ℓ` there is a coupling `Q'`
with `ℓmn · Q'` integral and `‖B(Q')‖ ≤ ‖B(Q)‖ + ε`. -/
theorem exists_integral_approx {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) [Nonempty V]
    [Nonempty W] {Q : V → W → ℝ} (hQ : IsCoupling Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ ℓ ≥ L₀, ∃ Q', IsCoupling Q' ∧
      (∀ v w, ∃ k : ℕ, ((Fintype.card V * (Fintype.card W * ℓ) : ℕ) : ℝ) * Q' v w = k) ∧
      opNorm p q (Bmat p q G H Q') ≤ opNorm p q (Bmat p q G H Q) + ε := by
  obtain ⟨δ, hδ, hcont⟩ := exists_delta_opNorm_Bmat (G := G) (H := H) hp hq Q hε
  obtain ⟨L₀, hL⟩ := exists_integral_approx_close hQ hδ
  refine ⟨L₀, fun ℓ hℓ => ?_⟩
  obtain ⟨Q', hQ', hint, hsupp, hclose⟩ := hL ℓ hℓ
  exact ⟨Q', hQ', hint, hcont Q' hsupp hclose⟩

end GsimOT
