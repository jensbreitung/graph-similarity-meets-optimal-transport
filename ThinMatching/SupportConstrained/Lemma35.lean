/-
# Lemma 3.5: the sample contains a perfect matching with high probability

[HOG26], Section 3, Lemma 3.5.  Let `x ∈ PM(G)` and let `x̃ ≤ x` with `x(E) - x̃(E) ≤ 1/4` (by
Lemma 3.2 this holds for the trimmed graph with `ε = 1/(4|V|)`, i.e. `ε = 1/(8n)` for `|V| = 2n`).
Sample `α` copies of every edge `e` with probability `x̃_e`.  Then

  `P[the sample Y has no perfect matching] ≤ (|V| + 1)^{|V|} · exp(-3α/4)`   (`lemma35`),

which is `≤ 1/4` for `α ≥ c |V| ln(2|V|)`, `c ≥ 4` (`witness_bound_le`).

*Proof (as in the paper).*  If `Y` has no perfect matching, Tutte's theorem gives a witness `L`
such that `Y ∩ F = ∅` (`exists_witness_of_no_pm`).  For a fixed witness,
`P[Y ∩ F = ∅] = ∏_{e ∈ F} (1 - x̃_e)^α ≤ exp(-α x̃(F))` and
`x̃(F) ≥ x(F) - (x(E) - x̃(E)) ≥ 1 - 1/4` (inequality (1); we have `x(F) ≥ 1`).  A union bound over
the at most `(|V| + 1)^{|V|}` witnesses (Lemma 3.4) concludes.
-/
import ThinMatching.SupportConstrained.TutteWitness

open Finset

namespace ThinMatching

section Lemma35

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weights of a point of `PM(G)` are at most `1`. -/
theorem IsFracPM.le_one {x : WGraph V} (hx : IsFracPM x) (u v : V) : x.w u v ≤ 1 := by
  obtain ⟨c, hc0, hc1, hc⟩ := hx
  rw [hc u v, ← hc1]
  refine Finset.sum_le_sum fun M _ => ?_
  have := hc0 M
  split_ifs <;> nlinarith

omit [Fintype V] [DecidableEq V] in
/-- `P[no copy of an edge of F is sampled] ≤ exp(-α y(F))`. -/
theorem prob_allFalse_le_exp (y : WGraph V) (hy : ∀ u v, y.w u v ≤ 1) (α : ℕ)
    (F : Finset (Sym2 V)) :
    ∏ i ∈ F ×ˢ (Finset.univ : Finset (Fin α)), (1 - sampleProb y α i) ≤
      Real.exp (-(α * ∑ e ∈ F, edgeW y e)) := by
  rw [Finset.prod_product]
  simp only [sampleProb, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ∏ e ∈ F, (1 - edgeW y e) ^ α ≤ ∏ e ∈ F, Real.exp (-edgeW y e) ^ α := by
        refine Finset.prod_le_prod₀ (fun e _ => ?_) fun e _ => ?_
        · have := (isProbVec_sampleProb y hy 1 (e, 0)).2
          simp only [sampleProb] at this
          exact pow_nonneg (by linarith) _
        · have := (isProbVec_sampleProb y hy 1 (e, 0)).2
          simp only [sampleProb] at this
          refine pow_le_pow_left₀ (by linarith) ?_ _
          linarith [Real.add_one_le_exp (-edgeW y e)]
    _ = Real.exp (-(α * ∑ e ∈ F, edgeW y e)) := by
        simp_rw [← Real.exp_nat_mul, ← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun e _ => by ring

/-- **Lemma 3.5.**  For `x ∈ PM(G)` and `x̃ ≤ x` with `x(E) - x̃(E) ≤ 1/4`, the sample with
probabilities `x̃` fails to contain a perfect matching with probability at most
`(|V| + 1)^{|V|} exp(-3α/4)`. -/
theorem lemma35 {x : WGraph V} (hx : IsFracPM x) (xt : WGraph V)
    (hle : ∀ u v, xt.w u v ≤ x.w u v) (hrem : edgeTotal x - edgeTotal xt ≤ 1 / 4) (α : ℕ) :
    prob (sampleProb xt α)
        (fun ω => ¬ ∃ M : PerfectMatching V, ∀ v, (sampleGraph ω).Adj v (M.1 v)) ≤
      (Fintype.card V + 1) ^ Fintype.card V * Real.exp (-(3 / 4 * α)) := by
  classical
  have hxt1 : ∀ u v, xt.w u v ≤ 1 := fun u v => (hle u v).trans (hx.le_one u v)
  have hp := isProbVec_sampleProb xt hxt1 α
  let Wit := Finset.univ.filter fun L : V → Option V => IsTutteWitness L
  -- reduction to the union of the events `Y ∩ F_L = ∅`
  have h1 : prob (sampleProb xt α)
        (fun ω => ¬ ∃ M : PerfectMatching V, ∀ v, (sampleGraph ω).Adj v (M.1 v)) ≤
      prob (sampleProb xt α) (fun ω => ∃ L ∈ Wit,
        ∀ i ∈ witnessF L ×ˢ (Finset.univ : Finset (Fin α)), ω i = false) := by
    refine prob_mono hp fun ω hω => ?_
    obtain ⟨L, hL, hF⟩ := exists_witness_of_no_pm _ hω
    refine ⟨L, by simp [Wit, hL], fun i hi => ?_⟩
    obtain ⟨e, k⟩ := i
    rw [Finset.mem_product] at hi
    obtain ⟨a, b, rfl, hab⟩ := exists_of_mem_witnessF hi.1
    have hne : a ≠ b := by
      rintro rfl
      obtain ⟨r, s, h1, h2, h3, -⟩ := hab
      rw [h1] at h2; exact h3 (Option.some_injective _ h2)
    have h0 : copies ω s(a, b) = 0 := by
      by_contra h0
      exact hF a b hab ⟨hne, Nat.pos_of_ne_zero h0⟩
    unfold copies at h0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
    simpa using h0 (Finset.mem_univ k)
  -- each event has probability `≤ exp(-3α/4)`
  have h2 : ∀ L ∈ Wit, prob (sampleProb xt α)
      (fun ω => ∀ i ∈ witnessF L ×ˢ (Finset.univ : Finset (Fin α)), ω i = false) ≤
        Real.exp (-(3 / 4 * α)) := by
    intro L hL
    have hL' : IsTutteWitness L := by simpa [Wit] using hL
    rw [prob_allFalse]
    refine (prob_allFalse_le_exp xt hxt1 α _).trans (Real.exp_le_exp.2 ?_)
    have hx1 := one_le_witnessF_weight hx hL'
    have hsub : ∑ e ∈ witnessF L, (edgeW x e - edgeW xt e) ≤ edgeTotal x - edgeTotal xt := by
      unfold edgeTotal
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun e _ _ => ?_
      induction e using Sym2.ind with
      | _ u v => simp [hle u v]
    rw [Finset.sum_sub_distrib] at hsub
    have hα : (0 : ℝ) ≤ α := Nat.cast_nonneg α
    nlinarith
  calc _ ≤ _ := h1
    _ ≤ ∑ L ∈ Wit, prob (sampleProb xt α)
          (fun ω => ∀ i ∈ witnessF L ×ˢ (Finset.univ : Finset (Fin α)), ω i = false) :=
        prob_exists_le hp Wit _
    _ ≤ ∑ _L ∈ Wit, Real.exp (-(3 / 4 * α)) := Finset.sum_le_sum h2
    _ = #Wit * Real.exp (-(3 / 4 * α)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact_mod_cast card_witnesses_le

/-- The numerical estimate closing Lemma 3.5: for `n ≥ 1` and `α ≥ c n ln(2n)` with `c ≥ 4`,
`(n + 1)^n exp(-3α/4) ≤ 1/4`. -/
theorem witness_bound_le {n : ℕ} (hn : 1 ≤ n) {c α : ℝ} (hc : 4 ≤ c)
    (hα : c * n * Real.log (2 * n) ≤ α) :
    ((n : ℝ) + 1) ^ n * Real.exp (-(3 / 4 * α)) ≤ 1 / 4 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log (2 * n) := Real.log_le_log (by norm_num) (by linarith)
  have hL : Real.log 2 ≤ n * Real.log (2 * n) := by nlinarith
  have h1 : ((n : ℝ) + 1) ^ n ≤ Real.exp (n * Real.log (2 * n)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    exact pow_le_pow_left₀ (by linarith) (by linarith) n
  have h2 : (n : ℝ) * Real.log (2 * n) - 3 / 4 * α ≤ -(2 * Real.log 2) := by
    have : 4 * (n * Real.log (2 * n)) ≤ α := by nlinarith
    linarith
  calc ((n : ℝ) + 1) ^ n * Real.exp (-(3 / 4 * α))
      ≤ Real.exp (n * Real.log (2 * n)) * Real.exp (-(3 / 4 * α)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (n * Real.log (2 * n) - 3 / 4 * α) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(2 * Real.log 2)) := Real.exp_le_exp.2 h2
    _ = 1 / 4 := by
        rw [show -(2 * Real.log 2) = Real.log (1 / 4) by
          rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
          ring]
        exact Real.exp_log (by norm_num)

end Lemma35

end ThinMatching
