/-
# Finite product spaces of independent Bernoulli coins

Probability model for the random sampling step of Algorithm 1 of [HOG26] (Section 3).  An outcome
is a map `ω : ι → Bool` (coin `i` comes up `true` or `false`), coins are independent and coin `i`
is `true` with probability `p i`.  Everything is a finite sum of real numbers:

* `bernW p ω = ∏ i, (if ω i then p i else 1 - p i)` : the probability of the outcome `ω`;
* `prob p E = ∑_{ω ∈ E} bernW p ω`                  : the probability of the event `E`.

Main facts: total mass `1`, union bound, the probability that all coins of a set `T` are `false`
(`∏_{i ∈ T} (1 - p i)`), invariance under taking marginals along an injection
(`prob_comp_injective`), and the probabilistic method (`exists_not_of_prob_lt_one`).
-/
import Mathlib

open Finset

namespace ThinMatching

section Prob

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The probability of the outcome `ω` when coin `i` is `true` with probability `p i`,
independently. -/
def bernW (p : ι → ℝ) (ω : ι → Bool) : ℝ := ∏ i, if ω i then p i else 1 - p i

open Classical in
/-- The probability of an event `E` in the product of independent Bernoulli coins. -/
noncomputable def prob (p : ι → ℝ) (E : (ι → Bool) → Prop) : ℝ :=
  ∑ ω, if E ω then bernW p ω else 0

/-- `p` is a vector of probabilities. -/
def IsProbVec (p : ι → ℝ) : Prop := ∀ i, 0 ≤ p i ∧ p i ≤ 1

omit [DecidableEq ι] in
theorem bernW_nonneg {p : ι → ℝ} (hp : IsProbVec p) (ω : ι → Bool) : 0 ≤ bernW p ω := by
  unfold bernW
  refine Finset.prod_nonneg fun i _ => ?_
  have := hp i
  split_ifs <;> linarith

/-- A "rectangle" event `{ω | ∀ i, ω i ∈ A i}` has probability `∏ i, ∑_{b ∈ A i} P[coin i = b]`. -/
theorem sum_bernW_rect (p : ι → ℝ) (A : ι → Finset Bool) :
    (∑ ω : ι → Bool, if ∀ i, ω i ∈ A i then bernW p ω else 0) =
      ∏ i, ∑ b ∈ A i, if b then p i else 1 - p i := by
  have h1 : ∀ i, (∑ b ∈ A i, if b then p i else 1 - p i) =
      ∑ b, if b ∈ A i then (if b then p i else 1 - p i) else 0 := fun i => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp_rw [h1]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.prod_ite_zero]
  simp [bernW]

/-- The total mass is `1`. -/
theorem sum_bernW (p : ι → ℝ) : ∑ ω, bernW p ω = 1 := by
  have := sum_bernW_rect p (fun _ => Finset.univ)
  simp only [Finset.mem_univ, implies_true, ite_true] at this
  rw [this]
  refine Finset.prod_eq_one fun i _ => ?_
  simp

theorem prob_def (p : ι → ℝ) (E : (ι → Bool) → Prop) [DecidablePred E] :
    prob p E = ∑ ω, if E ω then bernW p ω else 0 := by
  unfold prob; congr 1; ext ω; congr

theorem prob_nonneg {p : ι → ℝ} (hp : IsProbVec p) (E : (ι → Bool) → Prop) : 0 ≤ prob p E := by
  classical
  rw [prob_def]
  refine Finset.sum_nonneg fun ω _ => ?_
  split_ifs
  · exact bernW_nonneg hp ω
  · exact le_refl _

theorem prob_mono {p : ι → ℝ} (hp : IsProbVec p) {E E' : (ι → Bool) → Prop}
    (h : ∀ ω, E ω → E' ω) : prob p E ≤ prob p E' := by
  classical
  rw [prob_def, prob_def]
  refine Finset.sum_le_sum fun ω _ => ?_
  have := bernW_nonneg hp ω
  by_cases h1 : E ω
  · simp [h1, h ω h1]
  · simp only [h1, ite_false]; split_ifs <;> linarith

/-- Union bound for two events. -/
theorem prob_or_le {p : ι → ℝ} (hp : IsProbVec p) (E E' : (ι → Bool) → Prop) :
    prob p (fun ω => E ω ∨ E' ω) ≤ prob p E + prob p E' := by
  classical
  rw [prob_def, prob_def, prob_def, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have := bernW_nonneg hp ω
  by_cases h1 : E ω <;> by_cases h2 : E' ω <;> simp [h1, h2, this]

/-- Union bound over a finite family of events. -/
theorem prob_exists_le {κ : Type*} {p : ι → ℝ} (hp : IsProbVec p) (s : Finset κ)
    (E : κ → (ι → Bool) → Prop) :
    prob p (fun ω => ∃ k ∈ s, E k ω) ≤ ∑ k ∈ s, prob p (E k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prob_def]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc prob p (fun ω => ∃ k ∈ insert a s, E k ω)
        ≤ prob p (fun ω => E a ω ∨ ∃ k ∈ s, E k ω) :=
          prob_mono hp fun ω h => by simpa [Finset.mem_insert, or_and_right, exists_or] using h
      _ ≤ _ := (prob_or_le hp _ _).trans (by linarith)

/-- The probability that all coins in `T` come up `false` is `∏_{i ∈ T} (1 - p i)`. -/
theorem prob_allFalse (p : ι → ℝ) (T : Finset ι) :
    prob p (fun ω => ∀ i ∈ T, ω i = false) = ∏ i ∈ T, (1 - p i) := by
  classical
  rw [prob_def]
  have := sum_bernW_rect p (fun i => if i ∈ T then {false} else Finset.univ)
  have e1 : ∀ ω : ι → Bool, (∀ i ∈ T, ω i = false) ↔
      ∀ i, ω i ∈ (if i ∈ T then ({false} : Finset Bool) else Finset.univ) := fun ω => by
    refine ⟨fun h i => ?_, fun h i hi => ?_⟩
    · by_cases hi : i ∈ T <;> simp [hi, h]
    · simpa [hi] using h i
  simp_rw [e1, this]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ T)]
  have h2 : ∏ i ∈ Finset.univ.filter (· ∉ T),
      (∑ b ∈ (if i ∈ T then ({false} : Finset Bool) else Finset.univ),
        if b then p i else 1 - p i) = 1 :=
    Finset.prod_eq_one fun i hi => by
      simp only [Finset.mem_filter] at hi; simp [hi.2]
  rw [h2, mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.prod_congr rfl fun i hi => ?_
  simp [hi]

/-- Marginals: an event depending only on the coins `f j` (`f` injective) has the same probability
as the corresponding event in the product space indexed by `ι'` with probabilities `p ∘ f`. -/
theorem prob_comp_injective {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (p : ι → ℝ) {f : ι' → ι}
    (hf : Function.Injective f) (E : (ι' → Bool) → Prop) :
    prob p (fun ω => E (ω ∘ f)) = prob (p ∘ f) E := by
  classical
  rw [prob_def, prob_def]
  -- split according to the restriction `a = ω ∘ f`
  have hsplit : ∀ ω : ι → Bool, (if E (ω ∘ f) then bernW p ω else 0) =
      ∑ a : ι' → Bool, if E a then (if ω ∘ f = a then bernW p ω else 0) else 0 := fun ω => by
    rw [Finset.sum_eq_single (ω ∘ f)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hE : E a
  swap
  · simp [hE]
  simp only [hE, ite_true]
  -- the rectangle `{ω | ω ∘ f = a}`
  let A : ι → Finset Bool := fun i =>
    if h : ∃ j, f j = i then {a h.choose} else Finset.univ
  have hg : ∀ j, (⟨j, rfl⟩ : ∃ j', f j' = f j).choose = j := fun j =>
    hf (⟨j, rfl⟩ : ∃ j', f j' = f j).choose_spec
  have hmem : ∀ i, i ∈ Finset.univ.map ⟨f, hf⟩ ↔ ∃ j, f j = i := fun i => by simp
  have e1 : ∀ ω : ι → Bool, (ω ∘ f = a) ↔ ∀ i, ω i ∈ A i := fun ω => by
    constructor
    · rintro rfl i
      by_cases hi : i ∈ Finset.univ.map ⟨f, hf⟩
      · obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
        simp [A, hg]
      · rw [hmem] at hi
        simp [A, hi]
    · intro h
      funext j
      have := h (f j)
      simpa [A, hg] using this
  simp_rw [e1, sum_bernW_rect]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ Finset.univ.map ⟨f, hf⟩)]
  have h2 : ∏ i ∈ Finset.univ.filter (· ∉ Finset.univ.map ⟨f, hf⟩),
      (∑ b ∈ A i, if b then p i else 1 - p i) = 1 :=
    Finset.prod_eq_one fun i hi => by
      simp only [Finset.mem_filter, hmem] at hi
      simp [A, hi.2]
  rw [h2, mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_map]
  unfold bernW
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [A, hg]

/-- The probabilistic method: if `P[E] < 1` there is an outcome of positive probability outside
`E`. -/
theorem exists_not_of_prob_lt_one {p : ι → ℝ} (hp : IsProbVec p) {E : (ι → Bool) → Prop}
    (h : prob p E < 1) : ∃ ω, ¬ E ω ∧ 0 < bernW p ω := by
  classical
  by_contra hne
  push Not at hne
  have : prob p E = 1 := by
    rw [prob_def, ← sum_bernW p]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hE : E ω
    · simp [hE]
    · simp only [hE, ite_false]
      exact le_antisymm (hne ω hE) (bernW_nonneg hp ω) |>.symm
  linarith

omit [DecidableEq ι] in
/-- An outcome of positive probability only has `true` coins of positive probability. -/
theorem pos_of_bernW_pos {p : ι → ℝ} (hp : IsProbVec p) {ω : ι → Bool} (h : 0 < bernW p ω)
    {i : ι} (hi : ω i = true) : 0 < p i := by
  rcases (hp i).1.lt_or_eq with h' | h'
  · exact h'
  · exfalso
    have : bernW p ω = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, ← h'])
    linarith

end Prob

end ThinMatching
