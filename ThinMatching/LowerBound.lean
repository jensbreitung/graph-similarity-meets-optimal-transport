/-
# Lemma 1.2: linear thinness lower bound [HOG26, Section 1.1, Figure 1]

The graph of Figure 1 on `2n + 2` vertices `z_1, …, z_n, y_1, …, y_n, z, y`:
solid edges `(z_i, y_i)` of weight `1 - 1/n` and dotted edges `(z_i, y)`, `(z, y_i)` of
weight `1/n`.  Encoding: `V n = (Fin n × Bool) ⊕ Bool`, with `inl (i, false) = z_i`,
`inl (i, true) = y_i`, `inr false = z`, `inr true = y`.  The edges are exactly the pairs joining
a `false`-vertex to a `true`-vertex with compatible index.

`x` is the average of the `n` perfect matchings
`M_k = {(z_k, y), (z, y_k)} ∪ {(z_j, y_j) : j ≠ k}`.  Every perfect matching in `supp(x)` matches
`y` (whose only neighbours are the `z_i`) to some `z_i`, and the cut `S = {z_i, y_i}` has
`x(δ(S)) = 2/n` while `|M ∩ δ(S)| ≥ 1`.

The construction needs `n ≥ 1` (for `n = 0` the graph `{z, y}` has no edge and hence no
fractional perfect matching); for `n = 1` the solid edge has weight `0` and the argument still
goes through.
-/
import ThinMatching.Basic

open Finset

namespace ThinMatching

namespace LowerBound

/-- Vertices of the Figure 1 graph. -/
abbrev V (n : ℕ) : Type := (Fin n × Bool) ⊕ Bool

/-- Weights of the Figure 1 graph. -/
noncomputable def wt (n : ℕ) : V n → V n → ℝ
  | .inl (i, a), .inl (j, b) => if i = j ∧ a ≠ b then 1 - 1 / n else 0
  | .inl (_, a), .inr b => if a ≠ b then 1 / n else 0
  | .inr a, .inl (_, b) => if a ≠ b then 1 / n else 0
  | .inr _, .inr _ => 0

lemma one_div_le_one (n : ℕ) : (1 : ℝ) / n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast h

/-- The weighted graph of Figure 1. -/
noncomputable def fig1 (n : ℕ) : WGraph (V n) where
  w := wt n
  nonneg u v := by
    have h1 := one_div_le_one n
    have h2 : (0 : ℝ) ≤ 1 / n := by positivity
    rcases u with ⟨i, a⟩ | a <;> rcases v with ⟨j, b⟩ | b <;> simp only [wt] <;>
      (try split_ifs) <;> linarith
  symm u v := by
    rcases u with ⟨i, a⟩ | a <;> rcases v with ⟨j, b⟩ | b <;> simp only [wt]
    · simp only [eq_comm (a := i), ne_comm (a := a)]
    · simp only [ne_comm (a := a)]
    · simp only [ne_comm (a := a)]
  diag v := by rcases v with ⟨i, a⟩ | a <;> simp [wt]

lemma card_V (n : ℕ) : Fintype.card (V n) = 2 * n + 2 := by
  simp [Fintype.card_sum, Fintype.card_prod]; ring

/-- The involution of the perfect matching `M_k`. -/
def sig {n : ℕ} (k : Fin n) : V n → V n
  | .inl (i, a) => if i = k then .inr (!a) else .inl (i, !a)
  | .inr a => .inl (k, !a)

lemma sig_invol {n : ℕ} (k : Fin n) : Function.Involutive (sig k) := by
  intro v
  rcases v with ⟨i, a⟩ | a
  · by_cases h : i = k
    · subst h; simp [sig]
    · simp [sig, h]
  · simp [sig]

/-- The perfect matching `M_k = {(z_k, y), (z, y_k)} ∪ {(z_j, y_j) : j ≠ k}`. -/
def Mk {n : ℕ} (k : Fin n) : PerfectMatching (V n) :=
  ⟨(sig_invol k).toPerm, fun v => ⟨sig_invol k v, by
    rcases v with ⟨i, a⟩ | a
    · by_cases h : i = k <;> simp [sig, h]
    · simp [sig]⟩⟩

lemma Mk_apply {n : ℕ} (k : Fin n) (v : V n) : (Mk k).1 v = sig k v := rfl

/-- `x` of Figure 1 is a fractional perfect matching: the average of the `M_k`. -/
theorem fig1_isFracPM {n : ℕ} (hn : 1 ≤ n) : IsFracPM (fig1 n) := by
  classical
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨fun M => ∑ k : Fin n, if Mk k = M then 1 / (n : ℝ) else 0, ?_, ?_, ?_⟩
  · intro M; exact Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  · rw [Finset.sum_comm]; simp [Finset.sum_ite_eq, hn']
  · intro u v
    have key : ∀ f : PerfectMatching (V n) → ℝ,
        ∑ M, (∑ k : Fin n, if Mk k = M then 1 / (n : ℝ) else 0) * f M =
          ∑ k : Fin n, 1 / (n : ℝ) * f (Mk k) := by
      intro f
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]; simp [Finset.sum_ite_eq]
    rw [key]
    simp only [Mk_apply, fig1]
    rcases u with ⟨i, a⟩ | a <;> rcases v with ⟨j, b⟩ | b
    · -- solid edges: used by every `M_k` with `k ≠ i`
      have : ∀ k : Fin n, (sig k (.inl (i, a)) = (.inl (j, b) : V n)) ↔
          (k ≠ i ∧ i = j ∧ a ≠ b) := by
        intro k
        by_cases h : i = k
        · subst h; simp [sig]
        · simp only [sig, h, ite_false]
          cases a <;> cases b <;> simp [Ne.symm h]
      simp only [this, wt]
      by_cases hij : i = j ∧ a ≠ b
      · simp only [hij, ne_eq, not_false_eq_true, and_self, and_true, ite_true, mul_ite, mul_one,
          mul_zero]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_one]
        field_simp
      · simp [hij]
    · have : ∀ k : Fin n, (sig k (.inl (i, a)) = (.inr b : V n)) ↔ (k = i ∧ a ≠ b) := by
        intro k
        by_cases h : i = k
        · subst h; cases a <;> cases b <;> simp [sig]
        · simp [sig, h, Ne.symm h]
      simp only [this, wt]
      by_cases hab : a ≠ b
      · simp [hab]
      · simp [hab]
    · have : ∀ k : Fin n, (sig k (.inr a) = (.inl (j, b) : V n)) ↔ (k = j ∧ a ≠ b) := by
        intro k; cases a <;> cases b <;> simp [sig]
      simp only [this, wt]
      by_cases hab : a ≠ b
      · simp [hab]
      · simp [hab]
    · simp [sig, wt]

/-- The core of Lemma 1.2 for the Figure 1 graph: every perfect matching in `supp(x)` crosses a
cut `S = {z_i, y_i}` with `x(δ(S)) = 2/n` at least once. -/
theorem fig1_bad_cut {n : ℕ} (hn : 1 ≤ n) (M : PerfectMatching (V n))
    (hM : InSupport (fig1 n) M) :
    ∃ S : Finset (V n), S.Nonempty ∧ S ≠ univ ∧ 0 < cutWeight (fig1 n) S ∧
      ((n : ℝ) / 2) * cutWeight (fig1 n) S ≤ crossCount M S := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  -- `y` is matched to some `z_i`
  have hy := hM (.inr true)
  obtain ⟨i, hi⟩ : ∃ i : Fin n, M.1 (.inr true) = .inl (i, false) := by
    rcases h : M.1 (.inr true) with ⟨i, b⟩ | b
    · rw [h] at hy
      cases b
      · exact ⟨i, rfl⟩
      · simp [fig1, wt] at hy
    · rw [h] at hy; simp [fig1, wt] at hy
  have hz : M.1 (.inl (i, false)) = .inr true := by rw [← hi, (M.2 _).1]
  let S : Finset (V n) := {.inl (i, false), .inl (i, true)}
  have hyS : (.inr true : V n) ∉ S := by simp [S]
  have hne : (.inl (i, false) : V n) ≠ .inl (i, true) := by simp
  -- `x(δ(S)) = 2/n`
  have hz' : ∑ v ∈ Sᶜ, wt n (.inl (i, false)) v = 1 / n := by
    rw [Finset.sum_congr rfl (g := fun v => if v = (.inr true : V n) then 1 / (n : ℝ) else 0),
      Finset.sum_ite_eq']
    · simp [hyS]
    · intro v hv
      simp only [S, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      rcases v with ⟨j, b⟩ | b
      · by_cases hij : i = j
        · subst hij; cases b <;> simp_all
        · simp [wt, hij]
      · cases b <;> simp [wt]
  have hy' : ∑ v ∈ Sᶜ, wt n (.inl (i, true)) v = 1 / n := by
    rw [Finset.sum_congr rfl (g := fun v => if v = (.inr false : V n) then 1 / (n : ℝ) else 0),
      Finset.sum_ite_eq']
    · simp [S]
    · intro v hv
      simp only [S, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      rcases v with ⟨j, b⟩ | b
      · by_cases hij : i = j
        · subst hij; cases b <;> simp_all
        · simp [wt, hij]
      · cases b <;> simp [wt]
  have hcut : cutWeight (fig1 n) S = 2 / n := by
    unfold cutWeight
    rw [show S = {.inl (i, false), .inl (i, true)} from rfl, Finset.sum_pair hne]
    simp only [fig1]
    rw [← show S = {.inl (i, false), .inl (i, true)} from rfl, hz', hy']
    ring
  -- `|M ∩ δ(S)| ≥ 1`, witnessed by the dotted edge `(z_i, y)`
  have hcross : 1 ≤ crossCount M S := by
    unfold crossCount
    apply Finset.card_pos.mpr
    exact ⟨.inl (i, false), Finset.mem_filter.mpr ⟨by simp [S], by rw [hz]; exact hyS⟩⟩
  refine ⟨S, ⟨_, Finset.mem_insert_self _ _⟩, fun h => hyS (h ▸ Finset.mem_univ _), ?_, ?_⟩
  · rw [hcut]; have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  · rw [hcut, show (n : ℝ) / 2 * (2 / n) = 1 by field_simp]
    exact_mod_cast hcross

end LowerBound

open LowerBound

/-- **Lemma 1.2** (Linear thinness lower bound) [HOG26]. For every `n ≥ 1` there is a weighted
graph on `2n + 2` vertices with `x ∈ PM(G)` such that for every perfect matching `M ⊆ supp(x)`
there is a cut `∅ ≠ S ⊊ V` with `x(δ(S)) > 0` and `|M ∩ δ(S)| / x(δ(S)) ≥ n/2`. -/
theorem lemma12 (n : ℕ) (hn : 1 ≤ n) :
    ∃ x : WGraph (V n), Fintype.card (V n) = 2 * n + 2 ∧ IsFracPM x ∧
      ∀ M : PerfectMatching (V n), InSupport x M →
        ∃ S : Finset (V n), S.Nonempty ∧ S ≠ univ ∧ 0 < cutWeight x S ∧
          ((n : ℝ) / 2) * cutWeight x S ≤ crossCount M S :=
  ⟨fig1 n, card_V n, fig1_isFracPM hn, fig1_bad_cut hn⟩

/-- Corollary of Lemma 1.2: no perfect matching in `supp(x)` is `α`-thin for `α < n/2`. -/
theorem lemma12_not_thin (n : ℕ) (hn : 1 ≤ n) :
    ∃ x : WGraph (V n), Fintype.card (V n) = 2 * n + 2 ∧ IsFracPM x ∧
      ∀ M : PerfectMatching (V n), InSupport x M → ∀ α : ℝ, α < n / 2 → ¬ IsThin α x M := by
  obtain ⟨x, hc, hx, hM⟩ := lemma12 n hn
  refine ⟨x, hc, hx, fun M hMs α hα hthin => ?_⟩
  obtain ⟨S, -, -, hpos, hle⟩ := hM M hMs
  have := hthin S
  have : α * cutWeight x S < (n : ℝ) / 2 * cutWeight x S := mul_lt_mul_of_pos_right hα hpos
  linarith

end ThinMatching
