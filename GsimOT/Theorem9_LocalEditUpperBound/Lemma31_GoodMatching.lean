/-
# Lemma 31: a large matching with small error at every vertex

Paper, Appendix D.2, Lemma 31 (p. 29, l. 899–900; proof l. 901–907): Suppose that `L > 0`.  For
every `γ ∈ (0, 1/2]` there is a matching `M ⊆ supp(Q)` such that `n - |M| ≤ 2γn` and
`Φ_v(M) ≤ 2L + 10 ln(4n)/γ` for all `v ∈ V`.

The paper fixes an optimal `Q` and `L := d₁^OT(G, H)` (p. 28, l. 865–866) and the reference
bijection `σ` of Eq. (18).  `lemma31` is stated for any `Q ∈ DS(V, W)` whose supported local
costs are at most `L` and any bijection `σ` whose graph lies in `supp(Q)`.

The proof follows the paper: apply Lemma 30 to `q := Q`, bound the probability of a large error
at each `v` by the tail bound (19) with `μ := L`, `τ := 2 + 10 ln(4n)/(γL)`, take a union bound,
and use Markov's inequality for `n - |M|`.
-/
import GsimOT.Common.Lemma29_Integrality
import GsimOT.Theorem9_LocalEditUpperBound.Lemma30_DependentRounding

open Finset

namespace GsimOT

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- The error at `v` of a matching `M` relative to the reference bijection `σ`:
`Φ_v(M) := ∑_{(v', w') ∈ M} |A_G(v, v') - A_H(σ(v), w')|`. -/
def errAt (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (σ : V ≃ W) (v : V) (M : Finset (V × W)) : ℝ :=
  ∑ e ∈ M, |adj G v e.1 - adj H (σ v) e.2|

/-- A matching has at most `|V|` pairs. -/
lemma IsMatching.card_le {M : Finset (V × W)} (hM : IsMatching M) : M.card ≤ Fintype.card V := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun e => e.1) (fun _ _ => Finset.mem_univ _) ?_
  intro e he e' he' h
  exact Prod.ext h ((hM e he e' he').1 h)

/-- Rewriting a sum over `M` as a sum over all pairs with an indicator. -/
private lemma sum_mem_eq (M : Finset (V × W)) (f : V × W → ℝ) :
    ∑ e ∈ M, f e = ∑ e, f e * (if e ∈ M then 1 else 0) := by
  simp [mul_ite, Finset.sum_ite_mem]

/-- **Lemma 31.** -/
theorem lemma31 (hCVZ : CVZRounding) {Q : V → W → ℝ} (hQ : IsDS Q) {L : ℝ}
    (hL : ∀ v w, Q v w ≠ 0 → localCost G H Q v w ≤ L) {σ : V ≃ W}
    (hσ : ∀ v, Q v (σ v) ≠ 0) (hLpos : 0 < L) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) :
    ∃ M : Finset (V × W), IsMatching M ∧ (∀ e ∈ M, Q e.1 e.2 ≠ 0) ∧
      (Fintype.card V : ℝ) - M.card ≤ 2 * γ * Fintype.card V ∧
      ∀ v, errAt G H σ v M ≤ 2 * L + 10 * Real.log (4 * Fintype.card V) / γ := by
  set n := Fintype.card V with hn
  -- The degenerate case `n = 0`.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · refine ⟨∅, by simp [IsMatching], by simp, by simp [hn0], fun v => ?_⟩
    exact absurd hn0 (Fintype.card_pos_iff.2 ⟨v⟩).ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  obtain ⟨p, hp0, hp1, hpM, hpmarg, hptail⟩ := hCVZ V W Q hQ γ hγ0 hγ1
  -- Matchings in the support of `p` lie in `supp(Q)`.
  have hsupp : ∀ M, p M ≠ 0 → ∀ e ∈ M, Q e.1 e.2 ≠ 0 := by
    intro M hM e he hQe
    have h := hpmarg e
    rw [hQe, mul_zero] at h
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun M' _ => mul_nonneg (hp0 M')
      (by split_ifs <;> norm_num))).1 h M (Finset.mem_univ M)
    simp [he, hM] at this
  -- The threshold.
  set T : ℝ := 2 * L + 10 * Real.log (4 * n) / γ with hT
  have hlog : 0 ≤ Real.log (4 * n) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    linarith)
  -- Tail bound at a single vertex.
  have htail : ∀ v, ∑ M, (if T ≤ errAt G H σ v M then p M else 0) ≤ 1 / (4 * n) := by
    intro v
    set α : V × W → ℝ := fun e => |adj G v e.1 - adj H (σ v) e.2|
    have hα : ∀ e, 0 ≤ α e ∧ α e ≤ 1 := fun e => ⟨abs_nonneg _, abs_adj_sub_adj_le_one G H _ _ _ _⟩
    -- the expectation is `(1 - γ) L_Q(v, σ v) ≤ L`
    have hexp : ∑ M, p M * (∑ e ∈ M, α e) ≤ L := by
      have h1 : ∑ M, p M * (∑ e ∈ M, α e) = (1 - γ) * localCost G H Q v (σ v) := by
        simp_rw [sum_mem_eq _ α, Finset.mul_sum]
        rw [Finset.sum_comm]
        have : ∀ e : V × W, ∑ M, p M * (α e * (if e ∈ M then 1 else 0)) =
            α e * ((1 - γ) * Q e.1 e.2) := by
          intro e; rw [← hpmarg e, Finset.mul_sum]
          refine Finset.sum_congr rfl fun M _ => by ring
        simp_rw [this]
        unfold localCost disc
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w' _ => ?_
        simp only [α]; ring
      rw [h1]
      have h2 := hL v (σ v) (hσ v)
      have h3 := localCost_nonneg (G := G) (H := H) hQ.nonneg v (σ v)
      nlinarith
    set τ' : ℝ := 2 + 10 * Real.log (4 * n) / (γ * L)
    have hτ' : 2 ≤ τ' := by
      have : 0 ≤ 10 * Real.log (4 * n) / (γ * L) := by positivity
      linarith
    have hτμ : τ' * L = T := by
      simp only [τ', hT]; field_simp
    have h := hptail α hα L hLpos hexp τ' hτ'
    rw [hτμ] at h
    refine le_trans (le_of_eq ?_) (h.trans ?_)
    · rfl
    · have hexpo : -(L * γ * (2 * τ' - 3)) / 20 ≤ -Real.log (4 * n) := by
        have : L * γ * (2 * τ' - 3) = L * γ + 20 * Real.log (4 * n) := by
          simp only [τ']; field_simp; ring
        rw [this]
        have : 0 ≤ L * γ := by positivity
        linarith
      calc Real.exp (-(L * γ * (2 * τ' - 3)) / 20) ≤ Real.exp (-Real.log (4 * n)) :=
            Real.exp_le_exp.2 hexpo
        _ = 1 / (4 * n) := by
            rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
  -- Union bound: probability that some vertex has a large error is at most `1/4`.
  have hunion : ∑ M, (if ∃ v, T ≤ errAt G H σ v M then p M else 0) ≤ 1 / 4 := by
    calc ∑ M, (if ∃ v, T ≤ errAt G H σ v M then p M else 0)
        ≤ ∑ M, ∑ v, (if T ≤ errAt G H σ v M then p M else 0) := by
          refine Finset.sum_le_sum fun M _ => ?_
          split_ifs with h
          · obtain ⟨v, hv⟩ := h
            refine le_trans (le_of_eq ?_) (Finset.single_le_sum
              (f := fun v => if T ≤ errAt G H σ v M then p M else 0)
              (fun v _ => by split_ifs <;> simp [hp0]) (Finset.mem_univ v))
            simp [hv]
          · exact Finset.sum_nonneg fun v _ => by split_ifs <;> simp [hp0]
      _ = ∑ v, ∑ M, (if T ≤ errAt G H σ v M then p M else 0) := Finset.sum_comm
      _ ≤ ∑ _v : V, 1 / (4 * (n : ℝ)) := Finset.sum_le_sum fun v _ => htail v
      _ = 1 / 4 := by
          rw [Finset.sum_const, Finset.card_univ, ← hn, nsmul_eq_mul]
          field_simp
  -- Markov: probability that `n - |M| > 2γn` is at most `1/2`.
  have hmarkov : ∑ M, (if 2 * γ * n < (n : ℝ) - M.card then p M else 0) ≤ 1 / 2 := by
    have hE : ∑ M, p M * ((n : ℝ) - M.card) = γ * n := by
      have hcard : ∀ M : Finset (V × W), (M.card : ℝ) = ∑ e, (if e ∈ M then 1 else 0) := by
        intro M; rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, hcard,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [hpmarg]
      rw [← Finset.mul_sum, Fintype.sum_prod_type]
      simp only
      rw [hQ.sum_sum, ← hn]
      ring
    have hpt : ∀ M, (if 2 * γ * n < (n : ℝ) - M.card then p M else 0) ≤
        p M * ((n : ℝ) - M.card) / (2 * γ * n) := by
      intro M
      have h2 : 0 < 2 * γ * (n : ℝ) := by positivity
      split_ifs with h
      · rw [le_div_iff₀ h2]
        exact mul_le_mul_of_nonneg_left h.le (hp0 M)
      · by_cases hM : p M = 0
        · simp [hM]
        · have := (hpM M hM).card_le
          have : (M.card : ℝ) ≤ n := by exact_mod_cast this
          exact div_nonneg (mul_nonneg (hp0 M) (by linarith)) h2.le
    calc ∑ M, (if 2 * γ * n < (n : ℝ) - M.card then p M else 0)
        ≤ ∑ M, p M * ((n : ℝ) - M.card) / (2 * γ * n) := Finset.sum_le_sum fun M _ => hpt M
      _ = (∑ M, p M * ((n : ℝ) - M.card)) / (2 * γ * n) := by rw [Finset.sum_div]
      _ = 1 / 2 := by rw [hE]; field_simp
  -- Hence some matching in the support of `p` avoids both bad events.
  by_contra hcon
  push Not at hcon
  have hbad : ∀ M, p M ≤ (if ∃ v, T ≤ errAt G H σ v M then p M else 0) +
      (if 2 * γ * n < (n : ℝ) - M.card then p M else 0) := by
    intro M
    by_cases hM : p M = 0
    · rw [hM]; split_ifs <;> simp
    · by_cases h1 : ∃ v, T ≤ errAt G H σ v M
      · rw [ite_eq_left h1]; split_ifs <;> linarith [hp0 M]
      · push Not at h1
        have h2 := hcon M (hpM M hM) (hsupp M hM)
        by_cases h3 : (n : ℝ) - M.card ≤ 2 * γ * n
        · obtain ⟨v, hv⟩ := h2 h3
          exact absurd hv (not_lt.2 (h1 v).le)
        · rw [ite_eq_right (by push Not; exact fun v => h1 v), ite_eq_left (not_le.1 h3)]; simp
  have := Finset.sum_le_sum fun M (_ : M ∈ Finset.univ) => hbad M
  rw [Finset.sum_add_distrib, hp1] at this
  linarith

end GsimOT
