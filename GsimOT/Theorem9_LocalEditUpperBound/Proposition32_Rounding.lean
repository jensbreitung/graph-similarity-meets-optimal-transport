/-
# Proposition 32: rounding a fractional alignment to a bijection

Paper, Appendix D.2, Proposition 32 (p. 29, l. 908–909; proof pp. 29–30, l. 910–935): Suppose that
`L > 0`.  For all `γ ∈ (0, 1/2]` and `ℓ ∈ ℕ_{>0}`,
`d₁(G, H) ≤ 2L + 10 ln(4n)/γ + 2γn + n/ℓ + 2ℓL`.

As in Lemma 31, `Q ∈ DS(V, W)` is any fractional alignment whose supported local costs are at
most `L`, and `σ` is a bijection whose graph lies in `supp(Q)` (the paper: an optimal `Q`,
`L := d₁^OT(G, H)` and `σ` as in Eq. (18)).

The proof is split, as in the paper, into a deterministic part (`prop38_of_matching`): given any
matching `M ⊆ supp(Q)` with error at most `X` at every vertex, turn it into a bijection `π` by
pulling `M` back along `σ`, cutting the resulting paths into blocks of `ℓ` vertices and closing
them (`PathCutting.exists_perm_of_partialInj`); then the local costs of `π` are bounded via the
triangle inequality.  Lemma 31 supplies the matching (`proposition32`).
-/
import GsimOT.Theorem9_LocalEditUpperBound.Lemma31_GoodMatching
import GsimOT.Theorem9_LocalEditUpperBound.PathCutting

open Finset GsimOT.PathCutting

namespace GsimOT

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- **Proposition 32, deterministic part.**  Let `M ⊆ supp(Q)` be a matching with
`Φ_v(M) ≤ X` for all `v`.  Then
`d₁(G, H) ≤ X + (n - |M|) + n/ℓ + 2ℓL`. -/
theorem prop38_of_matching {Q : V → W → ℝ} (hQ : IsDS Q) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ v w, Q v w ≠ 0 → localCost G H Q v w ≤ L) {σ : V ≃ W}
    (hσ : ∀ v, Q v (σ v) ≠ 0) {M : Finset (V × W)} (hM : IsMatching M)
    (hMQ : ∀ e ∈ M, Q e.1 e.2 ≠ 0) {X : ℝ} (hX0 : 0 ≤ X) (hX : ∀ v, errAt G H σ v M ≤ X)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    dOne G H ≤ X + ((Fintype.card V : ℝ) - M.card) + Fintype.card V / ℓ + 2 * ℓ * L := by
  classical
  set n := Fintype.card V
  -- The partial injective map `μ(v) := σ⁻¹(w)` for `(v, w) ∈ M`.
  let μ : V → Option V := fun v =>
    if h : ∃ w, (v, w) ∈ M then some (σ.symm h.choose) else none
  have hμM : ∀ v x, μ v = some x → (v, σ x) ∈ M := by
    intro v x h
    simp only [μ] at h
    split_ifs at h with hv
    cases h
    simpa using hv.choose_spec
  have hμnone : ∀ v, μ v = none ↔ ¬ ∃ w, (v, w) ∈ M := by
    intro v; simp only [μ]; split_ifs with h <;> simp [h]
  have hμinj : PInj μ := by
    intro a b c ha hb
    have h1 := hμM a c ha
    have h2 := hμM b c hb
    exact (hM _ h1 _ h2).2 rfl
  -- exactly `m = n - |M|` vertices are unmatched
  have hm : ((Finset.univ.filter fun v => μ v = none).card : ℝ) = n - M.card := by
    have himg : (M.image Prod.fst).card = M.card :=
      Finset.card_image_of_injOn fun e he e' he' h => Prod.ext h ((hM e he e' he').1 h)
    have hfil : (Finset.univ.filter fun v => μ v = none) = Finset.univ \ M.image Prod.fst := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Finset.mem_image, hμnone]
      constructor
      · rintro h ⟨e, he, rfl⟩; exact h ⟨e.2, he⟩
      · rintro h ⟨w, hw⟩; exact h ⟨(v, w), hw, rfl⟩
    rw [hfil, Finset.card_sdiff_of_subset (Finset.subset_univ _), himg, Finset.card_univ]
    have : M.card ≤ n := by rw [← himg]; exact (Finset.card_le_univ _)
    exact Nat.cast_sub this
  -- cut and close
  obtain ⟨τ, B, hτB, hBcard, hBreach⟩ := exists_perm_of_partialInj μ hμinj ℓ hℓ
  let π : V ≃ W := τ.trans σ
  have hπ : ∀ v, π v = σ (τ v) := fun v => rfl
  -- each `μ`-step moves `σ` by at most `2L` in `ρ_H` (Lemma 29)
  have hstep : ∀ a b, μ a = some b → rho H (σ a) (σ b) ≤ 2 * L := fun a b h =>
    lemma29_rho_le hQ hL hσ (hMQ _ (hμM a b h))
  have hchain : ∀ k a b, iter μ k a = some b → rho H (σ a) (σ b) ≤ 2 * k * L := by
    intro k
    induction k with
    | zero => intro a b h; simp at h; subst h; simp [rho_self]
    | succ k ih =>
      intro a b h
      rw [iter_succ, Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, hcb⟩ := h
      calc rho H (σ a) (σ b) ≤ rho H (σ a) (σ c) + rho H (σ c) (σ b) := rho_triangle _ _ _
        _ ≤ 2 * k * L + 2 * L := add_le_add (ih a c hc) (hstep c b hcb)
        _ = 2 * ((k + 1 : ℕ) : ℝ) * L := by push_cast; ring
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  -- `ρ_H(σ(v), π(v)) ≤ 2ℓL` for every `v`
  have hrho : ∀ v, rho H (σ v) (π v) ≤ 2 * ℓ * L := by
    intro v
    by_cases hv : v ∈ B
    · obtain ⟨k, hk, hkv⟩ := hBreach v hv
      rw [rho_comm]
      have hkℓ : (k : ℝ) ≤ ℓ := by exact_mod_cast hk.le
      calc rho H (π v) (σ v) ≤ 2 * k * L := hchain k (τ v) v hkv
        _ ≤ 2 * ℓ * L := by nlinarith
    · calc rho H (σ v) (π v) ≤ 2 * L := hstep v (τ v) (hτB v hv)
        _ ≤ 2 * ℓ * L := by nlinarith
  -- `|B| ≤ m + n/ℓ`
  have hBR : (B.card : ℝ) ≤ (n - M.card) + n / ℓ := by
    rw [← hm]
    have : (ℓ : ℝ) * B.card ≤ ℓ * (Finset.univ.filter fun v => μ v = none).card + n := by
      exact_mod_cast hBcard
    rw [div_eq_mul_inv]
    have hℓpos : (0 : ℝ) < ℓ := by linarith
    have := (mul_le_mul_iff_of_pos_left hℓpos).1 (show (ℓ : ℝ) * B.card ≤
      ℓ * ((Finset.univ.filter fun v => μ v = none).card + n * (ℓ : ℝ)⁻¹) by
        rw [mul_add, mul_comm (n : ℝ), ← mul_assoc, mul_inv_cancel₀ hℓpos.ne', one_mul]
        exact this)
    exact this
  -- the bound on every local cost of `π`
  have hloc : ∀ v, ∑ v', |adj G v v' - adj H (π v) (π v')| ≤
      X + ((n : ℝ) - M.card) + n / ℓ + 2 * ℓ * L := by
    intro v
    have hsplit : ∑ v', |adj G v v' - adj H (π v) (π v')| ≤
        ∑ v', |adj G v v' - adj H (σ v) (π v')| +
          ∑ v', |adj H (σ v) (π v') - adj H (π v) (π v')| := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun v' _ => abs_sub_le _ _ _
    have hsecond : ∑ v', |adj H (σ v) (π v') - adj H (π v) (π v')| = rho H (σ v) (π v) := by
      unfold rho
      exact Equiv.sum_comp π (fun w'' => |adj H (σ v) w'' - adj H (π v) w''|)
    -- split the first sum along `B`
    have hfirst : ∑ v', |adj G v v' - adj H (σ v) (π v')| ≤ X + B.card := by
      rw [← Finset.sum_compl_add_sum B]
      refine add_le_add ?_ ?_
      · -- retained vertices: `(v', π v') ∈ M`
        have hsub : (Bᶜ).image (fun v' => (v', π v')) ⊆ M := by
          intro e he
          simp only [Finset.mem_image, Finset.mem_compl] at he
          obtain ⟨v', hv', rfl⟩ := he
          exact hμM v' (τ v') (hτB v' hv')
        calc ∑ v' ∈ Bᶜ, |adj G v v' - adj H (σ v) (π v')|
            = ∑ e ∈ (Bᶜ).image (fun v' => (v', π v')), |adj G v e.1 - adj H (σ v) e.2| := by
              rw [Finset.sum_image (fun a _ b _ h => (Prod.ext_iff.1 h).1)]
          _ ≤ errAt G H σ v M :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _
          _ ≤ X := hX v
      · calc ∑ v' ∈ B, |adj G v v' - adj H (σ v) (π v')| ≤ ∑ _v' ∈ B, (1 : ℝ) :=
              Finset.sum_le_sum fun v' _ => abs_adj_sub_adj_le_one G H _ _ _ _
          _ = B.card := by simp
    calc ∑ v', |adj G v v' - adj H (π v) (π v')|
        ≤ (X + B.card) + rho H (σ v) (π v) := by linarith
      _ ≤ (X + ((n - M.card) + n / ℓ)) + 2 * ℓ * L := add_le_add (by linarith) (hrho v)
      _ = _ := by ring
  have hnn : 0 ≤ X + ((n : ℝ) - M.card) + n / ℓ + 2 * ℓ * L := by
    have : (M.card : ℝ) ≤ n := by exact_mod_cast hM.card_le
    positivity
  exact (dOne_le π).trans ((costOneBij_le_iff π hnn).2 hloc)

/-- **Proposition 32.** Suppose that `L > 0`.  For all `γ ∈ (0, 1/2]` and `ℓ ∈ ℕ_{>0}`,
`d₁(G, H) ≤ 2L + 10 ln(4n)/γ + 2γn + n/ℓ + 2ℓL`. -/
theorem proposition32 (hCVZ : CVZRounding) {Q : V → W → ℝ} (hQ : IsDS Q) {L : ℝ}
    (hL : ∀ v w, Q v w ≠ 0 → localCost G H Q v w ≤ L) {σ : V ≃ W}
    (hσ : ∀ v, Q v (σ v) ≠ 0) (hLpos : 0 < L) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    dOne G H ≤ 2 * L + 10 * Real.log (4 * Fintype.card V) / γ + 2 * γ * Fintype.card V +
      Fintype.card V / ℓ + 2 * ℓ * L := by
  obtain ⟨M, hM, hMQ, hMcard, hMerr⟩ := lemma31 hCVZ hQ hL hσ hLpos hγ0 hγ1
  have hlog : 0 ≤ Real.log (4 * Fintype.card V) := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with h | h
    · simp [h]
    · exact Real.log_nonneg (by
        have : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast h
        linarith)
  have hX0 : 0 ≤ 2 * L + 10 * Real.log (4 * Fintype.card V) / γ := by positivity
  have := prop38_of_matching hQ hLpos.le hL hσ hM hMQ hX0 hMerr ℓ hℓ
  linarith

end GsimOT
