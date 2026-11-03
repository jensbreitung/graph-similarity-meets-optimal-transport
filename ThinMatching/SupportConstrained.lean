/-
# Theorem 1.3: support-constrained `O(n log n)`-thin perfect matchings

[HOG26], Theorem 1.3 and its proof in Section 3, assuming Lemma 3.6 (whose proof the paper omits)
as the hypothesis `Lemma36` (see `ThinMatching/SupportConstrained/Sampling.lean`).

**Theorem 1.3** (`theorem13_support`).  There is an absolute constant `C > 0` such that for every
weighted graph `x ∈ PM(G)` on a finite vertex set `V` there is a perfect matching `M ⊆ supp(x)` with
`|M ∩ δ(S)| ≤ C |V| ln(2|V|) · x(δ(S))` for all `S ⊆ V`.

*Proof (Algorithm 1).*  Let `n = |V|` and `ε = 1/(4n)` (the paper's `1/(8n)` for `|V| = 2n`).
1. Trim `x` with threshold `ε` (Definition 3.1, Lemma 3.2): blocks `C₁, …, C_k` (the components of
   `x̃`), each `ε`-edge-connected, `x̃ ≤ x` and `x(E) - x̃(E) ≤ (n - 1)ε ≤ 1/4`.
2. Sample `α = ⌈c' n ln(2n)⌉` copies of every edge `e` with probability `x̃_e` (`c' = max(c, 4)`,
   with `c` the constant of Lemma 3.6).
3. By Lemma 3.5, `P[Y has no perfect matching] ≤ 1/4`.
4. By Lemma 3.6 applied to each `G[Cᵢ]` with weights `x̃` and the global `N = n`, and a union bound
   over the `k ≤ n` blocks, `P[∃ i, ∃ S ⊆ Cᵢ, Y(δ_{Cᵢ}(S)) > K α x̃(δ_{Cᵢ}(S))] ≤ k/(4n) ≤ 1/4`.
5. Hence some outcome `ω` of positive probability avoids both events; let `M ⊆ Y` be a perfect
   matching of the sample.  Since `ω` has positive probability, only edges with `x̃_e > 0` are
   sampled, so `M ⊆ Y ⊆ supp(x̃) ⊆ supp(x)`.

*Thinness across several components* (the paper only argues per component: "`M ∩ G[Cᵢ]` is
`O(α)`-thin").  For an arbitrary `S ⊆ V`, all sampled edges lie inside blocks, so
`|M ∩ δ(S)| ≤ Y(δ(S)) = ∑ᵢ Y(δ_{Cᵢ}(S ∩ Cᵢ)) ≤ K α ∑ᵢ x̃(δ_{Cᵢ}(S ∩ Cᵢ))`
`= K α x̃(δ(S)) ≤ K α x(δ(S))`
(`sum_cut_eq_sum_blocks`): the per-component bounds add up, with no loss.

*Constants.*  `K α ≤ K (c' n ln(2n) + 1) ≤ K (c' + 2) n ln(2n)` since `n ln(2n) ≥ ln 2 ≥ 1/2`; so
`C = K (max(c, 4) + 2)` depends only on the constants `c, K` of Lemma 3.6.

For `V = ∅` the empty matching works; for `|V|` odd the hypothesis `x ∈ PM(G)` is never satisfied
(and the argument above does not need to treat this case separately).
-/
import ThinMatching.SupportConstrained.Trimming
import ThinMatching.SupportConstrained.Lemma35

open Finset

namespace ThinMatching

section Theorem13

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The coins of the sample restricted to block `a`: coin `(e, k)` of `G[C_a]` is coin
`(e, k)` of `G`. -/
def blockEmb (ℓ : V → ℕ) (a : ℕ) (α : ℕ) : Sym2 (Blk ℓ a) × Fin α → Sym2 V × Fin α :=
  fun i => (Sym2.map Subtype.val i.1, i.2)

omit [Fintype V] [DecidableEq V] in
theorem blockEmb_injective (ℓ : V → ℕ) (a α : ℕ) : Function.Injective (blockEmb ℓ a α) := by
  rintro ⟨e, k⟩ ⟨e', k'⟩ h
  simp only [blockEmb, Prod.mk.injEq] at h
  rw [Sym2.map.injective Subtype.val_injective h.1, h.2]

omit [Fintype V] [DecidableEq V] in
/-- Restricting the sampling probabilities `x̃` to block `a` gives the sampling probabilities of
the induced graph `G[C_a]`. -/
theorem sampleProb_comp_blockEmb (x : WGraph V) (ℓ : V → ℕ) (a α : ℕ) :
    sampleProb (trimGraph x ℓ) α ∘ blockEmb ℓ a α = sampleProb (blockGraph x ℓ a) α := by
  funext ⟨e, k⟩
  induction e using Sym2.ind with
  | _ u v =>
    simp [sampleProb, blockEmb, trimGraph, blockGraph, u.2, v.2]

/-- The part of `S` in block `a`. -/
def blockPart (ℓ : V → ℕ) (a : ℕ) (S : Finset V) : Finset (Blk ℓ a) := {u | u.1 ∈ S}

/-- **Cuts decompose over blocks.**  If `g` vanishes across blocks then
`∑_{u ∈ S, v ∉ S} g(u, v) = ∑_a ∑_{u ∈ S ∩ C_a, v ∈ C_a \ S} g(u, v)`. -/
theorem sum_cut_eq_sum_blocks (ℓ : V → ℕ) (g : V → V → ℝ) (hg : ∀ u v, ℓ u ≠ ℓ v → g u v = 0)
    (S : Finset V) :
    ∑ u ∈ S, ∑ v ∈ Sᶜ, g u v = ∑ a ∈ Finset.univ.image ℓ,
      ∑ u ∈ blockPart ℓ a S, ∑ v ∈ (blockPart ℓ a S)ᶜ, g u.1 v.1 := by
  have h1 : ∀ a, ∑ u ∈ blockPart ℓ a S, ∑ v ∈ (blockPart ℓ a S)ᶜ, g u.1 v.1 =
      ∑ u ∈ S with ℓ u = a, ∑ v ∈ Sᶜ with ℓ v = a, g u v := by
    intro a
    have hA : (blockPart ℓ a S).map (Function.Embedding.subtype _) = S.filter (ℓ · = a) := by
      ext v; simp only [blockPart, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨w, hw, rfl⟩; exact ⟨hw, w.2⟩
      · rintro ⟨hv, hl⟩; exact ⟨⟨v, hl⟩, hv, rfl⟩
    have hB : (blockPart ℓ a S)ᶜ.map (Function.Embedding.subtype _) = Sᶜ.filter (ℓ · = a) := by
      ext v; simp only [blockPart, Finset.mem_map, Finset.mem_compl, Finset.mem_filter,
        Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨w, hw, rfl⟩; exact ⟨hw, w.2⟩
      · rintro ⟨hv, hl⟩; exact ⟨⟨v, hl⟩, hv, rfl⟩
    rw [← hA, ← hB, Finset.sum_map]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_map]
    rfl
  simp_rw [h1]
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.univ.image ℓ) (g := ℓ)
    (fun u _ => Finset.mem_image_of_mem ℓ (Finset.mem_univ u))]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_filter] at hu
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : ℓ v = a
  · simp [hv]
  · simp only [hv, ite_false]
    exact hg u v (by rw [hu.2]; exact Ne.symm hv)

omit [DecidableEq V] in
/-- A sampled pair has positive probability in an outcome of positive probability. -/
theorem pos_of_copies_pos {y : WGraph V} (hy : ∀ u v, y.w u v ≤ 1) {α : ℕ}
    {ω : Sym2 V × Fin α → Bool} (hω : 0 < bernW (sampleProb y α) ω) {u v : V}
    (h : 0 < copies ω s(u, v)) : 0 < y.w u v := by
  obtain ⟨k, hk⟩ := Finset.card_pos.1 h
  rw [Finset.mem_filter] at hk
  exact pos_of_bernW_pos (isProbVec_sampleProb y hy α) hω (i := (s(u, v), k)) hk.2

/-- **Thinness from the per-block bounds** (end of the proof of Theorem 1.3).  If the sample `Y`
of an outcome of positive probability satisfies the conclusion of Lemma 3.6 in every block and
contains the perfect matching `M`, then `|M ∩ δ(S)| ≤ K α x(δ(S))` for every `S ⊆ V`. -/
theorem crossCount_le_of_good {x : WGraph V} (hx1 : ∀ u v, x.w u v ≤ 1) (ℓ : V → ℕ) {α : ℕ}
    {K : ℝ} (hK : 0 ≤ K) {ω : Sym2 V × Fin α → Bool}
    (hω : 0 < bernW (sampleProb (trimGraph x ℓ) α) ω) {M : PerfectMatching V}
    (hM : ∀ v, (sampleGraph ω).Adj v (M.1 v))
    (hblk : ∀ a ∈ Finset.univ.image ℓ, ∀ S' : Finset (Blk ℓ a),
      sampleCut (ω ∘ blockEmb ℓ a α) S' ≤ K * α * cutWeight (blockGraph x ℓ a) S')
    (S : Finset V) : (crossCount M S : ℝ) ≤ K * α * cutWeight x S := by
  have hxt1 : ∀ u v, (trimGraph x ℓ).w u v ≤ 1 := fun u v => (trimGraph_le x ℓ u v).trans (hx1 u v)
  -- `|M ∩ δ(S)| ≤ Y(δ(S))`
  have h1 : (crossCount M S : ℝ) ≤ sampleCut ω S := by
    have : (crossCount M S : ℝ) = ∑ u ∈ S, ∑ v ∈ Sᶜ, (if M.1 u = v then (1 : ℝ) else 0) := by
      unfold crossCount
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_ite_eq]
      simp
    rw [this]
    refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
    split_ifs with h
    · subst h
      exact_mod_cast (hM u).2
    · exact Nat.cast_nonneg _
  -- `Y(δ(S)) = ∑_a Y(δ_{C_a}(S ∩ C_a))`
  have h2 : sampleCut ω S = ∑ a ∈ Finset.univ.image ℓ,
      sampleCut (ω ∘ blockEmb ℓ a α) (blockPart ℓ a S) := by
    unfold sampleCut
    rw [sum_cut_eq_sum_blocks ℓ (fun u v => (copies ω s(u, v) : ℝ)) ?_ S]
    · rfl
    · intro u v huv
      by_contra h0
      exact huv (same_of_trimGraph_pos (pos_of_copies_pos hxt1 hω
        (Nat.pos_of_ne_zero (by exact_mod_cast h0))))
  -- `∑_a x̃(δ_{C_a}(S ∩ C_a)) = x̃(δ(S)) ≤ x(δ(S))`
  have h3 : ∑ a ∈ Finset.univ.image ℓ, cutWeight (blockGraph x ℓ a) (blockPart ℓ a S) ≤
      cutWeight x S := by
    have := sum_cut_eq_sum_blocks ℓ (trimGraph x ℓ).w (fun u v huv => by simp [trimGraph, huv]) S
    have e : ∀ a, cutWeight (blockGraph x ℓ a) (blockPart ℓ a S) =
        ∑ u ∈ blockPart ℓ a S, ∑ v ∈ (blockPart ℓ a S)ᶜ, (trimGraph x ℓ).w u.1 v.1 := by
      intro a
      unfold cutWeight
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      simp [blockGraph, trimGraph, u.2, v.2]
    simp_rw [e, ← this]
    exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => trimGraph_le x ℓ u v
  calc (crossCount M S : ℝ) ≤ sampleCut ω S := h1
    _ = _ := h2
    _ ≤ ∑ a ∈ Finset.univ.image ℓ, K * α * cutWeight (blockGraph x ℓ a) (blockPart ℓ a S) :=
        Finset.sum_le_sum fun a ha => hblk a ha _
    _ = K * α * ∑ a ∈ Finset.univ.image ℓ, cutWeight (blockGraph x ℓ a) (blockPart ℓ a S) := by
        rw [Finset.mul_sum]
    _ ≤ K * α * cutWeight x S := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- **Lemma 3.6 applied to all components, with a union bound.**  If every block of `ℓ` is
`1/(4n)`-edge-connected (`n = |V|`) and `α ≥ c n ln(2n)`, the probability that some block
violates the conclusion of Lemma 3.6 is at most `1/4`. -/
theorem prob_bad_blocks_le {c K : ℝ} (h36 : ∀ (W : Type) [Fintype W] [DecidableEq W] (y : WGraph W)
      (N α : ℕ), 1 ≤ N → Fintype.card W ≤ N → (∀ u v, y.w u v ≤ 1) →
      (∀ S : Finset W, S.Nonempty → S ≠ Finset.univ → 1 / (4 * (N : ℝ)) ≤ cutWeight y S) →
      c * N * Real.log (2 * N) ≤ α →
      prob (sampleProb y α) (fun ω => ∃ S : Finset W, K * α * cutWeight y S < sampleCut ω S)
        ≤ 1 / (4 * (N : ℝ)))
    {V : Type} [Fintype V] [DecidableEq V] {x : WGraph V} (hx1 : ∀ u v, x.w u v ≤ 1)
    (hn : 1 ≤ Fintype.card V) {ℓ : V → ℕ} (hℓ : IsTrimmed x (1 / (4 * Fintype.card V)) ℓ) {α : ℕ}
    (hα : c * Fintype.card V * Real.log (2 * Fintype.card V) ≤ α) :
    prob (sampleProb (trimGraph x ℓ) α) (fun ω => ∃ a ∈ Finset.univ.image ℓ,
      ∃ S' : Finset (Blk ℓ a),
      K * α * cutWeight (blockGraph x ℓ a) S' < sampleCut (ω ∘ blockEmb ℓ a α) S') ≤ 1 / 4 := by
  have hxt1 : ∀ u v, (trimGraph x ℓ).w u v ≤ 1 := fun u v => (trimGraph_le x ℓ u v).trans (hx1 u v)
  have hp := isProbVec_sampleProb (trimGraph x ℓ) hxt1 α
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  refine (prob_exists_le hp _ _).trans ?_
  have hblk : ∀ a, prob (sampleProb (trimGraph x ℓ) α) (fun ω => ∃ S' : Finset (Blk ℓ a),
      K * α * cutWeight (blockGraph x ℓ a) S' < sampleCut (ω ∘ blockEmb ℓ a α) S') ≤
        1 / (4 * (Fintype.card V : ℝ)) := by
    intro a
    rw [prob_comp_injective _ (blockEmb_injective ℓ a α)
      (fun ω' => ∃ S' : Finset (Blk ℓ a), K * α * cutWeight (blockGraph x ℓ a) S' <
        sampleCut ω' S'), sampleProb_comp_blockEmb]
    refine h36 (Blk ℓ a) (blockGraph x ℓ a) (Fintype.card V) α hn
      (Fintype.card_subtype_le _) (fun u v => hx1 u.1 v.1) (fun S hS hS' => ?_) hα
    exact (hℓ a S hS hS').le
  calc _ ≤ ∑ _a ∈ Finset.univ.image ℓ, 1 / (4 * (Fintype.card V : ℝ)) :=
        Finset.sum_le_sum fun a _ => hblk a
    _ = #(Finset.univ.image ℓ) * (1 / (4 * (Fintype.card V : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card V * (1 / (4 * (Fintype.card V : ℝ))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast Finset.card_image_le.trans (by simp)
    _ = 1 / 4 := by field_simp

/-- **Theorem 1.3 (support-constrained thin matching)**, assuming Lemma 3.6 (`Lemma36`).  There is
an absolute constant `C > 0` such that for every weighted graph `x ∈ PM(G)` on `V` there is a
perfect matching `M ⊆ supp(x)` that is `C |V| ln(2|V|)`-thin w.r.t. `x`. -/
theorem theorem13_support (h36 : Lemma36) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (x : WGraph V), IsFracPM x →
      ∃ M : PerfectMatching V, InSupport x M ∧
        IsThin (C * Fintype.card V * Real.log (2 * Fintype.card V)) x M := by
  obtain ⟨c, K, hc, hK, h36⟩ := h36
  refine ⟨K * (max c 4 + 2), by positivity, ?_⟩
  intro V _ _ x hx
  -- the empty vertex set
  rcases isEmpty_or_nonempty V with hV | hV
  · refine ⟨⟨Equiv.refl V, fun v => isEmptyElim v⟩, fun v => isEmptyElim v, fun S => ?_⟩
    simp [Finset.eq_empty_of_isEmpty S, crossCount]
  -- parameters of Algorithm 1
  have hx1 := hx.le_one
  have hn : 1 ≤ (Fintype.card V) := Fintype.card_pos
  have hn' : (1 : ℝ) ≤ (Fintype.card V) := by exact_mod_cast hn
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlogn : Real.log 2 ≤ Real.log (2 * Fintype.card V) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hnlog : (1 / 2 : ℝ) ≤ Fintype.card V * Real.log (2 * Fintype.card V) := by nlinarith
  let c' := max c 4
  let α : ℕ := ⌈c' * Fintype.card V * Real.log (2 * Fintype.card V)⌉₊
  have hα' : c' * Fintype.card V * Real.log (2 * Fintype.card V) ≤ α := Nat.le_ceil _
  have hα : c * Fintype.card V * Real.log (2 * Fintype.card V) ≤ α := by
    refine le_trans ?_ hα'
    have : c ≤ c' := le_max_left _ _
    have : 0 ≤ (Fintype.card V : ℝ) * Real.log (2 * Fintype.card V) := by linarith
    nlinarith
  have hαle : (α : ℝ) ≤ c' * Fintype.card V * Real.log (2 * Fintype.card V) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (by positivity) (by linarith))).le
  -- Step 1: trimming (Lemma 3.2) with `ε = 1/(4n)`
  obtain ⟨ℓ, hℓ, hrem⟩ := lemma32 x (ε := 1 / (4 * Fintype.card V)) (by positivity)
  have hrem' : edgeTotal x - edgeTotal (trimGraph x ℓ) ≤ 1 / 4 := by
    refine hrem.trans ?_
    rw [show ((Fintype.card V : ℝ) - 1) * (1 / (4 * Fintype.card V)) =
      1 / 4 - 1 / (4 * Fintype.card V) by field_simp]
    have : 0 < 1 / (4 * (Fintype.card V : ℝ)) := by positivity
    linarith
  have hxt1 : ∀ u v, (trimGraph x ℓ).w u v ≤ 1 := fun u v => (trimGraph_le x ℓ u v).trans (hx1 u v)
  have hp := isProbVec_sampleProb (trimGraph x ℓ) hxt1 α
  -- Step 2: the two bad events
  have hbad1 := (lemma35 hx (trimGraph x ℓ) (trimGraph_le x ℓ) hrem' α).trans
    (witness_bound_le hn (le_max_right c 4) hα')
  have hbad2 := prob_bad_blocks_le h36 hx1 hn hℓ hα
  obtain ⟨ω, hω, hωpos⟩ := exists_not_of_prob_lt_one hp
    ((prob_or_le hp
      (fun ω => ¬ ∃ M : PerfectMatching V, ∀ v, (sampleGraph ω).Adj v (M.1 v))
      (fun ω => ∃ a ∈ Finset.univ.image ℓ, ∃ S' : Finset (Blk ℓ a),
        K * α * cutWeight (blockGraph x ℓ a) S' < sampleCut (ω ∘ blockEmb ℓ a α) S')).trans_lt
      (by linarith))
  rw [not_or, not_not] at hω
  obtain ⟨⟨M, hM⟩, hgood⟩ := hω
  push Not at hgood
  refine ⟨M, fun v => ?_, fun S => ?_⟩
  · -- `M ⊆ Y ⊆ supp(x̃) ⊆ supp(x)`
    exact (pos_of_copies_pos hxt1 hωpos (hM v).2).trans_le (trimGraph_le x ℓ v (M.1 v))
  · -- thinness
    refine (crossCount_le_of_good hx1 ℓ hK.le hωpos hM hgood S).trans ?_
    refine mul_le_mul_of_nonneg_right ?_
      (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => x.nonneg u v)
    have : 0 ≤ (Fintype.card V : ℝ) * Real.log (2 * Fintype.card V) := by linarith
    calc K * α ≤ K * (c' * Fintype.card V * Real.log (2 * Fintype.card V) + 1) :=
          mul_le_mul_of_nonneg_left hαle hK.le
      _ ≤ K * (c' + 2) * Fintype.card V * Real.log (2 * Fintype.card V) := by nlinarith

end Theorem13

end ThinMatching
