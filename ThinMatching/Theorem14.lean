/-
# Theorem 1.4: relaxed thin perfect matchings

[HOG26], Theorem 1.4 and its proof in Section 4, assuming Theorem 2.2 ([RS14]).

Proof (Section 4): take a `q`-tree-cut sparsifier `T` of `x` with `q = O(log n log log n)`
(Theorem 2.2), the perfect matching `M` of Lemma 4.6 with `load_M(f) = Δ(V_s(f))` for every tree
edge `f`, and note `Δ(V_s(f)) ≤ x(δ(V_s(f)))` (Lemma 4.5); Proposition 4.3 with `β = 1` shows that
`M` is `q`-thin.

In the bipartite case we apply this to the weighted graph `bipGraph x` on `L ⊕ R` and translate
between the bipartite notions and the general ones (`cutWeight_bipGraph`, `crossCount_bipPM`,
`load_bipPM`); since `|L ⊕ R| = 2n`, the constant has to be adjusted (`log_mul_loglog_le`).
-/
import ThinMatching.Discrepancy
import ThinMatching.TreePairing
import ThinMatching.LoadVsCut

open Finset

namespace ThinMatching

namespace Theorem14

/-! ### Translating between bipartite and general notions -/

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- The perfect matching `{(l, π l)}` of `L ⊕ R`, as a fixed-point-free involution. -/
def bipPM (π : L ≃ R) : PerfectMatching (L ⊕ R) :=
  ⟨(Equiv.sumCongr π π.symm).trans (Equiv.sumComm R L), by rintro (l | r) <;> simp⟩

@[simp] lemma bipPM_inl (π : L ≃ R) (l : L) : (bipPM π).1 (Sum.inl l) = Sum.inr (π l) := rfl

@[simp] lemma bipPM_inr (π : L ≃ R) (r : R) : (bipPM π).1 (Sum.inr r) = Sum.inl (π.symm r) := rfl

/-- Counting the edges of `bipPM π` leaving a set `P ⊆ L ⊕ R`. -/
lemma card_cross_bipPM (π : L ≃ R) (P : L ⊕ R → Prop) [DecidablePred P] :
    #{u | P u ∧ ¬ P ((bipPM π).1 u)} = #{l | ¬ (P (Sum.inl l) ↔ P (Sum.inr (π l)))} := by
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  simp only [bipPM_inl, bipPM_inr]
  rw [← Equiv.sum_comp π, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Equiv.symm_apply_apply]
  by_cases h1 : P (Sum.inl l) <;> by_cases h2 : P (Sum.inr (π l)) <;> simp [h1, h2]

lemma crossCount_bipPM (π : L ≃ R) (SL : Finset L) (SR : Finset R) :
    crossCount (bipPM π) (SL.disjSum SR) = bipCrossCount π SL SR := by
  have : crossCount (bipPM π) (SL.disjSum SR) =
      #{u | u ∈ SL.disjSum SR ∧ ¬ (bipPM π).1 u ∈ SL.disjSum SR} := by
    unfold crossCount; congr 1; ext u; simp
  rw [this, card_cross_bipPM]
  unfold bipCrossCount
  simp

lemma load_bipPM {N : Type*} [Fintype N] [DecidableEq N] (T : RootedTree N) (e : L ⊕ R → N)
    (π : L ≃ R) (v : N) :
    load T e (bipPM π) v = loadBip T (e ∘ Sum.inl) (e ∘ Sum.inr) π v := by
  unfold load loadBip
  rw [card_cross_bipPM π (fun u => e u ∈ subtree T v)]
  rfl

/-- `x(δ(S))` in `bipGraph x` is the bipartite cut weight of `(S ∩ L, S ∩ R)`. -/
lemma cutWeight_bipGraph (x : L → R → ℝ) (hx : ∀ l r, 0 ≤ x l r) (S : Finset (L ⊕ R)) :
    cutWeight (bipGraph x hx) S =
      bipCutWeight x {l | Sum.inl l ∈ S} {r | Sum.inr r ∈ S} := by
  have hs : ∀ (T : Finset (L ⊕ R)) (f : L ⊕ R → ℝ),
      ∑ u ∈ T, f u = ∑ u, if u ∈ T then f u else 0 := fun T f => by
    rw [Finset.sum_ite_mem, univ_inter]
  calc cutWeight (bipGraph x hx) S
      = ∑ u, ∑ v, if u ∈ S ∧ v ∉ S then (bipGraph x hx).w u v else 0 := by
        unfold cutWeight; rw [hs]; refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : u ∈ S <;> simp [hu, hs Sᶜ]
    _ = _ := by
        unfold bipCutWeight
        simp only [Fintype.sum_sum_type, bipGraph, ite_self, Finset.sum_const_zero, zero_add,
          add_zero]
        rw [Finset.sum_comm (s := (univ : Finset R)), ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        by_cases h1 : Sum.inl l ∈ S <;> by_cases h2 : Sum.inr r ∈ S <;> simp [h1, h2]

lemma bipCutWeight_nonneg {x : L → R → ℝ} (hx : ∀ l r, 0 ≤ x l r) (SL : Finset L)
    (SR : Finset R) : 0 ≤ bipCutWeight x SL SR :=
  Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun r _ => by split_ifs <;> simp [hx]

lemma cutWeight_nonneg {V : Type*} [Fintype V] [DecidableEq V] (x : WGraph V) (S : Finset V) :
    0 ≤ cutWeight x S :=
  Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => x.nonneg u v

/-! ### Constants -/

/-- `ln(4n) ln ln(8n) ≤ 6 ln(2n) ln ln(4n)` for `n ≥ 1`: the sparsifier of `bipGraph x` has
`|L ⊕ R| = 2n` vertices. -/
lemma log_mul_loglog_le {n : ℝ} (hn : 1 ≤ n) :
    Real.log (4 * n) * Real.log (Real.log (8 * n)) ≤
      6 * (Real.log (2 * n) * Real.log (Real.log (4 * n))) := by
  have hl2 := Real.log_two_gt_d9
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn
  have h4 : Real.log (4 * n) = 2 * Real.log 2 + Real.log n := by
    rw [Real.log_mul (by norm_num) (by linarith), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]; push_cast; ring
  have h8 : Real.log (8 * n) = 3 * Real.log 2 + Real.log n := by
    rw [Real.log_mul (by norm_num) (by linarith), show (8 : ℝ) = 2 ^ 3 by norm_num,
      Real.log_pow]; push_cast; ring
  have h2 : Real.log (2 * n) = Real.log 2 + Real.log n := by
    rw [Real.log_mul (by norm_num) (by linarith)]
  set a := Real.log (4 * n) with ha
  have ha1 : 1 ≤ a := by linarith
  -- `ln(8n) ≤ (3/2) ln(4n) ≤ ln(4n)^3`
  have hcube : Real.log (8 * n) ≤ a ^ 3 := by
    have : a ^ 3 ≥ a * (1.38 : ℝ) ^ 2 := by
      have : a ^ 2 ≥ (1.38 : ℝ) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have hll : Real.log (Real.log (8 * n)) ≤ 3 * Real.log a := by
    have h3 : Real.log (a ^ 3) = 3 * Real.log a := by rw [Real.log_pow]; norm_num
    rw [← h3]
    exact Real.log_le_log (by linarith) hcube
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha1
  have hll0 : 0 ≤ Real.log (Real.log (8 * n)) := Real.log_nonneg (by linarith)
  calc a * Real.log (Real.log (8 * n)) ≤ (2 * Real.log (2 * n)) * (3 * Real.log a) :=
        mul_le_mul (by linarith) hll hll0 (by linarith)
    _ = _ := by ring

end Theorem14

open Theorem14

/-- **Theorem 1.4 (bipartite).** Assuming [RS14]: there is an absolute constant `C > 0` such that
for every bipartite graph `(L ∪ R, E, x)` with `|L| = |R| = n` and every fractional perfect
matching `x` there is a perfect matching `M ⊆ L × R` (not necessarily in `supp(x)`) with
`|M ∩ δ(S)| ≤ C ln(2n) ln ln(4n) · x(δ(S))` for all `S ⊆ L ∪ R`. -/
theorem theorem14_bip (hRS : RackeShahTheorem) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L R : Type) [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
      (x : L → R → ℝ), IsFracPMBip x → Fintype.card L = Fintype.card R →
      ∃ π : L ≃ R, IsThinBip (C * Real.log (2 * Fintype.card L) *
        Real.log (Real.log (4 * Fintype.card L))) x π := by
  obtain ⟨C, hC, hRS⟩ := hRS
  refine ⟨6 * C, by positivity, ?_⟩
  intro L R _ _ _ _ x hx hcard
  rcases Nat.eq_zero_or_pos (Fintype.card L) with h0 | hpos
  · -- `n = 0`: nothing to prove
    refine ⟨Fintype.equivOfCardEq hcard, fun SL SR => ?_⟩
    have : IsEmpty L := Fintype.card_eq_zero_iff.1 h0
    rw [h0]
    simp [bipCrossCount]
  have : Nonempty (L ⊕ R) := ⟨Sum.inl (Fintype.card_pos_iff.1 hpos).some⟩
  -- Theorem 2.2: a tree-cut sparsifier of `bipGraph x` on `L ⊕ R`
  obtain ⟨N, _, _, T, y, e, hT⟩ := hRS (L ⊕ R) (bipGraph x hx.nonneg)
  -- Lemma 4.6: a perfect matching with `load(f_v) = Δ_bip(V ∩ subtree T v)`
  obtain ⟨π, hπ⟩ := lemma46_bip T (e ∘ Sum.inl) (e ∘ Sum.inr) hcard
  refine ⟨π, fun SL SR => ?_⟩
  -- Proposition 4.3 with `β = 1`, using Lemma 4.5 for `Δ_bip ≤ x(δ(·))`
  have hthin := prop43 hT zero_le_one (bipPM π) fun v hv => by
    rw [load_bipPM, hπ v hv, one_mul, cutWeight_bipGraph]
    unfold discBip
    rw [Nat.cast_natAbs]
    push_cast
    convert lemma45_bip hx _ _ using 3 <;> simp
  have h := hthin (SL.disjSum SR)
  rw [crossCount_bipPM, cutWeight_bipGraph] at h
  have hSL : ({l | Sum.inl l ∈ SL.disjSum SR} : Finset L) = SL := by ext; simp
  have hSR : ({r | Sum.inr r ∈ SL.disjSum SR} : Finset R) = SR := by ext; simp
  rw [hSL, hSR] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (bipCutWeight_nonneg hx.nonneg SL SR))
  -- adjusting the constant: `|L ⊕ R| = 2n`
  have hn : (1 : ℝ) ≤ Fintype.card L := by exact_mod_cast hpos
  have hcardV : (Fintype.card (L ⊕ R) : ℝ) = 2 * Fintype.card L := by
    rw [Fintype.card_sum, ← hcard]; push_cast; ring
  rw [hcardV, one_mul, show 2 * (2 * (Fintype.card L : ℝ)) = 4 * Fintype.card L by ring,
    show 4 * (2 * (Fintype.card L : ℝ)) = 8 * Fintype.card L by ring]
  have := log_mul_loglog_le hn
  nlinarith

/-- **Theorem 1.4 (general graphs).** Assuming [RS14]: there is an absolute constant `C > 0` such
that for every graph with `|V| = 2n` and `x ∈ PM(G)` there is a perfect matching `M ⊆ (V choose 2)`
(not necessarily in `supp(x)`) that is `C ln(4n) ln ln(8n)`-thin. -/
theorem theorem14 (hRS : RackeShahTheorem) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (x : WGraph V), IsFracPM x →
      ∃ M : PerfectMatching V, IsThin (C * Real.log (2 * Fintype.card V) *
        Real.log (Real.log (4 * Fintype.card V))) x M := by
  obtain ⟨C, hC, hRS⟩ := hRS
  refine ⟨C, hC, ?_⟩
  intro V _ _ x hx
  -- `x ∈ PM(G)` forces a perfect matching to exist, hence `|V|` is even
  obtain ⟨M₀⟩ : Nonempty (PerfectMatching V) := by
    obtain ⟨c, -, hc1, -⟩ := hx
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hc1
  have heven : Even (Fintype.card V) := by
    by_contra hodd
    have := one_le_crossCount_of_odd M₀ (S := univ)
      (by rw [Finset.card_univ]; exact Nat.not_even_iff_odd.1 hodd)
    simp [crossCount] at this
  rcases isEmpty_or_nonempty V with hV | hV
  · refine ⟨M₀, fun S => ?_⟩
    simp [crossCount, Finset.eq_empty_of_isEmpty S]
  -- Theorem 2.2: a tree-cut sparsifier of `x`
  obtain ⟨N, _, _, T, y, e, hT⟩ := hRS V x
  -- Lemma 4.6: a perfect matching with `load(f_v) = Δ_non-bip(V ∩ subtree T v)`
  obtain ⟨M, hM⟩ := lemma46 T e heven
  refine ⟨M, ?_⟩
  -- Proposition 4.3 with `β = 1`, using Lemma 4.5 for `Δ_non-bip ≤ x(δ(·))`
  have hthin := prop43 hT zero_le_one M fun v hv => by
    rw [hM v hv, one_mul]
    unfold discNonBip
    split_ifs with hodd
    · exact_mod_cast lemma45 hx hodd
    · simpa using cutWeight_nonneg x _
  rwa [one_mul] at hthin

end ThinMatching
