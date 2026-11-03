/-
# Cutting paths into blocks and closing them into cycles

This file formalises the purely combinatorial part of the proof of Proposition 32 (App. D.2,
p. 29, l. 910–921):

> Let `μ` be the partial injective map on `V` …  In the directed graph on `V` with the edges
> `v → μ(v)`, every vertex has in- and outdegree at most 1.  Thus it decomposes into directed
> cycles and exactly `m` directed paths …  We keep all cycles, cut every path into consecutive
> blocks of `ℓ` vertices (plus a final shorter block), discard all edges between blocks, and close
> every block `v₁ → ⋯ → v_k` by adding the closing edge `v_k → v₁` …  The resulting directed cycles
> define a permutation `τ` of `V`. …  The number of closing edges is at most
> `∑_j ⌈p_j/ℓ⌉ ≤ m + n/ℓ` …

Formalisation.  A partial map is a function `μ : V → Option V`; `iter μ k v` is its `k`-th
iterate.  The construction proceeds in two steps, exactly as in the paper:

1. *Cutting* (`cutMap`): along each path, the vertex at position `p` (counted from the start of
   the path, `p = depth μ v`) loses its outgoing edge if `p ≡ ℓ - 1 (mod ℓ)`.  This cuts every
   path into blocks of `ℓ` vertices plus a final shorter block.  At most `n/ℓ` edges are cut
   (`card_cutSet_mul_le`), since each cut vertex owns the `ℓ` vertices of its block.
2. *Closing* (`exists_perm_close`): every block `v₁ → ⋯ → v_k` is closed by the edge
   `v_k → v₁`.  All other edges `v → μ(v)` are retained.

The main result is `exists_perm_of_partialInj`: there is a permutation `τ` and a set `B` of
"starting points of closing edges" with `ℓ |B| ≤ ℓ m + n`, such that `τ(v) = μ(v)` for `v ∉ B`, and
for `v ∈ B` the vertex `v` is reached from `τ(v)` (the start of its block) in fewer than `ℓ`
`μ`-steps.
-/
import Mathlib

open Finset

namespace GsimOT.PathCutting

variable {V : Type*}

/-- The `k`-th iterate of a partial map `μ : V → Option V`. -/
def iter (μ : V → Option V) : ℕ → V → Option V
  | 0, v => some v
  | k + 1, v => (iter μ k v).bind μ

/-- `μ` is injective where defined. -/
def PInj (μ : V → Option V) : Prop := ∀ a b c, μ a = some c → μ b = some c → a = b

/-- `v` does not lie on a cycle of `μ`: some iterate is undefined. -/
def NonCycle (μ : V → Option V) (v : V) : Prop := ∃ K, iter μ K v = none

section Iter

variable (μ : V → Option V)

@[simp] lemma iter_zero (v : V) : iter μ 0 v = some v := rfl

lemma iter_succ (k : ℕ) (v : V) : iter μ (k + 1) v = (iter μ k v).bind μ := rfl

@[simp] lemma iter_one (v : V) : iter μ 1 v = μ v := by simp [iter]

lemma iter_add (a b : ℕ) (v : V) : iter μ (a + b) v = (iter μ a v).bind (iter μ b) := by
  induction b with
  | zero => cases iter μ a v <;> rfl
  | succ b ih =>
    rw [← add_assoc, iter_succ, ih]
    cases iter μ a v <;> rfl

lemma iter_succ' (k : ℕ) (v : V) : iter μ (k + 1) v = (μ v).bind (iter μ k) := by
  rw [add_comm, iter_add, iter_one]

lemma iter_none_of_le {a b : ℕ} {v : V} (h : iter μ a v = none) (hab : a ≤ b) :
    iter μ b v = none := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [iter_add, h]; rfl

lemma iter_some_of_le {i k : ℕ} {v x : V} (h : iter μ k v = some x) (hik : i ≤ k) :
    ∃ y, iter μ i v = some y := by
  rcases hi : iter μ i v with _ | y
  · rw [iter_none_of_le μ hi hik] at h; cases h
  · exact ⟨y, rfl⟩

lemma iter_add_of_some {a b : ℕ} {v x : V} (h : iter μ a v = some x) :
    iter μ (a + b) v = iter μ b x := by
  rw [iter_add, h]; rfl

lemma iter_inj (hμ : PInj μ) : ∀ (k : ℕ) (a b c : V),
    iter μ k a = some c → iter μ k b = some c → a = b := by
  intro k
  induction k with
  | zero => intro a b c ha hb; simp at ha hb; rw [ha, hb]
  | succ k ih =>
    intro a b c ha hb
    rw [iter_succ, Option.bind_eq_some_iff] at ha hb
    obtain ⟨a', ha', ha'c⟩ := ha
    obtain ⟨b', hb', hb'c⟩ := hb
    have := hμ a' b' c ha'c hb'c
    subst this
    exact ih a b a' ha' hb'

lemma nonCycle_of_iter {v y : V} {i : ℕ} (hv : NonCycle μ v) (h : iter μ i v = some y) :
    NonCycle μ y := by
  obtain ⟨K, hK⟩ := hv
  by_cases hKi : K ≤ i
  · rw [iter_none_of_le μ hK hKi] at h; cases h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hKi)
    exact ⟨j, by rw [← iter_add_of_some μ h]; exact hK⟩

lemma iter_periodic {p : ℕ} {x : V} (h : iter μ p x = some x) :
    ∀ t, iter μ (t * p) x = some x := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.succ_mul, iter_add_of_some μ ih, h]

/-- Paths are short: if `v` is not on a cycle and is reached from `s` in `k` steps, then `k < n`.
(Pigeonhole: otherwise the walk from `s` revisits a vertex, so `v` lies on a cycle.) -/
lemma lt_card_of_iter [Fintype V] {s v : V} {k : ℕ} (hv : NonCycle μ v)
    (h : iter μ k s = some v) : k < Fintype.card V := by
  by_contra hk
  push Not at hk
  set n := Fintype.card V
  let f : Fin (n + 1) → V := fun i => (iter μ i s).getD s
  have hf : ∀ i : Fin (n + 1), iter μ i s = some (f i) := by
    intro i
    obtain ⟨y, hy⟩ := iter_some_of_le μ h (show (i : ℕ) ≤ k by have := i.isLt; omega)
    simp [f, hy]
  have key : ∀ i j : Fin (n + 1), (i : ℕ) < j → f i = f j → False := by
    intro i j hij hfij
    set x := f i
    have hper : iter μ ((j : ℕ) - i) x = some x := by
      have := hf j
      rw [show (j : ℕ) = i + ((j : ℕ) - i) by omega, iter_add_of_some μ (hf i)] at this
      rw [this, hfij]
    have hxv : iter μ (k - i) x = some v := by
      have := h
      rw [show k = i + (k - i) by have := i.isLt; omega, iter_add_of_some μ (hf i)] at this
      exact this
    obtain ⟨K, hK⟩ := hv
    have hnone : iter μ (k - i + K) x = none := by rw [iter_add_of_some μ hxv, hK]
    have hsome := iter_periodic μ hper (k - i + K)
    rw [iter_none_of_le μ hnone (show k - i + K ≤ (k - i + K) * ((j : ℕ) - i) from
      Nat.le_mul_of_pos_right _ (by omega))] at hsome
    cases hsome
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp [n])
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h1 | h1
  · exact key i j h1 hfij
  · exact key j i h1 hfij.symm

end Iter

/-! ### Depth: the position of a vertex on its path -/

section Depth

variable [Fintype V] (μ : V → Option V)

open Classical in
/-- The position of `v` on its path, i.e. the length of the longest walk ending in `v`
(bounded by `n`; for vertices not on a cycle this is the distance from the start of the path). -/
noncomputable def depth (v : V) : ℕ :=
  Nat.findGreatest (fun k => ∃ s, iter μ k s = some v) (Fintype.card V)

lemma depth_spec (v : V) : ∃ s, iter μ (depth μ v) s = some v := by
  classical
  exact Nat.findGreatest_spec (P := fun k => ∃ s, iter μ k s = some v) (Nat.zero_le _)
    ⟨v, rfl⟩

lemma le_depth {v s : V} {k : ℕ} (hv : NonCycle μ v) (h : iter μ k s = some v) :
    k ≤ depth μ v := by
  classical
  exact Nat.le_findGreatest (lt_card_of_iter μ hv h).le ⟨s, h⟩

variable {μ}

lemma depth_step (hμ : PInj μ) {v x : V} (hv : NonCycle μ v) (hx : μ v = some x) :
    depth μ x = depth μ v + 1 := by
  have hxnc : NonCycle μ x := nonCycle_of_iter μ hv (i := 1) (by simpa using hx)
  apply le_antisymm
  · obtain ⟨s, hs⟩ := depth_spec μ x
    rcases hd : depth μ x with _ | j
    · omega
    · rw [hd, iter_succ, Option.bind_eq_some_iff] at hs
      obtain ⟨y, hy, hyx⟩ := hs
      have := hμ y v x hyx hx
      subst this
      have := le_depth μ hv hy
      omega
  · obtain ⟨s, hs⟩ := depth_spec μ v
    refine le_depth μ hxnc (s := s) ?_
    rw [iter_succ, hs]; simpa using hx

lemma depth_iter (hμ : PInj μ) {v : V} (hv : NonCycle μ v) :
    ∀ (i : ℕ) (y : V), iter μ i v = some y → depth μ y = depth μ v + i := by
  intro i
  induction i with
  | zero => intro y h; simp at h; subst h; simp
  | succ i ih =>
    intro y h
    rw [iter_succ, Option.bind_eq_some_iff] at h
    obtain ⟨y', hy', hy'y⟩ := h
    rw [depth_step hμ (nonCycle_of_iter μ hv hy') hy'y, ih y' hy']
    ring

end Depth

/-! ### Step 1: cutting the paths -/

section Cut

variable [Fintype V] [DecidableEq V] (μ : V → Option V) (ℓ : ℕ)

open Classical in
/-- The cut vertices: vertices on a path at a position `p ≡ ℓ - 1 (mod ℓ)`. -/
noncomputable def cutSet : Finset V := {v | NonCycle μ v ∧ depth μ v % ℓ = ℓ - 1}

open Classical in
/-- The partial map with the outgoing edges of all cut vertices removed. -/
noncomputable def cutMap (v : V) : Option V := if v ∈ cutSet μ ℓ then none else μ v

variable {μ ℓ}

lemma cutMap_le {a b : V} (h : cutMap μ ℓ a = some b) : μ a = some b := by
  unfold cutMap at h; split_ifs at h; exact h

lemma cutMap_pinj (hμ : PInj μ) : PInj (cutMap μ ℓ) :=
  fun a b c ha hb => hμ a b c (cutMap_le ha) (cutMap_le hb)

lemma iter_cutMap_le : ∀ (k : ℕ) (a b : V), iter (cutMap μ ℓ) k a = some b → iter μ k a = some b := by
  intro k
  induction k with
  | zero => intro a b h; exact h
  | succ k ih =>
    intro a b h
    rw [iter_succ, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨c, hc, hcb⟩ := h
    exact ⟨c, ih a c hc, cutMap_le hcb⟩

/-- At most `n / ℓ` vertices are cut: each cut vertex owns the `ℓ` vertices of its block. -/
lemma card_cutSet_mul_le (hμ : PInj μ) (hℓ : 1 ≤ ℓ) :
    (cutSet μ ℓ).card * ℓ ≤ Fintype.card V := by
  classical
  have hback : ∀ v ∈ cutSet μ ℓ, ∀ i < ℓ, ∃ x, iter μ i x = some v := by
    intro v hv i hi
    simp only [cutSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨s, hs⟩ := depth_spec μ v
    have hdi : i ≤ depth μ v := by
      have := Nat.mod_le (depth μ v) ℓ; omega
    obtain ⟨x, hx⟩ := iter_some_of_le μ hs (Nat.sub_le (depth μ v) i)
    refine ⟨x, ?_⟩
    have := iter_add_of_some μ hx (b := i)
    rw [Nat.sub_add_cancel hdi, hs] at this
    exact this.symm
  let g : V × ℕ → V := fun p =>
    if h : p.1 ∈ cutSet μ ℓ ∧ p.2 < ℓ then (hback p.1 h.1 p.2 h.2).choose else p.1
  have hg : ∀ p ∈ cutSet μ ℓ ×ˢ Finset.range ℓ, iter μ p.2 (g p) = some p.1 := by
    rintro ⟨v, i⟩ hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [g, dite_eq_left hp]
    exact (hback v hp.1 i hp.2).choose_spec
  have hinj : Set.InjOn g (cutSet μ ℓ ×ˢ Finset.range ℓ : Finset (V × ℕ)) := by
    rintro ⟨v, i⟩ hp ⟨w, j⟩ hq hpq
    have hp' := hg _ hp
    have hq' := hg _ hq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.coe_range,
      Set.mem_Iio] at hp hq
    simp only at hp' hq' hpq
    rw [hpq] at hp'
    set x := g (w, j)
    have hvnc : NonCycle μ v := by
      simp only [cutSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp; exact hp.1.1
    have hxnc : NonCycle μ x := by
      obtain ⟨K, hK⟩ := hvnc
      exact ⟨i + K, by rw [iter_add_of_some μ hp', hK]⟩
    have hdv := depth_iter hμ hxnc i v hp'
    have hdw := depth_iter hμ hxnc j w hq'
    have hmv : depth μ v % ℓ = ℓ - 1 := by
      simp only [cutSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp; exact hp.1.2
    have hmw : depth μ w % ℓ = ℓ - 1 := by
      simp only [cutSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq; exact hq.1.2
    have hij : i = j := by
      have hmod : (depth μ x + i) % ℓ = (depth μ x + j) % ℓ := by rw [← hdv, ← hdw, hmv, hmw]
      have := Nat.ModEq.add_left_cancel' (depth μ x) hmod
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hp.2, Nat.mod_eq_of_lt hq.2] at this
    subst hij
    rw [hp'] at hq'
    cases hq'
    rfl
  have := Finset.card_le_card_of_injOn g (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
  simpa [Finset.card_product] using this

/-- After cutting, every path has fewer than `ℓ` edges: `ℓ` steps from a vertex that is not on a
cycle always lead out of the domain. -/
lemma iter_cutMap_eq_none (hμ : PInj μ) (hℓ : 1 ≤ ℓ) {s : V}
    (hs : NonCycle (cutMap μ ℓ) s) : iter (cutMap μ ℓ) ℓ s = none := by
  classical
  -- `s` is not on a cycle of `μ` either (cycles are never cut).
  have hsμ : NonCycle μ s := by
    by_contra hcyc
    have hcyc' : ∀ K, iter μ K s ≠ none := fun K hK => hcyc ⟨K, hK⟩
    have heq : ∀ K, iter (cutMap μ ℓ) K s = iter μ K s := by
      intro K
      induction K with
      | zero => rfl
      | succ K ih =>
        rw [iter_succ, iter_succ, ih]
        rcases hy : iter μ K s with _ | y
        · exact absurd hy (hcyc' K)
        · have hyc : ¬ NonCycle μ y := by
            rintro ⟨K', hK'⟩
            exact hcyc' (K + K') (by rw [iter_add_of_some μ hy, hK'])
          simp [cutMap, cutSet, hyc]
    obtain ⟨K, hK⟩ := hs
    exact hcyc' K (by rw [← heq]; exact hK)
  -- the next cut position along the path
  set d := depth μ s
  set j₀ := ℓ - 1 - d % ℓ with hj₀
  have hmodlt := Nat.mod_lt d (show 0 < ℓ by omega)
  have hj₀ℓ : j₀ < ℓ := by omega
  have hdj : (d + j₀) % ℓ = ℓ - 1 := by
    have hdiv := Nat.div_add_mod d ℓ
    have : d + j₀ = ℓ * (d / ℓ) + (ℓ - 1) := by
      generalize ℓ * (d / ℓ) = P at hdiv; omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rcases hx : iter (cutMap μ ℓ) j₀ s with _ | x
  · exact iter_none_of_le _ hx hj₀ℓ.le
  · have hxμ := iter_cutMap_le j₀ s x hx
    have hdx := depth_iter hμ hsμ j₀ x hxμ
    have hxcut : x ∈ cutSet μ ℓ := by
      simp only [cutSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨nonCycle_of_iter μ hsμ hxμ, by rw [hdx, hdj]⟩
    have : iter (cutMap μ ℓ) (j₀ + 1) s = none := by
      rw [iter_succ, hx]; simp [cutMap, hxcut]
    exact iter_none_of_le _ this hj₀ℓ

end Cut

/-! ### Step 2: closing the blocks -/

section Close

variable [Fintype V] [DecidableEq V]

/-- Closing the blocks.  If all paths of the partial injection `ν` have fewer than `ℓ` edges,
then there is a permutation `τ` that agrees with `ν` where `ν` is defined and maps the end `v` of
each block to its start, from which `v` is reached in fewer than `ℓ` steps. -/
theorem exists_perm_close (ν : V → Option V) (hν : PInj ν) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hshort : ∀ s, NonCycle ν s → iter ν ℓ s = none) :
    ∃ τ : Equiv.Perm V, ∀ v, ν v = some (τ v) ∨
      (ν v = none ∧ ∃ k < ℓ, iter ν k (τ v) = some v) := by
  classical
  -- every block end has a start without predecessor, at distance `< ℓ`
  have hstart : ∀ v, ν v = none →
      ∃ s, (∃ k < ℓ, iter ν k s = some v) ∧ ∀ u, ν u ≠ some s := by
    intro v hv
    set P : ℕ → Prop := fun k => ∃ s, iter ν k s = some v
    set K := Nat.findGreatest P (ℓ - 1)
    obtain ⟨s, hs⟩ : P K := Nat.findGreatest_spec (P := P) (Nat.zero_le _) ⟨v, rfl⟩
    have hK : K ≤ ℓ - 1 := Nat.findGreatest_le _
    refine ⟨s, ⟨K, by omega, hs⟩, fun u hu => ?_⟩
    have hu' : iter ν (K + 1) u = some v := by rw [iter_succ', hu]; exact hs
    by_cases hK1 : K + 1 ≤ ℓ - 1
    · have := Nat.le_findGreatest (P := P) hK1 ⟨u, hu'⟩
      omega
    · have hKℓ : K + 1 = ℓ := by omega
      have hunc : NonCycle ν u := ⟨K + 2, by rw [iter_succ, hu']; simpa using hv⟩
      have := hshort u hunc
      rw [← hKℓ, hu'] at this
      cases this
  let start : V → V := fun v => if h : ν v = none then (hstart v h).choose else v
  let τf : V → V := fun v => (ν v).getD (start v)
  have hτf_some : ∀ v x, ν v = some x → τf v = x := by intro v x h; simp [τf, h]
  have hτf_none : ∀ v, ν v = none →
      (∃ k < ℓ, iter ν k (τf v) = some v) ∧ ∀ u, ν u ≠ some (τf v) := by
    intro v h
    have := (hstart v h).choose_spec
    simpa [τf, start, h] using this
  have hinj : Function.Injective τf := by
    intro v w hvw
    rcases hv : ν v with _ | a <;> rcases hw : ν w with _ | b
    · -- both are block ends with the same start
      obtain ⟨⟨k, -, hk⟩, -⟩ := hτf_none v hv
      obtain ⟨⟨k', -, hk'⟩, -⟩ := hτf_none w hw
      rw [hvw] at hk
      have key : ∀ {a b : V} {i j : ℕ}, i < j → iter ν i (τf w) = some a → ν a = none →
          iter ν j (τf w) = some b → False := by
        intro a b i j hij ha hna hb
        obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hij
        rw [show i + c + 1 = i + (c + 1) by ring, iter_add_of_some ν ha, iter_succ', hna] at hb
        cases hb
      rcases lt_trichotomy k k' with h | rfl | h
      · exact (key h hk hv hk').elim
      · rw [hk] at hk'; cases hk'; rfl
      · exact (key h hk' hw hk).elim
    · -- `w` is retained, `v` is a block end: the start has no predecessor
      exact absurd (by rw [hvw, hτf_some w b hw]; exact hw) ((hτf_none v hv).2 w)
    · exact absurd (by rw [← hvw, hτf_some v a hv]; exact hv) ((hτf_none w hw).2 v)
    · rw [hτf_some v a hv, hτf_some w b hw] at hvw
      subst hvw
      exact hν v w a hv hw
  let τ : Equiv.Perm V := Equiv.ofBijective τf (Finite.injective_iff_bijective.1 hinj)
  refine ⟨τ, fun v => ?_⟩
  rcases hv : ν v with _ | a
  · exact Or.inr ⟨rfl, (hτf_none v hv).1⟩
  · exact Or.inl (by simp [τ, hτf_some v a hv])

end Close

/-! ### The combined statement used in Proposition 32 -/

section Main

variable [Fintype V] [DecidableEq V]

/-- **Cutting paths into blocks of `ℓ` vertices and closing them.**
For every partial injection `μ` on `V` and every `ℓ ≥ 1` there are a permutation `τ` of `V` and a
set `B` (the starting points of closing edges) such that
* `τ(v) = μ(v)` for every `v ∉ B` (these edges are retained),
* `ℓ · |B| ≤ ℓ · m + n`, where `m` is the number of vertices on which `μ` is undefined,
  i.e. `|B| ≤ m + n/ℓ`,
* every `v ∈ B` is reached from `τ(v)` (the start of its block) in fewer than `ℓ` steps of `μ`. -/
theorem exists_perm_of_partialInj (μ : V → Option V) (hμ : PInj μ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ (τ : Equiv.Perm V) (B : Finset V),
      (∀ v, v ∉ B → μ v = some (τ v)) ∧
      ℓ * B.card ≤ ℓ * (Finset.univ.filter fun v => μ v = none).card + Fintype.card V ∧
      (∀ v ∈ B, ∃ k < ℓ, iter μ k (τ v) = some v) := by
  classical
  obtain ⟨τ, hτ⟩ := exists_perm_close (cutMap μ ℓ) (cutMap_pinj hμ) ℓ hℓ
    (fun s hs => iter_cutMap_eq_none hμ hℓ hs)
  refine ⟨τ, Finset.univ.filter fun v => cutMap μ ℓ v = none, ?_, ?_, ?_⟩
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases hτ v with h | h
    · exact cutMap_le h
    · exact absurd h.1 hv
  · have hsub : (Finset.univ.filter fun v => cutMap μ ℓ v = none) ⊆
        (Finset.univ.filter fun v => μ v = none) ∪ cutSet μ ℓ := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hv ⊢
      unfold cutMap at hv
      split_ifs at hv with h
      · exact Or.inr h
      · exact Or.inl hv
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (Finset.univ.filter fun v => μ v = none) (cutSet μ ℓ)
    have h3 := card_cutSet_mul_le hμ hℓ
    calc ℓ * (Finset.univ.filter fun v => cutMap μ ℓ v = none).card
        ≤ ℓ * ((Finset.univ.filter fun v => μ v = none).card + (cutSet μ ℓ).card) :=
          Nat.mul_le_mul_left _ (h1.trans h2)
      _ ≤ _ := by rw [Nat.mul_add, mul_comm ℓ (cutSet μ ℓ).card]; omega
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases hτ v with h | ⟨-, k, hk, hkv⟩
    · rw [hv] at h; cases h
    · exact ⟨k, hk, iter_cutMap_le k _ _ hkv⟩

end Main

end GsimOT.PathCutting
