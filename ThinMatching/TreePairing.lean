/-
# Lemma 4.6: the tree pairing algorithm (Algorithm 2)

[HOG26], Algorithm 2 and Lemma 4.6.

## Formalisation of Algorithm 2

Algorithm 2 processes the tree bottom-up; at a vertex `w` it greedily pairs the still unmatched
points of `subtree T w` (points of different colours in the bipartite case, arbitrary points in the
general case) and passes the leftover points to the parent.  The main observation of the proof of
Lemma 4.6 is that the algorithm matches a *maximal* set of pairs inside every subtree, so that
exactly `Δ(subtree T v)` points of `subtree T v` are passed across the edge `f_v`.

We formalise the greedy procedure recursively on the number of points, one pair at a time.  The
first pair formed by the bottom-up greedy procedure is a matchable pair (`l ∈ L, r ∈ R`, resp. two
distinct points) at a vertex `w` such that no proper subtree of `subtree T w` contains a matchable
pair; we take `w` with `|subtree T w|` minimal among all vertices whose subtree contains a matchable
pair, match such a pair `{a, b}` inside `subtree T w`, and recurse on the remaining points.  The
greedy invariant then appears as follows: for every edge `f_x` separating `a` from `b`,
`subtree T x ⊊ subtree T w` (laminarity of subtrees), so `subtree T x` contains no matchable pair;
hence all points of `subtree T x` have the colour of the one of `a, b` it contains (resp.
`subtree T x` contains only that point), and both `load(f_x)` and `Δ(subtree T x)` grow by exactly
one when the pair `{a, b}` is added.  Edges not separating `a` from `b` see neither their load nor
their discrepancy change.

* `mem_subtree`, `subtree_self`, `mem_subtree_root`, `subtree_trans`, `subtree_laminar`,
  `subtree_ssubset_of_separates` : basic facts on subtrees (laminarity).
* `lemma46_bip`, `lemma46` : Lemma 4.6 (bipartite and general case).
-/
import ThinMatching.Load

open Finset

namespace ThinMatching

variable {N : Type*} [Fintype N] [DecidableEq N]

section TreeLemmas

lemma mem_subtree (T : RootedTree N) {u v : N} : u ∈ subtree T v ↔ ∃ k, T.parent^[k] u = v := by
  simp [subtree]

lemma subtree_self (T : RootedTree N) (v : N) : v ∈ subtree T v :=
  (mem_subtree T).2 ⟨0, rfl⟩

lemma mem_subtree_root (T : RootedTree N) (u : N) : u ∈ subtree T T.root :=
  (mem_subtree T).2 (T.reach u)

lemma subtree_trans (T : RootedTree N) {u v w : N} (hwv : w ∈ subtree T v)
    (huw : u ∈ subtree T w) : u ∈ subtree T v := by
  obtain ⟨a, ha⟩ := (mem_subtree T).1 huw
  obtain ⟨b, hb⟩ := (mem_subtree T).1 hwv
  exact (mem_subtree T).2 ⟨b + a, by rw [Function.iterate_add_apply, ha, hb]⟩

/-- Laminarity: two subtrees containing a common vertex are nested. -/
lemma subtree_laminar (T : RootedTree N) {u v w : N} (hv : u ∈ subtree T v)
    (hw : u ∈ subtree T w) : v ∈ subtree T w ∨ w ∈ subtree T v := by
  obtain ⟨a, ha⟩ := (mem_subtree T).1 hv
  obtain ⟨b, hb⟩ := (mem_subtree T).1 hw
  rcases le_total a b with hab | hab
  · left
    refine (mem_subtree T).2 ⟨b - a, ?_⟩
    rw [← ha, ← Function.iterate_add_apply, Nat.sub_add_cancel hab, hb]
  · right
    refine (mem_subtree T).2 ⟨a - b, ?_⟩
    rw [← hb, ← Function.iterate_add_apply, Nat.sub_add_cancel hab, ha]

/-- If the edge `f_x` separates two vertices `a, b` of `subtree T w`, then `subtree T x` is a
proper subset of `subtree T w`. -/
lemma subtree_ssubset_of_separates (T : RootedTree N) {w x a b : N}
    (ha : a ∈ subtree T w) (hb : b ∈ subtree T w) (hax : a ∈ subtree T x)
    (hbx : b ∉ subtree T x) : subtree T x ⊂ subtree T w := by
  rcases subtree_laminar T hax ha with h | h
  · exact ⟨fun y hy => subtree_trans T h hy, fun hsub => hbx (hsub hb)⟩
  · exact absurd (subtree_trans T h hb) hbx

end TreeLemmas

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_filter_split (q : V → Prop) [DecidablePred q] (s : Finset V)
    (hs : ∀ x, x ∈ s ↔ ¬ q x) (p : V → Prop) [DecidablePred p] :
    #{u | p u} = #{u' : {u // q u} | p u'.1} + #{u ∈ s | p u} := by
  rw [card_filter, card_filter, card_filter, Finset.sum_subtype s hs,
    ← Fintype.sum_subtype_add_sum_subtype q]

lemma card_filter_split_ne (a : V) (p : V → Prop) [DecidablePred p] :
    #{u | p u} = #{u' : {u // u ≠ a} | p u'.1} + (if p a then 1 else 0) := by
  rw [card_filter_split (fun u => u ≠ a) {a} (by simp) p]
  congr 1
  rw [card_filter, sum_singleton]

lemma card_filter_split_ne₂ (a b : V) (hab : a ≠ b) (p : V → Prop) [DecidablePred p] :
    #{u | p u} = #{u' : {u // u ≠ a ∧ u ≠ b} | p u'.1} + (if p a then 1 else 0) +
      (if p b then 1 else 0) := by
  rw [card_filter_split (fun u => u ≠ a ∧ u ≠ b) {a, b} (by intro x; simp; tauto) p, add_assoc]
  congr 1
  rw [card_filter, sum_pair hab]

/-- Extending a perfect matching of `V - {a, b}` by the pair `{a, b}`. -/
lemma exists_pm_extend (a b : V) (hab : a ≠ b) (M' : PerfectMatching {u // u ≠ a ∧ u ≠ b}) :
    ∃ M : PerfectMatching V, M.1 a = b ∧ M.1 b = a ∧
      ∀ u (h : u ≠ a ∧ u ≠ b), M.1 u = (M'.1 ⟨u, h⟩).1 := by
  let f : V → V := fun u => if h : u ≠ a ∧ u ≠ b then (M'.1 ⟨u, h⟩).1 else if u = a then b else a
  have hfa : f a = b := by simp [f]
  have hfb : f b = a := by simp [f, hab.symm]
  have hfV : ∀ u (h : u ≠ a ∧ u ≠ b), f u = (M'.1 ⟨u, h⟩).1 := fun u h => by simp [f, h]
  have hinv : Function.Involutive f := by
    intro u
    by_cases h : u ≠ a ∧ u ≠ b
    · rw [hfV u h, hfV _ (M'.1 ⟨u, h⟩).2]
      simp [(M'.2 ⟨u, h⟩).1]
    · have : u = a ∨ u = b := by tauto
      rcases this with rfl | rfl
      · rw [hfa, hfb]
      · rw [hfb, hfa]
  refine ⟨⟨hinv.toPerm f, fun u => ⟨hinv u, ?_⟩⟩, hfa, hfb, hfV⟩
  simp only [Function.Involutive.coe_toPerm]
  by_cases h : u ≠ a ∧ u ≠ b
  · rw [hfV u h]
    intro he
    exact (M'.2 ⟨u, h⟩).2 (Subtype.ext he)
  · have : u = a ∨ u = b := by tauto
    rcases this with rfl | rfl
    · rw [hfa]; exact hab.symm
    · rw [hfb]; exact hab

end Counting

/-- **Lemma 4.6 (bipartite).** For a rooted tree `T` and points of `L` and `R` placed at tree
vertices (`|L| = |R|`), there is a perfect matching `π : L ≃ R` with
`load(f_v) = Δ_bip(V ∩ subtree T v)` for every tree edge `f_v`. -/
theorem lemma46_bip {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (T : RootedTree N) (eL : L → N) (eR : R → N) (hcard : Fintype.card L = Fintype.card R) :
    ∃ π : L ≃ R, ∀ v, v ≠ T.root → loadBip T eL eR π v = discBip T eL eR v := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card L = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing L R with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : IsEmpty L := Fintype.card_eq_zero_iff.mp hn
    have : IsEmpty R := Fintype.card_eq_zero_iff.mp (hcard ▸ hn)
    refine ⟨Fintype.equivOfCardEq hcard, fun v _ => ?_⟩
    simp [loadBip, discBip]
  · obtain ⟨l0⟩ : Nonempty L := Fintype.card_pos_iff.mp (hn ▸ hpos)
    obtain ⟨r0⟩ : Nonempty R := Fintype.card_pos_iff.mp (hcard ▸ hn ▸ hpos)
    -- a vertex `w` with `|subtree T w|` minimal whose subtree contains a matchable pair
    obtain ⟨w, hwQ, hwmin⟩ := Finset.exists_min_image
      (univ.filter fun w => ∃ (l : L) (r : R), eL l ∈ subtree T w ∧ eR r ∈ subtree T w)
      (fun w => #(subtree T w))
      ⟨T.root, mem_filter.2 ⟨mem_univ _, l0, r0, mem_subtree_root T _, mem_subtree_root T _⟩⟩
    obtain ⟨l1, r1, hl1, hr1⟩ := (mem_filter.1 hwQ).2
    -- no proper subtree of `subtree T w` contains a matchable pair
    have hkey : ∀ x (l : L) (r : R), eL l ∈ subtree T x → eR r ∈ subtree T x →
        subtree T x ⊂ subtree T w → False := by
      intro x l r hl hr hss
      exact absurd (card_lt_card hss)
        (not_lt.2 (hwmin x (mem_filter.2 ⟨mem_univ _, l, r, hl, hr⟩)))
    have hcL : Fintype.card {l // l ≠ l1} = n - 1 := by
      rw [Fintype.card_subtype, filter_ne', card_erase_of_mem (mem_univ _), card_univ, hn]
    have hcR : Fintype.card {r // r ≠ r1} = n - 1 := by
      rw [Fintype.card_subtype, filter_ne', card_erase_of_mem (mem_univ _), card_univ, ← hcard,
        hn]
    obtain ⟨π', hπ'⟩ := ih (n - 1) (by omega) (fun l : {l // l ≠ l1} => eL l.1)
      (fun r : {r // r ≠ r1} => eR r.1) (hcL.trans hcR.symm) hcL
    let π : L ≃ R := (Equiv.optionSubtypeNe l1).symm.trans
      ((Equiv.optionCongr π').trans (Equiv.optionSubtypeNe r1))
    have hπ1 : π l1 = r1 := by simp [π]
    have hπV : ∀ l (h : l ≠ l1), π l = (π' ⟨l, h⟩).1 := by
      intro l h
      simp [π, Equiv.optionSubtypeNe_symm_of_ne h]
    refine ⟨π, fun x hx => ?_⟩
    have hIH := hπ' x hx
    unfold loadBip discBip at hIH ⊢
    rw [card_filter_split_ne l1, card_filter_split_ne l1 (fun l => eL l ∈ subtree T x),
      card_filter_split_ne r1 (fun r => eR r ∈ subtree T x), hπ1]
    have hfl : (univ.filter fun l' : {l // l ≠ l1} =>
        ¬ (eL l'.1 ∈ subtree T x ↔ eR (π l'.1) ∈ subtree T x)) =
        univ.filter fun l' : {l // l ≠ l1} =>
        ¬ (eL l'.1 ∈ subtree T x ↔ eR (π' l').1 ∈ subtree T x) := by
      ext l'
      simp [hπV l'.1 l'.2]
    rw [hfl, hIH]
    by_cases h1 : eL l1 ∈ subtree T x <;> by_cases h2 : eR r1 ∈ subtree T x
    · simp only [h1, h2, ite_true, not_true_eq_false, ite_false]
      push_cast
      ring_nf
    · -- `subtree T x` contains `l1` but not `r1`: it contains no point of `R`
      have h0 : #{r' : {r // r ≠ r1} | eR r'.1 ∈ subtree T x} = 0 :=
        card_eq_zero.2 (filter_eq_empty_iff.2 fun r' _ hr' => hkey x l1 r'.1 h1 hr'
          (subtree_ssubset_of_separates T hl1 hr1 h1 h2))
      simp only [h1, h2, h0, ite_true, ite_false, iff_false, not_false_eq_true, not_true_eq_false]
      push_cast
      simp only [sub_zero, Int.natAbs_natCast]
      omega
    · -- `subtree T x` contains `r1` but not `l1`: it contains no point of `L`
      have h0 : #{l' : {l // l ≠ l1} | eL l'.1 ∈ subtree T x} = 0 :=
        card_eq_zero.2 (filter_eq_empty_iff.2 fun l' _ hl' => hkey x l'.1 r1 hl' h2
          (subtree_ssubset_of_separates T hr1 hl1 h2 h1))
      simp only [h1, h2, h0, ite_true, ite_false, false_iff, not_false_eq_true, not_true_eq_false]
      push_cast
      simp only [zero_sub, Int.natAbs_neg, Int.natAbs_natCast]
      omega
    · simp only [h1, h2, ite_false, not_true_eq_false, iff_self, add_zero]

/-- **Lemma 4.6 (general).** For a rooted tree `T` and an even number of points placed at tree
vertices, there is a perfect matching `M` with `load(f_v) = Δ_non-bip(V ∩ subtree T v)` for
every tree edge `f_v`. -/
theorem lemma46 {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree N) (e : V → N)
    (heven : Even (Fintype.card V)) :
    ∃ M : PerfectMatching V, ∀ v, v ≠ T.root → load T e M v = discNonBip T e v := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card V = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn
    refine ⟨⟨Equiv.refl V, fun v => isEmptyElim v⟩, fun v _ => ?_⟩
    simp [load, discNonBip]
  · have h1n : 1 < Fintype.card V := by
      obtain ⟨k, hk⟩ := heven
      omega
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h1n
    -- a vertex `w` with `|subtree T w|` minimal whose subtree contains two distinct points
    obtain ⟨w, hwQ, hwmin⟩ := Finset.exists_min_image
      (univ.filter fun w => ∃ u1 u2 : V, u1 ≠ u2 ∧ e u1 ∈ subtree T w ∧ e u2 ∈ subtree T w)
      (fun w => #(subtree T w))
      ⟨T.root, mem_filter.2 ⟨mem_univ _, a, b, hab, mem_subtree_root T _,
        mem_subtree_root T _⟩⟩
    obtain ⟨u1, u2, h12, hu1, hu2⟩ := (mem_filter.1 hwQ).2
    -- no proper subtree of `subtree T w` contains two distinct points
    have hkey : ∀ x (u u' : V), u ≠ u' → e u ∈ subtree T x → e u' ∈ subtree T x →
        subtree T x ⊂ subtree T w → False := by
      intro x u u' hne hu hu' hss
      exact absurd (card_lt_card hss)
        (not_lt.2 (hwmin x (mem_filter.2 ⟨mem_univ _, u, u', hne, hu, hu'⟩)))
    have hcard' : Fintype.card {u // u ≠ u1 ∧ u ≠ u2} = n - 2 := by
      rw [Fintype.card_subtype, ← hn]
      have : (univ.filter fun u => u ≠ u1 ∧ u ≠ u2) = univ \ {u1, u2} := by
        ext; simp
      rw [this, card_sdiff_of_subset (subset_univ _), card_pair h12, card_univ]
    obtain ⟨M', hM'⟩ := ih (n - 2) (by omega) (fun u : {u // u ≠ u1 ∧ u ≠ u2} => e u.1)
      (by
        rw [hcard']
        obtain ⟨k, hk⟩ := heven
        exact ⟨k - 1, by omega⟩) hcard'
    obtain ⟨M, hM1, hM2, hMV⟩ := exists_pm_extend u1 u2 h12 M'
    refine ⟨M, fun x hx => ?_⟩
    have hIH := hM' x hx
    unfold load discNonBip at hIH ⊢
    rw [card_filter_split_ne₂ u1 u2 h12, card_filter_split_ne₂ u1 u2 h12
      (fun u => e u ∈ subtree T x), hM1, hM2]
    have hfl : (univ.filter fun u' : {u // u ≠ u1 ∧ u ≠ u2} =>
        e u'.1 ∈ subtree T x ∧ e (M.1 u'.1) ∉ subtree T x) =
        univ.filter fun u' : {u // u ≠ u1 ∧ u ≠ u2} =>
        e u'.1 ∈ subtree T x ∧ e (M'.1 u').1 ∉ subtree T x := by
      ext u'
      simp [hMV u'.1 u'.2]
    rw [hfl, hIH]
    by_cases h1 : e u1 ∈ subtree T x <;> by_cases h2 : e u2 ∈ subtree T x
    · simp [h1, h2, Nat.odd_add_one]
    · -- `subtree T x` contains `u1` but no other point
      have h0 : #{u' : {u // u ≠ u1 ∧ u ≠ u2} | e u'.1 ∈ subtree T x} = 0 :=
        card_eq_zero.2 (filter_eq_empty_iff.2 fun u' _ hu' => hkey x u1 u'.1 (Ne.symm u'.2.1)
          h1 hu' (subtree_ssubset_of_separates T hu1 hu2 h1 h2))
      simp [h1, h2, h0]
    · -- `subtree T x` contains `u2` but no other point
      have h0 : #{u' : {u // u ≠ u1 ∧ u ≠ u2} | e u'.1 ∈ subtree T x} = 0 :=
        card_eq_zero.2 (filter_eq_empty_iff.2 fun u' _ hu' => hkey x u2 u'.1 (Ne.symm u'.2.2)
          h2 hu' (subtree_ssubset_of_separates T hu2 hu1 h2 h1))
      simp [h1, h2, h0]
    · simp [h1, h2]

end ThinMatching
