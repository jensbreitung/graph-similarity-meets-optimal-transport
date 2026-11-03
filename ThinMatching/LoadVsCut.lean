/-
# Proposition 4.3: load versus cut value

[HOG26], Proposition 4.3.

Proof outline (as in the paper).  Fix `S ⊆ V` and a tree cut `S' ⊆ 𝒱` projecting to `S` with
`y(δ_T(S')) = λ_T(S)`.  Every matching edge `{u, M u}` crossing `S` has its endpoints on different
sides of `S'`, so its tree path uses an edge `f_v ∈ δ_T(S')` (`exists_cut_edge`).  Charging each
crossing matching edge to such an `f_v` gives `|M ∩ δ(S)| ≤ ∑_{f_v ∈ δ_T(S')} load_M(f_v)`.
Since the single-edge tree cut `subtree T v` projects to `V ∩ subtree T v` and the sparsifier never
underestimates cuts, `load_M(f_v) ≤ β x(δ(V ∩ subtree T v)) ≤ β λ_T(V ∩ subtree T v) ≤ β y_v`.
Hence `|M ∩ δ(S)| ≤ β y(δ_T(S')) = β λ_T(S) ≤ β q x(δ(S))`.

The paper's "tree path between `a` and `b` uses `f`" is expressed here, in the parent-function
representation of trees, as "exactly one of `a`, `b` lies in `subtree T v`".
-/
import ThinMatching.Load

open Finset

namespace ThinMatching

variable {N : Type*} [Fintype N] [DecidableEq N] {V : Type*} [Fintype V] [DecidableEq V]

namespace LoadVsCut

/-! ### Elementary facts about rooted trees in the parent-function representation -/

/-- The depth of `u`: the number of parent steps from `u` to the root. -/
noncomputable def depth (T : RootedTree N) (u : N) : ℕ := by
  classical exact Nat.find (T.reach u)

lemma iterate_depth (T : RootedTree N) (u : N) : T.parent^[depth T u] u = T.root := by
  classical
  unfold depth
  convert Nat.find_spec (T.reach u)

lemma depth_le (T : RootedTree N) {u : N} {k : ℕ} (h : T.parent^[k] u = T.root) :
    depth T u ≤ k := by
  classical
  unfold depth
  convert Nat.find_min' (T.reach u) h

lemma iterate_root (T : RootedTree N) (k : ℕ) : T.parent^[k] T.root = T.root :=
  Function.iterate_fixed T.parent_root k

lemma depth_eq_zero (T : RootedTree N) {u : N} : depth T u = 0 ↔ u = T.root := by
  constructor
  · intro h; have := iterate_depth T u; rwa [h] at this
  · rintro rfl; exact Nat.le_zero.1 (depth_le T (k := 0) rfl)

lemma depth_parent (T : RootedTree N) {u : N} (hu : u ≠ T.root) :
    depth T (T.parent u) + 1 = depth T u := by
  have h0 : depth T u ≠ 0 := fun h => hu ((depth_eq_zero T).1 h)
  apply le_antisymm
  · have : T.parent^[depth T u - 1] (T.parent u) = T.root := by
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.2 h0), iterate_depth]
    have := depth_le T this
    omega
  · apply depth_le
    rw [Function.iterate_succ_apply, iterate_depth]

/-- Walking `k` steps up from `u` without reaching the root decreases the depth by `k`. -/
lemma depth_iterate (T : RootedTree N) :
    ∀ (k : ℕ) (u : N), T.parent^[k] u ≠ T.root → depth T (T.parent^[k] u) + k = depth T u := by
  intro k
  induction k with
  | zero => intro u _; simp
  | succ k ih =>
    intro u hu
    have hu0 : u ≠ T.root := by
      rintro rfl; exact hu (iterate_root T _)
    rw [Function.iterate_succ_apply] at hu ⊢
    rw [← depth_parent T hu0, ← ih _ hu]
    omega

lemma mem_subtree (T : RootedTree N) {u v : N} : u ∈ subtree T v ↔ ∃ k, T.parent^[k] u = v := by
  simp [subtree]

lemma self_mem_subtree (T : RootedTree N) (v : N) : v ∈ subtree T v :=
  (mem_subtree T).2 ⟨0, rfl⟩

/-- `parent v` does not lie below `v` (acyclicity). -/
lemma parent_notMem_subtree (T : RootedTree N) {v : N} (hv : v ≠ T.root) :
    T.parent v ∉ subtree T v := by
  rw [mem_subtree]
  rintro ⟨k, hk⟩
  have h := depth_iterate T (k + 1) v (by rw [Function.iterate_succ_apply, hk]; exact hv)
  rw [Function.iterate_succ_apply, hk] at h
  omega

/-- For `w ≠ v`, the tree edge `f_w = {w, parent w}` does not separate `subtree T v`. -/
lemma parent_mem_subtree_iff (T : RootedTree N) {v w : N} (hwv : w ≠ v) :
    T.parent w ∈ subtree T v ↔ w ∈ subtree T v := by
  simp only [mem_subtree]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k + 1, by rwa [Function.iterate_succ_apply]⟩
  · rintro ⟨k, hk⟩
    cases k with
    | zero => exact absurd hk hwv
    | succ k => exact ⟨k, by rwa [Function.iterate_succ_apply] at hk⟩

/-- **Charging lemma.**  If `a` and `b` are on different sides of the tree cut `S'`, then some
tree edge `f_v ∈ δ_T(S')` lies on the tree path between `a` and `b`, i.e. exactly one of `a`, `b`
lies in `subtree T v`.  (Walk up from the deeper of the two vertices.) -/
theorem exists_cut_edge (T : RootedTree N) (S' : Finset N) {a b : N}
    (hab : ¬ (a ∈ S' ↔ b ∈ S')) :
    ∃ v, v ≠ T.root ∧ ¬ (v ∈ S' ↔ T.parent v ∈ S') ∧
      ¬ (a ∈ subtree T v ↔ b ∈ subtree T v) := by
  suffices H : ∀ n a b, depth T a + depth T b = n → ¬ (a ∈ S' ↔ b ∈ S') →
      ∃ v, v ≠ T.root ∧ ¬ (v ∈ S' ↔ T.parent v ∈ S') ∧
        ¬ (a ∈ subtree T v ↔ b ∈ subtree T v) from H _ a b rfl hab
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have main : ∀ a b, depth T b ≤ depth T a → depth T a + depth T b = n →
      ¬ (a ∈ S' ↔ b ∈ S') → ∃ v, v ≠ T.root ∧ ¬ (v ∈ S' ↔ T.parent v ∈ S') ∧
        ¬ (a ∈ subtree T v ↔ b ∈ subtree T v) := by
    intro a b hle hn hab
    have ha : a ≠ T.root := by
      rintro rfl
      have hb : b = T.root := (depth_eq_zero T).1 (by have := (depth_eq_zero T).2 rfl; omega)
      exact hab (by rw [hb])
    by_cases hp : (a ∈ S' ↔ T.parent a ∈ S')
    · -- the edge `f_a` is not cut: continue from `parent a`
      have hd := depth_parent T ha
      obtain ⟨v, hv0, hvcut, hvsep⟩ :=
        ih (depth T (T.parent a) + depth T b) (by omega) (T.parent a) b rfl (by tauto)
      have hva : a ≠ v := by rintro rfl; exact hvcut hp
      refine ⟨v, hv0, hvcut, ?_⟩
      rwa [← parent_mem_subtree_iff T hva]
    · -- the edge `f_a` is cut and separates `a` from `b`
      refine ⟨a, ha, hp, fun h => ?_⟩
      obtain ⟨k, hk⟩ := (mem_subtree T).1 (h.1 (self_mem_subtree T a))
      have := depth_iterate T k b (by rw [hk]; exact ha)
      rw [hk] at this
      have hk0 : k = 0 := by omega
      subst hk0
      exact hab (by simp only [Function.iterate_zero, id] at hk; rw [hk])
  intro a b hn hab
  rcases le_total (depth T b) (depth T a) with h | h
  · exact main a b h hn hab
  · obtain ⟨v, h1, h2, h3⟩ := main b a h (by omega) (by tauto)
    exact ⟨v, h1, h2, by tauto⟩

/-- The single-edge tree cut `subtree T v` has value `y_v`. -/
theorem treeCutWeight_subtree (T : RootedTree N) (y : N → ℝ) {v : N} (hv : v ≠ T.root) :
    treeCutWeight T y (subtree T v) = y v := by
  unfold treeCutWeight
  rw [Finset.sum_eq_single v]
  · simp [hv, self_mem_subtree, parent_notMem_subtree T hv]
  · intro w _ hwv
    rw [ite_eq_right_iff]
    rintro ⟨_, h⟩
    exact absurd (parent_mem_subtree_iff T hwv).symm h
  · simp

lemma treeCutWeight_nonneg (T : RootedTree N) {y : N → ℝ} (hy : ∀ v, 0 ≤ y v) (S' : Finset N) :
    0 ≤ treeCutWeight T y S' :=
  Finset.sum_nonneg fun v _ => by split_ifs <;> simp [hy]

end LoadVsCut

open LoadVsCut

/-- **Proposition 4.3.** Let `T` be a `q`-tree-cut-sparsifier of `x`.  If a perfect matching `M`
satisfies `load_M(f_v) ≤ β x(δ(V ∩ subtree T v))` for every tree edge `f_v`, then `M` is
`β q`-thin. -/
theorem prop43 {q β : ℝ} {x : WGraph V} {T : RootedTree N} {y : N → ℝ} {e : V ↪ N}
    (hT : IsTreeCutSparsifier q x T y e) (hβ : 0 ≤ β) (M : PerfectMatching V)
    (hload : ∀ v, v ≠ T.root →
      (load T e M v : ℝ) ≤ β * cutWeight x (univ.filter fun u => e u ∈ subtree T v)) :
    IsThin (β * q) x M := by
  intro S
  obtain ⟨hy, hsp⟩ := hT
  -- an optimal tree cut `S'` projecting to `S`: `y(δ_T(S')) = λ_T(S)`
  have : Nonempty {S' : Finset N // univ.filter (fun v => e v ∈ S') = S ∨
      univ.filter (fun v => e v ∈ S') = Sᶜ} :=
    ⟨⟨S.map e, Or.inl (by ext v; simp)⟩⟩
  obtain ⟨⟨S', hS'⟩, hopt⟩ := exists_eq_ciInf_of_finite
    (f := fun S' : {S' : Finset N // univ.filter (fun v => e v ∈ S') = S ∨
      univ.filter (fun v => e v ∈ S') = Sᶜ} => treeCutWeight T y S'.1)
  have hlam : treeCutWeight T y S' = lambdaT T y e S := hopt
  -- crossing matching edges have their endpoints on different sides of `S'`
  have hsep : ∀ u ∈ S, M.1 u ∉ S → ¬ (e u ∈ S' ↔ e (M.1 u) ∈ S') := by
    intro u hu hMu
    have key : ∀ w, e w ∈ S' ↔ w ∈ univ.filter (fun v => e v ∈ S') := by simp
    rw [key, key]
    rcases hS' with h | h <;> rw [h] <;> simp [hu, hMu]
  -- the cut tree edges `δ_T(S')`
  let C : Finset N := univ.filter fun v => v ≠ T.root ∧ ¬ (v ∈ S' ↔ T.parent v ∈ S')
  have hTC : treeCutWeight T y S' = ∑ v ∈ C, y v := by
    unfold treeCutWeight; rw [Finset.sum_filter]
  -- charging: `|M ∩ δ(S)| ≤ ∑_{f_v ∈ δ_T(S')} #(crossing edges whose path uses f_v)`
  let D : N → Finset V := fun v =>
    {u ∈ S | M.1 u ∉ S ∧ ¬ (e u ∈ subtree T v ↔ e (M.1 u) ∈ subtree T v)}
  have h1 : (crossCount M S : ℝ) ≤ ∑ v ∈ C, (#(D v) : ℝ) := by
    have hsub : {u ∈ S | M.1 u ∉ S} ⊆ C.biUnion D := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨v, hv0, hvcut, hvsep⟩ := exists_cut_edge T S' (hsep u hu.1 hu.2)
      exact Finset.mem_biUnion.2 ⟨v, by simp [C, hv0, hvcut], by simp [D, hu.1, hu.2, hvsep]⟩
    have := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    unfold crossCount
    exact_mod_cast this
  -- each `f_v` is charged at most `load_M(f_v)` times
  have h2 : ∀ v, #(D v) ≤ load T e M v := by
    intro v
    unfold load
    refine Finset.card_le_card_of_injOn (fun u => if e u ∈ subtree T v then u else M.1 u)
      ?_ ?_
    · intro u hu
      simp only [D, Finset.coe_filter, Set.mem_ofPred_eq] at hu
      obtain ⟨_, _, h⟩ := hu
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      split_ifs with h' <;> simp_all [(M.2 u).1]
    · intro u₁ hu₁ u₂ hu₂ h
      simp only [D, Finset.coe_filter, Set.mem_ofPred_eq] at hu₁ hu₂
      have hinj := M.1.injective
      dsimp only at h
      split_ifs at h with h₁ h₂ h₂
      · exact h
      · exact absurd (h ▸ hu₁.1) hu₂.2.1
      · exact absurd (h ▸ hu₂.1) hu₁.2.1
      · exact hinj h
  -- `load_M(f_v) ≤ β x(δ(V ∩ subtree T v)) ≤ β λ_T(V ∩ subtree T v) ≤ β y_v`
  have h3 : ∀ v ∈ C, (load T e M v : ℝ) ≤ β * y v := by
    intro v hv
    have hv0 : v ≠ T.root := (Finset.mem_filter.1 hv).2.1
    refine (hload v hv0).trans (mul_le_mul_of_nonneg_left ?_ hβ)
    refine ((hsp _).1).trans ?_
    rw [← treeCutWeight_subtree T y hv0]
    exact ciInf_le (f := fun S'' : {S'' : Finset N // univ.filter (fun u => e u ∈ S'') =
        univ.filter (fun u => e u ∈ subtree T v) ∨ univ.filter (fun u => e u ∈ S'') =
        (univ.filter (fun u => e u ∈ subtree T v))ᶜ} => treeCutWeight T y S''.1)
      ⟨0, by rintro _ ⟨S'', rfl⟩; exact treeCutWeight_nonneg T hy _⟩ ⟨subtree T v, Or.inl rfl⟩
  calc (crossCount M S : ℝ) ≤ ∑ v ∈ C, (#(D v) : ℝ) := h1
    _ ≤ ∑ v ∈ C, β * y v :=
        Finset.sum_le_sum fun v hv => (Nat.cast_le.2 (h2 v)).trans (h3 v hv)
    _ = β * lambdaT T y e S := by rw [← Finset.mul_sum, ← hTC, hlam]
    _ ≤ β * (q * cutWeight x S) := mul_le_mul_of_nonneg_left (hsp S).2 hβ
    _ = β * q * cutWeight x S := by ring

end ThinMatching
