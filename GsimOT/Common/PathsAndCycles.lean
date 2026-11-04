import GsimOT.Common.MatrixNorms

/-!
# Disjoint unions of paths and cycles

The reductions of Section 4 (proofs in Appendix G, pp. 50–57) compare a disjoint union of paths `F₁`
with a disjoint union of paths (Theorem 15) or cycles (Theorems 16 and 17). This file defines
these graphs and computes their degrees and edge counts.

* `pathUnion a`: the disjoint union of paths on `a i` vertices, `i : ι`;
* `cycleUnion m A`: the disjoint union of `m` cycles on `A` vertices each.

Vertex `⟨i, x⟩` is the `x`-th vertex of the `i`-th component. Degrees are `deg` from
`GsimOT.Common.Basic`, the row sums of `A_G` (`sum_adj_eq_deg`), and by symmetry also its column
sums (`sum_adj_eq_deg'`).
-/

open Finset

namespace GsimOT.Hardness

/-! ### Degrees -/

section Degree

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The degree is also the column sum of the adjacency matrix. -/
lemma sum_adj_eq_deg' (v : V) : ∑ u, adj G u v = (deg G v : ℝ) := by
  rw [← sum_adj_eq_deg]
  exact sum_congr rfl fun u _ ↦ adj_symm G u v

lemma one_le_deg {u v : V} (h : G.Adj u v) : 1 ≤ (deg G v : ℝ) := by
  rw [← sum_adj_eq_deg]
  calc (1 : ℝ) = adj G v u := by simp [adj, h.symm]
    _ ≤ ∑ v', adj G v v' := single_le_sum (fun v' _ ↦ adj_nonneg G v v') (mem_univ u)

end Degree

lemma sigma_ext_val {ι : Type*} {a : ι → ℕ} {u v : Σ i, Fin (a i)} (h1 : u.1 = v.1)
    (h2 : (u.2 : ℕ) = v.2) : u = v := by
  obtain ⟨i, x⟩ := u
  obtain ⟨j, y⟩ := v
  dsimp only at h1 h2
  subst h1
  rw [Fin.val_inj] at h2
  rw [h2]

/-! ### Unions of paths -/

section Paths

variable {ι : Type*} (a : ι → ℕ)

/-- The disjoint union of paths on `a i` vertices, `i : ι`. -/
def pathUnion : SimpleGraph (Σ i, Fin (a i)) where
  Adj u v := u.1 = v.1 ∧ ((u.2 : ℕ) + 1 = v.2 ∨ (v.2 : ℕ) + 1 = u.2)
  symm := ⟨fun _ _ ⟨h1, h2⟩ ↦ ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨fun _ ⟨_, h⟩ ↦ by omega⟩

instance [DecidableEq ι] : DecidableRel (pathUnion a).Adj := fun u v ↦
  inferInstanceAs (Decidable (u.1 = v.1 ∧ ((u.2 : ℕ) + 1 = v.2 ∨ (v.2 : ℕ) + 1 = u.2)))

@[simp] lemma pathUnion_adj {u v : Σ i, Fin (a i)} :
    (pathUnion a).Adj u v ↔ u.1 = v.1 ∧ ((u.2 : ℕ) + 1 = v.2 ∨ (v.2 : ℕ) + 1 = u.2) :=
  Iff.rfl

/-- Consecutive vertices of a path are adjacent. -/
lemma pathUnion_adj_succ (i : ι) (x : ℕ) (hx : x + 1 < a i) :
    (pathUnion a).Adj ⟨i, ⟨x, by omega⟩⟩ ⟨i, ⟨x + 1, hx⟩⟩ :=
  ⟨rfl, Or.inl rfl⟩

/-- Every vertex of a path on at least two vertices has a neighbour. -/
lemma exists_pathUnion_adj (v : Σ i, Fin (a i)) (hv : 2 ≤ a v.1) :
    ∃ u, (pathUnion a).Adj u v := by
  by_cases h : (v.2 : ℕ) + 1 < a v.1
  · exact ⟨⟨v.1, ⟨(v.2 : ℕ) + 1, h⟩⟩, rfl, Or.inr rfl⟩
  · refine ⟨⟨v.1, ⟨(v.2 : ℕ) - 1, by omega⟩⟩, rfl, Or.inl ?_⟩
    have := v.2.2
    simp only
    omega

variable [Fintype ι] [DecidableEq ι]

lemma card_pathUnion_adj_le (v : Σ i, Fin (a i)) : #{u | (pathUnion a).Adj u v} ≤ 2 := by
  have : #{u | (pathUnion a).Adj u v} ≤ #(univ : Finset Bool) := by
    refine card_le_card_of_injOn (fun u ↦ decide ((u.2 : ℕ) = v.2 + 1))
      (fun _ _ ↦ mem_coe.mpr (mem_univ _)) ?_
    intro u hu u' hu' huu'
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, pathUnion_adj] at hu hu'
    simp only [decide_eq_decide] at huu'
    exact sigma_ext_val (hu.1.trans hu'.1.symm) (by omega)
  simpa using this

lemma deg_pathUnion_le (v : Σ i, Fin (a i)) : deg (pathUnion a) v ≤ 2 := by
  unfold deg
  simpa only [(pathUnion a).adj_comm v] using card_pathUnion_adj_le a v

omit [Fintype ι] [DecidableEq ι] in
/-- A function that agrees on adjacent vertices is constant on every path. -/
lemma eq_of_pathUnion_adj {β : Type*} (f : (Σ i, Fin (a i)) → β)
    (hf : ∀ u v, (pathUnion a).Adj u v → f u = f v) (v : Σ i, Fin (a i)) :
    f v = f ⟨v.1, ⟨0, by have := v.2.2; omega⟩⟩ := by
  obtain ⟨i, x, hx⟩ := v
  induction x with
  | zero => rfl
  | succ k ih => exact (hf _ _ (pathUnion_adj_succ a i k hx)).symm.trans (ih (by omega))

/-- A path on `n ≥ 1` vertices has `n - 1` edges: `∑_{x,y} A(x,y) = 2n - 2`. -/
lemma sum_pathAdj (n : ℕ) (hn : 1 ≤ n) :
    ∑ x : Fin n, ∑ y : Fin n,
      (if (x : ℕ) + 1 = y ∨ (y : ℕ) + 1 = x then (1 : ℝ) else 0) = 2 * n - 2 := by
  have hone : ∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then (1 : ℝ) else 0) = n - 1 := by
    have h (x : Fin n) : ∑ y : Fin n, (if (x : ℕ) + 1 = y then (1 : ℝ) else 0) =
        if (x : ℕ) + 1 < n then 1 else 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun y ↦ if (x : ℕ) + 1 = y then (1 : ℝ) else 0) n,
        sum_ite_eq]
      simp only [mem_range]
    simp_rw [h]
    rw [Fin.sum_univ_eq_sum_range (fun x ↦ if x + 1 < n then (1 : ℝ) else 0) n, sum_boole]
    have : ({x ∈ range n | x + 1 < n} : Finset ℕ) = range (n - 1) := by
      ext x
      simp only [mem_filter, mem_range]
      omega
    rw [this, card_range, Nat.cast_sub hn, Nat.cast_one]
  have hsplit (x y : ℕ) : (if x + 1 = y ∨ y + 1 = x then (1 : ℝ) else 0) =
      (if x + 1 = y then 1 else 0) + (if y + 1 = x then 1 else 0) := by
    split_ifs <;> first | (exfalso; omega) | norm_num
  simp_rw [hsplit, sum_add_distrib]
  rw [hone, sum_comm, hone]
  ring

/-- `∑_{u,v} A(u,v) = ∑_i (2 a_i - 2)`, i.e. path `i` has `a_i - 1` edges. -/
lemma sum_adj_pathUnion (h : ∀ i, 1 ≤ a i) :
    ∑ u, ∑ v, adj (pathUnion a) u v = ∑ i, (2 * (a i : ℝ) - 2) := by
  rw [Fintype.sum_sigma]
  refine sum_congr rfl fun i _ ↦ ?_
  have (x : Fin (a i)) : ∑ v, adj (pathUnion a) ⟨i, x⟩ v =
      ∑ y : Fin (a i), if (x : ℕ) + 1 = y ∨ (y : ℕ) + 1 = x then (1 : ℝ) else 0 := by
    rw [Fintype.sum_sigma, Fintype.sum_eq_single i fun j hj ↦ ?_]
    · simp [adj]
    · simp [adj, hj.symm]
  simp_rw [this]
  exact sum_pathAdj (a i) (h i)

omit [Fintype ι] [DecidableEq ι] in
/-- In paths on at least three vertices, one endpoint of every edge has a second neighbour. -/
lemma exists_other_adj (h3 : ∀ i, 3 ≤ a i) {u u' : Σ i, Fin (a i)} (h : (pathUnion a).Adj u u') :
    (∃ u'', (pathUnion a).Adj u'' u ∧ u'' ≠ u') ∨ (∃ u'', (pathUnion a).Adj u'' u' ∧ u'' ≠ u) := by
  obtain ⟨h1, h2⟩ := h
  have hu := u.2.2
  have hu' := u'.2.2
  have hi := h3 u.1
  have hi' : a u'.1 = a u.1 := by rw [h1]
  rcases h2 with h2 | h2
  · by_cases hx : 1 ≤ (u.2 : ℕ)
    · refine Or.inl ⟨⟨u.1, ⟨(u.2 : ℕ) - 1, by omega⟩⟩, ⟨rfl, Or.inl (by simp only; omega)⟩,
        fun h ↦ ?_⟩
      have := congrArg (fun z : Σ i, Fin (a i) ↦ (z.2 : ℕ)) h
      simp only at this
      omega
    · refine Or.inr ⟨⟨u'.1, ⟨(u'.2 : ℕ) + 1, by omega⟩⟩, ⟨rfl, Or.inr rfl⟩, fun h ↦ ?_⟩
      have := congrArg (fun z : Σ i, Fin (a i) ↦ (z.2 : ℕ)) h
      simp only at this
      omega
  · by_cases hx : (u.2 : ℕ) + 1 < a u.1
    · refine Or.inl ⟨⟨u.1, ⟨(u.2 : ℕ) + 1, hx⟩⟩, ⟨rfl, Or.inr rfl⟩, fun h ↦ ?_⟩
      have := congrArg (fun z : Σ i, Fin (a i) ↦ (z.2 : ℕ)) h
      simp only at this
      omega
    · refine Or.inr ⟨⟨u'.1, ⟨(u'.2 : ℕ) - 1, by omega⟩⟩, ⟨rfl, Or.inl (by simp only; omega)⟩,
        fun h ↦ ?_⟩
      have := congrArg (fun z : Σ i, Fin (a i) ↦ (z.2 : ℕ)) h
      simp only at this
      omega

omit [Fintype ι] [DecidableEq ι] in
/-- A vertex with two distinct neighbours `v'`, `v''` in a union of paths has no others. -/
lemma eq_or_eq_of_pathUnion_adj {v v' v'' x : Σ i, Fin (a i)} (hv' : (pathUnion a).Adj v' v)
    (hv'' : (pathUnion a).Adj v'' v) (hne : v' ≠ v'') (hx : (pathUnion a).Adj x v) :
    x = v' ∨ x = v'' := by
  obtain ⟨h1', h2'⟩ := hv'
  obtain ⟨h1'', h2''⟩ := hv''
  obtain ⟨h1x, h2x⟩ := hx
  have hval : (v'.2 : ℕ) ≠ v''.2 := fun h ↦ hne (sigma_ext_val (h1'.trans h1''.symm) h)
  by_cases hxv' : (x.2 : ℕ) = v'.2
  · exact Or.inl (sigma_ext_val (h1x.trans h1'.symm) hxv')
  · exact Or.inr (sigma_ext_val (h1x.trans h1''.symm) (by omega))

end Paths

/-! ### Unions of cycles -/

/-- `x` and `y` are adjacent on the cycle `0, 1, …, n - 1, 0`. -/
def cycAdj (n x y : ℕ) : Prop :=
  x ≠ y ∧ (x + 1 = y ∨ y + 1 = x ∨ (x = 0 ∧ y + 1 = n) ∨ (y = 0 ∧ x + 1 = n))

instance (n x y : ℕ) : Decidable (cycAdj n x y) := by unfold cycAdj; infer_instance

lemma cycAdj_comm {n x y : ℕ} : cycAdj n x y ↔ cycAdj n y x := by unfold cycAdj; omega

/-- On a cycle with at least three vertices every vertex has exactly two neighbours. -/
lemma sum_cycAdj (n x : ℕ) (hn : 3 ≤ n) (hx : x < n) :
    ∑ y ∈ range n, (if cycAdj n y x then (1 : ℝ) else 0) = 2 := by
  have key : ∃ s t, s < n ∧ t < n ∧ s ≠ t ∧ cycAdj n s x ∧ cycAdj n t x ∧
      ∀ y < n, cycAdj n y x → y = s ∨ y = t := by
    unfold cycAdj
    by_cases h0 : x = 0
    · exact ⟨1, n - 1, by omega, by omega, by omega, by omega, by omega, fun y hyn hy ↦ by omega⟩
    by_cases h1 : x + 1 = n
    · exact ⟨0, x - 1, by omega, by omega, by omega, by omega, by omega, fun y hyn hy ↦ by omega⟩
    · exact ⟨x + 1, x - 1, by omega, by omega, by omega, by omega, by omega,
        fun y hyn hy ↦ by omega⟩
  obtain ⟨s, t, hs, ht, hst, hsx, htx, h⟩ := key
  rw [sum_eq_add s t hst (fun y hyr hy ↦ ?_) (fun h' ↦ absurd (mem_range.mpr hs) h')
    (fun h' ↦ absurd (mem_range.mpr ht) h')]
  · simp only [hsx, htx, ite_true]; norm_num
  · have hyn : y < n := mem_range.mp hyr
    have : ¬ cycAdj n y x := fun hy' ↦ by
      rcases h y hyn hy' with rfl | rfl
      · exact hy.1 rfl
      · exact hy.2 rfl
    simp [this]

/-- The disjoint union of `m` cycles on `A` vertices each (a cycle needs `A ≥ 3`). -/
def cycleUnion (m A : ℕ) : SimpleGraph (Σ _ : Fin m, Fin A) where
  Adj u v := u.1 = v.1 ∧ cycAdj A u.2 v.2
  symm := ⟨fun _ _ ⟨h1, h2⟩ ↦ ⟨h1.symm, cycAdj_comm.mp h2⟩⟩
  loopless := ⟨fun _ ⟨_, h⟩ ↦ h.1 rfl⟩

instance (m A : ℕ) : DecidableRel (cycleUnion m A).Adj := fun u v ↦
  inferInstanceAs (Decidable (u.1 = v.1 ∧ cycAdj A u.2 v.2))

@[simp] lemma cycleUnion_adj {m A : ℕ} {u v : Σ _ : Fin m, Fin A} :
    (cycleUnion m A).Adj u v ↔ u.1 = v.1 ∧ cycAdj A u.2 v.2 :=
  Iff.rfl

lemma deg_cycleUnion {m A : ℕ} (hA : 3 ≤ A) (v : Σ _ : Fin m, Fin A) :
    (deg (cycleUnion m A) v : ℝ) = 2 := by
  rw [← sum_adj_eq_deg']
  rw [Fintype.sum_sigma, Fintype.sum_eq_single v.1 ?_]
  · simp only [adj, cycleUnion_adj, true_and]
    rw [Fin.sum_univ_eq_sum_range (fun y ↦ if cycAdj A y v.2 then (1 : ℝ) else 0) A]
    exact sum_cycAdj A v.2 hA v.2.2
  · intro j hj
    simp [adj, hj]

/-- On a cycle with at least five vertices, two distinct vertices have at most one common
neighbour. -/
lemma card_common_adj_cycleUnion_le_one {m A : ℕ} (hA : 5 ≤ A) {w w' : Σ _ : Fin m, Fin A}
    (hww' : w ≠ w') :
    #({x | (cycleUnion m A).Adj x w ∧ (cycleUnion m A).Adj x w'} : Finset _) ≤ 1 := by
  refine card_le_one.mpr fun x hx y hy ↦ ?_
  simp only [mem_filter, mem_univ, true_and, cycleUnion_adj] at hx hy
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  obtain ⟨⟨hy1, hy2⟩, hy3, hy4⟩ := hy
  have hw : (w.2 : ℕ) ≠ w'.2 := fun h ↦ hww' (sigma_ext_val (hx1.symm.trans hx3) h)
  refine sigma_ext_val (hx1.trans hy1.symm) ?_
  have := x.2.2
  have := y.2.2
  have := w.2.2
  have := w'.2.2
  unfold cycAdj at hx2 hx4 hy2 hy4
  omega

end GsimOT.Hardness
