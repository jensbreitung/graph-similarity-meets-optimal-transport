import GsimOT.Common.PathsAndCycles

/-!
# Three-Partition

The NP-hard variant of Three-Partition [GJ79] used in the proofs of Theorems 15–17 (Appendix G,
p. 50, l. 1577–1580): given `A` and `a₁, …, a_{3m}` with `∑ aᵢ = mA` and `A/4 < aᵢ < A/2`, decide
whether the `aᵢ` can be partitioned into `m` triples of sum `A` each.

The reductions compare the paths `F₁ = pathUnion I.a` (path `i` has `aᵢ` vertices) with `m` paths
or cycles on `A` vertices each. This file provides the two directions shared by all reductions:

* `ThreePartition.layoutEquiv`: a solution lays out the paths of `F₁` on the `m` components so
  that edges go to edges;
* `ThreePartition.isYes_of_isDS`: conversely, a doubly stochastic matrix that maps every path
  of `F₁` into a single component yields a solution (the final counting step of the proofs of
  Theorems 15 and 17, p. 51, l. 1617–1620, and p. 56, l. 1786–1790, and of Eq. (44), p. 52,
  l. 1637–1642).
-/

open Finset

namespace GsimOT.Hardness

/-- An instance `(A, a₁, …, a_{3m})` of Three-Partition. -/
structure ThreePartition where
  m : ℕ
  A : ℕ
  a : Fin (3 * m) → ℕ
  sum_eq : ∑ i, a i = m * A
  lt_four_mul : ∀ i, A < 4 * a i
  two_mul_lt : ∀ i, 2 * a i < A

namespace ThreePartition

variable (I : ThreePartition)

/-- `I` is a YES-instance: the `aᵢ` can be partitioned into `m` triples of sum `A` each. -/
def IsYes : Prop :=
  ∃ σ : Fin (3 * I.m) → Fin I.m, ∀ j, #{i | σ i = j} = 3 ∧ ∑ i with σ i = j, I.a i = I.A

lemma a_pos (i : Fin (3 * I.m)) : 0 < I.a i := by
  have := I.lt_four_mul i
  omega

/-- Because `A/4 < aᵢ < A/2`, a class of sum `A` has exactly three elements. -/
lemma card_eq_three_of_sum_eq (σ : Fin (3 * I.m) → Fin I.m) (j : Fin I.m)
    (h : ∑ i with σ i = j, I.a i = I.A) : #{i | σ i = j} = 3 := by
  have hA : 0 < I.A := by
    have := I.two_mul_lt ⟨0, by have := j.pos; omega⟩
    omega
  have hS : ({i | σ i = j} : Finset (Fin (3 * I.m))).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hS
    rw [hS, sum_empty] at h
    omega
  have h1 := sum_lt_sum_of_nonempty hS fun i _ ↦ I.lt_four_mul i
  have h2 := sum_lt_sum_of_nonempty hS fun i _ ↦ I.two_mul_lt i
  rw [sum_const, smul_eq_mul, ← mul_sum, h] at h1
  rw [sum_const, smul_eq_mul, ← mul_sum, h] at h2
  have h3 : #{i | σ i = j} < 4 := Nat.lt_of_mul_lt_mul_right h1
  have h4 : 2 < #{i | σ i = j} := Nat.lt_of_mul_lt_mul_right h2
  omega

lemma three_le_A_of_mem {i : Fin (3 * I.m)} (h2 : 2 ≤ I.a i) : 3 ≤ I.A := by
  have := I.two_mul_lt i
  omega

lemma card_vertices :
    Fintype.card (Σ i, Fin (I.a i)) = Fintype.card (Σ _ : Fin I.m, Fin I.A) := by
  simp [Fintype.card_sigma, I.sum_eq]

/-! ### From a solution to a bijection -/

section Layout

variable {I} (σ : Fin (3 * I.m) → Fin I.m)

/-- The total length of the paths before `i` that `σ` puts into the class of `i`. -/
def offset (i : Fin (3 * I.m)) : ℕ := ∑ k with k < i ∧ σ k = σ i, I.a k

lemma offset_add_le_of_lt {i i' : Fin (3 * I.m)} (hii' : i < i') (hσ : σ i = σ i') :
    offset σ i + I.a i ≤ offset σ i' := by
  have hi : i ∉ ({k | k < i ∧ σ k = σ i} : Finset (Fin (3 * I.m))) := by simp
  calc offset σ i + I.a i = ∑ k ∈ insert i ({k | k < i ∧ σ k = σ i} : Finset _), I.a k := by
        rw [sum_insert hi, add_comm]; rfl
    _ ≤ offset σ i' := by
        refine sum_le_sum_of_subset fun k hk ↦ ?_
        simp only [mem_insert, mem_filter, mem_univ, true_and] at hk ⊢
        rcases hk with rfl | ⟨hk1, hk2⟩
        · exact ⟨hii', hσ⟩
        · exact ⟨hk1.trans hii', hk2.trans hσ⟩

variable (hσ : ∀ j, ∑ i with σ i = j, I.a i = I.A)
include hσ

lemma offset_add_le (i : Fin (3 * I.m)) : offset σ i + I.a i ≤ I.A := by
  have hi : i ∉ ({k | k < i ∧ σ k = σ i} : Finset (Fin (3 * I.m))) := by simp
  calc offset σ i + I.a i = ∑ k ∈ insert i ({k | k < i ∧ σ k = σ i} : Finset _), I.a k := by
        rw [sum_insert hi, add_comm]; rfl
    _ ≤ ∑ k with σ k = σ i, I.a k := by
        refine sum_le_sum_of_subset fun k hk ↦ ?_
        simp only [mem_insert, mem_filter, mem_univ, true_and] at hk ⊢
        rcases hk with rfl | ⟨_, hk2⟩
        · rfl
        · exact hk2
    _ = I.A := hσ (σ i)

omit hσ in
/-- The layout of the paths of `F₁` given by a solution `σ`: vertex `x` of path `i` goes to
position `offset σ i + x` of component `σ i`. -/
def layout (hσ : ∀ j, ∑ i with σ i = j, I.a i = I.A) (v : Σ i, Fin (I.a i)) :
    Σ _ : Fin I.m, Fin I.A :=
  ⟨σ v.1, ⟨offset σ v.1 + v.2, by have := offset_add_le σ hσ v.1; have := v.2.2; omega⟩⟩

@[simp] lemma layout_fst (v : Σ i, Fin (I.a i)) : (layout σ hσ v).1 = σ v.1 := rfl

@[simp] lemma layout_snd_val (v : Σ i, Fin (I.a i)) :
    ((layout σ hσ v).2 : ℕ) = offset σ v.1 + v.2 := rfl

lemma layout_injective : Function.Injective (layout σ hσ) := by
  intro u v huv
  have h1 : σ u.1 = σ v.1 := by simpa using congrArg Sigma.fst huv
  have h2 : offset σ u.1 + (u.2 : ℕ) = offset σ v.1 + v.2 := by
    simpa using congrArg (fun w ↦ (w.2 : ℕ)) huv
  have hu := u.2.2
  have hv := v.2.2
  rcases lt_trichotomy u.1 v.1 with h | h | h
  · have := offset_add_le_of_lt σ h h1
    omega
  · have : offset σ u.1 = offset σ v.1 := by rw [h]
    exact sigma_ext_val h (by omega)
  · have := offset_add_le_of_lt σ h h1.symm
    omega

/-- The bijection `V(F₁) ≃ V(F₂)` given by a solution `σ`. -/
noncomputable def layoutEquiv : (Σ i, Fin (I.a i)) ≃ (Σ _ : Fin I.m, Fin I.A) :=
  Equiv.ofBijective (layout σ hσ)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨layout_injective σ hσ, I.card_vertices⟩)

@[simp] lemma layoutEquiv_apply (v : Σ i, Fin (I.a i)) : layoutEquiv σ hσ v = layout σ hσ v :=
  rfl

/-- The layout maps edges of `F₁` to edges of the union of paths on `A` vertices. -/
lemma layout_adj_pathUnion {u v : Σ i, Fin (I.a i)} (h : (pathUnion I.a).Adj u v) :
    (pathUnion fun _ : Fin I.m ↦ I.A).Adj (layout σ hσ u) (layout σ hσ v) := by
  obtain ⟨h1, h2⟩ := h
  have : offset σ u.1 = offset σ v.1 := by rw [h1]
  refine ⟨by simp [h1], ?_⟩
  simp only [layout_snd_val]
  omega

/-- The layout maps edges of `F₁` to edges of the union of cycles on `A` vertices. -/
lemma layout_adj_cycleUnion {u v : Σ i, Fin (I.a i)} (h : (pathUnion I.a).Adj u v) :
    (cycleUnion I.m I.A).Adj (layout σ hσ u) (layout σ hσ v) := by
  obtain ⟨h1, h2⟩ := h
  have : offset σ u.1 = offset σ v.1 := by rw [h1]
  refine ⟨by simp [h1], ?_⟩
  simp only [layout_snd_val, cycAdj]
  omega

end Layout

/-! ### From a doubly stochastic matrix to a solution -/

/-- The counting argument of the proofs of Theorems 15–17: if `Q ∈ DS(V(F₁), V(F₂))` maps every
path `i` of `F₁` into the component `c i` of `F₂`, then `c` solves `I`. -/
lemma isYes_of_isDS {Q : (Σ i, Fin (I.a i)) → (Σ _ : Fin I.m, Fin I.A) → ℝ} (hQ : IsDS Q)
    (c : Fin (3 * I.m) → Fin I.m) (hc : ∀ v w, Q v w ≠ 0 → w.1 = c v.1) : I.IsYes := by
  have hsum (j : Fin I.m) : ∑ i with c i = j, I.a i = I.A := by
    have key : (∑ i with c i = j, (I.a i : ℝ)) = I.A := by
      calc (∑ i with c i = j, (I.a i : ℝ))
          = ∑ v : Σ i, Fin (I.a i), if c v.1 = j then (1 : ℝ) else 0 := by
            rw [Fintype.sum_sigma, sum_filter]
            refine sum_congr rfl fun i _ ↦ ?_
            split_ifs <;> simp
        _ = ∑ v, ∑ w, if w.1 = j then Q v w else 0 := by
            refine sum_congr rfl fun v _ ↦ ?_
            by_cases hcj : c v.1 = j
            · rw [ite_eq_left hcj, ← hQ.row_sum v]
              refine sum_congr rfl fun w _ ↦ ?_
              by_cases hw : Q v w = 0
              · simp [hw]
              · rw [ite_eq_left ((hc v w hw).trans hcj)]
            · rw [ite_eq_right hcj]
              refine (sum_eq_zero fun w _ ↦ ?_).symm
              by_cases hw : Q v w = 0
              · simp [hw]
              · exact ite_eq_right fun hwj ↦ hcj ((hc v w hw).symm.trans hwj)
        _ = ∑ w : Σ _ : Fin I.m, Fin I.A, if w.1 = j then (1 : ℝ) else 0 := by
            rw [sum_comm]
            refine sum_congr rfl fun w _ ↦ ?_
            by_cases hwj : w.1 = j
            · simp only [hwj, ite_true]; exact hQ.col_sum w
            · simp [hwj]
        _ = I.A := by
            rw [Fintype.sum_sigma, Fintype.sum_eq_single j fun j' hj' ↦ by simp [hj']]
            simp
    exact_mod_cast key
  exact ⟨c, fun j ↦ ⟨I.card_eq_three_of_sum_eq c j (hsum j), hsum j⟩⟩

/-! ### Making the `aᵢ` large -/

/-- The w.l.o.g. step of the proofs of Theorems 15–17 (p. 50, l. 1586–1587; p. 51, l. 1622–1624;
p. 54, l. 1712): add `3` to every `aᵢ` and `9` to `A`. -/
def shift : ThreePartition where
  m := I.m
  A := I.A + 9
  a i := I.a i + 3
  sum_eq := by
    rw [sum_add_distrib, I.sum_eq]
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  lt_four_mul i := by have := I.lt_four_mul i; omega
  two_mul_lt i := by have := I.two_mul_lt i; omega

lemma four_le_shift_a (i : Fin (3 * I.shift.m)) : 4 ≤ I.shift.a i := by
  have := I.a_pos i
  simp only [shift]
  omega

/-- Shifting preserves YES- and NO-instances, since every class has exactly three elements. -/
lemma shift_isYes_iff : I.shift.IsYes ↔ I.IsYes := by
  dsimp only [IsYes, shift]
  constructor <;> rintro ⟨σ, hσ⟩ <;> refine ⟨σ, fun j ↦ ⟨(hσ j).1, ?_⟩⟩
  · have h := (hσ j).2
    rw [sum_add_distrib, sum_const, smul_eq_mul, (hσ j).1] at h
    omega
  · rw [sum_add_distrib, sum_const, smul_eq_mul, (hσ j).1, (hσ j).2]

end ThreePartition

end GsimOT.Hardness
