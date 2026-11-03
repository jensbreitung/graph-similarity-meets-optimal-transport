/-
# Trimming (Definition 3.1) and Lemma 3.2

[HOG26], Section 3.  The trimming process of Definition 3.1 starts with `x̃ = x` and, as long as
some component `C` of `x̃` has a nonempty `S ⊊ C` with `x̃(S, C - S) ≤ ε`, zeroes out the edges of
the cut `(S, C - S)`.

*Formalisation.*  We record the state of the process by a labelling `ℓ : V → ℕ` of the vertices by
*blocks*; the current trimmed graph is `trimGraph x ℓ`, which keeps `x` on pairs inside a block and
is `0` across blocks.  One step of the process splits a block `C` into `S` and `C - S` when
`x̃(S, C - S) ≤ ε` (`exists_split`).  The process starts with a single block and stops when every
block is `ε`-edge-connected (`IsTrimmed`): every nonempty proper `S ⊊ C` has `x̃(S, C - S) > ε`.

Since `ε ≥ 0`, an `ε`-edge-connected block is connected in `supp(x̃)`, and `x̃` vanishes across
blocks, so at the end the blocks are exactly the connected components of `supp(x̃)` (we do not need
this identification).  In the paper, a step may split a component into more than two connected
components; in the block formulation the number of blocks grows by exactly one per step, and the
final output satisfies the same properties.

**Lemma 3.2** (`lemma32`): the total removed weight is `x(E) - x̃(E) ≤ (|V| - 1) ε`, since every
step removes weight `≤ ε` and there are at most `|V| - 1` steps.
-/
import ThinMatching.SupportConstrained.Sampling

open Finset

namespace ThinMatching

section Trimming

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices of block `a`, as a type. -/
abbrev Blk (ℓ : V → ℕ) (a : ℕ) : Type _ := {v : V // ℓ v = a}

/-- The weighted graph induced by `x` on block `a` (this is also the graph induced by the trimmed
graph `trimGraph x ℓ`). -/
def blockGraph (x : WGraph V) (ℓ : V → ℕ) (a : ℕ) : WGraph (Blk ℓ a) where
  w u v := x.w u.1 v.1
  nonneg u v := x.nonneg u.1 v.1
  symm u v := x.symm u.1 v.1
  diag v := x.diag v.1

/-- The trimmed graph for the block structure `ℓ`: keep `x` inside blocks, zero across blocks. -/
def trimGraph (x : WGraph V) (ℓ : V → ℕ) : WGraph V where
  w u v := if ℓ u = ℓ v then x.w u v else 0
  nonneg u v := by split_ifs <;> simp [x.nonneg]
  symm u v := by simp only [eq_comm (a := ℓ u), x.symm u v]
  diag v := by simp [x.diag]

/-- The final state of the trimming process: every block is `ε`-edge-connected. -/
def IsTrimmed (x : WGraph V) (ε : ℝ) (ℓ : V → ℕ) : Prop :=
  ∀ a (S : Finset (Blk ℓ a)), S.Nonempty → S ≠ Finset.univ → ε < cutWeight (blockGraph x ℓ a) S

/-- Twice the weight removed by trimming (sum over ordered pairs). -/
def removed (x : WGraph V) (ℓ : V → ℕ) : ℝ := ∑ u, ∑ v, if ℓ u = ℓ v then 0 else x.w u v

omit [Fintype V] [DecidableEq V] in
theorem trimGraph_le (x : WGraph V) (ℓ : V → ℕ) (u v : V) : (trimGraph x ℓ).w u v ≤ x.w u v := by
  simp only [trimGraph]; split_ifs <;> simp [x.nonneg]

omit [Fintype V] [DecidableEq V] in
theorem same_of_trimGraph_pos {x : WGraph V} {ℓ : V → ℕ} {u v : V}
    (h : 0 < (trimGraph x ℓ).w u v) : ℓ u = ℓ v := by
  by_contra h'; simp [trimGraph, h'] at h

/-- The cut of `S` inside block `a`, written as a sum over vertices of `V`. -/
theorem cutWeight_blockGraph (x : WGraph V) (ℓ : V → ℕ) (a : ℕ) (S : Finset (Blk ℓ a)) :
    cutWeight (blockGraph x ℓ a) S =
      ∑ u ∈ S.map (Function.Embedding.subtype _), ∑ v ∈ Sᶜ.map (Function.Embedding.subtype _),
        x.w u v := by
  simp [cutWeight, blockGraph, Finset.sum_map]

theorem sum_sum_ite_and (A B : Finset V) (f : V → V → ℝ) :
    ∑ u, ∑ v, (if u ∈ A ∧ v ∈ B then f u v else 0) = ∑ u ∈ A, ∑ v ∈ B, f u v := by
  have h : ∀ u, ∑ v, (if u ∈ A ∧ v ∈ B then f u v else 0) =
      if u ∈ A then ∑ v ∈ B, f u v else 0 := by
    intro u; by_cases hu : u ∈ A <;> simp [hu, Finset.sum_ite_mem]
  simp_rw [h]; rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- One step of the trimming process: if block `a` has a nonempty proper subset `S` with
`x̃(S, C - S) ≤ ε`, splitting it off increases the number of blocks by one and the removed weight
by at most `ε`. -/
theorem exists_split (x : WGraph V) (ℓ : V → ℕ) (a : ℕ) (S : Finset (Blk ℓ a))
    (hS : S.Nonempty) (hS' : S ≠ Finset.univ) :
    ∃ ℓ' : V → ℕ, #(Finset.univ.image ℓ') = #(Finset.univ.image ℓ) + 1 ∧
      removed x ℓ' = removed x ℓ + 2 * cutWeight (blockGraph x ℓ a) S := by
  classical
  let A : Finset V := S.map (Function.Embedding.subtype _)
  let B : Finset V := Sᶜ.map (Function.Embedding.subtype _)
  have hA : ∀ v, v ∈ A ↔ ∃ h : ℓ v = a, (⟨v, h⟩ : Blk ℓ a) ∈ S := fun v => by simp [A]
  have hB : ∀ v, v ∈ B ↔ ℓ v = a ∧ v ∉ A := fun v => by
    simp only [B, hA, Finset.mem_map, Finset.mem_compl, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, fun ⟨_, h⟩ => hw h⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨v, h1⟩, fun h => h2 ⟨h1, h⟩, rfl⟩
  have hAa : ∀ v ∈ A, ℓ v = a := fun v hv => ((hA v).1 hv).1
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ : ∃ t, t ∉ S := by
    by_contra h; push Not at h; exact hS' (Finset.eq_univ_iff_forall.2 h)
  have hsA : s.1 ∈ A := (hA _).2 ⟨s.2, hs⟩
  have htA : t.1 ∉ A := fun h => by
    obtain ⟨_, h'⟩ := (hA _).1 h; exact ht h'
  let m : ℕ := (Finset.univ.image ℓ).sup id + 1
  have hm : ∀ w, ℓ w ≠ m := fun w h => by
    have : ℓ w ≤ (Finset.univ.image ℓ).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem ℓ (Finset.mem_univ w))
    simp only [m] at h; omega
  let ℓ' : V → ℕ := fun v => if v ∈ A then m else ℓ v
  refine ⟨ℓ', ?_, ?_⟩
  · have : Finset.univ.image ℓ' = insert m (Finset.univ.image ℓ) := by
      ext b
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, ℓ']
      constructor
      · rintro ⟨w, rfl⟩
        by_cases hw : w ∈ A
        · simp [hw]
        · simp only [hw, ite_false]; exact Or.inr ⟨w, rfl⟩
      · rintro (rfl | ⟨w, rfl⟩)
        · exact ⟨s.1, by simp [hsA]⟩
        · by_cases hw : w ∈ A
          · refine ⟨t.1, ?_⟩
            simp only [htA, ite_false, t.2, hAa w hw]
          · exact ⟨w, by simp [hw]⟩
    rw [this, Finset.card_insert_of_notMem]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hm
  · rw [cutWeight_blockGraph]
    have hpt : ∀ u v, (if ℓ' u = ℓ' v then 0 else x.w u v) =
        (if ℓ u = ℓ v then 0 else x.w u v) + (if u ∈ A ∧ v ∈ B then x.w u v else 0) +
          (if v ∈ A ∧ u ∈ B then x.w v u else 0) := fun u v => by
      have hmu := hm u
      have hmv := hm v
      by_cases hu : u ∈ A <;> by_cases hv : v ∈ A
      · simp [ℓ', hu, hv, hB, hAa u hu, hAa v hv]
      · have := hAa u hu
        have ham : m ≠ a := fun h => hmu (this.trans h.symm)
        by_cases hlv : ℓ v = a
        · simp [ℓ', hu, hv, hB, this, hlv, ham]
        · simp [ℓ', hu, hv, hB, this, hlv, Ne.symm hmv, Ne.symm hlv]
      · have := hAa v hv
        have ham : a ≠ m := fun h => hmv (this.trans h)
        by_cases hlu : ℓ u = a
        · simp [ℓ', hu, hv, hB, this, hlu, x.symm u v, ham]
        · simp [ℓ', hu, hv, hB, this, hlu, hmu]
      · simp [ℓ', hu, hv, hB]
    unfold removed
    simp_rw [hpt, Finset.sum_add_distrib]
    rw [sum_sum_ite_and A B (fun u v => x.w u v), Finset.sum_comm (f := fun u v =>
      if v ∈ A ∧ u ∈ B then x.w v u else 0), sum_sum_ite_and A B (fun u v => x.w u v)]
    ring

/-- **Definition 3.1 (trimming) — existence of the output.**  For `ε ≥ 0` and `V` nonempty, the
trimming process terminates with a block structure `ℓ` in which every block is `ε`-edge-connected,
having removed (twice) a weight of at most `2 (|V| - 1) ε`. -/
theorem trimming_exists (x : WGraph V) {ε : ℝ} (hε : 0 ≤ ε) [Nonempty V] :
    ∃ ℓ : V → ℕ, IsTrimmed x ε ℓ ∧ removed x ℓ ≤ 2 * ((Fintype.card V : ℝ) - 1) * ε := by
  have hle : ∀ ℓ : V → ℕ, #(Finset.univ.image ℓ) ≤ Fintype.card V := fun ℓ =>
    Finset.card_image_le.trans (by simp)
  have key : ∀ k : ℕ, ∀ ℓ : V → ℕ, Fintype.card V - #(Finset.univ.image ℓ) = k →
      removed x ℓ + 2 * ε ≤ 2 * ε * #(Finset.univ.image ℓ) →
      ∃ ℓ' : V → ℕ, IsTrimmed x ε ℓ' ∧ removed x ℓ' + 2 * ε ≤ 2 * ε * Fintype.card V := by
    intro k
    induction k with
    | zero =>
      intro ℓ hk hinv
      by_cases hT : IsTrimmed x ε ℓ
      · refine ⟨ℓ, hT, hinv.trans ?_⟩
        have : (#(Finset.univ.image ℓ) : ℝ) ≤ Fintype.card V := by exact_mod_cast hle ℓ
        nlinarith
      · exfalso
        unfold IsTrimmed at hT; push Not at hT
        obtain ⟨a, S, hS, hS', -⟩ := hT
        obtain ⟨ℓ', hc, -⟩ := exists_split x ℓ a S hS hS'
        have := hle ℓ'; omega
    | succ k ih =>
      intro ℓ hk hinv
      by_cases hT : IsTrimmed x ε ℓ
      · refine ⟨ℓ, hT, hinv.trans ?_⟩
        have : (#(Finset.univ.image ℓ) : ℝ) ≤ Fintype.card V := by exact_mod_cast hle ℓ
        nlinarith
      · unfold IsTrimmed at hT; push Not at hT
        obtain ⟨a, S, hS, hS', hcut⟩ := hT
        obtain ⟨ℓ', hc, hr⟩ := exists_split x ℓ a S hS hS'
        refine ih ℓ' (by omega) ?_
        rw [hr, hc]; push_cast; linarith
  obtain ⟨ℓ, h1, h2⟩ := key _ (fun _ => 0) rfl (by
    have : Finset.univ.image (fun _ : V => (0 : ℕ)) = {0} :=
      Finset.image_const Finset.univ_nonempty 0
    rw [this]; simp [removed])
  exact ⟨ℓ, h1, by linarith⟩

/-- `x(E) - x̃(E)` is half the (ordered) removed weight. -/
theorem edgeTotal_sub_trimGraph (x : WGraph V) (ℓ : V → ℕ) :
    edgeTotal x - edgeTotal (trimGraph x ℓ) = removed x ℓ / 2 := by
  have hf : ∀ u v, (x.w u v - (trimGraph x ℓ).w u v) = (x.w v u - (trimGraph x ℓ).w v u) :=
    fun u v => by rw [x.symm, (trimGraph x ℓ).symm]
  have hpt : ∀ e : Sym2 V, edgeW x e - edgeW (trimGraph x ℓ) e =
      Sym2.lift ⟨fun u v => x.w u v - (trimGraph x ℓ).w u v, hf⟩ e := fun e => by
    induction e using Sym2.ind with
    | _ u v => simp
  unfold edgeTotal
  rw [← Finset.sum_sub_distrib]
  simp_rw [hpt]
  rw [sum_sym2_lift _ hf (fun v => by simp [x.diag, (trimGraph x ℓ).diag])]
  congr 1
  unfold removed trimGraph
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  by_cases h : ℓ u = ℓ v <;> simp [h]

/-- **Lemma 3.2.**  The trimming process with threshold `ε ≥ 0` produces `x̃ = trimGraph x ℓ ≤ x`
whose blocks are `ε`-edge-connected (`IsTrimmed`), with `x(E) - x̃(E) ≤ (|V| - 1) ε`. -/
theorem lemma32 (x : WGraph V) {ε : ℝ} (hε : 0 ≤ ε) [Nonempty V] :
    ∃ ℓ : V → ℕ, IsTrimmed x ε ℓ ∧
      edgeTotal x - edgeTotal (trimGraph x ℓ) ≤ ((Fintype.card V : ℝ) - 1) * ε := by
  obtain ⟨ℓ, h1, h2⟩ := trimming_exists x hε
  exact ⟨ℓ, h1, by rw [edgeTotal_sub_trimGraph]; linarith⟩

end Trimming

end ThinMatching
