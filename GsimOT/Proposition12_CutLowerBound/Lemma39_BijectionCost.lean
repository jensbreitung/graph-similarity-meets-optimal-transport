/-
# Lemma 33: `d_□(G, H) = 8`

Paper, App. E.1, Lemma 33 (p. 31, l. 967; proof p. 31, l. 968–988).

* Upper bound (l. 984–988): for the natural bijection `id`, `A = A_G^{id} - A_H` vanishes outside
  the core and every cut value equals `xᵀ Z y` with `x, y ∈ {-1, 0, 1}^5`, hence
  `C_□(id) ≤ ‖Z‖_{∞→1} = 8`.
* Lower bound (l. 968–984): taking `S = {π(v)}`, `T = W` gives `C_□(π) ≥ |deg_G(v) - deg_H(π v)|`,
  which is `≥ 9` unless `π` maps every pair `{v_i^+, v_i^-}` onto `{w_i^+, w_i^-}`.  Otherwise
  `π(v_i^σ) = w_i^{r_i σ}` and on the core `A(w_i^σ, w_j^τ) = M_ij στ` with
  `M_ij = ½ Z_ij (1 + r_i r_j)`.  Cuts inside the core realise `xᵀ M y` for all
  `x, y ∈ {-1, 0, 1}^5`; for each of the `32` sign patterns `r` we exhibit explicit `x, y` with
  `xᵀ M y ≥ 8` (a finite check replacing the paper's case analysis over `K`, l. 982–984).
-/
import GsimOT.Proposition12_CutLowerBound.Construction

open Finset

namespace GsimOT.Prop12

/-! ## Rewriting cut sums -/

/-- A cut sum of a matrix vanishing outside `core × core` only sees the core. -/
lemma cut_sum_eq_core (A : Matrix Vtx Vtx ℝ) (hA : ∀ a b, (a.isRight ∨ b.isRight) → A a b = 0)
    (S T : Finset Vtx) :
    ∑ a ∈ S, ∑ b ∈ T, A a b =
      ∑ p : Core, ∑ q : Core, (if .inl p ∈ S then 1 else 0) * ((if .inl q ∈ T then 1 else 0) *
        A (.inl p) (.inl q)) := by
  rw [sum_mem_eq_sum_ite]
  simp_rw [sum_mem_eq_sum_ite T]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  simp [hA]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

/-- If `A(w_i^σ, w_j^τ) = c_ij στ` on the core, every cut of the core has value `xᵀ c y`
with `x_i = 1[w_i^+ ∈ S] - 1[w_i^- ∈ S]` and `y_j = 1[w_j^+ ∈ T] - 1[w_j^- ∈ T]`. -/
lemma core_sum_eq_bilin (c : Fin 5 → Fin 5 → ℝ) (A : Matrix Vtx Vtx ℝ)
    (hA : ∀ i s j t, A (.inl (i, s)) (.inl (j, t)) = c i j * sg s * sg t) (S T : Finset Vtx) :
    ∑ p : Core, ∑ q : Core, (if .inl p ∈ S then 1 else 0) * ((if .inl q ∈ T then 1 else 0) *
        A (.inl p) (.inl q)) =
      ∑ i, ∑ j, c i j *
        ((if .inl (i, true) ∈ S then 1 else 0) - (if .inl (i, false) ∈ S then 1 else 0)) *
        ((if .inl (j, true) ∈ T then 1 else 0) - (if .inl (j, false) ∈ T then 1 else 0)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hA, sg]
  push_cast
  ring

/-! ## Upper bound: the natural bijection -/

lemma alignedDiff_refl_inl (p q : Core) :
    alignedDiff G12 H12 (Equiv.refl Vtx) (.inl p) (.inl q) = Z p.1 q.1 * sg p.2 * sg q.2 := by
  simp only [alignedDiff, Equiv.refl_symm, Equiv.refl_apply, adj_G12_inl_inl, adj_H12_inl_inl]
  rw [← Int.cast_sub, gCore_sub_hCore]
  push_cast; ring

/-- `C_□(id) ≤ 8` (proof of Lemma 33, upper bound). -/
lemma cutNorm_refl_le : cutNorm (alignedDiff G12 H12 (Equiv.refl Vtx)) ≤ 8 := by
  refine cutNorm_le _ fun S T => ?_
  have h0 : ∀ a b : Vtx, (a.isRight ∨ b.isRight) →
      alignedDiff G12 H12 (Equiv.refl Vtx) a b = 0 := by
    intro a b h
    simp only [alignedDiff, Equiv.refl_symm, Equiv.refl_apply]
    rw [adj_G12_eq_adj_H12 a b h, sub_self]
  rw [cut_sum_eq_core _ h0, core_sum_eq_bilin (fun i j => (Z i j : ℝ)) _
    (fun i s j t => by rw [alignedDiff_refl_inl])]
  exact abs_bilin_Z_le (fun i => isTri_ite_sub_ite _ _) (fun j => isTri_ite_sub_ite _ _)

/-! ## Lower bound: every bijection -/

/-- `C_□(π) ≥ |deg_G(π⁻¹ w) - deg_H(w)|`, via `S = {w}`, `T = W`. -/
lemma abs_dg_sub_le (π : Vtx ≃ Vtx) (w : Vtx) :
    |(dg (π.symm w) : ℝ) - dg w| ≤ cutNorm (alignedDiff G12 H12 π) := by
  have h := le_cutNorm (alignedDiff G12 H12 π) {w} univ
  simp only [Finset.sum_singleton, alignedDiff, Finset.sum_sub_distrib] at h
  rwa [Equiv.sum_comp π.symm (fun v => adj G12 (π.symm w) v), sum_adj_G12, sum_adj_H12] at h

/-- The matrix `M = Z[K] ⊕ Z[K^c]` for the flip pattern `r` (`K = {i | r_i = true}`, up to a
global flip), i.e. `M_ij = ½ Z_ij (1 + r_i r_j)`. -/
def Mr (r : Fin 5 → Bool) (i j : Fin 5) : ℤ := if r i = r j then Z i j else 0

/-- Explicit maximisers `x, y ∈ {-1, 0, 1}^5` of `xᵀ M y` for each of the 32 flip patterns. -/
def wit : Bool → Bool → Bool → Bool → Bool → (Fin 5 → ℤ) × (Fin 5 → ℤ)
  | true, true, true, true, true => (![-1, -1, -1, -1, 1], ![1, -1, -1, 1, 0])
  | true, true, true, true, false => (![-1, -1, 1, 1, -1], ![-1, -1, 1, 1, 0])
  | true, true, true, false, true => (![-1, 1, -1, -1, 1], ![1, -1, 1, 0, -1])
  | true, true, true, false, false => (![-1, 1, -1, -1, -1], ![1, -1, 1, -1, -1])
  | true, true, false, true, true => (![-1, -1, -1, 1, 1], ![-1, -1, 0, 1, 1])
  | true, true, false, true, false => (![-1, -1, -1, 1, -1], ![-1, -1, 1, 1, 1])
  | true, true, false, false, true => (![-1, 1, -1, -1, 1], ![1, -1, -1, -1, -1])
  | true, true, false, false, false => (![-1, -1, -1, 1, -1], ![-1, -1, 1, -1, 1])
  | true, false, true, true, true => (![-1, -1, 1, -1, 1], ![1, 0, -1, 1, -1])
  | true, false, true, true, false => (![-1, -1, 1, 1, -1], ![-1, 1, 1, 1, 1])
  | true, false, true, false, true => (![-1, -1, 1, -1, -1], ![-1, 1, 1, 1, -1])
  | true, false, true, false, false => (![-1, -1, -1, 1, 1], ![1, -1, 1, 1, 1])
  | true, false, false, true, true => (![-1, -1, -1, -1, 1], ![1, -1, -1, 1, -1])
  | true, false, false, true, false => (![-1, -1, -1, -1, 1], ![1, -1, -1, 1, 1])
  | true, false, false, false, true => (![-1, -1, 1, -1, -1], ![-1, 1, -1, 1, -1])
  | true, false, false, false, false => (![-1, -1, -1, 1, 1], ![0, -1, -1, 1, 1])
  | false, true, true, true, true => (![-1, -1, -1, 1, 1], ![0, -1, -1, 1, 1])
  | false, true, true, true, false => (![-1, -1, 1, -1, -1], ![-1, 1, -1, 1, -1])
  | false, true, true, false, true => (![-1, -1, -1, -1, 1], ![1, -1, -1, 1, 1])
  | false, true, true, false, false => (![-1, -1, -1, -1, 1], ![1, -1, -1, 1, -1])
  | false, true, false, true, true => (![-1, -1, -1, 1, 1], ![1, -1, 1, 1, 1])
  | false, true, false, true, false => (![-1, -1, 1, -1, -1], ![-1, 1, 1, 1, -1])
  | false, true, false, false, true => (![-1, -1, 1, 1, -1], ![-1, 1, 1, 1, 1])
  | false, true, false, false, false => (![-1, -1, 1, -1, 1], ![1, 0, -1, 1, -1])
  | false, false, true, true, true => (![-1, -1, -1, 1, -1], ![-1, -1, 1, -1, 1])
  | false, false, true, true, false => (![-1, 1, -1, -1, 1], ![1, -1, -1, -1, -1])
  | false, false, true, false, true => (![-1, -1, -1, 1, -1], ![-1, -1, 1, 1, 1])
  | false, false, true, false, false => (![-1, -1, -1, 1, 1], ![-1, -1, 0, 1, 1])
  | false, false, false, true, true => (![-1, 1, -1, -1, -1], ![1, -1, 1, -1, -1])
  | false, false, false, true, false => (![-1, 1, -1, -1, 1], ![1, -1, 1, 0, -1])
  | false, false, false, false, true => (![-1, -1, 1, 1, -1], ![-1, -1, 1, 1, 0])
  | false, false, false, false, false => (![-1, -1, -1, -1, 1], ![1, -1, -1, 1, 0])

/-- The core cut realising `x`: `{w_i^σ | x_i = σ}`. -/
def cutOf (x : Fin 5 → ℤ) : Finset Core := univ.filter fun p => x p.1 = sg p.2

/-- Finite check: `‖M‖_{∞→1} ≥ 8` for all 32 flip patterns (proof of Lemma 33, the cases
`|K| ≤ 2` up to symmetry). -/
lemma eight_le_wit : ∀ r0 r1 r2 r3 r4 : Bool,
    8 ≤ ∑ p ∈ cutOf (wit r0 r1 r2 r3 r4).1, ∑ q ∈ cutOf (wit r0 r1 r2 r3 r4).2,
      Mr ![r0, r1, r2, r3, r4] p.1 q.1 * sg p.2 * sg q.2 := by
  decide

lemma exists_core_cut (r : Fin 5 → Bool) :
    ∃ S T : Finset Core, 8 ≤ ∑ p ∈ S, ∑ q ∈ T, Mr r p.1 q.1 * sg p.2 * sg q.2 := by
  have hr : r = ![r 0, r 1, r 2, r 3, r 4] := by funext i; fin_cases i <;> rfl
  rw [hr]
  exact ⟨_, _, eight_le_wit _ _ _ _ _⟩

/-- If `π` preserves degrees, it maps each core vertex into its own pair. -/
lemma symm_inl_of_dg (π : Vtx ≃ Vtx) (h : ∀ w, dg (π.symm w) = dg w) (i : Fin 5) (s : Bool) :
    ∃ b, π.symm (.inl (i, s)) = .inl (i, b) := by
  have hd := h (.inl (i, s))
  rcases hπ : π.symm (.inl (i, s)) with ⟨j, b⟩ | m
  · rw [hπ] at hd
    simp only [dg] at hd
    have : j = i := Fin.ext (by omega)
    exact ⟨b, by rw [this]⟩
  · rw [hπ] at hd
    simp only [dg] at hd
    omega

/-- Lower bound of Lemma 33 for a bijection preserving all degrees. -/
lemma eight_le_of_dg (π : Vtx ≃ Vtx) (h : ∀ w, dg (π.symm w) = dg w) :
    8 ≤ cutNorm (alignedDiff G12 H12 π) := by
  choose f hf using symm_inl_of_dg π h
  have hne : ∀ i, f i true ≠ f i false := by
    intro i he
    have := π.symm.injective ((hf i true).trans ((congrArg _ (congrArg _ he)).trans
      (hf i false).symm))
    simp at this
  -- `π⁻¹(w_i^σ) = v_i^{r_i σ}` with `r_i := f i false`
  have hf' : ∀ i s, π.symm (.inl (i, s)) = .inl (i, Bool.xor s (f i false)) := by
    intro i s
    rw [hf]
    have := hne i
    cases s <;> cases hft : f i true <;> cases hff : f i false <;> simp_all
  obtain ⟨S, T, hST⟩ := exists_core_cut (fun i => f i false)
  have hA : ∀ p q : Core, alignedDiff G12 H12 π (.inl p) (.inl q) =
      ((Mr (fun i => f i false) p.1 q.1 * sg p.2 * sg q.2 : ℤ) : ℝ) := by
    rintro ⟨i, s⟩ ⟨j, t⟩
    simp only [alignedDiff, hf', adj_G12_inl_inl, adj_H12_inl_inl, Mr]
    rw [← Int.cast_sub, gCore_xor_sub_hCore]
  have hc := le_cutNorm (alignedDiff G12 H12 π) (S.map .inl) (T.map .inl)
  simp only [Finset.sum_map, Function.Embedding.inl_apply, hA] at hc
  refine le_trans ?_ (le_trans (le_abs_self _) hc)
  exact_mod_cast hST

/-- Lower bound of Lemma 33: `C_□(π) ≥ 8` for every bijection `π`. -/
lemma eight_le_cutNorm (π : Vtx ≃ Vtx) : 8 ≤ cutNorm (alignedDiff G12 H12 π) := by
  by_cases h : ∀ w, dg (π.symm w) = dg w
  · exact eight_le_of_dg π h
  · push Not at h
    obtain ⟨w, hw⟩ := h
    exact le_trans (by linarith [nine_le_of_dg_ne hw]) (abs_dg_sub_le π w)

/-- **Lemma 33.** `d_□(G, H) = 8`. -/
theorem lemma39 : dCut G12 H12 = 8 := by
  unfold dCut
  apply le_antisymm
  · exact (ciInf_le ⟨0, by rintro _ ⟨π, rfl⟩; exact cutNorm_nonneg _⟩ (Equiv.refl Vtx)).trans
      cutNorm_refl_le
  · exact le_ciInf eight_le_cutNorm

end GsimOT.Prop12
