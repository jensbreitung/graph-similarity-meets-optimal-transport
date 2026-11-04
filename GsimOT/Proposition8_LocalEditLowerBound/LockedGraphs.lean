/-
# `G_r`, `H_r` (applying Lemma 22) and the shifts `σ_i`

Paper, Appendix D.1 (p. 26, l. 803–809):

> To force every bijection of small cost to fix markers and preserve core vertices, let `G_r` and
> `H_r` be obtained from `G⁰_r` and `H⁰_r`, respectively, by applying Lemma 22 with their markers
> enumerated `z₁, …, z_{n_M}` (ordered non-decreasingly in order of their degrees in `G⁰_r`),
> `Δ := n_X`, `τ := r` and `δ := 1`.

and, from the proof of Lemma 27 (p. 27, l. 821–823),

> For `i ∈ [r]`, let `σ_i` be the bijection from `G_r` to `H_r` that acts as the identity on the
> marker vertices and shifts the core vertices of the `i`-th branch along one step, that is
> `σ_i(u) = v_{i,1}`, `σ_i(v_{i,k}) = v_{i,k+1}` for `k ∈ [ℓ-2]` and `σ_i(v_{i,ℓ-1}) = u`.
-/
import GsimOT.Proposition8_LocalEditLowerBound.Patterns

open Finset

namespace GsimOT.Prop8

variable {r : ℕ}

/-! ### The marker enumeration and the graphs `G_r`, `H_r` -/

/-- The number of markers `n_M`. -/
abbrev nM (r : ℕ) : ℕ := Fintype.card (Marker r)
/-- The number of core vertices `n_X`. -/
abbrev nX (r : ℕ) : ℕ := Fintype.card (Core r)

/-- The degree of the `j`-th marker (in an arbitrary fixed enumeration) in `G⁰_r`. -/
noncomputable def markerDeg (r : ℕ) (j : Fin (nM r)) : ℕ :=
  deg (G0 r) (.marker ((Fintype.equivFin (Marker r)).symm j))

/-- The markers `z₁, …, z_{n_M}`, enumerated non-decreasingly by their degree in `G⁰_r`. -/
noncomputable def markerEnum (r : ℕ) (j : Fin (nM r)) : Base r :=
  .marker ((Fintype.equivFin (Marker r)).symm (Tuple.sort (markerDeg r) j))

lemma markerEnum_injective : Function.Injective (markerEnum r) := by
  intro a b h
  simp only [markerEnum, Base.marker.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  exact h

lemma markerEnum_mono (a b : Fin (nM r)) (hab : a ≤ b) :
    deg (G0 r) (markerEnum r a) ≤ deg (G0 r) (markerEnum r b) :=
  Tuple.monotone_sort (markerDeg r) hab

lemma exists_markerEnum (z : Marker r) : ∃ j, markerEnum r j = .marker z := by
  refine ⟨(Tuple.sort (markerDeg r)).symm (Fintype.equivFin (Marker r) z), ?_⟩
  simp [markerEnum]

/-- The size of the clique added by Lemma 22. -/
abbrev mK (r : ℕ) : ℕ := lockSize (nM r) (nX r) r 1

/-- The common vertex set `V(G_r) = V(H_r) = X ∪ M ∪ K`. -/
abbrev Vr (r : ℕ) : Type := Base r ⊕ Fin (mK r)

/-- **The graph `G_r`.** -/
noncomputable def Gr (r : ℕ) : SimpleGraph (Vr r) := lockGraph (G0 r) (markerEnum r) (nX r) r 1
/-- **The graph `H_r`.** -/
noncomputable def Hr (r : ℕ) : SimpleGraph (Vr r) := lockGraph (H0 r) (markerEnum r) (nX r) r 1

noncomputable instance : DecidableRel (Gr r).Adj := by unfold Gr; infer_instance
noncomputable instance : DecidableRel (Hr r).Adj := by unfold Hr; infer_instance

/-- **Size of `G_r`:** `|V(G_r)| + r = 5r³ + 10r² + 4`, in particular `|V(G_r)| = Θ(r³)`. -/
lemma card_Vr (hr : 1 ≤ r) : Fintype.card (Vr r) + r = 5 * r ^ 3 + 10 * r ^ 2 + 4 := by
  simp only [Vr, mK, nM, nX, lockSize, Fintype.card_sum, Fintype.card_fin, card_base,
    card_marker hr, card_core, ell]
  obtain ⟨r', rfl⟩ := Nat.exists_eq_add_of_le hr
  have : (1 + r') * (1 + r') + 2 * (1 + r') - 1 = r' * r' + 4 * r' + 2 := by ring_nf; omega
  rw [this]
  ring

lemma card_Vr_bounds (hr : 1 ≤ r) :
    r ^ 3 ≤ Fintype.card (Vr r) ∧ Fintype.card (Vr r) ≤ 19 * r ^ 3 := by
  have h := card_Vr hr
  have h1 : r ≤ r ^ 3 := by
    calc r = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ 3 := Nat.pow_le_pow_right hr (by norm_num)
  have h2 : r ^ 2 ≤ r ^ 3 := Nat.pow_le_pow_right hr (by norm_num)
  have h3 : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ hr
  constructor <;> omega

/-! ### Hypotheses of Lemma 22 for `G⁰_r`, `H⁰_r` -/

lemma lock_hyp_deg_G (hr : 1 ≤ r) (a : Base r) : deg (G0 r) a ≤ nX r := deg_bip_le hr _ a
lemma lock_hyp_deg_H (hr : 1 ≤ r) (a : Base r) : deg (H0 r) a ≤ nX r := deg_bip_le hr _ a

lemma lock_hyp_delta (j : Fin (nM r)) :
    deg (G0 r) (markerEnum r j) ≤ deg (H0 r) (markerEnum r j) + 1 ∧
      deg (H0 r) (markerEnum r j) ≤ deg (G0 r) (markerEnum r j) + 1 := by
  simp only [markerEnum]
  rw [deg_H0_marker]
  constructor <;> split_ifs <;> omega

/-! ### The shifts `σ_i` -/

/-- The core vertex of branch `i` at time `t` (time `0` and times `≥ ℓ` give `u`). -/
def node (i : Fin r) (t : ℕ) : Core r :=
  if h : 1 ≤ t ∧ t ≤ ell r - 1 then .v i ⟨t - 1, by omega⟩ else .u

lemma node_zero (i : Fin r) : node i 0 = .u := by simp [node]

lemma node_succ (i : Fin r) (k : Fin (ell r - 1)) : node i (k.val + 1) = .v i k := by
  have := k.isLt
  simp only [node]
  rw [dite_eq_left (by omega)]
  rfl

lemma node_ell (i : Fin r) : node i (ell r) = .u := by
  simp only [node]; rw [dite_eq_right (by omega)]

lemma one_lt_ell (i : Fin r) : 2 ≤ ell r := by
  have := i.isLt; unfold ell; nlinarith

/-- `σ_i` on core vertices. -/
def shift (i : Fin r) : Core r → Core r
  | .u => node i 1
  | .v i' k => if i' = i then node i (k.val + 2) else .v i' k

/-- `σ_i⁻¹` on core vertices. -/
def unshift (i : Fin r) : Core r → Core r
  | .u => node i (ell r - 1)
  | .v i' k => if i' = i then node i k.val else .v i' k

lemma node_eq_v (i : Fin r) {t : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ ell r - 1) :
    node i t = .v i ⟨t - 1, by omega⟩ := by
  simp only [node]; rw [dite_eq_left ⟨h1, h2⟩]

lemma node_eq_u (i : Fin r) {t : ℕ} (h : t = 0 ∨ ell r ≤ t) : node i t = .u := by
  simp only [node]; rw [dite_eq_right (by omega)]

lemma unshift_shift (i : Fin r) (x : Core r) : unshift i (shift i x) = x := by
  have h2 := one_lt_ell i
  cases x with
  | u =>
    simp only [shift]
    rw [node_eq_v i (le_refl 1) (by omega)]
    simp only [unshift, ite_true]
    exact node_eq_u i (Or.inl rfl)
  | v i' k =>
    have hk := k.isLt
    by_cases hi : i' = i
    · subst hi
      simp only [shift, ite_true]
      by_cases hk2 : k.val + 2 ≤ ell r - 1
      · rw [node_eq_v i' (by omega) hk2]
        simp only [unshift, ite_true]
        rw [node_eq_v i' (by omega) (by omega)]
        congr 1
      · rw [node_eq_u i' (Or.inr (by omega))]
        simp only [unshift]
        rw [node_eq_v i' (by omega) le_rfl]
        congr 1; ext; simp; omega
    · simp [shift, unshift, hi]

lemma shift_unshift (i : Fin r) (x : Core r) : shift i (unshift i x) = x := by
  have h2 := one_lt_ell i
  cases x with
  | u =>
    simp only [unshift]
    rw [node_eq_v i (by omega) le_rfl]
    simp only [shift, ite_true]
    exact node_eq_u i (Or.inr (by omega))
  | v i' k =>
    have hk := k.isLt
    by_cases hi : i' = i
    · subst hi
      simp only [unshift, ite_true]
      by_cases hk0 : 1 ≤ k.val
      · rw [node_eq_v i' hk0 (by omega)]
        simp only [shift, ite_true]
        rw [node_eq_v i' (by omega) (by omega)]
        congr 1; ext; simp; omega
      · rw [node_eq_u i' (Or.inl (by omega))]
        simp only [shift]
        rw [node_eq_v i' le_rfl (by omega)]
        congr 1; ext; simp; omega
    · simp [shift, unshift, hi]

/-- `σ_i` as a permutation of the core. -/
def shiftPerm (i : Fin r) : Equiv.Perm (Core r) :=
  ⟨shift i, unshift i, unshift_shift i, shift_unshift i⟩

/-- `σ_i` as a permutation of `X ∪ M` (the identity on markers). -/
def sigma (i : Fin r) : Equiv.Perm (Base r) :=
  ((baseEquiv r).trans ((shiftPerm i).sumCongr (Equiv.refl _))).trans (baseEquiv r).symm

@[simp] lemma sigma_core (i : Fin r) (x : Core r) : sigma i (.core x) = .core (shift i x) := rfl
@[simp] lemma sigma_marker (i : Fin r) (z : Marker r) : sigma i (.marker z) = .marker z := rfl

lemma shift_node (i : Fin r) {t : ℕ} (ht : t < ell r) : shift i (node i t) = node i (t + 1) := by
  rcases t with _ | t
  · simp [node_zero, shift]
  · have hk : t < ell r - 1 := by omega
    rw [show t + 1 = (⟨t, hk⟩ : Fin (ell r - 1)).val + 1 from rfl, node_succ]
    simp [shift]

lemma shift_off (i i' : Fin r) (hi : i' ≠ i) (k : Fin (ell r - 1)) :
    shift i (.v i' k) = .v i' k := by
  simp [shift, hi]

/-- Every core vertex is either on branch `i` (including `u`) or fixed by `σ_i`. -/
lemma core_cases (i : Fin r) (x : Core r) :
    (∃ t < ell r, x = node i t) ∨ (∃ i' k, i' ≠ i ∧ x = .v i' k) := by
  cases x with
  | u => exact Or.inl ⟨0, by have := one_lt_ell i; omega, (node_zero i).symm⟩
  | v i' k =>
    by_cases hi : i' = i
    · subst hi
      exact Or.inl ⟨k.val + 1, by have := k.isLt; omega, (node_succ i' k).symm⟩
    · exact Or.inr ⟨i', k, hi, rfl⟩

/-- The pattern in `G_r` along branch `i`. -/
lemma chiG_node (i : Fin r) {t : ℕ} (ht : t < ell r) : chiG (node i t) = pat r i t := by
  rcases t with _ | t
  · rw [node_zero, chiG_u, pat_zero]
  · have hk : t < ell r - 1 := by omega
    rw [show t + 1 = (⟨t, hk⟩ : Fin (ell r - 1)).val + 1 from rfl, node_succ]
    rfl

/-- The pattern in `H_r` along branch `i` (time `ℓ` is `u`, uses that `r` is even). -/
lemma chiH_node (hev : Even r) (i : Fin r) {t : ℕ} (ht1 : 1 ≤ t) (ht : t ≤ ell r) :
    chiH (node i t) = pat r i t := by
  rcases Nat.lt_or_ge t (ell r) with h | h
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' ht1
    have hk : t < ell r - 1 := by omega
    rw [show t + 1 = (⟨t, hk⟩ : Fin (ell r - 1)).val + 1 from rfl, node_succ]
    rfl
  · have : t = ell r := by omega
    subst this
    rw [node_ell, chiH_u, pat_ell hev]

end GsimOT.Prop8
