/-
# Lemma 27: the fractional alignment `Q_r` has cost at most `1`

Paper, Appendix D.1, Lemma 27 (p. 27, l. 820; proof l. 821–837): `d₁^OT(G_r, H_r) = 1`.

Proof (paper).  For `i ∈ [r]` let `σ_i` be the shift along branch `i` and
`Q_r := (1/r) ∑_{i=1}^r P_{σ_i}`.  Since `Q_r` fixes all markers and all vertices of `K`, the
second item of Lemma 22 shows that `C₁(Q_r)` is the same w.r.t. `(G_r, H_r)` and w.r.t.
`(G⁰_r, H⁰_r)`.  The local cost of a supported pair of core vertices is the Hamming distance of
their patterns, which is `0` or `1`; the local cost of a marker `z` is the total `Q_r`-mass of
supported core pairs whose patterns differ at `z`: `1` for clock markers, `2/r` for tags, `1` for
bits.  Thus `C₁(Q_r) ≤ 1`, and equality follows from Lemma 29 since `G_r ≇ H_r`.

This file proves the upper bound `C₁(Q_r) ≤ 1` (`costOne_Qr_le_one`) and, by the same
computation, `C₁(σ_i) ≤ r` (used in the proof of Proposition 8).  The equality
`d₁^OT(G_r, H_r) = 1` is stated in `Proposition8.lean` as `lemma27`; it uses Lemma 29 with
`G_r ≇ H_r`, which the formalisation derives from Lemma 28.
-/
import GsimOT.Proposition8_LocalEditLowerBound.LockedGraphs

open Finset

namespace GsimOT.Prop8

variable {r : ℕ}

/-- The Hamming distance as a real sum of absolute differences of indicators. -/
lemma sum_abs_ind_eq_ham (x y : Marker r → Bool) :
    ∑ z, |(if x z then (1 : ℝ) else 0) - (if y z then 1 else 0)| = ham x y := by
  unfold ham
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  cases x z <;> cases y z <;> simp

/-! ### Local costs of a single shift `σ_i` in `(G⁰_r, H⁰_r)` -/

/-- For core vertices, `L_{σ_i}(x, y)` is the Hamming distance of the patterns. -/
lemma localCost_sigma_core (i : Fin r) (x y : Core r) :
    localCost (G0 r) (H0 r) (permMat (sigma i)) (.core x) (.core y) = ham (chiG x) (chiH y) := by
  rw [localCost_permMat, sum_base]
  have h1 : ∑ x' : Core r, |adj (G0 r) (.core x) (.core x') -
      adj (H0 r) (.core y) (sigma i (.core x'))| = 0 := by
    simp
  rw [h1, zero_add, ← sum_abs_ind_eq_ham]
  simp

/-- For a marker `z`, `L_{σ_i}(z, z)` is the number of times `z` changes along branch `i`. -/
lemma localCost_sigma_marker (hev : Even r) (i : Fin r) (z : Marker r) :
    localCost (G0 r) (H0 r) (permMat (sigma i)) (.marker z) (.marker z) = nchg i z := by
  rw [localCost_permMat, sum_base]
  have h2 : ∑ z' : Marker r, |adj (G0 r) (.marker z) (.marker z') -
      adj (H0 r) (.marker z) (sigma i (.marker z'))| = 0 := by simp
  rw [h2, add_zero]
  simp only [sigma_core, adj_bip_marker_core]
  -- the summand as a function of the core vertex
  set F : Core r → ℝ := fun x =>
    |(if chiG x z then (1 : ℝ) else 0) - (if chiH (shift i x) z then 1 else 0)| with hF
  change ∑ x, F x = _
  -- off branch `i` the summand vanishes
  have hoff : ∀ i' k, i' ≠ i → F (.v i' k) = 0 := by
    intro i' k hi
    simp only [hF, shift_off i i' hi]
    rw [chiG_eq_chiH_of_ne_u (by simp : (Core.v i' k : Core r) ≠ .u), sub_self, abs_zero]
  -- on branch `i`, the summand at time `t` compares `pat t` and `pat (t+1)`
  have hon : ∀ t < ell r, F (node i t) =
      if pat r i t z ≠ pat r i (t + 1) z then 1 else 0 := by
    intro t ht
    simp only [hF, shift_node i ht, chiG_node i ht,
      chiH_node hev i (t := t + 1) (by omega) (by omega)]
    cases pat r i t z <;> cases pat r i (t + 1) z <;> simp
  have hℓ := one_lt_ell i
  rw [sum_core, Finset.sum_eq_single i (fun i' _ hi => by simp [hoff i' _ hi]) (by simp)]
  -- reindex the branch by time
  have hu : F .u = if pat r i 0 z ≠ pat r i 1 z then 1 else 0 := by
    rw [← node_zero i]; exact hon 0 (by omega)
  have hv : ∀ k : Fin (ell r - 1), F (.v i k) =
      if pat r i (k.val + 1) z ≠ pat r i (k.val + 1 + 1) z then 1 else 0 := by
    intro k; rw [← node_succ i k]; exact hon _ (by have := k.isLt; omega)
  simp_rw [hu, hv]
  rw [Fin.sum_univ_eq_sum_range (fun k => if pat r i (k + 1) z ≠ pat r i (k + 1 + 1) z
    then (1 : ℝ) else 0)]
  unfold nchg
  rw [Finset.card_filter, Nat.cast_sum]
  conv_rhs => rw [show ell r = (ell r - 1) + 1 by omega, Finset.sum_range_succ']
  push_cast
  ring

/-! ### The fractional alignment `Q_r` -/

/-- `Q_r := (1/r) ∑_i P_{σ_i}` on `X ∪ M`. -/
noncomputable def Qr (r : ℕ) (a b : Base r) : ℝ := (1 / r) * ∑ i, permMat (sigma i) a b

lemma Qr_isDS (hr : 1 ≤ r) : IsDS (Qr r) where
  nonneg a b := mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
    (permMat_isDS (sigma i)).nonneg a b)
  row_sum a := by
    have hr0 : (r : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ r := by exact_mod_cast hr
                                 linarith
    unfold Qr
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [(permMat_isDS _).row_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    field_simp
  col_sum b := by
    have hr0 : (r : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ r := by exact_mod_cast hr
                                 linarith
    unfold Qr
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [(permMat_isDS _).col_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    field_simp

lemma Qr_marker (hr : 1 ≤ r) (z : Marker r) : Qr r (.marker z) (.marker z) = 1 := by
  simp [Qr, permMat]; field_simp

/-- `L_{Q_r}` is the average of the `L_{σ_i}`. -/
lemma localCost_Qr (a b : Base r) :
    localCost (G0 r) (H0 r) (Qr r) a b =
      (1 / r) * ∑ i, localCost (G0 r) (H0 r) (permMat (sigma i)) a b := by
  unfold localCost Qr
  have h1 : ∀ a' b', |disc (G0 r) (H0 r) a b a' b'| * ((1 / (r : ℝ)) * ∑ i, permMat (sigma i) a' b') =
      (1 / (r : ℝ)) * ∑ i, |disc (G0 r) (H0 r) a b a' b'| * permMat (sigma i) a' b' := by
    intro a' b'
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [h1, ← Finset.mul_sum]
  congr 1
  simp_rw [Finset.mul_sum]
  conv_lhs => arg 2; ext a'; rw [Finset.sum_comm]
  exact Finset.sum_comm

lemma exists_sigma_of_Qr_ne_zero {a b : Base r} (h : Qr r a b ≠ 0) : ∃ i, sigma i a = b := by
  by_contra hcon
  push Not at hcon
  apply h
  simp [Qr, permMat, hcon]

/-- Consecutive patterns along a shift differ in at most one marker. -/
lemma ham_shift_le_one (hev : Even r) (i : Fin r) (x : Core r) :
    ham (chiG x) (chiH (shift i x)) ≤ 1 := by
  rcases core_cases i x with ⟨t, ht, rfl⟩ | ⟨i', k, hi, rfl⟩
  · rw [shift_node i ht, chiG_node i ht, chiH_node hev i (by omega) (by omega)]
    exact ham_pat_succ_le_one i ht
  · rw [shift_off i i' hi]
    simp [ham, chiG, chiH]

/-- **Lemma 27, main computation.**  `C₁(Q_r) ≤ 1` w.r.t. `(G⁰_r, H⁰_r)`. -/
lemma costOne_Qr_base_le_one (hr : 2 ≤ r) (hev : Even r) :
    costOne (G0 r) (H0 r) (Qr r) ≤ 1 := by
  refine costOne_le zero_le_one fun a b hab => ?_
  obtain ⟨i, rfl⟩ := exists_sigma_of_Qr_ne_zero hab
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  rw [localCost_Qr]
  rcases a with x | z
  · -- supported core pairs: Hamming distance `≤ 1`, independent of the summation index
    simp only [sigma_core, localCost_sigma_core, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have := ham_shift_le_one hev i x
    have : (ham (chiG x) (chiH (shift i x)) : ℝ) ≤ 1 := by exact_mod_cast this
    field_simp
    nlinarith
  · -- markers: total mass of changes is `(1/r) ∑_i nchg i z ≤ 1`
    simp only [sigma_marker, localCost_sigma_marker hev]
    have := sum_nchg_le hr z
    have : (∑ i, (nchg i z : ℝ)) ≤ r := by exact_mod_cast this
    rw [div_mul_eq_mul_div, one_mul, div_le_one hrR]
    exact this

/-- `C₁(σ_i) ≤ r` w.r.t. `(G⁰_r, H⁰_r)`: core pairs cost at most `1`, markers at most `r`. -/
lemma costOne_sigma_base_le (hr : 2 ≤ r) (hev : Even r) (i : Fin r) :
    costOne (G0 r) (H0 r) (permMat (sigma i)) ≤ r := by
  refine costOne_le (by positivity) fun a b hab => ?_
  have hb : sigma i a = b := (permMat_ne_zero_iff _ a b).1 hab
  subst hb
  rcases a with x | z
  · rw [sigma_core, localCost_sigma_core]
    have := ham_shift_le_one hev i x
    have : (ham (chiG x) (chiH (shift i x)) : ℝ) ≤ 1 := by exact_mod_cast this
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  · rw [sigma_marker, localCost_sigma_marker hev]
    exact_mod_cast nchg_le hr i z

/-! ### Lifting to `(G_r, H_r)` via Lemma 22 (2) -/

/-- `Q_r` extended by the identity on the clique `K`. -/
noncomputable def QrExt (r : ℕ) : Vr r → Vr r → ℝ := extendId (Qr r)

lemma QrExt_isDS (hr : 1 ≤ r) : IsDS (QrExt r) := extendId_isDS (Qr_isDS hr)

/-- **Lemma 27 (upper bound).** `C₁(Q_r) ≤ 1` w.r.t. `(G_r, H_r)`. -/
lemma costOne_Qr_le_one (hr : 2 ≤ r) (hev : Even r) :
    costOne (Gr r) (Hr r) (QrExt r) ≤ 1 := by
  have hz1 : ∀ j, Qr r (markerEnum r j) (markerEnum r j) = 1 := fun j => by
    simp only [markerEnum]; exact Qr_marker (by omega) _
  unfold Gr Hr QrExt
  rw [lemma22_cost (Qr_isDS (by omega)) hz1]
  exact costOne_Qr_base_le_one hr hev

/-- The bijection `σ_i` extended by the identity on `K`. -/
def sigmaExt (i : Fin r) : Vr r ≃ Vr r := (sigma i).sumCongr (Equiv.refl _)

/-- `C₁(σ_i) ≤ r` w.r.t. `(G_r, H_r)`. -/
lemma costOneBij_sigmaExt_le (hr : 2 ≤ r) (hev : Even r) (i : Fin r) :
    costOneBij (Gr r) (Hr r) (sigmaExt i) ≤ r := by
  have hz1 : ∀ j, permMat (sigma i) (markerEnum r j) (markerEnum r j) = 1 := fun j => by
    simp [markerEnum, permMat]
  unfold costOneBij sigmaExt Gr Hr
  rw [← extendId_permMat, lemma22_cost (permMat_isDS _) hz1]
  exact costOne_sigma_base_le hr hev i

end GsimOT.Prop8
