import GsimOT.Theorem18_OperatorNormHardness.Corollary20_ColumnBound
import GsimOT.Common.Leaves

/-!
# Claim 55

Claim 55 of the proof of Theorem 17 (p. 55, l. 1741–1742; proof l. 1743–1759).

The graphs `G`, `H` of Theorem 17 carry `M` leaves at every base vertex. If a base vertex `v` of
`G` (with a base neighbour) sends mass `η` to the leaves of `H` and `M > 2(4/η)² + 1`, then
`‖B_p(G, H, Q)‖_p > 2^{b(p)}` (`claim54`). The proof finds `M - 1` entries of size `η/4` in
column `v` of `A^Q` and applies Corollary 54.
-/

open Finset Matrix WithLp
open scoped ENNReal

namespace GsimOT.Hardness

section Claims54And55

/-- Entries of `A^Q` for adjacent `x, x'`: `A^Q(x,x') = ∑ Q(x,y) (1 - A_H(y,y')) Q(x',y')`. -/
lemma aggMatrix_of_adj {V W : Type*} [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (Q : V → W → ℝ) {x x' : V} (h : G.Adj x x') :
    aggMatrix G H Q x x' = ∑ y, ∑ y', Q x y * (1 - adj H y y') * Q x' y' := by
  simp [aggMatrix, disc, adj, h]

/-- Entries of `A^Q` for non-adjacent `x, x'`: `A^Q(x,x') = -∑ Q(x,y) A_H(y,y') Q(x',y')`. -/
lemma aggMatrix_of_not_adj {V W : Type*} [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (Q : V → W → ℝ) {x x' : V} (h : ¬G.Adj x x') :
    aggMatrix G H Q x x' = -∑ y, ∑ y', Q x y * adj H y y' * Q x' y' := by
  simp only [aggMatrix, disc, adj, h, ite_false, zero_sub, mul_neg,
    neg_mul, sum_neg_distrib]

/-- `(2^{b(p)} a)^{1/b(p)} ≤ 2a²` for `a ≥ 1`: the size condition of Claims 55 and 56. -/
lemma rpow_inv_bExp_le {p : ℝ≥0∞} [Fact (1 ≤ p)] {a : ℝ} (ha : 1 ≤ a) :
    (2 ^ bExp p * a) ^ (1 / bExp p) ≤ 2 * a ^ 2 := by
  have hb := half_le_bExp p
  have hb0 : 0 < bExp p := by linarith
  rw [Real.mul_rpow (by positivity) (by linarith), ← Real.rpow_mul (by norm_num),
    mul_one_div_cancel hb0.ne', Real.rpow_one]
  gcongr
  calc a ^ (1 / bExp p) ≤ a ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ha (by rw [div_le_iff₀ hb0]; linarith)
    _ = a ^ 2 := by norm_cast

variable {βG βH : Type*} [Fintype βG] [Fintype βH] [DecidableEq βG] [DecidableEq βH]
  {G' : SimpleGraph βG} {H' : SimpleGraph βH} [DecidableRel G'.Adj] [DecidableRel H'.Adj]
  {M : ℕ} {Q : (βG ⊕ Σ _ : βG, Fin M) → (βH ⊕ Σ _ : βH, Fin M) → ℝ} {p : ℝ≥0∞}
  [Fact (1 ≤ p)]

local notation "GG" => addLeaves G' fun _ : βG ↦ M
local notation "HH" => addLeaves H' fun _ : βH ↦ M

/-- A base vertex with a base neighbour has at least `M + 1` neighbours. -/
lemma card_adj_inl_ge {v u : βG} (hu : G'.Adj u v) :
    (M : ℝ) + 1 ≤ #({x | (GG).Adj x (.inl v)} : Finset (βG ⊕ Σ _ : βG, Fin M)) := by
  have hsub : insert (.inl u) (leavesOf (fun _ : βG ↦ M) v) ⊆
      ({x | (GG).Adj x (.inl v)} : Finset (βG ⊕ Σ _ : βG, Fin M)) := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · simpa using hu
    · obtain ⟨t, rfl⟩ := mem_leavesOf.mp hx
      simp
  have := card_le_card hsub
  rw [card_insert_of_notMem (by simp [mem_leavesOf]), card_leavesOf] at this
  exact_mod_cast this

/-- **Claim 55.** If a base vertex `v` (with a base neighbour) sends mass `η` to the leaves of `H`
and `M > 2(4/η)² + 1`, then `‖B_p(G, H, Q)‖_p > 2^{b(p)}`. -/
lemma claim54 (hQ : IsDS Q) {v : βG} (hv : ∃ u, G'.Adj u v) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hvL : η ≤ ∑ t, Q (.inl v) (.inr t)) (hM : 2 * (4 / η) ^ 2 + 1 < M) :
    2 ^ bExp p < opNorm p p (Bmat p p GG HH Q) := by
  obtain ⟨u, hu⟩ := hv
  set N : Finset (βG ⊕ Σ _ : βG, Fin M) := {x | (GG).Adj x (.inl v)}
  have hN := card_adj_inl_ge (M := M) hu
  have hb0 : 0 < bExp p := lt_of_lt_of_le (by norm_num) (half_le_bExp p)
  have hnum : (2 ^ bExp p / (η / 4)) ^ (1 / bExp p) ≤ 2 * (4 / η) ^ 2 := by
    have : 2 ^ bExp p / (η / 4) = 2 ^ bExp p * (4 / η) := by field_simp
    rw [this]
    exact rpow_inv_bExp_le (by rw [le_div_iff₀ hη]; linarith)
  have hF (x : βG ⊕ Σ _ : βG, Fin M) (y y') :
      0 ≤ Q x y * (1 - adj HH y y') * Q (.inl v) y' :=
    mul_nonneg (mul_nonneg (hQ.nonneg _ _) (sub_nonneg.mpr (adj_le_one _ _ _)))
      (hQ.nonneg _ _)
  -- the entry `A^Q(x, v)` is at least the part of the sum over the leaves `y'`
  have hleaves (x) (hx : x ∈ N) (c : βH ⊕ (Σ _ : βH, Fin M) → ℝ)
      (hc : ∀ y, c y ≤ ∑ t, (1 - adj HH y (.inr t)) * Q (.inl v) (.inr t)) :
      ∑ y, Q x y * c y ≤ aggMatrix GG HH Q x (.inl v) := by
    rw [aggMatrix_of_adj _ _ _ (mem_filter.mp hx).2]
    refine sum_le_sum fun y _ ↦ ?_
    calc Q x y * c y ≤ Q x y * ∑ t, (1 - adj HH y (.inr t)) * Q (.inl v) (.inr t) :=
          mul_le_mul_of_nonneg_left (hc y) (hQ.nonneg _ _)
      _ = ∑ t, Q x y * (1 - adj HH y (.inr t)) * Q (.inl v) (.inr t) := by
          rw [mul_sum]; exact sum_congr rfl fun t _ ↦ by ring
      _ ≤ ∑ y', Q x y * (1 - adj HH y y') * Q (.inl v) y' := by
          rw [Fintype.sum_sum_type]
          linarith [sum_nonneg fun b (_ : b ∈ univ) ↦ hF x y (.inl b)]
  by_cases hcase : ∀ w : βH, ∑ s : Fin M, Q (.inl v) (.inr ⟨w, s⟩) ≤ η / 2
  · -- Case 1: every neighbour `x` of `v` gives an entry `A^Q(x, v) ≥ η/2`
    have hinner (y : βH ⊕ Σ _ : βH, Fin M) :
        η / 2 ≤ ∑ t, (1 - adj HH y (.inr t)) * Q (.inl v) (.inr t) := by
      have hsplit : ∑ t, (1 - adj HH y (.inr t)) * Q (.inl v) (.inr t) =
          ∑ t, Q (.inl v) (.inr t) - ∑ t, adj HH y (.inr t) * Q (.inl v) (.inr t) := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun t _ ↦ by ring
      have hle : ∑ t, adj HH y (.inr t) * Q (.inl v) (.inr t) ≤ η / 2 := by
        cases y with
        | inl b =>
          simp only [adj_addLeaves_inl_inr, ite_mul, one_mul, zero_mul]
          rw [Fintype.sum_sigma, Fintype.sum_eq_single b fun b' hb' ↦ by simp [hb']]
          simpa using hcase b
        | inr t' =>
          simp only [adj_addLeaves_inr, reduceCtorEq, ite_false, zero_mul,
            sum_const_zero]
          linarith
      rw [hsplit]
      linarith
    refine lt_opNorm_Bpq GG HH hQ (v := .inl v) (K := N) (ε := η / 4) (by positivity)
      (by positivity) (fun x hx ↦ ?_) ?_
    · have h := hleaves x hx (fun _ ↦ η / 2) hinner
      rw [← sum_mul, hQ.row_sum, one_mul] at h
      rw [abs_of_nonneg (by linarith)]
      linarith
    · linarith
  · -- Case 2: `v` sends mass `> η/2` to the leaves of a single `w`
    obtain ⟨w, hw⟩ := not_forall.mp hcase
    replace hw := lt_of_not_ge hw
    set K := {x ∈ N | Q x (.inl w) ≤ 1 / 2}
    have hK : (M : ℝ) - 1 ≤ #K := by
      have h1 := card_mul_le_of_lt_mass hQ N {.inl w} (1 / 2)
      have h2 := card_filter_add_card_filter_not (s := N) fun x ↦ Q x (.inl w) ≤ 1 / 2
      simp only [sum_singleton, card_singleton, Nat.cast_one, not_le] at h1 h2
      have h3 : (#K : ℝ) + #{x ∈ N | 1 / 2 < Q x (.inl w)} = #N := by exact_mod_cast h2
      linarith
    have hinner (y : βH ⊕ Σ _ : βH, Fin M) :
        (if y = .inl w then 0 else η / 2) ≤
          ∑ t, (1 - adj HH y (.inr t)) * Q (.inl v) (.inr t) := by
      split_ifs with hy
      · exact sum_nonneg fun t _ ↦ mul_nonneg (sub_nonneg.mpr (adj_le_one _ _ _))
          (hQ.nonneg _ _)
      · calc η / 2 ≤ ∑ s : Fin M, Q (.inl v) (.inr ⟨w, s⟩) := hw.le
          _ ≤ ∑ s : Fin M, (1 - adj HH y (.inr ⟨w, s⟩)) * Q (.inl v) (.inr ⟨w, s⟩) := by
              refine le_of_eq (sum_congr rfl fun s _ ↦ ?_)
              have : adj HH y (.inr ⟨w, s⟩) = 0 := by
                rw [adj_symm HH, adj_addLeaves_inr]
                simp [hy]
              rw [this, sub_zero, one_mul]
          _ ≤ ∑ t, (1 - adj HH y (.inr t)) * Q (.inl v) (.inr t) := by
              rw [Fintype.sum_sigma]
              exact single_le_sum (f := fun b ↦ ∑ s : Fin M,
                (1 - adj HH y (.inr ⟨b, s⟩)) * Q (.inl v) (.inr ⟨b, s⟩))
                (fun b _ ↦ sum_nonneg fun s _ ↦ mul_nonneg
                  (sub_nonneg.mpr (adj_le_one _ _ _)) (hQ.nonneg _ _)) (mem_univ w)
    refine lt_opNorm_Bpq GG HH hQ (v := .inl v) (K := K) (ε := η / 4) (by positivity)
      (by positivity) (fun x hx ↦ ?_) ?_
    · obtain ⟨hxN, hxw⟩ := mem_filter.mp hx
      have h := hleaves x hxN _ hinner
      have hsum : ∑ y, Q x y * (if y = .inl w then 0 else η / 2) =
          (1 - Q x (.inl w)) * (η / 2) := by
        have h' (y) : Q x y * (if y = .inl w then 0 else η / 2) =
            Q x y * (η / 2) - (if y = .inl w then Q x y * (η / 2) else 0) := by
          split_ifs <;> ring
        simp_rw [h']
        rw [sum_sub_distrib, ← sum_mul, hQ.row_sum]
        simp only [sum_ite_eq', mem_univ, ite_true]
        ring
      rw [hsum] at h
      rw [abs_of_nonneg (by nlinarith [hQ.nonneg x (.inl w)])]
      nlinarith
    · linarith

end Claims54And55

end GsimOT.Hardness
