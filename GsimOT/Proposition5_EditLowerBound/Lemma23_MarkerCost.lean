/-
# Lemma 23: the cost of the core-marker pairs

Paper, Appendix C.1, Lemma 23 (p. 22, l. 700–702; proof l. 703–706): For every compliant
`Q ∈ DS(V, W)`, the core-marker pairs contribute exactly
`2 ∑_{v_i ∈ S_G, w_j ∈ S_H} Q(v_i, w_j) ℓ(v_i, w_j)` to `C_ed(Q)`.

Here `Q` is *compliant* if it acts as the identity on the markers and on the clique added by
Lemma 22, and `ℓ(v_i, w_j) := min_{k ∈ ℤ} |i - j + 2kN|` is the distance of the positions `i` and
`j` on the cycle `C_{2N}` (l. 695–699).  The proof: mapping `v_i` to `w_j` changes the adjacency
to exactly `ℓ(v_i, w_j)` markers (Figure 4), and each core-marker pair is counted in both
orientations.

Formalisation notes.
* A compliant `Q` is `extendId (extMarkers R)` for the restriction `R` of `Q` to the core
  vertices: `extMarkers R` extends `R` by the identity on the markers and `extendId` (from
  Lemma 22) by the identity on the clique.
* `card_semicircle_ne` is the counting step: the number of semicircles `I_r` that contain exactly
  one of two positions `x, y` is their cyclic distance `cycDist N x y`.
* `costEdit_extMarkers` splits `C_ed` w.r.t. `(G', H')` into the core-core pairs (`coreCost`), the
  core-marker pairs (Lemma 23) and the marker-marker pairs (which contribute nothing).  By
  Lemma 22 (2) the same holds w.r.t. `(G, H)` (`lemma23`).
-/
import GsimOT.Proposition5_EditLowerBound.Construction

open Finset

namespace GsimOT.Prop5

variable {N : ℕ}

/-! ### Counting markers -/

/-- The distance `ℓ` of two positions `x, y ∈ {0, …, 2N - 1}` on the cycle `C_{2N}`. The paper
writes `ℓ(v_i, w_j) := min_{k ∈ ℤ} |i - j + 2kN|`, which for `i, j ∈ {0, …, 2N - 1}` is
`min(|i - j|, 2N - |i - j|)`; here `|x - y| = (x - y) + (y - x)` in `ℕ`. -/
def cycDist (N x y : ℕ) : ℕ := min (x - y + (y - x)) (2 * N - (x - y + (y - x)))

lemma cycDist_comm (x y : ℕ) : cycDist N x y = cycDist N y x := by
  unfold cycDist; omega

/-- `|[p] - [q]| = [p ∧ ¬q] + [q ∧ ¬p]`. -/
lemma abs_ite_sub_ite (p q : Prop) [Decidable p] [Decidable q] :
    |(if p then (1 : ℝ) else 0) - (if q then 1 else 0)| =
      (if p ∧ ¬q then 1 else 0) + (if q ∧ ¬p then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- Moving a core vertex from position `x` to position `y` changes its adjacency to exactly
`ℓ(x, y)` markers (Figure 4): the number of semicircles `I_r`, `r ∈ {0, …, N - 1}`, that contain
exactly one of `x` and `y` is `ℓ(x, y)`. -/
lemma card_semicircle_ne {x y : ℕ} (hx : x < 2 * N) (hy : y < 2 * N) :
    ∑ r : Fin N, |(if r.val ≤ x ∧ x < r.val + N then (1 : ℝ) else 0) -
      (if r.val ≤ y ∧ y < r.val + N then 1 else 0)| = cycDist N x y := by
  wlog hxy : x ≤ y generalizing x y
  · rw [cycDist_comm, ← this hy hx (by omega)]
    exact sum_congr rfl fun r _ => abs_sub_comm _ _
  rw [Fin.sum_univ_eq_sum_range (fun r => |(if r ≤ x ∧ x < r + N then (1 : ℝ) else 0) -
      (if r ≤ y ∧ y < r + N then 1 else 0)|) N]
  simp only [abs_ite_sub_ite, sum_add_distrib, sum_boole]
  -- positions in `I_r` for `x` but not for `y`, and conversely, form intervals of indices `r`
  have hA : {r ∈ range N | (r ≤ x ∧ x < r + N) ∧ ¬(r ≤ y ∧ y < r + N)} =
      Ico (x + 1 - N) (min (x + 1) (y + 1 - N)) := by
    ext r; simp only [mem_filter, mem_range, mem_Ico]; omega
  have hB : {r ∈ range N | (r ≤ y ∧ y < r + N) ∧ ¬(r ≤ x ∧ x < r + N)} =
      Ico (max (x + 1) (y + 1 - N)) (min (y + 1) N) := by
    ext r; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [hA, hB, Nat.card_Ico, Nat.card_Ico]
  exact_mod_cast (show min (x + 1) (y + 1 - N) - (x + 1 - N) +
    (min (y + 1) N - max (x + 1) (y + 1 - N)) = cycDist N x y by unfold cycDist; omega)

/-- `ℓ(v_{2c}, w_{2d+1})`: the distance of the positions of the core vertex `v_{2c}` of `G'` and the
core vertex `w_{2d+1}` of `H'`. -/
def ell (c d : Fin N) : ℕ := cycDist N (posG c) (posH d)

/-- Mapping `v_{2c}` to `w_{2d+1}` changes the adjacency to exactly `ℓ(v_{2c}, w_{2d+1})`
markers. -/
lemma sum_marker_inl (c d : Fin N) :
    ∑ r : Fin N, |adj (Gp N) (.inl c) (.inr r) - adj (Hp N) (.inl d) (.inr r)| = ell c d := by
  simp only [adj_Gp_inl_inr, adj_Hp_inl_inr]
  exact card_semicircle_ne (by omega) (by omega)

lemma sum_marker_inr (c d : Fin N) :
    ∑ r : Fin N, |adj (Gp N) (.inr r) (.inl c) - adj (Hp N) (.inr r) (.inl d)| = ell c d := by
  simp only [adj_Gp_inr_inl, adj_Hp_inr_inl]
  exact card_semicircle_ne (by omega) (by omega)

/-! ### Compliant fractional alignments -/

/-- The extension of `R ∈ ℝ^{S_G × S_H}` (on the core vertices) by the identity on the markers. -/
def extMarkers (R : Fin N → Fin N → ℝ) : Base N → Base N → ℝ
  | .inl c, .inl d => R c d
  | .inr r, .inr r' => if r = r' then 1 else 0
  | _, _ => 0

@[simp] lemma extMarkers_inl_inl (R : Fin N → Fin N → ℝ) (c d : Fin N) :
    extMarkers R (.inl c) (.inl d) = R c d := rfl
@[simp] lemma extMarkers_inr_inr (R : Fin N → Fin N → ℝ) (r r' : Fin N) :
    extMarkers R (.inr r) (.inr r') = if r = r' then 1 else 0 := rfl
@[simp] lemma extMarkers_inl_inr (R : Fin N → Fin N → ℝ) (c r : Fin N) :
    extMarkers R (.inl c) (.inr r) = 0 := rfl
@[simp] lemma extMarkers_inr_inl (R : Fin N → Fin N → ℝ) (r c : Fin N) :
    extMarkers R (.inr r) (.inl c) = 0 := rfl

lemma extMarkers_isDS {R : Fin N → Fin N → ℝ} (hR : IsDS R) : IsDS (extMarkers R) where
  nonneg := by
    rintro (c | r) (d | r') <;> simp [hR.nonneg, apply_ite]
  row_sum := by
    rintro (c | r) <;> simp [Fintype.sum_sum_type, hR.row_sum]
  col_sum := by
    rintro (d | r) <;> simp [Fintype.sum_sum_type, hR.col_sum]

/-- A bijection that maps the core onto the core by `ρ` and fixes the markers. -/
lemma extMarkers_permMat (ρ : Fin N ≃ Fin N) :
    extMarkers (permMat ρ) = permMat (ρ.sumCongr (Equiv.refl (Fin N))) := by
  funext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [permMat, extMarkers]

/-- The contribution of the core-core pairs to `C_ed`:
`∑ |A_{G'}(v_{2c}, v_{2c'}) - A_{H'}(w_{2d+1}, w_{2d'+1})| R(c, d) R(c', d')`. -/
def coreCost (N : ℕ) (R : Fin N → Fin N → ℝ) : ℝ :=
  ∑ c, ∑ d, ∑ c', ∑ d',
    |adj (Gp N) (.inl c) (.inl c') - adj (Hp N) (.inl d) (.inl d')| * R c d * R c' d'

/-- `C_ed` of a fractional alignment that fixes the markers, w.r.t. `(G', H')`: the core-core
pairs contribute `coreCost N R`, the core-marker pairs `2 ∑ R(c, d) ℓ(c, d)` (Lemma 23), and the
marker-marker pairs nothing. -/
theorem costEdit_extMarkers (R : Fin N → Fin N → ℝ) :
    costEdit (Gp N) (Hp N) (extMarkers R) = coreCost N R + 2 * ∑ c, ∑ d, R c d * ell c d := by
  unfold costEdit disc
  simp only [Fintype.sum_sum_type, extMarkers_inl_inl, extMarkers_inr_inr, extMarkers_inl_inr,
    extMarkers_inr_inl, adj_Gp_inr_inr, adj_Hp_inr_inr, mul_zero, zero_mul, sum_const_zero,
    add_zero, zero_add, mul_ite, mul_one, sum_ite_eq, mem_univ, ite_true]
  -- pairs `(v, v')` with `v` a core vertex and `v'` a marker: Lemma 23
  have h1 : ∀ c d, ∑ r : Fin N,
      |adj (Gp N) (.inl c) (.inr r) - adj (Hp N) (.inl d) (.inr r)| * R c d = R c d * ell c d :=
    fun c d => by rw [← sum_mul, sum_marker_inl, mul_comm]
  -- pairs `(v, v')` with `v` a marker: Lemma 23 for `v'` a core vertex, nothing for `v'` a marker
  have h2 : ∑ r : Fin N, ∑ r' : Fin N,
      ((∑ c, ∑ d, (if r = r' then
          |adj (Gp N) (.inr r) (.inl c) - adj (Hp N) (.inr r') (.inl d)| else 0) * R c d) +
        ∑ _s : Fin N, if r = r' then |(0 : ℝ) - 0| else 0) =
      ∑ c, ∑ d, R c d * ell c d := by
    rw [sum_congr rfl fun r _ => Fintype.sum_eq_single r fun r' hr' => by
      simp [Ne.symm hr']]
    simp only [ite_true, sub_self, abs_zero, sum_const_zero, add_zero]
    calc ∑ r : Fin N, ∑ c, ∑ d,
          |adj (Gp N) (.inr r) (.inl c) - adj (Hp N) (.inr r) (.inl d)| * R c d
        = ∑ c, ∑ r : Fin N, ∑ d,
          |adj (Gp N) (.inr r) (.inl c) - adj (Hp N) (.inr r) (.inl d)| * R c d := sum_comm
      _ = ∑ c, ∑ d, ∑ r : Fin N,
          |adj (Gp N) (.inr r) (.inl c) - adj (Hp N) (.inr r) (.inl d)| * R c d :=
          sum_congr rfl fun c _ => sum_comm
      _ = ∑ c, ∑ d, R c d * ell c d :=
          sum_congr rfl fun c _ => sum_congr rfl fun d _ => by
            rw [← sum_mul, sum_marker_inr, mul_comm]
  rw [h2]
  simp only [h1, sum_add_distrib]
  rw [coreCost]
  ring

/-- **Lemma 23.** Let `Q ∈ DS(V, W)` be compliant, i.e. `Q = extendId (extMarkers R)` with
`R ∈ DS(S_G, S_H)`. Then, w.r.t. `(G, H)`, the core-marker pairs contribute exactly
`2 ∑_{v_i ∈ S_G, w_j ∈ S_H} Q(v_i, w_j) ℓ(v_i, w_j)` to `C_ed(Q)`; the core-core pairs contribute
`coreCost N R` and all other pairs nothing. -/
theorem lemma23 {R : Fin N → Fin N → ℝ} (hR : IsDS R) :
    costEdit (GN N) (HN N) (extendId (extMarkers R)) =
      coreCost N R + 2 * ∑ c, ∑ d, R c d * ell c d := by
  have hz : ∀ j, extMarkers R (markerEnum N j) (markerEnum N j) = 1 := fun j => by
    simp [markerEnum]
  unfold GN HN
  rw [lemma22_cost_edit (extMarkers_isDS hR) hz, costEdit_extMarkers]

end GsimOT.Prop5
