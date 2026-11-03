/-
# Lemma 49: `r/√n ≤ d^OT_2(G_r, H_r) ≤ 1`

Paper, App. F.1, Lemma 49 (p. 45, l. 1417) and its proof (pp. 45–46, l. 1418–1446).

* Upper bound (l. 1418–1436): `Q = (1/2r) ∑_i P_{σ_i}`, where `σ_i` shifts the core vertices of
  branch `i` one step along the cycle `u → v_{i,0} → ⋯ → v_{i,r} → u` and fixes everything else.
  The matrix `B = B_{2→2}(G_r, H_r, Q)` has the block form `[[0, K], [Kᵀ, 0]]` (rows of `K`
  indexed by core pairs `(x, y)`, columns by diagonal marker pairs `(z, z)`, entries
  `√Q(x,y) d_{xy}(z)`).
  Instead of computing `‖KᵀK‖`, we show `‖K ζ‖² = ∑_{x,y} Q(x,y) (d_{xy} ⬝ ζ)² ≤ ‖ζ‖²`
  (Cauchy–Schwarz on every tag block, orthogonality of the clocks; this is the quadratic form of
  `KᵀK = (1/r) ∑_i 1_{T_i} 1_{T_i}ᵀ + ∑_j 1_{c_j} 1_{c_j}ᵀ` from the paper) and conclude
  `|yᵀ B x| ≤ ‖y_X‖ ‖x_M‖ + ‖x_X‖ ‖y_M‖ ≤ 1` for unit vectors `x, y` (Lemma 19).
* Lower bound (l. 1437–1446): for every `R ∈ DS`, the unit vector `1_R(x, y) = √(R(x,y)/n)`
  satisfies `(B 1_R)(x, y) = 1_R(x, y) (deg_G x - deg_H y)`, and the rows of `u` give
  `‖B 1_R‖ ≥ r/√n`. This part is proved for arbitrary graphs (`le_dOT_of_deg`).
-/
import GsimOT.Proposition14_SpectralLowerBound.SpectralDistance

open Finset Matrix

namespace GsimOT.Prop14

/-! ## `B_{2→2}` for `p = q = 2` -/

lemma powZ_half (x : ℝ) : powZ x (2⁻¹ : ENNReal).toReal = Real.sqrt x := by
  have h2 : (2⁻¹ : ENNReal).toReal = 1 / 2 := by simp
  rw [h2, powZ]
  split_ifs with h
  · simp [h]
  · rw [Real.sqrt_eq_rpow]

section General

variable {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel H.Adj]

omit [Fintype V] [DecidableEq V] in
/-- For `p = q = 2` the entries of `B_{2→2}(G, H, Q)` are `√Q(a) D(a, b) √Q(b)`. -/
lemma Bmat_two_apply (Q : V → V → ℝ) (a b : V × V) :
    Bmat 2 2 G H Q a b =
      Real.sqrt (Q a.1 a.2) * disc G H a.1 a.2 b.1 b.2 * Real.sqrt (Q b.1 b.2) := by
  have h : (1 - (2⁻¹ : ENNReal).toReal) = (2⁻¹ : ENNReal).toReal := by simp; norm_num
  simp only [Bmat]
  rw [h, powZ_half, powZ_half]

/-- **Lower bound of Lemma 49, general form** (p. 46, l. 1437–1446). If some vertex `u` satisfies
`|deg_G u - deg_H y| ≥ c` for all `y`, then `‖B_{2→2}(G, H, R)‖_2 ≥ c/√n` for all `R ∈ DS`. -/
lemma le_opNorm_Bmat {R : V → V → ℝ} (hR : IsDS R) (u : V) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y, c ≤ |(deg G u : ℝ) - deg H y|) :
    c / Real.sqrt (Fintype.card V) ≤ opNorm 2 2 (Bmat 2 2 G H R) := by
  have : Nonempty V := ⟨u⟩
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hsn : 0 < Real.sqrt (Fintype.card V) := Real.sqrt_pos.2 hn
  set e : V × V → ℝ := fun a => Real.sqrt (R a.1 a.2) / Real.sqrt (Fintype.card V) with he_def
  have hsq : ∀ v w, Real.sqrt (R v w) ^ 2 = R v w := fun v w => Real.sq_sqrt (hR.nonneg v w)
  have he : lpNorm 2 e = 1 := by
    rw [lpNorm_two, Fintype.sum_prod_type]
    simp only [he_def, div_pow, hsq, Real.sq_sqrt hn.le]
    simp_rw [← Finset.sum_div]
    rw [hR.sum_sum, div_self hn.ne', Real.sqrt_one]
  have hdeg : ∀ x y, ∑ b : V × V, disc G H x y b.1 b.2 * R b.1 b.2 =
      (deg G x : ℝ) - deg H y := by
    intro x y
    rw [Fintype.sum_prod_type]
    simp only [disc, sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun b₁ b₂ => adj H y b₂ * R b₁ b₂)]
    simp only [← Finset.mul_sum, hR.row_sum, hR.col_sum, mul_one, sum_adj_eq_deg]
  have hBe : ∀ x y, (Bmat 2 2 G H R *ᵥ e) (x, y) =
      Real.sqrt (R x y) / Real.sqrt (Fintype.card V) * ((deg G x : ℝ) - deg H y) := by
    intro x y
    rw [← hdeg, Finset.mul_sum]
    simp only [mulVec, dotProduct, Bmat_two_apply G H R, he_def]
    refine Finset.sum_congr rfl fun b _ => ?_
    have := Real.mul_self_sqrt (hR.nonneg b.1 b.2)
    generalize Real.sqrt (R b.1 b.2) = s at this ⊢
    rw [← this]; ring
  -- `‖B e‖² ≥ c²/n`
  have hlow : c ^ 2 / Fintype.card V ≤ ∑ a, (Bmat 2 2 G H R *ᵥ e) a ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine le_trans ?_ (Finset.single_le_sum (f := fun x => ∑ y, (Bmat 2 2 G H R *ᵥ e) (x, y) ^ 2)
      (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (mem_univ u))
    simp only [hBe, mul_pow, div_pow, hsq, Real.sq_sqrt hn.le]
    calc c ^ 2 / Fintype.card V = ∑ y, R u y / Fintype.card V * c ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.sum_div, hR.row_sum]; ring
      _ ≤ _ := Finset.sum_le_sum fun y _ => by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (hR.nonneg _ _) hn.le)
          calc c ^ 2 ≤ |(deg G u : ℝ) - deg H y| ^ 2 := pow_le_pow_left₀ hc (h y) 2
            _ = _ := sq_abs _
  have hop : lpNorm 2 (Bmat 2 2 G H R *ᵥ e) ≤ opNorm 2 2 (Bmat 2 2 G H R) := by
    have := lpNorm_mulVec_le (p := 2) (q := 2) (by norm_num) (by norm_num) (Bmat 2 2 G H R) e
    rwa [he, mul_one] at this
  rw [lpNorm_two] at hop
  refine le_trans ?_ hop
  rw [show c / Real.sqrt (Fintype.card V) = Real.sqrt (c ^ 2 / Fintype.card V) by
    rw [Real.sqrt_div' _ hn.le, Real.sqrt_sq hc]]
  exact Real.sqrt_le_sqrt hlow

/-- **Lower bound of Lemma 49, general form**: `d^OT_2(G, H) ≥ c/√n`. -/
lemma le_dOT_of_deg (u : V) {c : ℝ} (hc : 0 ≤ c) (h : ∀ y, c ≤ |(deg G u : ℝ) - deg H y|) :
    c / Real.sqrt (Fintype.card V) ≤ dOT 2 2 G H := by
  have : Nonempty {Q : V → V → ℝ // IsDS Q} :=
    ⟨⟨permMat (Equiv.refl V), permMat_isDS _⟩⟩
  exact le_ciInf fun R => le_opNorm_Bmat G H R.2 u hc h

end General

/-! ## The fractional alignment `Q = (1/2r) ∑_i P_{σ_i}` -/

/-- The shift `σ_i` restricted to the core: `u ↦ v_{i,0}`, `v_{i,k} ↦ v_{i,k+1}` (`k < r`),
`v_{i,r} ↦ u`, and all other core vertices are fixed. -/
def shift (r : ℕ) (i : Fin (2 * r)) : Core r → Core r
  | none => some (i, 0)
  | some (j, k) =>
      if j = i then (if h : k.val < r then some (i, ⟨k.val + 1, by omega⟩) else none)
      else some (j, k)

lemma shift_injective (r : ℕ) (i : Fin (2 * r)) : Function.Injective (shift r i) := by
  intro a b h
  rcases a with _ | ⟨j, k⟩ <;> rcases b with _ | ⟨j', k'⟩ <;> simp only [shift] at h
  · rfl
  all_goals
    split_ifs at h <;>
    simp only [Option.some.injEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero, reduceCtorEq,
      and_false] at * <;> omega

/-- `σ_i` on the core, as a permutation. -/
noncomputable def tau (r : ℕ) (i : Fin (2 * r)) : Core r ≃ Core r :=
  Equiv.ofBijective (shift r i) (shift_injective r i).bijective_of_finite

/-- `Q` on the core: `(1/2r) ∑_i P_{σ_i}`. -/
noncomputable def qc (r : ℕ) (x y : Core r) : ℝ :=
  (2 * r : ℝ)⁻¹ * ∑ i, permMat (tau r i) x y

/-- `Q = (1/2r) ∑_i P_{σ_i}`; it fixes all markers. -/
noncomputable def Qs (r : ℕ) : Vtx r → Vtx r → ℝ
  | .inl x, .inl y => qc r x y
  | .inr m, .inr m' => if m = m' then 1 else 0
  | _, _ => 0

lemma qc_nonneg (r : ℕ) (x y : Core r) : 0 ≤ qc r x y :=
  mul_nonneg (by positivity) (sum_nonneg fun i _ => (permMat_isDS _).nonneg _ _)

lemma Qs_nonneg (r : ℕ) (a b : Vtx r) : 0 ≤ Qs r a b := by
  rcases a with x | m <;> rcases b with y | m' <;> simp only [Qs]
  · exact qc_nonneg r x y
  · exact le_rfl
  · exact le_rfl
  · split_ifs <;> norm_num

lemma qc_row (r : ℕ) (hr : 1 ≤ r) (x : Core r) : ∑ y, qc r x y = 1 := by
  have : (2 * r : ℝ) ≠ 0 := by positivity
  simp only [qc, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [(permMat_isDS _).row_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  push_cast
  field_simp

lemma qc_col (r : ℕ) (hr : 1 ≤ r) (y : Core r) : ∑ x, qc r x y = 1 := by
  have : (2 * r : ℝ) ≠ 0 := by positivity
  simp only [qc, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [(permMat_isDS _).col_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  push_cast
  field_simp

lemma Qs_isDS (r : ℕ) (hr : 1 ≤ r) : IsDS (Qs r) where
  nonneg := Qs_nonneg r
  row_sum a := by
    rcases a with x | m
    · simp [Fintype.sum_sum_type, Qs, qc_row r hr]
    · simp [Fintype.sum_sum_type, Qs]
  col_sum b := by
    rcases b with y | m
    · simp [Fintype.sum_sum_type, Qs, qc_col r hr]
    · simp [Fintype.sum_sum_type, Qs]

/-! ## The bound `∑_{x,y} Q(x,y) (d_{xy} ⬝ ζ)² ≤ ‖ζ‖²` (i.e. `‖K‖ ≤ 1`) -/

/-- `d_{xy}(z) = 1_{N_G(x)}(z) - 1_{N_H(y)}(z)` for core vertices `x, y` and a marker `z`. -/
def dv (r : ℕ) (x y : Core r) (m : Marker r) : ℝ := cmR r false x m - cmR r true y m

/-- `d_{xy} ⬝ ζ`. -/
def dvDot (r : ℕ) (ζ : Marker r → ℝ) (x y : Core r) : ℝ := ∑ m, dv r x y m * ζ m

/-- The sum of `ζ` over the tags of branch `i`. -/
def tagSum (r : ℕ) (ζ : Marker r → ℝ) (i : Fin (2 * r)) : ℝ := ∑ t, ζ (.inr (i, t))

lemma dvDot_u (r : ℕ) (ζ : Marker r → ℝ) (i : Fin (2 * r)) :
    dvDot r ζ none (some (i, 0)) = -tagSum r ζ i := by
  simp [dvDot, dv, tagSum, Fintype.sum_sum_type, Fintype.sum_prod_type, ite_mul]

lemma dvDot_same (r : ℕ) (ζ : Marker r → ℝ) (v : Fin (2 * r) × Fin (r + 1)) :
    dvDot r ζ (some v) (some v) = 0 := by
  simp [dvDot, dv, cmR_some_eq]

lemma dvDot_step (r : ℕ) (ζ : Marker r → ℝ) (i : Fin (2 * r)) (k : Fin r) :
    dvDot r ζ (some (i, k.castSucc)) (some (i, ⟨k.val + 1, by omega⟩)) = -ζ (.inl k) := by
  have hj : ∀ j : Fin r, ((if j.val < k.val then (1 : ℝ) else 0) -
      if j.val < k.val + 1 then 1 else 0) * ζ (.inl j) = if k = j then -ζ (.inl j) else 0 := by
    intro j
    by_cases h : k = j
    · subst h; simp
    · have : j.val ≠ k.val := fun h' => h (Fin.ext h'.symm)
      rw [ite_eq_right_iff.2 (fun h' => absurd h' h)]
      split_ifs <;> first | (exfalso; omega) | ring
  simp only [dvDot, dv, Fintype.sum_sum_type, Fintype.sum_prod_type, cmR_some_inl,
    Fin.val_castSucc, hj, Finset.sum_ite_eq, mem_univ, ite_true, cmR_some_inr, sub_self, zero_mul,
    sum_const_zero, add_zero]

lemma dvDot_last (r : ℕ) (ζ : Marker r → ℝ) (i : Fin (2 * r)) :
    dvDot r ζ (some (i, Fin.last r)) none = tagSum r ζ i := by
  simp [dvDot, dv, tagSum, Fintype.sum_sum_type, Fintype.sum_prod_type, ite_mul]

/-- One branch: `∑_x (d_{x σ_i(x)} ⬝ ζ)² = 2 (∑_{t ∈ T_i} ζ_t)² + ∑_j ζ_{c_j}²`, which is at most
`2r ∑_{t ∈ T_i} ζ_t² + ∑_j ζ_{c_j}²` by Cauchy–Schwarz. -/
lemma sum_branch_le (r : ℕ) (ζ : Marker r → ℝ) (i : Fin (2 * r)) :
    ∑ x, dvDot r ζ x (shift r i x) ^ 2 ≤
      2 * r * ∑ t, ζ (.inr (i, t)) ^ 2 + ∑ j, ζ (.inl j) ^ 2 := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i (fun j _ hj => by
    refine Finset.sum_eq_zero fun k _ => ?_
    simp [shift, hj, dvDot_same]) (by simp)]
  rw [Fin.sum_univ_castSucc]
  have h1 : shift r i none = some (i, 0) := rfl
  have h2 : ∀ k : Fin r, shift r i (some (i, k.castSucc)) = some (i, ⟨k.val + 1, by omega⟩) := by
    intro k; simp [shift]
  have h3 : shift r i (some (i, Fin.last r)) = none := by simp [shift]
  simp only [h1, h2, h3, dvDot_u, dvDot_step, dvDot_last, neg_sq]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin r)))
    (f := fun t => ζ (.inr (i, t)))
  simp only [card_univ, Fintype.card_fin] at hcs
  unfold tagSum
  linarith

lemma sum_qc_dvDot_le (r : ℕ) (hr : 1 ≤ r) (ζ : Marker r → ℝ) :
    ∑ x, ∑ y, qc r x y * dvDot r ζ x y ^ 2 ≤ ∑ m, ζ m ^ 2 := by
  have hr0 : (0 : ℝ) < 2 * r := by positivity
  have hrow : ∀ x, ∑ y, qc r x y * dvDot r ζ x y ^ 2 =
      (2 * r : ℝ)⁻¹ * ∑ i, dvDot r ζ x (shift r i x) ^ 2 := by
    intro x
    have hP : ∀ i, ∑ y, permMat (tau r i) x y * dvDot r ζ x y ^ 2 =
        dvDot r ζ x (shift r i x) ^ 2 := by
      intro i
      rw [Finset.sum_eq_single (shift r i x)]
      · simp [permMat, tau]
      · intro y _ hy
        simp [permMat, tau, Ne.symm hy]
      · simp
    simp only [qc, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun y i => permMat (tau r i) x y * dvDot r ζ x y ^ 2)]
    simp only [hP]
  have hsum : ∑ x, ∑ y, qc r x y * dvDot r ζ x y ^ 2 =
      (2 * r : ℝ)⁻¹ * ∑ i, ∑ x, dvDot r ζ x (shift r i x) ^ 2 := by
    simp only [hrow, ← Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsum]
  have hb : ∑ i, ∑ x, dvDot r ζ x (shift r i x) ^ 2 ≤ 2 * r * ∑ m, ζ m ^ 2 := by
    refine (Finset.sum_le_sum fun i _ => sum_branch_le r ζ i).trans_eq ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  calc (2 * r : ℝ)⁻¹ * ∑ i, ∑ x, dvDot r ζ x (shift r i x) ^ 2
      ≤ (2 * r : ℝ)⁻¹ * (2 * r * ∑ m, ζ m ^ 2) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ∑ m, ζ m ^ 2 := by field_simp

/-- Cauchy–Schwarz: `(∑_{x,y} Z(x,y) √Q(x,y) (d_{xy} ⬝ ζ))² ≤ ‖Z‖² ‖ζ‖²`. -/
lemma sq_T_le (r : ℕ) (hr : 1 ≤ r) (Z : Core r → Core r → ℝ) (ζ : Marker r → ℝ) :
    (∑ x, ∑ y, Z x y * (Real.sqrt (qc r x y) * dvDot r ζ x y)) ^ 2 ≤
      (∑ x, ∑ y, Z x y ^ 2) * ∑ m, ζ m ^ 2 := by
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset (Core r × Core r))
    (fun p => Z p.1 p.2) (fun p => Real.sqrt (qc r p.1 p.2) * dvDot r ζ p.1 p.2)
  simp only [Fintype.sum_prod_type, mul_pow, Real.sq_sqrt (qc_nonneg _ _ _)] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_left (sum_qc_dvDot_le r hr ζ)
    (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _))

/-! ## The bilinear form of `B_{2→2}(G_r, H_r, Q)` -/

/-- Splitting a sum over pairs of vertices into the four blocks core/marker × core/marker. -/
lemma sum_pair {α β : Type*} [Fintype α] [Fintype β] (f : (α ⊕ β) × (α ⊕ β) → ℝ) :
    ∑ a, f a = ∑ c, ∑ c', f (.inl c, .inl c') + ∑ c, ∑ m, f (.inl c, .inr m) +
      ∑ m, ∑ c, f (.inr m, .inl c) + ∑ m, ∑ m', f (.inr m, .inr m') := by
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, Finset.sum_add_distrib]
  ring

/-- `‖y‖² ≥ ‖y_X‖² + ‖y_M‖²` (core pairs and diagonal marker pairs). -/
lemma sum_sq_split {α β : Type*} [Fintype α] [Fintype β] (y : (α ⊕ β) × (α ⊕ β) → ℝ) :
    (∑ c, ∑ c', y (.inl c, .inl c') ^ 2) + ∑ m, y (.inr m, .inr m) ^ 2 ≤ ∑ a, y a ^ 2 := by
  rw [sum_pair (fun a => y a ^ 2)]
  have h1 : ∑ m, y (.inr m, .inr m) ^ 2 ≤ ∑ m, ∑ m', y (.inr m, .inr m') ^ 2 :=
    Finset.sum_le_sum fun m _ => Finset.single_le_sum (f := fun m' => y (.inr m, .inr m') ^ 2)
      (fun _ _ => sq_nonneg _) (mem_univ m)
  have h2 : 0 ≤ ∑ c : α, ∑ m : β, y (.inl c, .inr m) ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have h3 : 0 ≤ ∑ m : β, ∑ c : α, y (.inr m, .inl c) ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- `B_{2→2}(G_r, H_r, Q)`. -/
noncomputable abbrev Bq (r : ℕ) : Matrix (Vtx r × Vtx r) (Vtx r × Vtx r) ℝ :=
  Bmat 2 2 (Gr r) (Hr r) (Qs r)

section Entries

variable (r : ℕ) (x : Vtx r × Vtx r → ℝ)

lemma Bq_apply (a b : Vtx r × Vtx r) :
    Bq r a b = Real.sqrt (Qs r a.1 a.2) * disc (Gr r) (Hr r) a.1 a.2 b.1 b.2 *
      Real.sqrt (Qs r b.1 b.2) :=
  Bmat_two_apply _ _ (Qs r) a b

lemma Bq_mulVec_cc (c c' : Core r) :
    (Bq r *ᵥ x) (.inl c, .inl c') =
      Real.sqrt (qc r c c') * dvDot r (fun m => x (.inr m, .inr m)) c c' := by
  simp only [mulVec, dotProduct]
  rw [sum_pair]
  simp only [Bq_apply, Qs, disc, adj_Gr_inl_inl, adj_Hr_inl_inl, adj_Gr_inl_inr, adj_Hr_inl_inr,
    sub_self, mul_zero, zero_mul, Real.sqrt_zero, sum_const_zero, zero_add, apply_ite Real.sqrt,
    Real.sqrt_one, mul_ite, mul_one, ite_mul, Finset.sum_ite_eq, mem_univ, ite_true]
  simp only [dvDot, dv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma Bq_mulVec_cm (c : Core r) (m : Marker r) : (Bq r *ᵥ x) (.inl c, .inr m) = 0 := by
  simp only [mulVec, dotProduct, Bq_apply, Qs, Real.sqrt_zero, zero_mul, sum_const_zero]

lemma Bq_mulVec_mc (c : Core r) (m : Marker r) : (Bq r *ᵥ x) (.inr m, .inl c) = 0 := by
  simp only [mulVec, dotProduct, Bq_apply, Qs, Real.sqrt_zero, zero_mul, sum_const_zero]

lemma Bq_mulVec_mm (m m' : Marker r) :
    (Bq r *ᵥ x) (.inr m, .inr m') = if m = m' then
      ∑ c, ∑ c', dv r c c' m * Real.sqrt (qc r c c') * x (.inl c, .inl c') else 0 := by
  simp only [mulVec, dotProduct]
  rw [sum_pair]
  split_ifs with h
  · subst h
    simp only [Bq_apply, Qs, disc, adj_Gr_inr_inl, adj_Hr_inr_inl, adj_Gr_inr_inr,
      adj_Hr_inr_inr, sub_self, mul_zero, zero_mul, Real.sqrt_zero, sum_const_zero, add_zero,
      ite_true, Real.sqrt_one, one_mul, dv]
  · simp only [Bq_apply, Qs, h, ite_false, Real.sqrt_zero, zero_mul, sum_const_zero, add_zero]

end Entries

/-- `yᵀ B x = T(y_X, x_M) + T(x_X, y_M)` (block form `[[0, K], [Kᵀ, 0]]`). -/
lemma dotProduct_Bq (r : ℕ) (x y : Vtx r × Vtx r → ℝ) :
    y ⬝ᵥ (Bq r *ᵥ x) =
      ∑ c, ∑ c', y (.inl c, .inl c') *
          (Real.sqrt (qc r c c') * dvDot r (fun m => x (.inr m, .inr m)) c c') +
        ∑ c, ∑ c', x (.inl c, .inl c') *
          (Real.sqrt (qc r c c') * dvDot r (fun m => y (.inr m, .inr m)) c c') := by
  simp only [dotProduct]
  rw [sum_pair (fun a => y a * (Bq r *ᵥ x) a)]
  simp only [Bq_mulVec_cc, Bq_mulVec_cm, Bq_mulVec_mc, Bq_mulVec_mm, mul_zero, sum_const_zero,
    add_zero, mul_ite, Finset.sum_ite_eq, mem_univ, ite_true]
  congr 1
  simp only [dvDot, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma sum_sq_le_one_of_lpNorm {ι : Type*} [Fintype ι] {x : ι → ℝ} (hx : lpNorm 2 x ≤ 1) :
    ∑ i, x i ^ 2 ≤ 1 := by
  rw [lpNorm_two] at hx
  have h := Real.sq_sqrt (sum_nonneg fun i (_ : i ∈ univ) => sq_nonneg (x i))
  nlinarith [Real.sqrt_nonneg (∑ i, x i ^ 2)]

lemma abs_add_le_one {T₁ T₂ a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h₁ : T₁ ^ 2 ≤ a * b) (h₂ : T₂ ^ 2 ≤ c * d) (hy : a + d ≤ 1) (hx : c + b ≤ 1) :
    |T₁ + T₂| ≤ 1 := by
  have e1 : |T₁| ≤ (a + b) / 2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).1
    (by rw [sq_abs]; nlinarith [sq_nonneg (a - b)])
  have e2 : |T₂| ≤ (c + d) / 2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).1
    (by rw [sq_abs]; nlinarith [sq_nonneg (c - d)])
  calc |T₁ + T₂| ≤ |T₁| + |T₂| := abs_add_le _ _
    _ ≤ 1 := by linarith

/-- `C_2(Q) = ‖B_{2→2}(G_r, H_r, Q)‖_2 ≤ 1`. -/
lemma opNorm_Bq_le (r : ℕ) (hr : 1 ≤ r) : opNorm 2 2 (Bq r) ≤ 1 := by
  obtain ⟨x, y, hx, hy, heq⟩ :=
    exists_abs_dotProduct_mulVec_eq_opNorm (p := 2) (q := 2) (by norm_num) (by norm_num) (Bq r)
  rw [conjExponent_two] at hy
  rw [← heq, dotProduct_Bq]
  have hx1 := (sum_sq_split x).trans (sum_sq_le_one_of_lpNorm hx)
  have hy1 := (sum_sq_split y).trans (sum_sq_le_one_of_lpNorm hy)
  exact abs_add_le_one (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
    (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
    (sum_nonneg fun _ _ => sq_nonneg _)
    (sq_T_le r hr (fun c c' => y (.inl c, .inl c')) (fun m => x (.inr m, .inr m)))
    (sq_T_le r hr (fun c c' => x (.inl c, .inl c')) (fun m => y (.inr m, .inr m))) hy1 hx1

/-- `d^OT_2(G_r, H_r) ≤ 1`. -/
lemma dOT_le_one (r : ℕ) (hr : 1 ≤ r) : dOT 2 2 (Gr r) (Hr r) ≤ 1 := by
  have h := ciInf_le (f := fun Q : {Q : Vtx r → Vtx r → ℝ // IsDS Q} =>
      opNorm 2 2 (Bmat 2 2 (Gr r) (Hr r) Q.1))
    ⟨0, by rintro _ ⟨Q, rfl⟩; exact opNorm_nonneg _ _ _⟩ ⟨Qs r, Qs_isDS r hr⟩
  exact h.trans (opNorm_Bq_le r hr)

/-- `d^OT_2(G_r, H_r) ≥ r/√n`. -/
lemma le_dOT (r : ℕ) : r / Real.sqrt (4 * r ^ 2 + 3 * r + 1) ≤ dOT 2 2 (Gr r) (Hr r) := by
  have h := le_dOT_of_deg (Gr r) (Hr r) (.inl none) (c := r) (Nat.cast_nonneg r) fun y => by
    have h0 : deg (Gr r) (.inl none) = 0 := by
      have := sum_adj_eq_deg (Gr r) (.inl none)
      simp only [adj_Gr_u, sum_const_zero] at this
      exact_mod_cast this.symm
    rw [h0, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast le_deg_Hr r y
  rw [card_Vtx] at h
  push_cast at h
  exact h

/-- **Lemma 49** (p. 45, l. 1417). `r/√n ≤ d^OT_2(G_r, H_r) ≤ 1` with `n = 4r² + 3r + 1`. -/
theorem lemma53 (r : ℕ) (hr : 1 ≤ r) :
    r / Real.sqrt (4 * r ^ 2 + 3 * r + 1) ≤ dOT 2 2 (Gr r) (Hr r) ∧
      dOT 2 2 (Gr r) (Hr r) ≤ 1 :=
  ⟨le_dOT r, dOT_le_one r hr⟩

end GsimOT.Prop14
