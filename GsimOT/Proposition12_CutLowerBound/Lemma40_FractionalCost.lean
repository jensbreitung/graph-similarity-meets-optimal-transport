/-
# Lemma 34: `d_□^OT(G, H) ≤ 4`

Paper, App. E.1, Lemma 34 (p. 31, l. 989; proof pp. 31–32, l. 990–1000).

The coupling `Q` maps each marker set `L_i` identically onto `L'_i` and each pair
`{v_i^+, v_i^-}` uniformly onto `{w_i^+, w_i^-}` (`Q(v_i^σ, w_i^τ) = ½`).  Discrepancies involving a
marker atom vanish, and on the 20 core atoms `(v_i^σ, w_i^τ)`
`D(v_i^σ, w_i^τ, v_j^{σ'}, w_j^{τ'}) = ½ Z_ij (σσ' + ττ')`.
Splitting the atoms into *straight* (`σ = τ`) and *crossed* (`σ = -τ`) ones, every cut value is
`¼ (uᵀ Z v + cᵀ Z d)` with `u, v, c, d ∈ {-1, 0, 1}^5`, hence at most `¼ · 8 + ¼ · 8 = 4`.
-/
import GsimOT.Proposition12_CutLowerBound.Construction

open Finset

namespace GsimOT.Prop12

/-! ## The coupling `Q` -/

/-- The doubly stochastic matrix `Q` of Lemma 34. -/
noncomputable def Q40 : Vtx → Vtx → ℝ
  | .inl p, .inl q => if p.1 = q.1 then 1 / 2 else 0
  | .inr m, .inr m' => if m = m' then 1 else 0
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0

lemma Q40_symm (v w : Vtx) : Q40 v w = Q40 w v := by
  rcases v with p | m <;> rcases w with q | m' <;> simp only [Q40, eq_comm]

lemma Q40_row_sum (v : Vtx) : ∑ w, Q40 v w = 1 := by
  rw [Fintype.sum_sum_type]
  rcases v with ⟨i, s⟩ | m
  · simp only [Q40, Finset.sum_const_zero, add_zero]
    rw [Fintype.sum_prod_type]
    simp
  · simp [Q40]

lemma Q40_isDS : IsDS Q40 where
  nonneg v w := by
    rcases v with p | m <;> rcases w with q | m' <;> simp only [Q40] <;> (try split_ifs) <;> norm_num
  row_sum := Q40_row_sum
  col_sum w := by simp_rw [Q40_symm _ w]; exact Q40_row_sum w

/-- The support of `Q`: core atoms `(v_i^σ, w_i^τ)` and marker atoms `(z, z)`. -/
lemma Q40_ne_zero {v w : Vtx} (h : Q40 v w ≠ 0) :
    (∃ i s s', v = .inl (i, s) ∧ w = .inl (i, s')) ∨ (∃ m, v = .inr m ∧ w = .inr m) := by
  rcases v with ⟨i, s⟩ | m <;> rcases w with ⟨j, s'⟩ | m' <;> simp only [Q40] at h
  · split_ifs at h with hij
    · obtain rfl : i = j := hij
      exact Or.inl ⟨i, s, s', rfl, rfl⟩
    · exact absurd rfl h
  · exact absurd rfl h
  · exact absurd rfl h
  · split_ifs at h with hm
    · exact Or.inr ⟨m, rfl, by rw [hm]⟩
    · exact absurd rfl h

/-- Every discrepancy between a marker atom and an atom of `supp Q` vanishes. -/
lemma adj_marker_eq {m : Marker} {v w : Vtx} (h : Q40 v w ≠ 0) :
    adj G12 (.inr m) v = adj H12 (.inr m) w := by
  rcases Q40_ne_zero h with ⟨i, s, s', rfl, rfl⟩ | ⟨m', rfl, rfl⟩
  · rw [adj_G12_inr_inl, adj_H12_inr_inl]
  · rw [adj_G12_inr_inr, adj_H12_inr_inr]

/-! ## Core atoms -/

/-- The entries `Q(v,w) D(v,w,v',w') Q(v',w')` of `B(G, H, Q)` for the coupling `Q` of Lemma 34. -/
noncomputable def B40 (a b : Vtx × Vtx) : ℝ :=
  Q40 a.1 a.2 * disc G12 H12 a.1 a.2 b.1 b.2 * Q40 b.1 b.2

/-- The core atom `(v_i^σ, w_i^τ)` encoded by `(i, σ, τ)`. -/
def atom (x : Fin 5 × Bool × Bool) : Vtx × Vtx := (.inl (x.1, x.2.1), .inl (x.1, x.2.2))

lemma atom_injective : Function.Injective atom := by
  rintro ⟨i, s, s'⟩ ⟨j, t, t'⟩ h
  simp only [atom, Prod.mk.injEq, Sum.inl.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := h
  rfl

lemma B40_eq_zero_left {a : Vtx × Vtx} (ha : a ∉ Set.range atom) (b : Vtx × Vtx) :
    B40 a b = 0 := by
  unfold B40
  by_cases hQa : Q40 a.1 a.2 = 0
  · rw [hQa]; ring
  by_cases hQb : Q40 b.1 b.2 = 0
  · rw [hQb]; ring
  rcases Q40_ne_zero hQa with ⟨i, s, s', h1, h2⟩ | ⟨m, h1, h2⟩
  · exact absurd ⟨(i, s, s'), by rw [atom, ← h1, ← h2]⟩ ha
  · rw [disc, h1, h2, adj_marker_eq hQb]; ring

lemma B40_eq_zero_right (a : Vtx × Vtx) {b : Vtx × Vtx} (hb : b ∉ Set.range atom) :
    B40 a b = 0 := by
  unfold B40
  by_cases hQa : Q40 a.1 a.2 = 0
  · rw [hQa]; ring
  by_cases hQb : Q40 b.1 b.2 = 0
  · rw [hQb]; ring
  rcases Q40_ne_zero hQb with ⟨i, s, s', h1, h2⟩ | ⟨m, h1, h2⟩
  · exact absurd ⟨(i, s, s'), by rw [atom, ← h1, ← h2]⟩ hb
  · rw [disc, h1, h2, adj_symm G12, adj_symm H12, adj_marker_eq hQa]; ring

/-- On core atoms `(v_i^σ, w_i^τ)`, `(v_j^{σ'}, w_j^{τ'})`, `Q D Q = ½ · ½ Z_ij (σσ' + ττ') · ½`. -/
lemma B40_atom (x y : Fin 5 × Bool × Bool) :
    B40 (atom x) (atom y) =
      (Z x.1 y.1 : ℝ) * (sg x.2.1 * sg y.2.1 + sg x.2.2 * sg y.2.2) / 8 := by
  obtain ⟨i, s, s'⟩ := x
  obtain ⟨j, t, t'⟩ := y
  have h := two_mul_gCore_sub_hCore i j s s' t t'
  have h' : ((gCore (i, s) (j, t) : ℝ) - hCore (i, s') (j, t')) =
      (Z i j : ℝ) * (sg s * sg t + sg s' * sg t') / 2 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this
    linarith
  simp only [B40, atom, Q40, disc, adj_G12_inl_inl, adj_H12_inl_inl, ite_true, h']
  ring

/-! ## Straight and crossed atoms -/

/-- The cut value over core atoms splits into a straight and a crossed copy of the pentagon
pattern: `∑ 1_S 1_T Q D Q = ¼ ∑_{ij} Z_ij (u_i v_j + c_i d_j)`. -/
lemma atom_sum_eq (a b : Fin 5 × Bool × Bool → ℝ) :
    ∑ x : Fin 5 × Bool × Bool, a x * ∑ y : Fin 5 × Bool × Bool, b y *
        ((Z x.1 y.1 : ℝ) * (sg x.2.1 * sg y.2.1 + sg x.2.2 * sg y.2.2) / 8) =
      ∑ i, ∑ j, ((Z i j : ℝ) * (a (i, true, true) - a (i, false, false)) *
          (b (j, true, true) - b (j, false, false)) / 4 +
        (Z i j : ℝ) * (a (i, true, false) - a (i, false, true)) *
          (b (j, true, false) - b (j, false, true)) / 4) := by
  simp_rw [Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp_rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sg]
  push_cast
  ring

/-- `C_□(Q) ≤ 4` (proof of Lemma 34). -/
lemma costCut_Q40_le : costCut G12 H12 Q40 ≤ 4 := by
  refine cutNorm_le _ fun S T => ?_
  change |∑ a ∈ S, ∑ b ∈ T, B40 a b| ≤ 4
  rw [sum_mem_eq_sum_ite]
  simp_rw [sum_mem_eq_sum_ite T]
  have hin : ∀ a, ∑ b, (if b ∈ T then (1 : ℝ) else 0) * B40 a b =
      ∑ y, (if atom y ∈ T then (1 : ℝ) else 0) * B40 a (atom y) := fun a =>
    (Fintype.sum_of_injective atom atom_injective
      (fun y => (if atom y ∈ T then (1 : ℝ) else 0) * B40 a (atom y))
      (fun b => (if b ∈ T then (1 : ℝ) else 0) * B40 a b)
      (fun b hb => by rw [B40_eq_zero_right a hb]; ring) (fun _ => rfl)).symm
  simp_rw [hin]
  rw [← Fintype.sum_of_injective atom atom_injective
      (fun x => (if atom x ∈ S then (1 : ℝ) else 0) *
        ∑ y, (if atom y ∈ T then (1 : ℝ) else 0) * B40 (atom x) (atom y))
      (fun a => (if a ∈ S then (1 : ℝ) else 0) *
        ∑ y, (if atom y ∈ T then (1 : ℝ) else 0) * B40 a (atom y))
      (fun a ha => by simp only [B40_eq_zero_left ha]; simp) (fun _ => rfl)]
  simp_rw [B40_atom]
  rw [atom_sum_eq (fun x => if atom x ∈ S then 1 else 0) (fun y => if atom y ∈ T then 1 else 0)]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.sum_div]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h1 := abs_bilin_Z_le (fun i => isTri_ite_sub_ite (atom (i, true, true) ∈ S)
    (atom (i, false, false) ∈ S)) (fun j => isTri_ite_sub_ite (atom (j, true, true) ∈ T)
    (atom (j, false, false) ∈ T))
  have h2 := abs_bilin_Z_le (fun i => isTri_ite_sub_ite (atom (i, true, false) ∈ S)
    (atom (i, false, true) ∈ S)) (fun j => isTri_ite_sub_ite (atom (j, true, false) ∈ T)
    (atom (j, false, true) ∈ T))
  linarith

/-- **Lemma 34.** `d_□^OT(G, H) ≤ 4`. -/
theorem lemma40 : dOTCut G12 H12 ≤ 4 :=
  (ciInf_le (f := fun Q : {Q : Vtx → Vtx → ℝ // IsDS Q} => costCut G12 H12 Q.1)
    ⟨0, by rintro _ ⟨Q, rfl⟩; exact cutNorm_nonneg (B G12 H12 Q.1)⟩
    ⟨Q40, Q40_isDS⟩).trans costCut_Q40_le

end GsimOT.Prop12
