/-
# `d_□^OT(G, H) ≥ 4`: the fractional alignment of Lemma 34 is optimal

This file is the Lean certificate that the paper cites in Section 3.3, in the remark after
Proposition 10 (p. 10, l. 330; footnote 2 gives the link to this file): "Note that one of our Lean
certificates verifies that the `d_□^OT`-bound is tight, so `d_□^OT(G, H) = 4`." For the graphs
`G`, `H` of Proposition 10 (Appendix E.1) it proves `C_□(Q) ≥ 4` for every `Q ∈ DS(V, W)`
(`four_le_costCut`), hence `d_□^OT(G, H) ≥ 4` (`four_le_dOTCut`), and with Lemma 34
`d_□^OT(G, H) = 4` (`dOTCut_eq_four`). The paper refers to this file for the proof; the argument
is outlined here.

Fix `Q ∈ DS(V, W)` and write `q_x = Q(v, w)` for an atom `x = (v, w) ∈ Ω = V × W`,
`d(x) = deg_G(v) - deg_H(w)`, `L = ∑_x q_x |d(x)|`, `B(f, g) = ∑_{x,y} f(x) q_x D(x, y) q_y g(y)`
(so `C_□(Q) = max_{S,T} |B(1_S, 1_T)|`) and `T` for the mass of `Q` on the 20 core atoms
`(v_i^σ, w_i^τ)`.
1. Fractional cuts: `|B(f, g)| ≤ C_□(Q)` for `f, g : Ω → [0, 1]`, since a linear form on a box is
   extremal at a vertex (`abs_bilin_le_cutNorm`; compare Eq. (22), p. 32, l. 1007–1009).
2. Degree identities: `∑_y D(x, y) q_y = d(x)` and `∑_x q_x d(x) = 0` (`sum_B_right`,
   `sum_mul_dd`).
3. Combining a core test with the degree discrepancy: if `|s|, |t| ≤ 1` and `s` vanishes where
   `d ≠ 0`, then `L + B(s, t) ≤ 4 C_□(Q)` (`degree_add_bil_le`). With `e = sgn d`, the pairs
   `f_± = (1 + e ± s)/2`, `g_± = (1 ± t)/2` take values in `[0, 1]`, and
   `B(f_+, g_+) + B(f_-, g_-) = (L + B(s, t))/2` by step 2.
4. Mass leaving the pairs: a core vertex sent outside its pair changes the degree by at least `9`,
   so `L ≥ 9 (10 - T)` (`nine_mul_le_L`).
5. The pentagon: for `x ∈ [0, 2]^5`, `max_{a,b ∈ {±1}^5} aᵀ diag(x) Z diag(x) b ≥ 16/5 ∑ x_i - 8`
   (`exists_zForm_ge`). On core atoms `D = ½ Z_ij (σσ' + ττ')`, which vanishes between straight
   atoms `(v_i^σ, w_i^σ)` and crossed atoms `(v_i^σ, w_i^{-σ})`; so test functions `σ a_i` on
   straight and `σ a'_i` on crossed atoms give `B(s, t) = aᵀ CZC b + a'ᵀ HZH b'`, where `c_i`, `h_i`
   are the straight and crossed masses of pair `i` (`bil_testFn`), and `B(s, t) ≥ 16/5 · T - 16`.
Together `4 C_□(Q) ≥ 9 (10 - T) + 16/5 · T - 16 ≥ 16`, since `T ≤ 10`.
-/
import GsimOT.Proposition10_CutLowerBound.Lemma34_FractionalCost

open Finset

namespace GsimOT.Prop10

/-! ## Step 1: fractional cuts -/

section Box

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A linear form on `[0, 1]^ι` is bounded in absolute value by its value on some indicator. -/
lemma exists_abs_sum_mul_le (c f : ι → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    ∃ S : Finset ι, |∑ i, f i * c i| ≤ |∑ i ∈ S, c i| := by
  rcases le_total 0 (∑ i, f i * c i) with h | h
  · refine ⟨univ.filter (fun i => 0 < c i), ?_⟩
    rw [Finset.sum_filter, abs_of_nonneg h]
    refine (Finset.sum_le_sum fun i _ => ?_).trans (le_abs_self _)
    split_ifs with hc
    · exact mul_le_of_le_one_left hc.le (hf i).2
    · exact mul_nonpos_of_nonneg_of_nonpos (hf i).1 (not_lt.mp hc)
  · refine ⟨univ.filter (fun i => c i < 0), ?_⟩
    rw [Finset.sum_filter, abs_of_nonpos h]
    refine (neg_le_neg (Finset.sum_le_sum fun i _ => ?_)).trans (neg_le_abs _)
    split_ifs with hc
    · nlinarith [(hf i).1, (hf i).2]
    · exact mul_nonneg (hf i).1 (not_lt.mp hc)

/-- Step 1: `|∑ f(x) A(x, y) g(y)| ≤ ‖A‖_□` for `f, g : ι → [0, 1]`. -/
lemma abs_bilin_le_cutNorm (A : Matrix ι ι ℝ) (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ 1) :
    |∑ i, ∑ j, f i * A i j * g j| ≤ cutNorm A := by
  have e1 : ∑ i, ∑ j, f i * A i j * g j = ∑ i, f i * ∑ j, A i j * g j := by
    simp_rw [Finset.mul_sum, mul_assoc]
  obtain ⟨S, hS⟩ := exists_abs_sum_mul_le (fun i => ∑ j, A i j * g j) f hf
  have e2 : ∑ i ∈ S, ∑ j, A i j * g j = ∑ j, g j * ∑ i ∈ S, A i j := by
    have h : ∑ i ∈ S, ∑ j, A i j * g j = ∑ j, ∑ i ∈ S, A i j * g j := Finset.sum_comm
    rw [h]; simp_rw [Finset.mul_sum, mul_comm]
  obtain ⟨T, hT⟩ := exists_abs_sum_mul_le (fun j => ∑ i ∈ S, A i j) g hg
  have e3 : ∑ j ∈ T, ∑ i ∈ S, A i j = ∑ i ∈ S, ∑ j ∈ T, A i j := Finset.sum_comm
  rw [e1]
  refine hS.trans ?_
  rw [e2]
  refine hT.trans ?_
  rw [e3]
  exact le_cutNorm A S T

end Box

/-! ## Degree discrepancies -/

section DS

variable {Q : Vtx → Vtx → ℝ} (hQ : IsDS Q)
include hQ

/-- The degree discrepancy `d(x) = deg_G(v) - deg_H(w)` of an atom `x = (v, w)`. -/
def dd (x : Vtx × Vtx) : ℝ := (dg x.1 : ℝ) - dg x.2

/-- Step 2: `∑_y D(x, y) q_y = d(x)`. -/
lemma sum_disc_mul (v w : Vtx) :
    ∑ y : Vtx × Vtx, disc G12 H12 v w y.1 y.2 * Q y.1 y.2 = (dg v : ℝ) - dg w := by
  rw [Fintype.sum_prod_type]
  simp only [disc, sub_mul, Finset.sum_sub_distrib]
  have h1 : ∑ v', ∑ w', adj G12 v v' * Q v' w' = dg v := by
    simp_rw [← Finset.mul_sum, hQ.row_sum, mul_one, sum_adj_G12]
  have h2 : ∑ v', ∑ w', adj H12 w w' * Q v' w' = dg w := by
    have h : ∑ v', ∑ w', adj H12 w w' * Q v' w' = ∑ w', ∑ v', adj H12 w w' * Q v' w' :=
      Finset.sum_comm
    rw [h]; simp_rw [← Finset.mul_sum, hQ.col_sum, mul_one, sum_adj_H12]
  rw [h1, h2]

lemma sum_B_right (x : Vtx × Vtx) : ∑ y, B G12 H12 Q x y = Q x.1 x.2 * dd x := by
  simp only [B, mul_assoc, ← Finset.mul_sum]
  rw [sum_disc_mul hQ, dd]

/-- Step 2: `B(1, 1) = ∑_x q_x d(x) = 0`. -/
lemma sum_mul_dd : ∑ x : Vtx × Vtx, Q x.1 x.2 * dd x = 0 := by
  rw [Fintype.sum_prod_type]
  simp only [dd, mul_sub, Finset.sum_sub_distrib]
  have h : ∑ v, ∑ w, Q v w * (dg w : ℝ) = ∑ w, ∑ v, Q v w * (dg w : ℝ) := Finset.sum_comm
  rw [h]
  simp_rw [mul_comm (Q _ _), ← Finset.mul_sum, hQ.row_sum, hQ.col_sum]
  ring

/-! ## Step 3: core test and degree discrepancy -/

/-- Step 3: `L + B(s, t) ≤ 4 C_□(Q)` for `s, t : Ω → [-1, 1]`, `s` vanishing outside
`d = 0`. -/
lemma degree_add_bil_le (s t : Vtx × Vtx → ℝ) (hs : ∀ x, |s x| ≤ 1) (ht : ∀ x, |t x| ≤ 1)
    (hsd : ∀ x, s x ≠ 0 → dd x = 0) :
    ∑ x, Q x.1 x.2 * |dd x| + ∑ x, ∑ y, s x * B G12 H12 Q x y * t y ≤
      4 * costCut G12 H12 Q := by
  set e : Vtx × Vtx → ℝ := fun x => if 0 < dd x then 1 else if dd x < 0 then -1 else 0 with he_def
  have he : ∀ x, (1 + e x) * dd x = dd x + |dd x| := by
    intro x
    simp only [he_def]
    split_ifs with h1 h2
    · rw [abs_of_pos h1]; ring
    · rw [abs_of_neg h2]; ring
    · rw [le_antisymm (not_lt.mp h1) (not_lt.mp h2)]; simp
  have hf : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ x, 0 ≤ (1 + e x + ε * s x) / 2 ∧
      (1 + e x + ε * s x) / 2 ≤ 1 := by
    intro ε hε x
    have hεs : |ε * s x| ≤ 1 := by
      rcases hε with rfl | rfl <;> simpa using hs x
    obtain ⟨h1, h2⟩ := abs_le.mp hεs
    by_cases hx : s x = 0
    · rw [hx, mul_zero, add_zero]
      simp only [he_def]
      split_ifs <;> norm_num
    · have h0 : e x = 0 := by simp [he_def, hsd x hx]
      rw [h0]
      constructor <;> linarith
  have hg : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ y, 0 ≤ (1 + ε * t y) / 2 ∧ (1 + ε * t y) / 2 ≤ 1 := by
    intro ε hε y
    have hεt : |ε * t y| ≤ 1 := by
      rcases hε with rfl | rfl <;> simpa using ht y
    obtain ⟨h1, h2⟩ := abs_le.mp hεt
    constructor <;> linarith
  have hb : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ∑ x, ∑ y, (1 + e x + ε * s x) / 2 * B G12 H12 Q x y * ((1 + ε * t y) / 2) ≤
        costCut G12 H12 Q := fun ε hε =>
    (le_abs_self _).trans (abs_bilin_le_cutNorm _ _ _ (hf ε hε) (hg ε hε))
  have key : (∑ x, ∑ y, (1 + e x + 1 * s x) / 2 * B G12 H12 Q x y * ((1 + 1 * t y) / 2)) +
      ∑ x, ∑ y, (1 + e x + -1 * s x) / 2 * B G12 H12 Q x y * ((1 + -1 * t y) / 2) =
      (∑ x, Q x.1 x.2 * |dd x| + ∑ x, ∑ y, s x * B G12 H12 Q x y * t y) / 2 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib]
    have h : ∀ x y, (1 + e x + 1 * s x) / 2 * B G12 H12 Q x y * ((1 + 1 * t y) / 2) +
        (1 + e x + -1 * s x) / 2 * B G12 H12 Q x y * ((1 + -1 * t y) / 2) =
        (1 + e x) / 2 * B G12 H12 Q x y + s x * B G12 H12 Q x y * t y / 2 := by
      intro x y; ring
    simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, sum_B_right hQ, ← Finset.sum_div]
    have h' : ∀ x, (1 + e x) / 2 * (Q x.1 x.2 * dd x) =
        (Q x.1 x.2 * dd x + Q x.1 x.2 * |dd x|) / 2 := by
      intro x
      linear_combination (Q x.1 x.2 / 2) * he x
    simp_rw [h', ← Finset.sum_div, Finset.sum_add_distrib, sum_mul_dd hQ]
    ring
  have h1 := hb 1 (Or.inl rfl)
  have h2 := hb (-1) (Or.inr rfl)
  linarith

end DS

/-! ## Step 5: the pentagon -/

lemma abs_Z_le (i j : Fin 5) : |(Z i j : ℝ)| ≤ 1 := by
  have h : ∀ i j, |Z i j| ≤ 1 := by decide
  exact_mod_cast h i j

/-- The bilinear form `aᵀ diag(x) Z diag(x) b`. -/
noncomputable def zForm (x a b : Fin 5 → ℝ) : ℝ := ∑ i, ∑ j, a i * x i * Z i j * x j * b j

/-- For `x_k = max x`, flipping `a_k` in `a_j = Z_kj` changes `aᵀ diag(x) Z diag(x) a` by
`4 x_k (S - x_k)`. -/
lemma zForm_flip (x : Fin 5 → ℝ) (k : Fin 5) :
    zForm x (fun j => if j = k then 1 else (Z k j : ℝ)) (fun j => if j = k then 1 else (Z k j : ℝ)) -
      zForm x (fun j => if j = k then -1 else (Z k j : ℝ))
        (fun j => if j = k then -1 else (Z k j : ℝ)) =
      4 * x k * (∑ i, x i - x k) := by
  fin_cases k <;> simp [zForm, Fin.sum_univ_five, Z] <;> ring

/-- Step 5: for `x ∈ [0, 2]^5` there are `a, b ∈ [-1, 1]^5` with
`aᵀ diag(x) Z diag(x) b ≥ 16/5 ∑ x_i - 8`. -/
lemma exists_zForm_ge (x : Fin 5 → ℝ) (h0 : ∀ i, 0 ≤ x i) (h2 : ∀ i, x i ≤ 2) :
    ∃ a b : Fin 5 → ℝ, (∀ i, |a i| ≤ 1) ∧ (∀ i, |b i| ≤ 1) ∧
      16 / 5 * ∑ i, x i - 8 ≤ zForm x a b := by
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image univ x univ_nonempty
  have hS1 : x k ≤ ∑ i, x i := Finset.single_le_sum (fun i _ => h0 i) (mem_univ k)
  have hS5 : ∑ i, x i ≤ 5 * x k := by
    have := Finset.sum_le_sum fun i (hi : i ∈ univ) => hk i hi
    simpa using this
  have hpoly : 16 / 5 * ∑ i, x i - 8 ≤ 2 * x k * (∑ i, x i - x k) := by
    have := h0 k; have := h2 k
    rcases le_total (x k) (8 / 5) with h | h
    · nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hS5), sq_nonneg (x k - 1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hS1)]
  set aP : Fin 5 → ℝ := fun j => if j = k then 1 else (Z k j : ℝ)
  set aM : Fin 5 → ℝ := fun j => if j = k then -1 else (Z k j : ℝ)
  have hP : ∀ i, |aP i| ≤ 1 := fun i => by
    simp only [aP]; split_ifs <;> simp [abs_Z_le]
  have hM : ∀ i, |aM i| ≤ 1 := fun i => by
    simp only [aM]; split_ifs <;> simp [abs_Z_le]
  have hflip := zForm_flip x k
  rcases le_total (2 * x k * (∑ i, x i - x k)) (zForm x aP aP) with h | h
  · exact ⟨aP, aP, hP, hP, hpoly.trans h⟩
  · refine ⟨aM, fun j => -aM j, hM, fun j => by simpa using hM j, ?_⟩
    have hneg : zForm x aM (fun j => -aM j) = -zForm x aM aM := by
      simp [zForm, Finset.sum_neg_distrib]
    rw [hneg]
    linarith

/-! ## Step 5: test functions on the core atoms -/

/-- The test function with value `σ a_i` on straight atoms `(v_i^σ, w_i^σ)`, `σ a'_i` on crossed
atoms `(v_i^σ, w_i^{-σ})` and `0` elsewhere. -/
noncomputable def testFn (a a' : Fin 5 → ℝ) : Vtx × Vtx → ℝ
  | (.inl (i, σ), .inl (j, τ)) => if i = j then (sg σ : ℝ) * (if σ = τ then a i else a' i) else 0
  | _ => 0

lemma testFn_atom (a a' : Fin 5 → ℝ) (x : Fin 5 × Bool × Bool) :
    testFn a a' (atom x) = (sg x.2.1 : ℝ) * (if x.2.1 = x.2.2 then a x.1 else a' x.1) := by
  simp [testFn, atom]

lemma testFn_eq_zero (a a' : Fin 5 → ℝ) {x : Vtx × Vtx} (hx : x ∉ Set.range atom) :
    testFn a a' x = 0 := by
  rcases x with ⟨⟨i, σ⟩ | m, ⟨j, τ⟩ | m'⟩ <;> simp only [testFn]
  by_cases h : i = j
  · subst h; exact absurd ⟨(i, σ, τ), rfl⟩ hx
  · simp [h]

lemma abs_testFn_le {a a' : Fin 5 → ℝ} (ha : ∀ i, |a i| ≤ 1) (ha' : ∀ i, |a' i| ≤ 1)
    (x : Vtx × Vtx) : |testFn a a' x| ≤ 1 := by
  rcases x with ⟨⟨i, σ⟩ | m, ⟨j, τ⟩ | m'⟩ <;> simp only [testFn, abs_zero, zero_le_one]
  split_ifs <;> simp [sg] <;> split_ifs <;> simp [ha, ha']

lemma dd_of_testFn_ne_zero (a a' : Fin 5 → ℝ) {x : Vtx × Vtx} (hx : testFn a a' x ≠ 0) :
    dd x = 0 := by
  by_cases h : x ∈ Set.range atom
  · obtain ⟨⟨i, σ, τ⟩, rfl⟩ := h
    simp [dd, atom, dg]
  · exact absurd (testFn_eq_zero a a' h) hx

/-- A function on atoms vanishing outside the core atoms sums over the core atoms. -/
lemma sum_eq_sum_atom (f : Vtx × Vtx → ℝ) (hf : ∀ x, x ∉ Set.range atom → f x = 0) :
    ∑ x, f x = ∑ y, f (atom y) :=
  (Fintype.sum_of_injective atom atom_injective _ f hf fun _ => rfl).symm

/-- On core atoms `D = ½ Z_ij (σσ' + ττ')`. -/
lemma disc_atom (x y : Fin 5 × Bool × Bool) :
    disc G12 H12 (atom x).1 (atom x).2 (atom y).1 (atom y).2 =
      (Z x.1 y.1 : ℝ) * (sg x.2.1 * sg y.2.1 + sg x.2.2 * sg y.2.2) / 2 := by
  obtain ⟨i, s, s'⟩ := x
  obtain ⟨j, t, t'⟩ := y
  have h := congrArg (fun z : ℤ => (z : ℝ)) (two_mul_gCore_sub_hCore i j s s' t t')
  push_cast at h
  simp only [disc, atom, adj_G12_inl_inl, adj_H12_inl_inl]
  linarith

/-- Step 5: the test functions realise the straight and the crossed block,
`B(s, t) = aᵀ C Z C b + a'ᵀ H Z H b'`. -/
lemma bil_testFn (Q : Vtx → Vtx → ℝ) (a a' b b' : Fin 5 → ℝ) :
    ∑ x, ∑ y, testFn a a' x * B G12 H12 Q x y * testFn b b' y =
      zForm (fun i => Q (.inl (i, true)) (.inl (i, true)) + Q (.inl (i, false)) (.inl (i, false)))
          a b +
        zForm (fun i => Q (.inl (i, true)) (.inl (i, false)) +
          Q (.inl (i, false)) (.inl (i, true))) a' b' := by
  have hin : ∀ x, ∑ y, testFn a a' x * B G12 H12 Q x y * testFn b b' y =
      ∑ y, testFn a a' x * B G12 H12 Q x (atom y) * testFn b b' (atom y) := fun x =>
    sum_eq_sum_atom _ fun y hy => by simp [testFn_eq_zero b b' hy]
  simp_rw [hin]
  rw [sum_eq_sum_atom _ fun x hx => by simp [testFn_eq_zero a a' hx]]
  simp only [B, testFn_atom, disc_atom]
  simp only [zForm, atom, ← Finset.sum_add_distrib]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp_rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sg]
  push_cast
  ring

/-! ## Step 4: `L ≥ 9 (10 - T)` -/

section DS

variable {Q : Vtx → Vtx → ℝ} (hQ : IsDS Q)
include hQ

/-- The mass `∑_τ Q(v, w_i^τ)` of a row on the pair `i`, as a sum over all columns. -/
lemma sum_pair_eq (v : Vtx) (i : Fin 5) :
    ∑ τ : Bool, Q v (.inl (i, τ)) =
      ∑ w, Sum.elim (fun q : Core => if q.1 = i then Q v (.inl q) else 0)
        (fun _ : Marker => (0 : ℝ)) w := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [Finset.sum_add_distrib]

lemma sum_pair_le_one (v : Vtx) (i : Fin 5) : ∑ τ : Bool, Q v (.inl (i, τ)) ≤ 1 := by
  rw [sum_pair_eq hQ, ← hQ.row_sum v]
  refine Finset.sum_le_sum fun w _ => ?_
  rcases w with q | m
  · simp only [Sum.elim_inl]; split_ifs
    · rfl
    · exact hQ.nonneg _ _
  · exact hQ.nonneg _ _

/-- A row of a core vertex `v_i^σ` contributes at least `9 (1 - ∑_τ Q(v_i^σ, w_i^τ))` to `L`. -/
lemma nine_mul_le_row (p : Core) :
    9 - 9 * ∑ τ : Bool, Q (.inl p) (.inl (p.1, τ)) ≤ ∑ w, Q (.inl p) w * |dd (.inl p, w)| := by
  have h9 : (9 : ℝ) = ∑ w, 9 * Q (.inl p) w := by rw [← Finset.mul_sum, hQ.row_sum, mul_one]
  rw [sum_pair_eq hQ, Finset.mul_sum]
  nth_rw 1 [h9]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  have hq := hQ.nonneg (.inl p) w
  have h9 : dg (.inl p) ≠ dg w → 9 * Q (.inl p) w ≤ Q (.inl p) w * |dd (.inl p, w)| := fun h => by
    have := nine_le_of_dg_ne h
    rw [dd]; nlinarith
  rcases w with ⟨j, τ⟩ | m
  · simp only [Sum.elim_inl]
    split_ifs with hj
    · nlinarith [abs_nonneg (dd (.inl p, .inl (j, τ)))]
    · have : dg (.inl p) ≠ dg (.inl (j, τ)) := by
        simp only [dg, ne_eq, Nat.add_left_cancel_iff, mul_eq_mul_left_iff, add_left_inj,
          OfNat.ofNat_ne_zero, or_false]
        exact fun h => hj (Fin.ext h).symm
      linarith [h9 this]
  · simp only [Sum.elim_inr, mul_zero, sub_zero]
    exact h9 (by simp only [dg]; omega)

/-- Step 4: `L ≥ 9 (10 - T)`. -/
lemma nine_mul_le_L :
    90 - 9 * ∑ i : Fin 5, ∑ σ : Bool, ∑ τ : Bool, Q (.inl (i, σ)) (.inl (i, τ)) ≤
      ∑ x : Vtx × Vtx, Q x.1 x.2 * |dd x| := by
  have e1 : ∑ p : Core, (9 - 9 * ∑ τ : Bool, Q (.inl p) (.inl (p.1, τ))) =
      90 - 9 * ∑ i : Fin 5, ∑ σ : Bool, ∑ τ : Bool, Q (.inl (i, σ)) (.inl (i, τ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul, Fintype.sum_prod_type]
    norm_num
  have e2 : ∑ x : Vtx × Vtx, Q x.1 x.2 * |dd x| =
      ∑ p : Core, ∑ w, Q (.inl p) w * |dd (.inl p, w)| +
        ∑ m : Marker, ∑ w, Q (.inr m) w * |dd (.inr m, w)| := by
    simp only [Fintype.sum_prod_type, Fintype.sum_sum_type]
  have hm : 0 ≤ ∑ m : Marker, ∑ w, Q (.inr m) w * |dd (.inr m, w)| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun w _ =>
      mul_nonneg (hQ.nonneg _ _) (abs_nonneg _)
  have hc := Finset.sum_le_sum fun (p : Core) (_ : p ∈ univ) => nine_mul_le_row hQ p
  rw [e2, ← e1]
  linarith

/-! ## The lower bound -/

/-- **`C_□(Q) ≥ 4`** for every `Q ∈ DS(V, W)`. -/
theorem four_le_costCut : 4 ≤ costCut G12 H12 Q := by
  set c : Fin 5 → ℝ := fun i => Q (.inl (i, true)) (.inl (i, true)) +
    Q (.inl (i, false)) (.inl (i, false))
  set h : Fin 5 → ℝ := fun i => Q (.inl (i, true)) (.inl (i, false)) +
    Q (.inl (i, false)) (.inl (i, true))
  have hle (v w : Vtx) := hQ.le_one v w
  have hn (v w : Vtx) := hQ.nonneg v w
  have hc : ∀ i, 0 ≤ c i ∧ c i ≤ 2 := fun i => by
    have := hn (.inl (i, true)) (.inl (i, true)); have := hn (.inl (i, false)) (.inl (i, false))
    have := hle (.inl (i, true)) (.inl (i, true)); have := hle (.inl (i, false)) (.inl (i, false))
    simp only [c]; constructor <;> linarith
  have hh : ∀ i, 0 ≤ h i ∧ h i ≤ 2 := fun i => by
    have := hn (.inl (i, true)) (.inl (i, false)); have := hn (.inl (i, false)) (.inl (i, true))
    have := hle (.inl (i, true)) (.inl (i, false)); have := hle (.inl (i, false)) (.inl (i, true))
    simp only [h]; constructor <;> linarith
  obtain ⟨a, b, ha, hb, hab⟩ := exists_zForm_ge c (fun i => (hc i).1) (fun i => (hc i).2)
  obtain ⟨a', b', ha', hb', hab'⟩ := exists_zForm_ge h (fun i => (hh i).1) (fun i => (hh i).2)
  have h1 := degree_add_bil_le hQ (testFn a a') (testFn b b') (abs_testFn_le ha ha')
    (abs_testFn_le hb hb') fun x hx => dd_of_testFn_ne_zero a a' hx
  rw [bil_testFn] at h1
  have hL := nine_mul_le_L hQ
  have hT : ∑ i : Fin 5, ∑ σ : Bool, ∑ τ : Bool, Q (.inl (i, σ)) (.inl (i, τ)) =
      ∑ i, c i + ∑ i, h i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fintype.sum_bool, c, h]; ring
  have hT10 : ∑ i : Fin 5, ∑ σ : Bool, ∑ τ : Bool, Q (.inl (i, σ)) (.inl (i, τ)) ≤ 10 := by
    have := Finset.sum_le_sum fun (i : Fin 5) (_ : i ∈ univ) =>
      Finset.sum_le_sum fun (σ : Bool) (_ : σ ∈ univ) => sum_pair_le_one hQ (.inl (i, σ)) i
    simpa using this.trans (by norm_num)
  linarith

end DS

/-- **`d_□^OT(G, H) ≥ 4`** (the remark after Proposition 10, p. 10, l. 330). -/
theorem four_le_dOTCut : 4 ≤ dOTCut G12 H12 :=
  have : Nonempty {Q : Vtx → Vtx → ℝ // IsDS Q} := ⟨⟨Q40, Q40_isDS⟩⟩
  le_ciInf fun Q => four_le_costCut Q.2

/-- **`d_□^OT(G, H) = 4`** (Proposition 10 with the remark after it): Lemma 34 and
`four_le_dOTCut`. -/
theorem dOTCut_eq_four : dOTCut G12 H12 = 4 :=
  le_antisymm lemma34 four_le_dOTCut

end GsimOT.Prop10
