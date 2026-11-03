/-
# The graphs `G` and `H` of Proposition 10

Paper, Proposition 10 (p. 9, l. 324), Figure 3 (p. 10) and App. E.1 (construction, pp. 30–31,
l. 950–966).

Both graphs live on the same vertex set `Vtx` consisting of
* a *core* of ten vertices `v_i^σ` (`i ∈ ℤ₅`, `σ ∈ {+1, -1}`), represented by `(i, b) : Fin 5 × Bool`
  with `σ = sg b` (`sg true = +1`, `sg false = -1`), and
* for every `i ∈ ℤ₅` a set `L_i` of `9(i+1)` *markers*, represented by `⟨i, k⟩ : Σ i, Fin (9(i+1))`.

Core vertices are joined according to the pentagon matrix `Z` (`Z_ij = +1` if `j = i ± 1`,
`Z_ij = -1` if `j = i ± 2`, `Z_ii = 0`):
`v_i^σ v_j^τ ∈ E(G) ⟺ στ = Z_ij` and `w_i^σ w_j^τ ∈ E(H) ⟺ στ = -Z_ij`.
Every marker of `L_i` is adjacent to both core vertices of the pair `i`, in both graphs.
We identify `V` and `W` with `Vtx` via the natural bijection `id` of the paper (`v_i^σ ↦ w_i^σ`,
`L_i → L'_i`; proof of Lemma 33, p. 31, l. 984–985).

The file also contains the two finite facts used in Lemmas 33 and 34:
* the degrees `13, 22, 31, 40, 49` (core pairs) and `2` (markers), in both graphs;
* the pentagon bound `|xᵀ Z y| ≤ 8` for `x, y ∈ {-1, 0, 1}^5` (`‖Z‖_{∞→1} ≤ 8`).
-/
import GsimOT.Common.CutNorm

open Finset

namespace GsimOT.Prop12

/-! ## Vertices -/

/-- Core vertices `v_i^σ`: `(i, b)` stands for `v_i^{sg b}`. -/
abbrev Core := Fin 5 × Bool

/-- Markers: `⟨i, k⟩` is the `k`-th marker of `L_i`, `|L_i| = 9(i+1)`. -/
abbrev Marker := Σ i : Fin 5, Fin (9 * (i.val + 1))

/-- The common vertex set of `G` and `H`: core plus markers. -/
abbrev Vtx := Core ⊕ Marker

lemma card_Vtx : Fintype.card Vtx = 145 := by
  simp [Fintype.card_sum, Fintype.card_sigma, Fin.sum_univ_five]

/-! ## The pentagon matrix -/

/-- The sign `σ ∈ {+1, -1}` encoded by a boolean. -/
def sg (b : Bool) : ℤ := if b then 1 else -1

/-- The pentagon matrix `Z` of App. E.1: `+1` on sides, `-1` on diagonals, `0` on the diagonal. -/
def Z (i j : Fin 5) : ℤ :=
  if j = i + 1 ∨ i = j + 1 then 1 else if j = i + 2 ∨ i = j + 2 then -1 else 0

lemma Z_symm (i j : Fin 5) : Z i j = Z j i := by revert i j; decide

/-! ## The graphs -/

/-- Adjacency of `G` (as a boolean function). -/
def gAdj : Vtx → Vtx → Bool
  | .inl p, .inl q => decide (Z p.1 q.1 = sg p.2 * sg q.2)
  | .inl p, .inr m => decide (m.1 = p.1)
  | .inr m, .inl p => decide (m.1 = p.1)
  | .inr _, .inr _ => false

/-- Adjacency of `H` (as a boolean function). -/
def hAdj : Vtx → Vtx → Bool
  | .inl p, .inl q => decide (Z p.1 q.1 = -(sg p.2 * sg q.2))
  | .inl p, .inr m => decide (m.1 = p.1)
  | .inr m, .inl p => decide (m.1 = p.1)
  | .inr _, .inr _ => false

lemma gAdj_symm (a b : Vtx) : gAdj a b = gAdj b a := by
  rcases a with ⟨i, s⟩ | m <;> rcases b with ⟨j, t⟩ | m' <;> simp only [gAdj]
  rw [Z_symm i j, mul_comm]

lemma hAdj_symm (a b : Vtx) : hAdj a b = hAdj b a := by
  rcases a with ⟨i, s⟩ | m <;> rcases b with ⟨j, t⟩ | m' <;> simp only [hAdj]
  rw [Z_symm i j, mul_comm]

lemma gAdj_self (a : Vtx) : gAdj a a = false := by
  rcases a with ⟨i, b⟩ | m
  · revert i b; decide
  · rfl

lemma hAdj_self (a : Vtx) : hAdj a a = false := by
  rcases a with ⟨i, b⟩ | m
  · revert i b; decide
  · rfl

/-- The graph `G` of Proposition 10 (App. E.1). -/
def G12 : SimpleGraph Vtx where
  Adj a b := gAdj a b = true
  symm := ⟨fun a b h => by rw [gAdj_symm]; exact h⟩
  loopless := ⟨fun a h => by rw [gAdj_self] at h; exact Bool.false_ne_true h⟩

/-- The graph `H` of Proposition 10 (App. E.1). -/
def H12 : SimpleGraph Vtx where
  Adj a b := hAdj a b = true
  symm := ⟨fun a b h => by rw [hAdj_symm]; exact h⟩
  loopless := ⟨fun a h => by rw [hAdj_self] at h; exact Bool.false_ne_true h⟩

instance : DecidableRel G12.Adj := fun a b => inferInstanceAs (Decidable (gAdj a b = true))

instance : DecidableRel H12.Adj := fun a b => inferInstanceAs (Decidable (hAdj a b = true))

/-! ## Adjacency entries -/

/-- `A_G` on the core, as an integer. -/
def gCore (p q : Core) : ℤ := if Z p.1 q.1 = sg p.2 * sg q.2 then 1 else 0

/-- `A_H` on the core, as an integer. -/
def hCore (p q : Core) : ℤ := if Z p.1 q.1 = -(sg p.2 * sg q.2) then 1 else 0

lemma adj_G12_inl_inl (p q : Core) : adj G12 (.inl p) (.inl q) = (gCore p q : ℝ) := by
  simp only [adj, G12, gAdj, gCore, decide_eq_true_eq]; split_ifs <;> simp

lemma adj_H12_inl_inl (p q : Core) : adj H12 (.inl p) (.inl q) = (hCore p q : ℝ) := by
  simp only [adj, H12, hAdj, hCore, decide_eq_true_eq]; split_ifs <;> simp

/-- Outside the core, `G` and `H` coincide. -/
lemma adj_G12_inl_inr (p : Core) (m : Marker) :
    adj G12 (.inl p) (.inr m) = if m.1 = p.1 then 1 else 0 := by
  simp [adj, G12, gAdj]

lemma adj_H12_inl_inr (p : Core) (m : Marker) :
    adj H12 (.inl p) (.inr m) = if m.1 = p.1 then 1 else 0 := by
  simp [adj, H12, hAdj]

lemma adj_G12_inr_inl (m : Marker) (p : Core) :
    adj G12 (.inr m) (.inl p) = if m.1 = p.1 then 1 else 0 := by
  simp [adj, G12, gAdj]

lemma adj_H12_inr_inl (m : Marker) (p : Core) :
    adj H12 (.inr m) (.inl p) = if m.1 = p.1 then 1 else 0 := by
  simp [adj, H12, hAdj]

lemma adj_G12_inr_inr (m m' : Marker) : adj G12 (.inr m) (.inr m') = 0 := by
  simp [adj, G12, gAdj]

lemma adj_H12_inr_inr (m m' : Marker) : adj H12 (.inr m) (.inr m') = 0 := by
  simp [adj, H12, hAdj]

/-- `G` and `H` agree on every pair of vertices that is not a pair of core vertices. -/
lemma adj_G12_eq_adj_H12 (a b : Vtx) (h : a.isRight ∨ b.isRight) :
    adj G12 a b = adj H12 a b := by
  rcases a with p | m <;> rcases b with q | m' <;> simp at h <;>
    simp [adj_G12_inl_inr, adj_H12_inl_inr, adj_G12_inr_inl, adj_H12_inr_inl,
      adj_G12_inr_inr, adj_H12_inr_inr]

/-- On the core, `A_G(v_i^σ, v_j^τ) - A_H(w_i^{σ'}, w_j^{τ'}) = ½ Z_ij (στ + σ'τ')`
(App. E.1, proof of Lemma 34; with `σ' = σ, τ' = τ` this is `Z_ij στ`, proof of Lemma 33). -/
lemma two_mul_gCore_sub_hCore (i j : Fin 5) (s s' t t' : Bool) :
    2 * (gCore (i, s) (j, t) - hCore (i, s') (j, t')) =
      Z i j * (sg s * sg t + sg s' * sg t') := by
  revert i j s s' t t'; decide

lemma gCore_sub_hCore (i j : Fin 5) (s t : Bool) :
    gCore (i, s) (j, t) - hCore (i, s) (j, t) = Z i j * sg s * sg t := by
  revert i j s t; decide

/-- Proof of Lemma 33: if the pairs are flipped according to signs `r_i` (`π(v_i^σ) = w_i^{r_iσ}`),
then on the core `A(w_i^σ, w_j^τ) = M_ij στ` with `M_ij = ½ Z_ij (1 + r_i r_j)`. -/
lemma gCore_xor_sub_hCore (i j : Fin 5) (a b s t : Bool) :
    gCore (i, Bool.xor s a) (j, Bool.xor t b) - hCore (i, s) (j, t) =
      (if a = b then Z i j else 0) * sg s * sg t := by
  revert i j a b s t; decide

/-! ## Degrees -/

/-- The common degree function: pair `i` has degree `4 + 9(i+1)`, markers have degree `2`. -/
def dg : Vtx → ℕ
  | .inl p => 4 + 9 * (p.1.val + 1)
  | .inr _ => 2

lemma sum_gCore (p : Core) : ∑ q : Core, gCore p q = 4 := by
  revert p; decide

lemma sum_hCore (p : Core) : ∑ q : Core, hCore p q = 4 := by
  revert p; decide

lemma sum_marker_ite (i : Fin 5) :
    ∑ m : Marker, (if m.1 = i then (1 : ℝ) else 0) = 9 * (i.val + 1) := by
  rw [Fintype.sum_sigma]
  fin_cases i <;> simp [Fin.sum_univ_five] <;> norm_num

lemma sum_core_ite (i : Fin 5) :
    ∑ p : Core, (if i = p.1 then (1 : ℝ) else 0) = 2 := by
  rw [Fintype.sum_prod_type]
  fin_cases i <;> simp [Fin.sum_univ_five]

/-- Degrees in `G` (App. E.1: `13, 22, 31, 40, 49` on the pairs, `2` on markers). -/
lemma sum_adj_G12 (v : Vtx) : ∑ v', adj G12 v v' = dg v := by
  rw [Fintype.sum_sum_type]
  rcases v with p | m
  · simp only [adj_G12_inl_inl, adj_G12_inl_inr, dg]
    rw [sum_marker_ite, ← Int.cast_sum, sum_gCore]
    push_cast; ring
  · simp only [adj_G12_inr_inl, adj_G12_inr_inr, dg]
    rw [sum_core_ite]
    simp

/-- Degrees in `H` (same as in `G`). -/
lemma sum_adj_H12 (v : Vtx) : ∑ v', adj H12 v v' = dg v := by
  rw [Fintype.sum_sum_type]
  rcases v with p | m
  · simp only [adj_H12_inl_inl, adj_H12_inl_inr, dg]
    rw [sum_marker_ite, ← Int.cast_sum, sum_hCore]
    push_cast; ring
  · simp only [adj_H12_inr_inl, adj_H12_inr_inr, dg]
    rw [sum_core_ite]
    simp

/-- Distinct degrees differ by at least `9`. -/
lemma nine_le_of_dg_ne {a b : Vtx} (h : dg a ≠ dg b) : 9 ≤ |(dg a : ℝ) - dg b| := by
  have key : 9 ≤ |(dg a : ℤ) - dg b| := by
    rcases a with ⟨i, _⟩ | _ <;> rcases b with ⟨j, _⟩ | _ <;> simp only [dg] at h ⊢ <;>
      push_cast <;> rw [le_abs] <;> omega
  exact_mod_cast key

/-! ## Cut sums as indicator sums -/

/-- `∑_{a ∈ S} f a = ∑_a 1[a ∈ S] f a`. -/
lemma sum_mem_eq_sum_ite {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (f : α → ℝ) :
    ∑ a ∈ S, f a = ∑ a, (if a ∈ S then 1 else 0) * f a := by
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-! ## The pentagon bound `‖Z‖_{∞→1} ≤ 8` -/

/-- Encoding of `{0, +1, -1}`. -/
def e3 : Fin 3 → ℤ := ![0, 1, -1]

/-- Finite check: `∑_j |(Zx)_j| ≤ 8` for all `x ∈ {-1, 0, 1}^5`. -/
lemma sum_abs_Z_mul_le_int : ∀ a b c d e : Fin 3,
    ∑ j, |∑ i, Z i j * e3 (![a, b, c, d, e] i)| ≤ 8 := by decide

/-- A real number in `{-1, 0, 1}`. -/
def IsTri (x : ℝ) : Prop := x = -1 ∨ x = 0 ∨ x = 1

lemma IsTri.exists_e3 {x : ℝ} (h : IsTri x) : ∃ c : Fin 3, x = e3 c := by
  rcases h with h | h | h
  · exact ⟨2, by simp [h, e3]⟩
  · exact ⟨0, by simp [h, e3]⟩
  · exact ⟨1, by simp [h, e3]⟩

lemma IsTri.abs_le_one {x : ℝ} (h : IsTri x) : |x| ≤ 1 := by
  rcases h with h | h | h <;> simp [h]

lemma isTri_ite_sub_ite (P Q : Prop) [Decidable P] [Decidable Q] :
    IsTri ((if P then 1 else 0) - (if Q then 1 else 0)) := by
  unfold IsTri; split_ifs <;> norm_num

lemma sum_abs_Z_mul_le {x : Fin 5 → ℝ} (hx : ∀ i, IsTri (x i)) :
    ∑ j, |∑ i, (Z i j : ℝ) * x i| ≤ 8 := by
  choose c hc using fun i => (hx i).exists_e3
  have hc' : c = ![c 0, c 1, c 2, c 3, c 4] := by
    funext i; fin_cases i <;> rfl
  have h := sum_abs_Z_mul_le_int (c 0) (c 1) (c 2) (c 3) (c 4)
  rw [← hc'] at h
  simp_rw [hc]
  exact_mod_cast h

/-- The pentagon bound `|xᵀ Z y| ≤ 8` for `x, y ∈ {-1, 0, 1}^5` (App. E.1, proof of Lemma 33:
`C_□(id) = ‖Z‖_{∞→1} = 8`). -/
lemma abs_bilin_Z_le {x y : Fin 5 → ℝ} (hx : ∀ i, IsTri (x i)) (hy : ∀ j, IsTri (y j)) :
    |∑ i, ∑ j, (Z i j : ℝ) * x i * y j| ≤ 8 := by
  have e : ∑ i, ∑ j, (Z i j : ℝ) * x i * y j = ∑ j, (∑ i, (Z i j : ℝ) * x i) * y j := by
    rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => ?_).trans
    (sum_abs_Z_mul_le hx))
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hy j).abs_le_one

end GsimOT.Prop12
