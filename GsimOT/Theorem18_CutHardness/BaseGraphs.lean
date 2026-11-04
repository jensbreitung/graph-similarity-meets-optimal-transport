import GsimOT.Common.MatrixNorms

/-!
# The base graphs of Theorem 18

The proof of Theorem 18 (p. 57, l. 1826–1830) uses the graphs `G'`, `H'` of [GG22, Theorem 23],
with `C_□(π) = ‖A_{G'} - A_{H'}‖_□ = 2 · maxcut(F)` for the canonical bijection `π`. As in the
proof of Claim 59 (p. 59, l. 1885–1891), they are built from the `2m × n` matrix of
[AN06, Proposition 3.2], in which every edge of `F` contributes two rows with one entry `+1` and
one entry `-1`: `G'` has the edges of the positive entries, `H'` those of the negative entries.
`cutNorm_anG_sub_anH` proves `‖A_{G'} - A_{H'}‖_□ = 2 · maxcut(F)`.

For a graph `F` on `Fin n`, the base vertices are the signed edges `e⁺, e⁻` of `F` and the
vertices of `F`; for an edge `e = uv` with `u < v`, `G'` has the edges `e⁺u` and `e⁻v`, and `H'`
has the edges `e⁺v` and `e⁻u`. Then `A_{G'} - A_{H'}` consists of the blocks `N` and `Nᵀ` with
`N(e^±, c) = ±([c = u] - [c = v])`, so a set `R` of signed edges and a set `C` of vertices give
`|N(R, C)| ≤ cut(C)`, with equality for the signed edges that `C` cuts positively.
-/

open Finset

namespace GsimOT.Hardness

/-! ### Bipartite graphs from a relation -/

section Bip

variable {R C : Type*} (P : R → C → Prop)

/-- The adjacency relation of `bipGraph P`. -/
def bipAdj : R ⊕ C → R ⊕ C → Prop
  | .inl r, .inr c => P r c
  | .inr c, .inl r => P r c
  | _, _ => False

/-- The bipartite graph on `R ⊕ C` with an edge `rc` whenever `P r c`. -/
def bipGraph : SimpleGraph (R ⊕ C) where
  Adj := bipAdj P
  symm := ⟨fun x y h ↦ by cases x <;> cases y <;> exact h⟩
  loopless := ⟨fun x h ↦ by cases x <;> exact h⟩

instance [DecidableRel P] : DecidableRel (bipGraph P).Adj
  | .inl r, .inr c => inferInstanceAs (Decidable (P r c))
  | .inr c, .inl r => inferInstanceAs (Decidable (P r c))
  | .inl _, .inl _ => inferInstanceAs (Decidable False)
  | .inr _, .inr _ => inferInstanceAs (Decidable False)

variable {P}

@[simp] lemma bipGraph_adj_inl_inr {r : R} {c : C} : (bipGraph P).Adj (.inl r) (.inr c) ↔ P r c :=
  Iff.rfl

@[simp] lemma bipGraph_adj_inr_inl {r : R} {c : C} : (bipGraph P).Adj (.inr c) (.inl r) ↔ P r c :=
  Iff.rfl

@[simp] lemma bipGraph_adj_inl_inl {r r' : R} : ¬(bipGraph P).Adj (.inl r) (.inl r') := id

@[simp] lemma bipGraph_adj_inr_inr {c c' : C} : ¬(bipGraph P).Adj (.inr c) (.inr c') := id

variable [DecidableRel P]

@[simp] lemma adj_bipGraph_inl_inr (r : R) (c : C) :
    adj (bipGraph P) (.inl r) (.inr c) = if P r c then 1 else 0 := rfl

@[simp] lemma adj_bipGraph_inr_inl (r : R) (c : C) :
    adj (bipGraph P) (.inr c) (.inl r) = if P r c then 1 else 0 := rfl

@[simp] lemma adj_bipGraph_inl_inl (r r' : R) :
    adj (bipGraph P) (.inl r) (.inl r') = 0 := rfl

@[simp] lemma adj_bipGraph_inr_inr (c c' : C) :
    adj (bipGraph P) (.inr c) (.inr c') = 0 := rfl

end Bip

/-! ### MaxCut -/

section MaxCut

variable {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]

/-- The edges of `F`, as pairs `(u, v)` with `u < v`. -/
abbrev Edge := {p : Fin n × Fin n // p.1 < p.2 ∧ F.Adj p.1 p.2}

/-- The number of edges of `F` cut by `U`. -/
def cutSize (U : Finset (Fin n)) : ℕ := #{e : Edge F | (e.1.1 ∈ U ↔ e.1.2 ∉ U)}

/-- `maxcut(F)`: the maximum number of edges cut by a vertex set. -/
def maxcut : ℕ := (univ : Finset (Finset (Fin n))).sup (cutSize F)

/-- `G'`: the signed edge `e⁺` is adjacent to `u` and `e⁻` to `v`, for `e = uv`, `u < v`. -/
def anG : SimpleGraph ((Edge F × Bool) ⊕ Fin n) :=
  bipGraph fun r c ↦ (r.2 = true ∧ c = r.1.1.1) ∨ (r.2 = false ∧ c = r.1.1.2)

/-- `H'`: the signed edge `e⁺` is adjacent to `v` and `e⁻` to `u`, for `e = uv`, `u < v`. -/
def anH : SimpleGraph ((Edge F × Bool) ⊕ Fin n) :=
  bipGraph fun r c ↦ (r.2 = true ∧ c = r.1.1.2) ∨ (r.2 = false ∧ c = r.1.1.1)

instance : DecidableRel (anG F).Adj := inferInstanceAs (DecidableRel (bipGraph _).Adj)
instance : DecidableRel (anH F).Adj := inferInstanceAs (DecidableRel (bipGraph _).Adj)

omit [DecidableRel F.Adj] in
lemma adj_anG (r : Edge F × Bool) (c : Fin n) :
    adj (anG F) (.inl r) (.inr c) =
      if (r.2 = true ∧ c = r.1.1.1) ∨ (r.2 = false ∧ c = r.1.1.2) then 1 else 0 := rfl

omit [DecidableRel F.Adj] in
lemma adj_anH (r : Edge F × Bool) (c : Fin n) :
    adj (anH F) (.inl r) (.inr c) =
      if (r.2 = true ∧ c = r.1.1.2) ∨ (r.2 = false ∧ c = r.1.1.1) then 1 else 0 := rfl

/-- The sign `±1` of a signed edge. -/
def sgn (s : Bool) : ℝ := if s then 1 else -1

/-- `d_e(C) = [u ∈ C] - [v ∈ C]` for the edge `e = uv`. -/
def dE (C : Finset (Fin n)) (e : Edge F) : ℝ :=
  (if e.1.1 ∈ C then 1 else 0) - (if e.1.2 ∈ C then 1 else 0)

omit [DecidableRel F.Adj] in
/-- The Alon–Naor matrix `N(e^s, c) = s([c = u] - [c = v])`, i.e. the off-diagonal block of
`A_{G'} - A_{H'}`. -/
lemma anG_sub_anH_inl_inr (r : Edge F × Bool) (c : Fin n) :
    adj (anG F) (.inl r) (.inr c) - adj (anH F) (.inl r) (.inr c) =
      sgn r.2 * ((if c = r.1.1.1 then 1 else 0) - (if c = r.1.1.2 then 1 else 0)) := by
  obtain ⟨⟨⟨u, v⟩, huv, -⟩, s⟩ := r
  have : u ≠ v := huv.ne
  rw [adj_anG, adj_anH]
  simp only [sgn]
  cases s <;> by_cases hu : c = u <;> by_cases hv : c = v <;> simp_all

omit [DecidableRel F.Adj] in
lemma sum_N (R' : Finset (Edge F × Bool)) (C' : Finset (Fin n)) :
    ∑ r ∈ R', ∑ c ∈ C', (adj (anG F) (.inl r) (.inr c) -
      adj (anH F) (.inl r) (.inr c)) = ∑ r ∈ R', sgn r.2 * dE F C' r.1 := by
  refine sum_congr rfl fun r _ ↦ ?_
  simp only [anG_sub_anH_inl_inr, ← mul_sum, sum_sub_distrib, sum_ite_eq', dE]

omit [DecidableRel F.Adj] in
lemma abs_dE (C : Finset (Fin n)) (e : Edge F) :
    |dE F C e| = if (e.1.1 ∈ C ↔ e.1.2 ∉ C) then 1 else 0 := by
  unfold dE
  by_cases hu : e.1.1 ∈ C <;> by_cases hv : e.1.2 ∈ C <;> simp [hu, hv]

lemma cutSize_eq_sum (C : Finset (Fin n)) :
    (cutSize F C : ℝ) = ∑ e : Edge F, |dE F C e| := by
  simp only [abs_dE, cutSize, sum_boole]

omit [DecidableRel F.Adj] in
lemma sum_le_sum_max {ι : Type*} [Fintype ι] (R' : Finset ι) (x : ι → ℝ) :
    ∑ r ∈ R', x r ≤ ∑ r, max (x r) 0 :=
  (sum_le_sum fun _ _ ↦ le_max_left _ _).trans
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ le_max_right _ _)

/-- Summing the positive (or the negative) parts of the row sums `N(r, C)` counts the cut. -/
lemma sum_max_sgn_dE (C' : Finset (Fin n)) {t : ℝ} (ht : t = 1 ∨ t = -1) :
    ∑ r : Edge F × Bool, max (t * (sgn r.2 * dE F C' r.1)) 0 = cutSize F C' := by
  rw [cutSize_eq_sum, Fintype.sum_prod_type]
  refine sum_congr rfl fun e _ ↦ ?_
  rw [Fintype.sum_bool]
  simp only [sgn, ite_true, Bool.false_eq_true, ite_false]
  rcases ht with rfl | rfl
  · simp [max_zero_add_max_neg_zero_eq_abs_self]
  · rw [add_comm]; simp [max_zero_add_max_neg_zero_eq_abs_self]

/-- `|N(R, C)| ≤ cut(C)`. -/
lemma abs_sum_N_le (R' : Finset (Edge F × Bool)) (C' : Finset (Fin n)) :
    |∑ r ∈ R', sgn r.2 * dE F C' r.1| ≤ cutSize F C' := by
  rw [abs_le]
  constructor
  · have h := sum_le_sum_max R' fun r ↦ -1 * (sgn r.2 * dE F C' r.1)
    rw [sum_max_sgn_dE F C' (Or.inr rfl), ← mul_sum] at h
    linarith
  · have h := sum_le_sum_max R' fun r ↦ 1 * (sgn r.2 * dE F C' r.1)
    rw [sum_max_sgn_dE F C' (Or.inl rfl), ← mul_sum] at h
    linarith

/-! ### The cut norm of `A_{G'} - A_{H'}` -/

omit [DecidableRel F.Adj] in
/-- `D = A_{G'} - A_{H'}` vanishes on pairs of signed edges and on pairs of vertices, and is
symmetric. -/
lemma anD_inl_inl (r r' : Edge F × Bool) :
    (adj (anG F) - adj (anH F)) (.inl r) (.inl r') = 0 := by
  rw [Pi.sub_apply, Pi.sub_apply]
  exact sub_self 0

omit [DecidableRel F.Adj] in
lemma anD_inr_inr (c c' : Fin n) :
    (adj (anG F) - adj (anH F)) (.inr c) (.inr c') = 0 := by
  rw [Pi.sub_apply, Pi.sub_apply]
  exact sub_self 0

omit [DecidableRel F.Adj] in
/-- `D(S, T) = N(S_L, T_R) + N(T_L, S_R)`. -/
lemma sum_anD (S T : Finset ((Edge F × Bool) ⊕ Fin n)) :
    ∑ x ∈ S, ∑ y ∈ T, (adj (anG F) - adj (anH F)) x y =
      ∑ r ∈ S.toLeft, sgn r.2 * dE F T.toRight r.1 +
        ∑ r ∈ T.toLeft, sgn r.2 * dE F S.toRight r.1 := by
  conv_lhs => rw [← toLeft_disjSum_toRight (u := S)]
  rw [sum_disjSum]
  congr 1
  · rw [← sum_N]
    refine sum_congr rfl fun r _ ↦ ?_
    conv_lhs => rw [← toLeft_disjSum_toRight (u := T)]
    rw [sum_disjSum, sum_eq_zero fun r' _ ↦ anD_inl_inl F r r', zero_add]
    exact sum_congr rfl fun c _ ↦ rfl
  · rw [← sum_N, sum_comm (s := T.toLeft)]
    refine sum_congr rfl fun c _ ↦ ?_
    conv_lhs => rw [← toLeft_disjSum_toRight (u := T)]
    rw [sum_disjSum, sum_eq_zero (s := T.toRight) fun c' _ ↦ anD_inr_inr F c c', add_zero]
    refine sum_congr rfl fun r _ ↦ ?_
    simp only [Pi.sub_apply, adj, (anG F).adj_comm (Sum.inr c), (anH F).adj_comm (Sum.inr c)]

lemma cutSize_le_maxcut (C : Finset (Fin n)) : cutSize F C ≤ maxcut F :=
  le_sup (f := cutSize F) (mem_univ C)

/-- **[GG22, Theorem 23]**: `‖A_{G'} - A_{H'}‖_□ = 2 · maxcut(F)`. -/
theorem cutNorm_anG_sub_anH :
    cutNorm (adj (anG F) - adj (anH F)) = 2 * maxcut F := by
  apply le_antisymm
  · refine cutNorm_le _ fun S T ↦ ?_
    rw [sum_anD]
    have h1 := abs_sum_N_le F S.toLeft T.toRight
    have h2 := abs_sum_N_le F T.toLeft S.toRight
    have h3 : (cutSize F T.toRight : ℝ) ≤ maxcut F := by exact_mod_cast cutSize_le_maxcut F _
    have h4 : (cutSize F S.toRight : ℝ) ≤ maxcut F := by exact_mod_cast cutSize_le_maxcut F _
    exact (abs_add_le _ _).trans (by linarith)
  · obtain ⟨U, -, hU⟩ := exists_mem_eq_sup (univ : Finset (Finset (Fin n))) univ_nonempty
      (cutSize F)
    set Rp : Finset (Edge F × Bool) := {r | 0 < sgn r.2 * dE F U r.1}
    set S := Rp.disjSum U
    have hRp : ∑ r ∈ Rp, sgn r.2 * dE F U r.1 = maxcut F := by
      rw [maxcut, hU, ← sum_max_sgn_dE F U (t := 1) (Or.inl rfl), sum_filter]
      refine sum_congr rfl fun r _ ↦ ?_
      rw [one_mul]
      split_ifs with h
      · exact (max_eq_left h.le).symm
      · exact (max_eq_right (not_lt.mp h)).symm
    calc (2 * maxcut F : ℝ) =
          |∑ x ∈ S, ∑ y ∈ S, (adj (anG F) - adj (anH F)) x y| := by
          rw [sum_anD]
          simp only [S, toLeft_disjSum, toRight_disjSum, hRp]
          rw [abs_of_nonneg (by positivity)]
          ring
      _ ≤ _ := abs_sum_le_cutNorm _ _ _

end MaxCut

end GsimOT.Hardness
