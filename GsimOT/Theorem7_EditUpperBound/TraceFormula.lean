/-
# Eq. (17): the edit cost in terms of Frobenius norms

Paper, App. C.2, Eq. (17) (p. 24, l. 762–765): for every `R ∈ DS(V, W)`,
`C_ed(R) = ‖A_G‖²_F + ‖A_H‖²_F - 2⟨A_G R, R A_H⟩_F`. It holds because `|a - b| = a² + b² - 2ab`
for `a, b ∈ {0, 1}` and because the row and column sums of `R` are `1`.

We also prove the facts about the Frobenius inner product and the products `A_G R`, `R A_H` that
the proof of Theorem 6 uses:
* for a bijection `π`, `C_ed(π) = ‖A_G - P_π A_H P_πᵀ‖²_F` (the first step of the chain, l. 767) and
  `‖A_G - P_π A_H P_πᵀ‖_F = ‖A_G P_π - P_π A_H‖_F` (step (a));
* `‖A_G P_π‖_F = ‖A_G‖_F` and `‖P_π A_H‖_F = ‖A_H‖_F` (permutation invariance, step (g));
* `R ↦ A_G R` and `R ↦ R A_H` are linear, and so is `⟨·, ·⟩_F` in each argument (steps (d), (g));
* `‖X - Y‖²_F = ‖X‖²_F + ‖Y‖²_F - 2⟨X, Y⟩_F` (steps (c), (f)) and the squared triangle
  inequality `‖X + Y‖²_F ≤ 2‖X‖²_F + 2‖Y‖²_F` (step (b)).

Formalisation notes.
* Matrices are functions `V → W → ℝ`, as in `GsimOT.Common.Basic`, with the pointwise `+` and `-`:
  `adjMul G R` is `A_G R`, `mulAdj H R` is `R A_H`, `conjMul H R` is `R A_H Rᵀ` and `frob X Y` is
  `⟨X, Y⟩_F`, so `‖X‖²_F = frob X X`.
-/
import GsimOT.Common.EditDistance

open Finset

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-! ### The Frobenius inner product -/

section Frobenius

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The Frobenius inner product `⟨X, Y⟩_F = ∑_{a,b} X(a,b) Y(a,b)`. -/
def frob (X Y : α → β → ℝ) : ℝ :=
  ∑ a, ∑ b, X a b * Y a b

lemma frob_comm (X Y : α → β → ℝ) : frob X Y = frob Y X := by
  simp only [frob, mul_comm]

/-- Expanding a square: `‖X - Y‖²_F = ‖X‖²_F + ‖Y‖²_F - 2⟨X, Y⟩_F`. -/
lemma frob_sub_self (X Y : α → β → ℝ) :
    frob (X - Y) (X - Y) = frob X X + frob Y Y - 2 * frob X Y := by
  simp only [frob, Pi.sub_apply, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-- The squared triangle inequality `‖X + Y‖²_F ≤ 2‖X‖²_F + 2‖Y‖²_F`. -/
lemma frob_add_self_le (X Y : α → β → ℝ) :
    frob (X + Y) (X + Y) ≤ 2 * frob X X + 2 * frob Y Y := by
  simp only [frob, Pi.add_apply, mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun a _ => sum_le_sum fun b _ => by nlinarith [sq_nonneg (X a b - Y a b)]

/-- Linearity in the first argument: if `X = ∑ᵢ λᵢ Xᵢ`, then `⟨X, Y⟩_F = ∑ᵢ λᵢ ⟨Xᵢ, Y⟩_F`. -/
lemma frob_eq_sum_left {ι : Type*} [Fintype ι] (wt : ι → ℝ) (Xs : ι → α → β → ℝ)
    {X : α → β → ℝ} (hX : ∀ a b, X a b = ∑ i, wt i * Xs i a b) (Y : α → β → ℝ) :
    frob X Y = ∑ i, wt i * frob (Xs i) Y := by
  have h : ∀ a b, X a b * Y a b = ∑ i, wt i * (Xs i a b * Y a b) := fun a b => by
    rw [hX, sum_mul]
    exact sum_congr rfl fun i _ => by ring
  simp only [frob, h, mul_sum]
  calc ∑ a, ∑ b, ∑ i, wt i * (Xs i a b * Y a b)
      = ∑ a, ∑ i, ∑ b, wt i * (Xs i a b * Y a b) := sum_congr rfl fun a _ => sum_comm
    _ = ∑ i, ∑ a, ∑ b, wt i * (Xs i a b * Y a b) := sum_comm

/-- Linearity in the second argument: if `Y = ∑ᵢ λᵢ Yᵢ`, then `⟨X, Y⟩_F = ∑ᵢ λᵢ ⟨X, Yᵢ⟩_F`. -/
lemma frob_eq_sum_right {ι : Type*} [Fintype ι] (wt : ι → ℝ) (X : α → β → ℝ)
    (Ys : ι → α → β → ℝ) {Y : α → β → ℝ} (hY : ∀ a b, Y a b = ∑ i, wt i * Ys i a b) :
    frob X Y = ∑ i, wt i * frob X (Ys i) := by
  rw [frob_comm, frob_eq_sum_left wt Ys hY X]
  simp only [frob_comm]

end Frobenius

/-! ### The products `A_G R`, `R A_H` and `R A_H Rᵀ` -/

section Products

variable (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The matrix product `A_G R`, i.e. `(A_G R)(v, w') = ∑_{v'} A_G(v, v') R(v', w')`. -/
def adjMul (R : V → W → ℝ) (v : V) (w' : W) : ℝ := ∑ v', adj G v v' * R v' w'

/-- The matrix product `R A_H`, i.e. `(R A_H)(v, w') = ∑_w R(v, w) A_H(w, w')`. -/
def mulAdj (R : V → W → ℝ) (v : V) (w' : W) : ℝ := ∑ w, R v w * adj H w w'

/-- The matrix product `R A_H Rᵀ`, i.e.
`(R A_H Rᵀ)(v, v') = ∑_{w,w'} R(v, w) A_H(w, w') R(v', w')`. -/
def conjMul (R : V → W → ℝ) (v v' : V) : ℝ := ∑ w, ∑ w', R v w * adj H w w' * R v' w'

variable {G H}

/-- `A_G P_π` is `A_G` with permuted columns: `(A_G P_π)(v, w') = A_G(v, π⁻¹ w')`. -/
lemma adjMul_permMat (π : V ≃ W) (v : V) (w' : W) :
    adjMul G (permMat π) v w' = adj G v (π.symm w') := by
  unfold adjMul
  rw [Fintype.sum_eq_single (π.symm w') fun v' hv' => by
    simp [permMat, show π v' ≠ w' from fun h => hv' (by simp [← h])]]
  simp [permMat]

/-- `P_π A_H` is `A_H` with permuted rows: `(P_π A_H)(v, w') = A_H(π v, w')`. -/
lemma mulAdj_permMat (π : V ≃ W) (v : V) (w' : W) :
    mulAdj H (permMat π) v w' = adj H (π v) w' := by
  unfold mulAdj
  rw [Fintype.sum_eq_single (π v) fun w hw => by simp [permMat, Ne.symm hw]]
  simp [permMat]

/-- `P_π A_H P_πᵀ` is `A_H` pulled back along `π`: `(P_π A_H P_πᵀ)(v, v') = A_H(π v, π v')`. -/
lemma conjMul_permMat (π : V ≃ W) (v v' : V) :
    conjMul H (permMat π) v v' = adj H (π v) (π v') := by
  unfold conjMul
  rw [Fintype.sum_eq_single (π v) fun w hw => by simp [permMat, Ne.symm hw]]
  rw [Fintype.sum_eq_single (π v') fun w' hw' => by simp [permMat, Ne.symm hw']]
  simp [permMat]

/-- Permutation invariance of the Frobenius norm: `‖A_G P_π‖_F = ‖A_G‖_F`. -/
lemma frob_adjMul_permMat (π : V ≃ W) :
    frob (adjMul G (permMat π)) (adjMul G (permMat π)) = frob (adj G) (adj G) := by
  simp only [frob, adjMul_permMat]
  exact sum_congr rfl fun v _ => Equiv.sum_comp π.symm fun v' => adj G v v' * adj G v v'

/-- Permutation invariance of the Frobenius norm: `‖P_π A_H‖_F = ‖A_H‖_F`. -/
lemma frob_mulAdj_permMat (π : V ≃ W) :
    frob (mulAdj H (permMat π)) (mulAdj H (permMat π)) = frob (adj H) (adj H) := by
  simp only [frob, mulAdj_permMat]
  exact Equiv.sum_comp π fun w => ∑ w', adj H w w' * adj H w w'

/-- Linearity: if `Q = ∑ᵢ λᵢ Rᵢ`, then `A_G Q = ∑ᵢ λᵢ A_G Rᵢ`. -/
lemma adjMul_eq_sum {ι : Type*} [Fintype ι] (wt : ι → ℝ) (R : ι → V → W → ℝ)
    {Q : V → W → ℝ} (hQ : ∀ v w, Q v w = ∑ i, wt i * R i v w) (v : V) (w' : W) :
    adjMul G Q v w' = ∑ i, wt i * adjMul G (R i) v w' := by
  simp only [adjMul, hQ, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun v' _ => by ring

/-- Linearity: if `Q = ∑ᵢ λᵢ Rᵢ`, then `Q A_H = ∑ᵢ λᵢ Rᵢ A_H`. -/
lemma mulAdj_eq_sum {ι : Type*} [Fintype ι] (wt : ι → ℝ) (R : ι → V → W → ℝ)
    {Q : V → W → ℝ} (hQ : ∀ v w, Q v w = ∑ i, wt i * R i v w) (v : V) (w' : W) :
    mulAdj H Q v w' = ∑ i, wt i * mulAdj H (R i) v w' := by
  simp only [mulAdj, hQ, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun w _ => by ring

/-- The first step of the proof of Theorem 6 (p. 24, l. 767): as the entries of `A_G` and `A_H`
are in `{0, 1}`, `C_ed(π) = ‖A_G - P_π A_H P_πᵀ‖²_F`. -/
lemma costEditBij_eq_frob_conjMul (π : V ≃ W) :
    costEditBij G H π =
      frob (adj G - conjMul H (permMat π)) (adj G - conjMul H (permMat π)) := by
  rw [costEditBij_eq]
  simp only [frob, Pi.sub_apply, conjMul_permMat]
  refine sum_congr rfl fun v _ => sum_congr rfl fun v' _ => ?_
  rcases adj_eq_zero_or_one G v v' with h | h <;>
    rcases adj_eq_zero_or_one H (π v) (π v') with h' | h' <;> rw [h, h'] <;> norm_num

/-- Step (a) of the proof of Theorem 6 (permutation invariance of `‖·‖_F`):
`‖A_G - P_π A_H P_πᵀ‖_F = ‖A_G P_π - P_π A_H‖_F`. -/
lemma frob_conjMul_eq (π : V ≃ W) :
    frob (adj G - conjMul H (permMat π)) (adj G - conjMul H (permMat π)) =
      frob (adjMul G (permMat π) - mulAdj H (permMat π))
        (adjMul G (permMat π) - mulAdj H (permMat π)) := by
  simp only [frob, Pi.sub_apply, conjMul_permMat, adjMul_permMat, mulAdj_permMat]
  refine sum_congr rfl fun v _ => ?_
  rw [← Equiv.sum_comp π]
  simp

end Products

/-! ### Eq. (17) -/

section Eq20

variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- `|a - b| = a² + b² - 2ab` for the entries `a` of `A_G` and `b` of `A_H`, as both are in
`{0, 1}`. -/
lemma abs_disc_eq (v : V) (w : W) (v' : V) (w' : W) :
    |disc G H v w v' w'| =
      adj G v v' * adj G v v' + adj H w w' * adj H w w' - 2 * (adj G v v' * adj H w w') := by
  unfold disc
  rcases adj_eq_zero_or_one G v v' with h | h <;> rcases adj_eq_zero_or_one H w w' with h' | h' <;>
    rw [h, h'] <;> norm_num

/-- **Eq. (17)** (p. 24, l. 765). For every `R ∈ DS(V, W)`,
`C_ed(R) = ‖A_G‖²_F + ‖A_H‖²_F - 2⟨A_G R, R A_H⟩_F`. -/
theorem costEdit_eq_frob {R : V → W → ℝ} (hR : IsDS R) :
    costEdit G H R = frob (adj G) (adj G) + frob (adj H) (adj H) -
      2 * frob (adjMul G R) (mulAdj H R) := by
  -- expand `|a - b| = a² + b² - 2ab` in every term
  have hsplit : costEdit G H R =
      (∑ v, ∑ w, ∑ v', ∑ w', adj G v v' * adj G v v' * R v w * R v' w') +
      (∑ v, ∑ w, ∑ v', ∑ w', adj H w w' * adj H w w' * R v w * R v' w') -
      2 * ∑ v, ∑ w, ∑ v', ∑ w', adj G v v' * adj H w w' * R v w * R v' w' := by
    unfold costEdit
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun v _ => ?_
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun w _ => ?_
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun v' _ => ?_
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun w' _ => ?_
    rw [abs_disc_eq]
    ring
  -- the row sums of `R` reduce the first term to `‖A_G‖²_F`
  have hG : (∑ v, ∑ w, ∑ v', ∑ w', adj G v v' * adj G v v' * R v w * R v' w') =
      frob (adj G) (adj G) := by
    simp only [frob, ← mul_sum, ← sum_mul, hR.row_sum, mul_one]
  -- the column sums of `R` reduce the second term to `‖A_H‖²_F`
  have hH : (∑ v, ∑ w, ∑ v', ∑ w', adj H w w' * adj H w w' * R v w * R v' w') =
      frob (adj H) (adj H) := by
    have h : ∀ v w, ∑ v', ∑ w', adj H w w' * adj H w w' * R v w * R v' w' =
        (∑ w', adj H w w' * adj H w w') * R v w := by
      intro v w
      rw [sum_comm]
      simp only [← mul_sum, hR.col_sum, mul_one, ← sum_mul]
    simp only [h]
    rw [sum_comm]
    simp only [frob, ← mul_sum, hR.col_sum, mul_one]
  -- the mixed term is `⟨A_G R, R A_H⟩_F`
  have hGH : (∑ v, ∑ w, ∑ v', ∑ w', adj G v v' * adj H w w' * R v w * R v' w') =
      frob (adjMul G R) (mulAdj H R) := by
    simp only [frob, adjMul, mulAdj, sum_mul_sum]
    refine sum_congr rfl fun v _ => ?_
    calc ∑ w, ∑ v', ∑ w', adj G v v' * adj H w w' * R v w * R v' w'
        = ∑ v', ∑ w, ∑ w', adj G v v' * adj H w w' * R v w * R v' w' := sum_comm
      _ = ∑ v', ∑ w', ∑ w, adj G v v' * adj H w w' * R v w * R v' w' :=
          sum_congr rfl fun v' _ => sum_comm
      _ = ∑ w', ∑ v', ∑ w, adj G v v' * adj H w w' * R v w * R v' w' := sum_comm
      _ = ∑ w', ∑ v', ∑ w, adj G v v' * R v' w' * (R v w * adj H w w') :=
          sum_congr rfl fun w' _ => sum_congr rfl fun v' _ => sum_congr rfl fun w _ => by ring
  rw [hsplit, hG, hH, hGH]

end Eq20

end GsimOT
