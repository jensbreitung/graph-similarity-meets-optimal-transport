/-
# Lemma 22: locking markers

Paper, Appendix C, Lemma 22 (Locking Markers, pp. 20–21, l. 650–659; proof l. 660–674), for the
local edit distance (`♢ = 1`).

Let `G, H` be graphs on a common vertex set `V` with maximum degree at most `Δ`, and let
`z₁, …, z_k ∈ V` be markers ordered such that `deg_G(z₁) ≤ ⋯ ≤ deg_G(z_k)`.  Let `τ ≥ 1` and
`δ ≥ 0` be integers with `|deg_G(z_j) - deg_H(z_j)| ≤ δ` for all `j ∈ [k]`.  Obtain `G'`, `H'` by
adding the same clique `K` on `m := 2Δ + 2τ + k(τ + δ) + 1` new vertices `y₁, …, y_m` and joining
every marker `z_j` to `y₁, …, y_{Δ+τ+j(τ+δ)}`.  Then
1. every bijection `π` of `V'` with `C₁(π) < τ` (w.r.t. `(G', H')`) fixes every marker and
   satisfies `π(V) = V`;
2. if `Q ∈ DS(V, V)` with `Q(z_j, z_j) = 1` for all `j`, and `Q'` extends `Q` by the identity on
   `K`, then `C₁(Q')` w.r.t. `(G', H')` equals `C₁(Q)` w.r.t. `(G, H)`.

Formalisation notes.
* The new vertex set is `V' = V ⊕ Fin m`; the clique vertex `y_{i+1}` is `Sum.inr i`.
* Markers are indexed by `Fin k` with paper index `j = j.val + 1`.
* `Δ`, `τ`, `δ` are natural numbers; both items hold for every `τ ∈ ℕ` (for `τ = 0` the first is
  vacuous).
* The paper states the lemma for `♢ ∈ {ed, 1}`; this file formalises `♢ = 1`, and
  `GsimOT.Common.Lemma22_LockingMarkersEdit` formalises `♢ = ed`.
-/
import GsimOT.Common.Observation21_DegreeBound

open Finset

namespace GsimOT

section Lock

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Size of the added clique: `m = 2Δ + 2τ + k(τ + δ) + 1`. -/
def lockSize (k Δ τ δ : ℕ) : ℕ := 2 * Δ + 2 * τ + k * (τ + δ) + 1

/-- The staircase: vertex `v` is joined to clique vertex `y` iff `v = z_j` for some (paper) index
`j` with `y ∈ {y₁, …, y_{Δ+τ+j(τ+δ)}}`. -/
def stair {k : ℕ} (z : Fin k → V) (Δ τ δ : ℕ) {m : ℕ} (v : V) (y : Fin m) : Prop :=
  ∃ j : Fin k, z j = v ∧ y.val < Δ + τ + (j.val + 1) * (τ + δ)

instance {k : ℕ} (z : Fin k → V) (Δ τ δ : ℕ) {m : ℕ} (v : V) (y : Fin m) :
    Decidable (stair z Δ τ δ v y) := by unfold stair; infer_instance

/-- Adjacency relation of the locked graph `G'` on `V ⊕ Fin m`. -/
def lockAdj (G : SimpleGraph V) {k : ℕ} (z : Fin k → V) (Δ τ δ : ℕ) {m : ℕ} :
    V ⊕ Fin m → V ⊕ Fin m → Prop
  | .inl a, .inl b => G.Adj a b
  | .inr y, .inr y' => y ≠ y'
  | .inl a, .inr y => stair z Δ τ δ a y
  | .inr y, .inl a => stair z Δ τ δ a y

/-- The graph `G'` of Lemma 22: `G` plus a clique `K` on `m` vertices attached to the markers in a
staircase fashion. -/
def lockGraph (G : SimpleGraph V) {k : ℕ} (z : Fin k → V) (Δ τ δ : ℕ) :
    SimpleGraph (V ⊕ Fin (lockSize k Δ τ δ)) where
  Adj := lockAdj G z Δ τ δ
  symm := ⟨by
    rintro (a | a) (b | b) h <;> simp only [lockAdj] at h ⊢
    · exact h.symm
    · exact h
    · exact h
    · exact Ne.symm h⟩
  loopless := ⟨by
    rintro (a | a) h <;> simp only [lockAdj] at h
    · exact G.irrefl h
    · exact h rfl⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (z : Fin k → V) (Δ τ δ : ℕ) :
    DecidableRel (lockGraph G z Δ τ δ).Adj := fun a b =>
  match a, b with
  | .inl a, .inl b => inferInstanceAs (Decidable (G.Adj a b))
  | .inr y, .inr y' => inferInstanceAs (Decidable (y ≠ y'))
  | .inl a, .inr y => inferInstanceAs (Decidable (stair z Δ τ δ a y))
  | .inr y, .inl a => inferInstanceAs (Decidable (stair z Δ τ δ a y))

variable (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (z : Fin k → V) (Δ τ δ : ℕ)

@[simp] lemma adj_lock_inl_inl (a b : V) :
    adj (lockGraph G z Δ τ δ) (.inl a) (.inl b) = adj G a b := by
  simp only [adj]; rfl

@[simp] lemma adj_lock_inl_inr (a : V) (y : Fin (lockSize k Δ τ δ)) :
    adj (lockGraph G z Δ τ δ) (.inl a) (.inr y) = if stair z Δ τ δ a y then 1 else 0 := by
  simp only [adj]; rfl

@[simp] lemma adj_lock_inr_inl (a : V) (y : Fin (lockSize k Δ τ δ)) :
    adj (lockGraph G z Δ τ δ) (.inr y) (.inl a) = if stair z Δ τ δ a y then 1 else 0 := by
  simp only [adj]; rfl

@[simp] lemma adj_lock_inr_inr (y y' : Fin (lockSize k Δ τ δ)) :
    adj (lockGraph G z Δ τ δ) (.inr y) (.inr y') = if y ≠ y' then 1 else 0 := by
  simp only [adj]; rfl

/-! ### Degrees in the locked graph -/

lemma card_stair_marker (hz : Function.Injective z) (j : Fin k)
    (hle : Δ + τ + (j.val + 1) * (τ + δ) ≤ lockSize k Δ τ δ) :
    #{y : Fin (lockSize k Δ τ δ) | stair z Δ τ δ (z j) y} = Δ + τ + (j.val + 1) * (τ + δ) := by
  have : (Finset.univ.filter fun y : Fin (lockSize k Δ τ δ) => stair z Δ τ δ (z j) y) =
      Finset.univ.filter fun y : Fin (lockSize k Δ τ δ) => y.val < Δ + τ + (j.val + 1) * (τ + δ) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, hy⟩
      rw [hz hi] at hy; exact hy
    · intro hy; exact ⟨j, rfl, hy⟩
  rw [this, Fin.card_filter_val_lt]
  omega

lemma card_stair_nonmarker {v : V} (hv : ∀ j, z j ≠ v) :
    #{y : Fin (lockSize k Δ τ δ) | stair z Δ τ δ v y} = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro y - ⟨j, hj, -⟩
  exact hv j hj

/-- Degree of an original vertex in `G'`. -/
lemma deg_lock_inl (v : V) :
    deg (lockGraph G z Δ τ δ) (.inl v) =
      deg G v + #{y : Fin (lockSize k Δ τ δ) | stair z Δ τ δ v y} := by
  have h : ((deg (lockGraph G z Δ τ δ) (.inl v) : ℕ) : ℝ) =
      ((deg G v + #{y : Fin (lockSize k Δ τ δ) | stair z Δ τ δ v y} : ℕ) : ℝ) := by
    rw [← sum_adj_eq_deg, Fintype.sum_sum_type]
    simp only [adj_lock_inl_inl, adj_lock_inl_inr, sum_adj_eq_deg]
    push_cast
    rw [Finset.sum_boole]
  exact_mod_cast h

/-- Clique vertices have degree at least `m - 1` in `G'`. -/
lemma deg_lock_inr_ge (y : Fin (lockSize k Δ τ δ)) :
    lockSize k Δ τ δ - 1 ≤ deg (lockGraph G z Δ τ δ) (.inr y) := by
  have h : ((lockSize k Δ τ δ - 1 : ℕ) : ℝ) ≤ (deg (lockGraph G z Δ τ δ) (.inr y) : ℝ) := by
    rw [← sum_adj_eq_deg, Fintype.sum_sum_type]
    simp only [adj_lock_inr_inl, adj_lock_inr_inr]
    have h1 : 0 ≤ ∑ a : V, (if stair z Δ τ δ a y then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have h2 : ∑ y' : Fin (lockSize k Δ τ δ), (if y ≠ y' then (1 : ℝ) else 0) =
        ((lockSize k Δ τ δ - 1 : ℕ) : ℝ) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        mul_one]
      congr 1
      have : ({y' : Fin (lockSize k Δ τ δ) | y ≠ y'} : Finset _) = Finset.univ.erase y := by
        ext y'; simp [eq_comm]
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    linarith
  exact_mod_cast h

end Lock

/-! ### Lemma 22, first item -/

section Item1

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
variable {k : ℕ} {z : Fin k → V} {Δ τ δ : ℕ}

/-- **Lemma 22 (1).** Every bijection `π` of `V' = V ⊕ K` with `C₁(π) < τ` w.r.t. `(G', H')` fixes
every marker and maps `V` into `V` (hence `π(V) = V`). -/
theorem lemma22_bij (hz : Function.Injective z)
    (hmono : ∀ i j : Fin k, i ≤ j → deg G (z i) ≤ deg G (z j))
    (hΔG : ∀ v, deg G v ≤ Δ) (hΔH : ∀ v, deg H v ≤ Δ)
    (hδ : ∀ j, deg G (z j) ≤ deg H (z j) + δ ∧ deg H (z j) ≤ deg G (z j) + δ)
    (π : (V ⊕ Fin (lockSize k Δ τ δ)) ≃ (V ⊕ Fin (lockSize k Δ τ δ)))
    (hπ : costOneBij (lockGraph G z Δ τ δ) (lockGraph H z Δ τ δ) π < τ) :
    (∀ j, π (.inl (z j)) = .inl (z j)) ∧ (∀ v, ∃ v', π (.inl v) = .inl v') := by
  -- By Observation 21, `|deg_{(lockGraph G z Δ τ δ)}(a) - deg_{(lockGraph H z Δ τ δ)}(π a)| < τ` for all `a`.
  have hdeg : ∀ a, deg (lockGraph G z Δ τ δ) a < deg (lockGraph H z Δ τ δ) (π a) + τ ∧ deg (lockGraph H z Δ τ δ) (π a) < deg (lockGraph G z Δ τ δ) a + τ := by
    intro a
    have h := (observation21_bij (G := (lockGraph G z Δ τ δ)) (H := (lockGraph H z Δ τ δ)) π a).trans
      ((localCost_permMat_le_costOneBij (G := (lockGraph G z Δ τ δ)) (H := (lockGraph H z Δ τ δ)) π a)) |>.trans_lt hπ
    have h' := abs_lt.1 h
    constructor
    · have : (deg (lockGraph G z Δ τ δ) a : ℝ) < deg (lockGraph H z Δ τ δ) (π a) + τ := by linarith
      exact_mod_cast this
    · have : (deg (lockGraph H z Δ τ δ) (π a) : ℝ) < deg (lockGraph G z Δ τ δ) a + τ := by linarith
      exact_mod_cast this
  -- Degrees in `(lockGraph G z Δ τ δ)` and `(lockGraph H z Δ τ δ)`.
  have hmarkG : ∀ j : Fin k, deg (lockGraph G z Δ τ δ) (.inl (z j)) = deg G (z j) + (Δ + τ + (j.val + 1) * (τ + δ)) := by
    intro j
    rw [deg_lock_inl, card_stair_marker z Δ τ δ hz j]
    have := j.isLt
    simp only [lockSize]; nlinarith
  have hmarkH : ∀ j : Fin k, deg (lockGraph H z Δ τ δ) (.inl (z j)) = deg H (z j) + (Δ + τ + (j.val + 1) * (τ + δ)) := by
    intro j
    rw [deg_lock_inl, card_stair_marker z Δ τ δ hz j]
    have := j.isLt
    simp only [lockSize]; nlinarith
  have hnonG : ∀ v, (∀ j, z j ≠ v) → deg (lockGraph G z Δ τ δ) (.inl v) ≤ Δ := by
    intro v hv; rw [deg_lock_inl, card_stair_nonmarker z Δ τ δ hv]; simpa using hΔG v
  have hnonH : ∀ v, (∀ j, z j ≠ v) → deg (lockGraph H z Δ τ δ) (.inl v) ≤ Δ := by
    intro v hv; rw [deg_lock_inl, card_stair_nonmarker z Δ τ δ hv]; simpa using hΔH v
  have hcliqueG : ∀ y, lockSize k Δ τ δ - 1 ≤ deg (lockGraph G z Δ τ δ) (.inr y) := deg_lock_inr_ge G z Δ τ δ
  have hcliqueH : ∀ y, lockSize k Δ τ δ - 1 ≤ deg (lockGraph H z Δ τ δ) (.inr y) := deg_lock_inr_ge H z Δ τ δ
  have hm : lockSize k Δ τ δ - 1 = 2 * Δ + 2 * τ + k * (τ + δ) := by simp [lockSize]
  have hjk : ∀ j : Fin k, (j.val + 1) * (τ + δ) ≤ k * (τ + δ) :=
    fun j => Nat.mul_le_mul_right _ j.isLt
  -- Markers are fixed.
  have hfix : ∀ j, π (.inl (z j)) = .inl (z j) := by
    intro j
    obtain ⟨h1, h2⟩ := hdeg (.inl (z j))
    rw [hmarkG j] at h1 h2
    have hGj := hΔG (z j)
    have hj := hjk j
    rcases hπj : π (.inl (z j)) with b | y
    · rw [hπj] at h1 h2
      by_cases hb : ∃ i, z i = b
      · obtain ⟨i, rfl⟩ := hb
        rw [hmarkH i] at h1 h2
        rcases lt_trichotomy i j with hij | rfl | hij
        · exfalso
          have hm1 := hmono i j hij.le
          have hδi := hδ i
          have : (i.val + 1) * (τ + δ) + (τ + δ) ≤ (j.val + 1) * (τ + δ) := by
            have : i.val + 1 + 1 ≤ j.val + 1 := by
              have := Fin.lt_def.1 hij; omega
            nlinarith
          omega
        · rfl
        · exfalso
          have hm1 := hmono j i hij.le
          have hδi := hδ i
          have hδj := hδ j
          have : (j.val + 1) * (τ + δ) + (τ + δ) ≤ (i.val + 1) * (τ + δ) := by
            have : j.val + 1 + 1 ≤ i.val + 1 := by
              have := Fin.lt_def.1 hij; omega
            nlinarith
          omega
      · push Not at hb
        have := hnonH b hb
        omega
    · rw [hπj] at h1 h2
      have := hcliqueH y
      omega
  refine ⟨hfix, fun v => ?_⟩
  by_cases hv : ∃ j, z j = v
  · obtain ⟨j, rfl⟩ := hv
    exact ⟨z j, hfix j⟩
  · push Not at hv
    obtain ⟨h1, h2⟩ := hdeg (.inl v)
    have hGv := hnonG v hv
    rcases hπv : π (.inl v) with b | y
    · exact ⟨b, rfl⟩
    · rw [hπv] at h1 h2
      have := hcliqueH y
      omega

end Item1

/-! ### Lemma 22, second item -/

section Item2

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
variable {k : ℕ} {z : Fin k → V} {Δ τ δ : ℕ}

/-- The extension `Q'` of `Q ∈ DS(V, V)` by the identity on the clique `K`. -/
def extendId {m : ℕ} (Q : V → V → ℝ) : V ⊕ Fin m → V ⊕ Fin m → ℝ
  | .inl a, .inl b => Q a b
  | .inr y, .inr y' => if y = y' then 1 else 0
  | _, _ => 0

@[simp] lemma extendId_inl_inl {m : ℕ} (Q : V → V → ℝ) (a b : V) :
    extendId (m := m) Q (.inl a) (.inl b) = Q a b := rfl
@[simp] lemma extendId_inr_inr {m : ℕ} (Q : V → V → ℝ) (y y' : Fin m) :
    extendId (m := m) Q (.inr y) (.inr y') = if y = y' then 1 else 0 := rfl
@[simp] lemma extendId_inl_inr {m : ℕ} (Q : V → V → ℝ) (a : V) (y : Fin m) :
    extendId (m := m) Q (.inl a) (.inr y) = 0 := rfl
@[simp] lemma extendId_inr_inl {m : ℕ} (Q : V → V → ℝ) (a : V) (y : Fin m) :
    extendId (m := m) Q (.inr y) (.inl a) = 0 := rfl

lemma extendId_isDS {m : ℕ} {Q : V → V → ℝ} (hQ : IsDS Q) : IsDS (extendId (m := m) Q) where
  nonneg := by
    rintro (a | a) (b | b) <;> simp [hQ.nonneg, apply_ite]
  row_sum := by
    rintro (a | y) <;> simp [Fintype.sum_sum_type, hQ.row_sum]
  col_sum := by
    rintro (b | y) <;> simp [Fintype.sum_sum_type, hQ.col_sum]

/-- The extension of a permutation matrix is the permutation matrix of the extended bijection. -/
lemma extendId_permMat {m : ℕ} (σ : V ≃ V) :
    extendId (m := m) (permMat σ) = permMat (σ.sumCongr (Equiv.refl (Fin m))) := by
  funext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [permMat, extendId]

/-- If `Q(z_j, z_j) = 1`, then `z_j` is the only partner of `z_j` in `supp(Q)` (row version). -/
lemma eq_of_marker_row {Q : V → V → ℝ} (hQ : IsDS Q) {a b : V} (ha : Q a a = 1)
    (hab : Q a b ≠ 0) : b = a := by
  by_contra hne
  have h := hQ.row_sum a
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ha] at h
  have h0 : ∑ x ∈ Finset.univ.erase a, Q a x = 0 := by linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hQ.nonneg a x)).1 h0 b
    (Finset.mem_erase.2 ⟨hne, Finset.mem_univ b⟩)
  exact hab this

/-- Column version of `eq_of_marker_row`. -/
lemma eq_of_marker_col {Q : V → V → ℝ} (hQ : IsDS Q) {a b : V} (hb : Q b b = 1)
    (hab : Q a b ≠ 0) : a = b := by
  by_contra hne
  have h := hQ.col_sum b
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), hb] at h
  have h0 : ∑ x ∈ Finset.univ.erase b, Q x b = 0 := by linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hQ.nonneg x b)).1 h0 a
    (Finset.mem_erase.2 ⟨hne, Finset.mem_univ a⟩)
  exact hab this

/-- Supported pairs have the same neighbours in `K`. -/
lemma stair_iff_of_supp {Q : V → V → ℝ} (hQ : IsDS Q) (hz1 : ∀ j, Q (z j) (z j) = 1)
    {a b : V} (hab : Q a b ≠ 0) {m : ℕ} (y : Fin m) :
    stair z Δ τ δ a y ↔ stair z Δ τ δ b y := by
  constructor
  · rintro ⟨j, rfl, hy⟩
    exact ⟨j, (eq_of_marker_row hQ (hz1 j) hab).symm, hy⟩
  · rintro ⟨j, rfl, hy⟩
    exact ⟨j, eq_of_marker_col hQ (hz1 j) hab |>.symm, hy⟩

lemma localCost_extendId_inl {Q : V → V → ℝ} (hQ : IsDS Q) (hz1 : ∀ j, Q (z j) (z j) = 1)
    {a b : V} (hab : Q a b ≠ 0) :
    localCost (lockGraph G z Δ τ δ) (lockGraph H z Δ τ δ) (extendId Q) (.inl a) (.inl b) =
      localCost G H Q a b := by
  unfold localCost disc
  simp only [Fintype.sum_sum_type, adj_lock_inl_inl, extendId_inl_inl, adj_lock_inl_inr,
    extendId_inl_inr, mul_zero, Finset.sum_const_zero, add_zero, extendId_inr_inl,
    extendId_inr_inr, zero_add]
  simp [stair_iff_of_supp hQ hz1 hab]

lemma localCost_extendId_inr {Q : V → V → ℝ} (hQ : IsDS Q) (hz1 : ∀ j, Q (z j) (z j) = 1)
    (y : Fin (lockSize k Δ τ δ)) :
    localCost (lockGraph G z Δ τ δ) (lockGraph H z Δ τ δ) (extendId Q) (.inr y) (.inr y) = 0 := by
  unfold localCost disc
  simp only [Fintype.sum_sum_type, adj_lock_inr_inl, extendId_inl_inl, adj_lock_inr_inr,
    extendId_inl_inr, mul_zero, Finset.sum_const_zero, add_zero, extendId_inr_inl,
    extendId_inr_inr, zero_add]
  have h1 : ∀ a b, |(if stair z Δ τ δ a y then (1 : ℝ) else 0) -
      (if stair z Δ τ δ b y then 1 else 0)| * Q a b = 0 := by
    intro a b
    by_cases hab : Q a b = 0
    · simp [hab]
    · simp [stair_iff_of_supp hQ hz1 hab y]
  have h2 : ∀ x x' : Fin (lockSize k Δ τ δ), |(if y ≠ x then (1 : ℝ) else 0) -
      (if y ≠ x' then 1 else 0)| * (if x = x' then 1 else 0) = 0 := by
    intro x x'
    by_cases h : x = x' <;> simp [h]
  simp only [h1, h2, Finset.sum_const_zero, add_zero]

/-- **Lemma 22 (2).** If `Q ∈ DS(V, V)` fixes all markers (`Q(z_j, z_j) = 1`) and `Q'` extends `Q`
by the identity on `K`, then `C₁(Q')` w.r.t. `(G', H')` equals `C₁(Q)` w.r.t. `(G, H)`. -/
theorem lemma22_cost {Q : V → V → ℝ} (hQ : IsDS Q) (hz1 : ∀ j, Q (z j) (z j) = 1) :
    costOne (lockGraph G z Δ τ δ) (lockGraph H z Δ τ δ) (extendId Q) = costOne G H Q := by
  apply le_antisymm
  · refine costOne_le (costOne_nonneg hQ.nonneg) ?_
    rintro (a | y) (b | y') h
    · rw [localCost_extendId_inl hQ hz1 h]
      exact localCost_le_costOne h
    · exact absurd rfl h
    · exact absurd rfl h
    · have : y = y' := by by_contra hne; simp [hne] at h
      subst this
      rw [localCost_extendId_inr hQ hz1]
      exact costOne_nonneg hQ.nonneg
  · refine costOne_le (costOne_nonneg (extendId_isDS hQ).nonneg) fun a b h => ?_
    rw [← localCost_extendId_inl (G := G) (H := H) (Δ := Δ) (τ := τ) (δ := δ) hQ hz1 h]
    exact localCost_le_costOne (by simpa using h)

end Item2

end GsimOT
