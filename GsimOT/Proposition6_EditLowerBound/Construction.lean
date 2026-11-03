/-
# The graphs `G` and `H` of Proposition 5

Paper, App. C.1, pp. 21–22, l. 677–694, and Figures 1 and 4 (pp. 6, 22).

Fix an odd `N ≥ 3`.  The graphs `G'` and `H'` share the markers `M = {z₀, …, z_{N-1}}`.  The core
of `G'` is `S_G = {v₀, v₂, …, v_{2N-2}}` and the core of `H'` is `S_H = {w₁, w₃, …, w_{2N-1}}`; the
index of a core vertex is its position on the cycle `ℤ_{2N}`.  In each graph, distinct core
vertices are adjacent iff their positions sum to `0` modulo `2N`, and the marker `z_r` is adjacent
to the core vertices on the semicircle `I_r = {(r + s) mod 2N | s ∈ {0, …, N - 1}}`.  Finally `G`
and `H` are obtained from `G'` and `H'` by Lemma 22 (Locking Markers), identifying `v_i` of `G'`
with `w_{i+1}` of `H'`, with the markers ordered nondecreasingly by their degree in `G'` and
`Δ := N + 1`, `τ := 4N - 1`, `δ := 1` (l. 688–691).

Formalisation notes.
* The common vertex set of `G'` and `H'` is `Base N = Fin N ⊕ Fin N`: `Sum.inl c` is the core
  vertex `v_{2c}` of `G'` and the core vertex `w_{2c+1}` of `H'` (the identification
  `v_i ↔ w_{i+1}`), and `Sum.inr r` is the marker `z_r`.  `posG c = 2c` and `posH c = 2c + 1` are
  the positions, and `ℤ_{2N}` is represented by `{0, …, 2N - 1}`.
* `G'` and `H'` are both instances of `coreGraph N pos`, which places the core vertex `c` at
  `pos c`.
* For odd `N`, the core edges are the pairs `{c, c'}` with `c + c' = N` in `G'` (`adj_Gp_inl_inl`)
  and with `c + c' + 1 = N`, `c ≠ c'` in `H'` (`adj_Hp_inl_inl`).  The isolated core vertices are
  `v₀` (`c = 0`) and `w_N` (`2c + 1 = N`).
-/
import GsimOT.Common.Lemma27_LockingMarkersEdit

open Finset

namespace GsimOT.Prop6

variable {N : ℕ}

/-! ### Positions, semicircles and the graphs `G'`, `H'` -/

/-- The common vertex set of `G'` and `H'`: core vertices `Sum.inl c` and markers `Sum.inr r`. -/
abbrev Base (N : ℕ) : Type := Fin N ⊕ Fin N

/-- The semicircle `I_r = {(r + s) mod 2N | s ∈ {0, …, N - 1}} ⊆ ℤ_{2N}`. -/
def semicircle (N r : ℕ) : Finset ℕ := (range N).image fun s => (r + s) % (2 * N)

/-- For `r < N` there is no wrap-around: `x ∈ I_r ↔ r ≤ x < r + N`. -/
lemma mem_semicircle {r x : ℕ} (hr : r < N) : x ∈ semicircle N r ↔ r ≤ x ∧ x < r + N := by
  simp only [semicircle, mem_image, mem_range]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨x - r, by omega, by rw [Nat.mod_eq_of_lt (by omega)]; omega⟩

/-- The position `2c` of the core vertex `v_{2c}` of `G'`. -/
def posG (c : Fin N) : ℕ := 2 * c.val

/-- The position `2c + 1` of the core vertex `w_{2c+1}` of `H'`. -/
def posH (c : Fin N) : ℕ := 2 * c.val + 1

/-- Adjacency in `coreGraph N pos`. -/
def coreAdj (N : ℕ) (pos : Fin N → ℕ) : Base N → Base N → Prop
  | .inl c, .inl c' => c ≠ c' ∧ (pos c + pos c') % (2 * N) = 0
  | .inl c, .inr r => pos c ∈ semicircle N r
  | .inr r, .inl c => pos c ∈ semicircle N r
  | .inr _, .inr _ => False

/-- The graph with the core vertex `c` at position `pos c` and the markers `z_r`: distinct core
vertices are adjacent iff their positions sum to `0` modulo `2N`, and `z_r` is adjacent to the core
vertices on the semicircle `I_r`. -/
def coreGraph (N : ℕ) (pos : Fin N → ℕ) : SimpleGraph (Base N) where
  Adj := coreAdj N pos
  symm := ⟨by
    rintro (c | r) (c' | r') h <;> simp only [coreAdj] at h ⊢
    · exact ⟨Ne.symm h.1, by rw [add_comm]; exact h.2⟩
    · exact h
    · exact h⟩
  loopless := ⟨by
    rintro (c | r) h <;> simp only [coreAdj] at h
    exact h.1 rfl⟩

instance (pos : Fin N → ℕ) : DecidableRel (coreGraph N pos).Adj := fun a b =>
  match a, b with
  | .inl c, .inl c' => inferInstanceAs (Decidable (c ≠ c' ∧ (pos c + pos c') % (2 * N) = 0))
  | .inl c, .inr r => inferInstanceAs (Decidable (pos c ∈ semicircle N r))
  | .inr r, .inl c => inferInstanceAs (Decidable (pos c ∈ semicircle N r))
  | .inr _, .inr _ => inferInstanceAs (Decidable False)

/-- **The graph `G'`** of App. C.1 (before locking): the core vertex `v_{2c}` at position
`2c`. -/
def Gp (N : ℕ) : SimpleGraph (Base N) := coreGraph N posG

/-- **The graph `H'`** of App. C.1 (before locking): the core vertex `w_{2c+1}` at position
`2c + 1`. -/
def Hp (N : ℕ) : SimpleGraph (Base N) := coreGraph N posH

instance : DecidableRel (Gp N).Adj := inferInstanceAs (DecidableRel (coreGraph N posG).Adj)
instance : DecidableRel (Hp N).Adj := inferInstanceAs (DecidableRel (coreGraph N posH).Adj)

/-! ### Adjacency -/

/-- For `s < 2N`: `s ≡ 0 (mod N)` iff `s ∈ {0, N}`. -/
lemma mod_eq_zero_iff_of_lt {s : ℕ} (hs : s < 2 * N) : s % N = 0 ↔ s = 0 ∨ s = N := by
  rcases lt_or_ge s N with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega

/-- The core edges of `G'`: for odd `N`, `{v_{2c}, v_{2c'}}` is an edge iff `c + c' = N`. -/
lemma Gp_adj_inl_inl (hN : Odd N) (c c' : Fin N) :
    (Gp N).Adj (.inl c) (.inl c') ↔ c.val + c'.val = N := by
  have h2 : posG c + posG c' = 2 * (c.val + c'.val) := by simp only [posG]; ring
  have hmod := mod_eq_zero_iff_of_lt (N := N) (s := c.val + c'.val) (by omega)
  have hne : c ≠ c' ↔ c.val ≠ c'.val := Fin.val_ne_iff.symm
  obtain ⟨m, rfl⟩ := hN
  change c ≠ c' ∧ (posG c + posG c') % (2 * (2 * m + 1)) = 0 ↔ _
  rw [h2, Nat.mul_mod_mul_left]
  omega

/-- The core edges of `H'`: `{w_{2c+1}, w_{2c'+1}}` is an edge iff `c + c' + 1 = N` and `c ≠ c'`. -/
lemma Hp_adj_inl_inl (c c' : Fin N) :
    (Hp N).Adj (.inl c) (.inl c') ↔ c.val + c'.val + 1 = N ∧ c ≠ c' := by
  have h2 : posH c + posH c' = 2 * (c.val + c'.val + 1) := by simp only [posH]; ring
  have hmod := mod_eq_zero_iff_of_lt (N := N) (s := c.val + c'.val + 1) (by omega)
  change c ≠ c' ∧ (posH c + posH c') % (2 * N) = 0 ↔ _
  rw [h2, Nat.mul_mod_mul_left]
  omega

lemma Gp_adj_inl_inr (c r : Fin N) :
    (Gp N).Adj (.inl c) (.inr r) ↔ r.val ≤ 2 * c.val ∧ 2 * c.val < r.val + N :=
  mem_semicircle r.isLt

lemma Gp_adj_inr_inl (r c : Fin N) :
    (Gp N).Adj (.inr r) (.inl c) ↔ r.val ≤ 2 * c.val ∧ 2 * c.val < r.val + N :=
  mem_semicircle r.isLt

lemma Hp_adj_inl_inr (c r : Fin N) :
    (Hp N).Adj (.inl c) (.inr r) ↔ r.val ≤ 2 * c.val + 1 ∧ 2 * c.val + 1 < r.val + N :=
  mem_semicircle r.isLt

lemma Hp_adj_inr_inl (r c : Fin N) :
    (Hp N).Adj (.inr r) (.inl c) ↔ r.val ≤ 2 * c.val + 1 ∧ 2 * c.val + 1 < r.val + N :=
  mem_semicircle r.isLt

lemma Gp_not_adj_inr_inr (r r' : Fin N) : ¬ (Gp N).Adj (.inr r) (.inr r') := id

lemma Hp_not_adj_inr_inr (r r' : Fin N) : ¬ (Hp N).Adj (.inr r) (.inr r') := id

lemma adj_Gp_inl_inl (hN : Odd N) (c c' : Fin N) :
    adj (Gp N) (.inl c) (.inl c') = if c.val + c'.val = N then 1 else 0 :=
  if_congr (Gp_adj_inl_inl hN c c') rfl rfl

lemma adj_Hp_inl_inl (c c' : Fin N) :
    adj (Hp N) (.inl c) (.inl c') = if c.val + c'.val + 1 = N ∧ c ≠ c' then 1 else 0 :=
  if_congr (Hp_adj_inl_inl c c') rfl rfl

lemma adj_Gp_inl_inr (c r : Fin N) :
    adj (Gp N) (.inl c) (.inr r) = if r.val ≤ 2 * c.val ∧ 2 * c.val < r.val + N then 1 else 0 :=
  if_congr (Gp_adj_inl_inr c r) rfl rfl

lemma adj_Gp_inr_inl (r c : Fin N) :
    adj (Gp N) (.inr r) (.inl c) = if r.val ≤ 2 * c.val ∧ 2 * c.val < r.val + N then 1 else 0 :=
  if_congr (Gp_adj_inr_inl r c) rfl rfl

lemma adj_Hp_inl_inr (c r : Fin N) :
    adj (Hp N) (.inl c) (.inr r) =
      if r.val ≤ 2 * c.val + 1 ∧ 2 * c.val + 1 < r.val + N then 1 else 0 :=
  if_congr (Hp_adj_inl_inr c r) rfl rfl

lemma adj_Hp_inr_inl (r c : Fin N) :
    adj (Hp N) (.inr r) (.inl c) =
      if r.val ≤ 2 * c.val + 1 ∧ 2 * c.val + 1 < r.val + N then 1 else 0 :=
  if_congr (Hp_adj_inr_inl r c) rfl rfl

lemma adj_Gp_inr_inr (r r' : Fin N) : adj (Gp N) (.inr r) (.inr r') = 0 := rfl

lemma adj_Hp_inr_inr (r r' : Fin N) : adj (Hp N) (.inr r) (.inr r') = 0 := rfl

/-! ### Degrees -/

/-- Counting indices of core vertices (or markers) with a given property. -/
lemma sum_fin_ite_eq_card (p : ℕ → Prop) [DecidablePred p] :
    ∑ c : Fin N, (if p c.val then 1 else 0 : ℕ) = #{c ∈ range N | p c} := by
  rw [Fin.sum_univ_eq_sum_range (fun c => if p c then 1 else 0) N, sum_boole, Nat.cast_id]

/-- The degree of a vertex of a graph on `Base N`, split into core and marker neighbours. -/
lemma deg_eq_sum (G : SimpleGraph (Base N)) [DecidableRel G.Adj] (v : Base N) :
    deg G v = ∑ c : Fin N, (if G.Adj v (.inl c) then 1 else 0) +
      ∑ r : Fin N, (if G.Adj v (.inr r) then 1 else 0) := by
  rw [deg, card_filter, Fintype.sum_sum_type]

/-- The degree of the marker `z_r` in `G'`. -/
lemma deg_Gp_inr (r : Fin N) : deg (Gp N) (.inr r) = (r.val + N + 1) / 2 - (r.val + 1) / 2 := by
  have hr := r.isLt
  rw [deg_eq_sum]
  simp only [Gp_adj_inr_inl, Gp_not_adj_inr_inr, ite_false, sum_const_zero, add_zero]
  rw [sum_fin_ite_eq_card (fun c => r.val ≤ 2 * c ∧ 2 * c < r.val + N)]
  have : {c ∈ range N | r.val ≤ 2 * c ∧ 2 * c < r.val + N} =
      Ico ((r.val + 1) / 2) ((r.val + N + 1) / 2) := by
    ext c; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico]

/-- The degree of the marker `z_r` in `H'`. -/
lemma deg_Hp_inr (r : Fin N) : deg (Hp N) (.inr r) = (r.val + N) / 2 - r.val / 2 := by
  have hr := r.isLt
  rw [deg_eq_sum]
  simp only [Hp_adj_inr_inl, Hp_not_adj_inr_inr, ite_false, sum_const_zero, add_zero]
  rw [sum_fin_ite_eq_card (fun c => r.val ≤ 2 * c + 1 ∧ 2 * c + 1 < r.val + N)]
  have : {c ∈ range N | r.val ≤ 2 * c + 1 ∧ 2 * c + 1 < r.val + N} =
      Ico (r.val / 2) ((r.val + N) / 2) := by
    ext c; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico]

/-- At most `N` markers. -/
lemma sum_marker_le (p : Fin N → Prop) [DecidablePred p] :
    ∑ r : Fin N, (if p r then 1 else 0 : ℕ) ≤ N := by
  calc ∑ r : Fin N, (if p r then 1 else 0 : ℕ) ≤ ∑ _r : Fin N, 1 :=
        sum_le_sum fun r _ => by split_ifs <;> norm_num
    _ = N := by simp

/-- Every vertex of `G'` has degree at most `Δ = N + 1`. -/
lemma deg_Gp_le (hN : Odd N) (v : Base N) : deg (Gp N) v ≤ N + 1 := by
  rcases v with c | r
  · rw [deg_eq_sum]
    have hcore : ∑ c' : Fin N, (if (Gp N).Adj (.inl c) (.inl c') then 1 else 0 : ℕ) ≤ 1 := by
      simp only [Gp_adj_inl_inl hN, sum_boole, Nat.cast_id]
      exact card_le_one.2 fun a ha b hb => by
        simp only [mem_filter, mem_univ, true_and] at ha hb
        exact Fin.ext (by omega)
    have := sum_marker_le (fun r => (Gp N).Adj (.inl c) (.inr r))
    omega
  · rw [deg_Gp_inr]; omega

/-- Every vertex of `H'` has degree at most `Δ = N + 1`. -/
lemma deg_Hp_le (v : Base N) : deg (Hp N) v ≤ N + 1 := by
  rcases v with c | r
  · rw [deg_eq_sum]
    have hcore : ∑ c' : Fin N, (if (Hp N).Adj (.inl c) (.inl c') then 1 else 0 : ℕ) ≤ 1 := by
      simp only [Hp_adj_inl_inl, sum_boole, Nat.cast_id]
      exact card_le_one.2 fun a ha b hb => by
        simp only [mem_filter, mem_univ, true_and] at ha hb
        exact Fin.ext (by omega)
    have := sum_marker_le (fun r => (Hp N).Adj (.inl c) (.inr r))
    omega
  · rw [deg_Hp_inr]; omega

/-! ### The markers in the order of Lemma 22 and the graphs `G`, `H` -/

/-- The degree of the marker `z_r` in `G'`. -/
def markerDeg (N : ℕ) (r : Fin N) : ℕ := deg (Gp N) (.inr r)

/-- The markers `z_r`, enumerated nondecreasingly by their degree in `G'`. -/
def markerEnum (N : ℕ) (j : Fin N) : Base N := .inr (Tuple.sort (markerDeg N) j)

lemma markerEnum_injective : Function.Injective (markerEnum N) := fun a b h => by
  simpa [markerEnum] using h

lemma markerEnum_mono (a b : Fin N) (hab : a ≤ b) :
    deg (Gp N) (markerEnum N a) ≤ deg (Gp N) (markerEnum N b) :=
  Tuple.monotone_sort (markerDeg N) hab

lemma exists_markerEnum (r : Fin N) : ∃ j, markerEnum N j = .inr r :=
  ⟨(Tuple.sort (markerDeg N)).symm r, by simp [markerEnum]⟩

/-- The degrees of `z_r` in `G'` and `H'` differ by at most `δ = 1`. -/
lemma markerEnum_deg (j : Fin N) :
    deg (Gp N) (markerEnum N j) ≤ deg (Hp N) (markerEnum N j) + 1 ∧
      deg (Hp N) (markerEnum N j) ≤ deg (Gp N) (markerEnum N j) + 1 := by
  simp only [markerEnum, deg_Gp_inr, deg_Hp_inr]
  omega

/-- The size `m` of the clique added by Lemma 22, for `k = N` markers, `Δ = N + 1`, `τ = 4N - 1`
and `δ = 1`. -/
abbrev mK (N : ℕ) : ℕ := lockSize N (N + 1) (4 * N - 1) 1

/-- The common vertex set `V(G) = V(H)` of the graphs of Proposition 5. -/
abbrev VN (N : ℕ) : Type := Base N ⊕ Fin (mK N)

/-- **The graph `G`** of Proposition 5: `G'` with the clique of Lemma 22. -/
def GN (N : ℕ) : SimpleGraph (VN N) := lockGraph (Gp N) (markerEnum N) (N + 1) (4 * N - 1) 1

/-- **The graph `H`** of Proposition 5: `H'` with the clique of Lemma 22. -/
def HN (N : ℕ) : SimpleGraph (VN N) := lockGraph (Hp N) (markerEnum N) (N + 1) (4 * N - 1) 1

instance : DecidableRel (GN N).Adj := by unfold GN; infer_instance
instance : DecidableRel (HN N).Adj := by unfold HN; infer_instance

end GsimOT.Prop6
