/-
# The core edges of `G'` and `H'`

Counting lemmas for the core-core pairs, used in the proofs of Lemmas 24 and 25 (App. C.1).

For odd `N`, both cores consist of `(N - 1)/2` disjoint edges and one isolated vertex
(p. 22, l. 692–693): the core edges of `G'` are the pairs `{c, c'}` with `c + c' = N`, so `v₀` is
isolated; those of `H'` are the pairs with `c + c' + 1 = N`, so `w_N` (`2c + 1 = N`) is isolated.

If the core vertex `c` of `G'` is mapped to `f(c)` in the first and to `g(c)` in the second
coordinate of a pair, the core-core pairs cost `mixCore N f g = 2(N - 1) - 2 · pres N f g`
(`mixCore_eq`), where `pres N f g` counts the ordered core edges of `G'` that are mapped onto core
edges of `H'`.  This is the identity `|a - b| = a + b - 2ab` for `a, b ∈ {0, 1}`, as in the proof
of Lemma 25 (p. 24, l. 750–751: "Their ordered pairs therefore contribute `2(N - 1 - 2k)` to
the cost").
-/
import GsimOT.Proposition6_EditLowerBound.Lemma28_MarkerCost

open Finset

namespace GsimOT.Prop6

variable {N : ℕ}

/-! ### Counting core vertices -/

/-- Counting core vertices with a property of their index. -/
lemma sum_fin_ite_eq_card' (p : ℕ → Prop) [DecidablePred p] :
    ∑ c : Fin N, (if p c.val then (1 : ℝ) else 0) = #{c ∈ range N | p c} := by
  rw [Fin.sum_univ_eq_sum_range (fun c => if p c then (1 : ℝ) else 0) N, sum_boole]

/-- `N - 1` core vertices `c ≥ 1`. -/
lemma sum_one_le (hN : 1 ≤ N) : ∑ c : Fin N, (if 1 ≤ c.val then (1 : ℝ) else 0) = N - 1 := by
  rw [sum_fin_ite_eq_card' (fun c => 1 ≤ c)]
  have : {c ∈ range N | 1 ≤ c} = Ico 1 N := by
    ext c; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico, Nat.cast_sub hN, Nat.cast_one]

/-- All but one core vertex: `#{c | p c} = N - 1` if `p` fails exactly at `a < N`. -/
lemma sum_ne_one (p : ℕ → Prop) [DecidablePred p] {a : ℕ} (ha : a < N)
    (hp : ∀ c < N, (p c ↔ c ≠ a)) : ∑ c : Fin N, (if p c.val then (1 : ℝ) else 0) = N - 1 := by
  rw [sum_fin_ite_eq_card' p]
  have : {c ∈ range N | p c} = (range N).erase a := by
    ext c; simp only [mem_filter, mem_range, mem_erase]
    constructor
    · rintro ⟨hc, h⟩; exact ⟨(hp c hc).1 h, hc⟩
    · rintro ⟨h, hc⟩; exact ⟨hc, (hp c hc).2 h⟩
  rw [this, card_erase_of_mem (mem_range.2 ha), card_range, Nat.cast_sub (by omega), Nat.cast_one]

/-- All core vertices `c ≥ 1` but one: `#{c | p c} = N - 2` if `p c ↔ 1 ≤ c ∧ c ≠ a` and
`1 ≤ a < N`. -/
lemma sum_ne_two (p : ℕ → Prop) [DecidablePred p] {a : ℕ} (ha : 1 ≤ a) (haN : a < N)
    (hp : ∀ c < N, (p c ↔ 1 ≤ c ∧ c ≠ a)) :
    ∑ c : Fin N, (if p c.val then (1 : ℝ) else 0) = N - 2 := by
  rw [sum_fin_ite_eq_card' p]
  have : {c ∈ range N | p c} = (Ico 1 N).erase a := by
    ext c; simp only [mem_filter, mem_range, mem_erase, mem_Ico]
    constructor
    · rintro ⟨hc, h⟩; have := (hp c hc).1 h; omega
    · rintro ⟨h, h1, hc⟩; exact ⟨hc, (hp c hc).2 ⟨h1, h⟩⟩
  have hcard : ((Ico 1 N).erase a).card = N - 2 := by
    rw [card_erase_of_mem (mem_Ico.2 ⟨ha, haN⟩), Nat.card_Ico]; omega
  rw [this, hcard, Nat.cast_sub (by omega)]
  norm_num

/-! ### Partners -/

/-- The partner `N - c` of a core vertex `c ≥ 1` of `G'` (and `0` for `c = 0`). -/
def partner (c : Fin N) : Fin N := ⟨(N - c.val) % N, Nat.mod_lt _ (by have := c.isLt; omega)⟩

lemma partner_val {c : Fin N} (hc : 1 ≤ c.val) : (partner c).val = N - c.val :=
  Nat.mod_eq_of_lt (by omega)

/-- `c + c' = N` iff `c ≥ 1` and `c'` is the partner of `c`. -/
lemma add_eq_iff_partner (c c' : Fin N) : c.val + c'.val = N ↔ 1 ≤ c.val ∧ c' = partner c := by
  constructor
  · intro h
    have hc : 1 ≤ c.val := by have := c'.isLt; omega
    exact ⟨hc, Fin.ext (by rw [partner_val hc]; omega)⟩
  · rintro ⟨hc, rfl⟩
    rw [partner_val hc]
    have := c.isLt
    omega

/-- Summing over the partner `c'` of `c` in `G'`. -/
lemma sum_partner (Φ : Fin N → Fin N → Prop) [DecidableRel Φ] (c : Fin N) :
    ∑ c', (if c.val + c'.val = N ∧ Φ c c' then (1 : ℝ) else 0) =
      if 1 ≤ c.val ∧ Φ c (partner c) then 1 else 0 := by
  simp only [add_eq_iff_partner]
  rw [Fintype.sum_eq_single (partner c) fun c' hc' => ite_eq_right fun h => hc' h.1.2]
  exact if_congr (by simp) rfl rfl

/-! ### The number of core edges -/

/-- `G'` has `(N - 1)/2` core edges, i.e. `N - 1` ordered ones. -/
lemma sum_adj_Gp_core (hN : Odd N) :
    ∑ c, ∑ c', adj (Gp N) (.inl c) (.inl c') = (N : ℝ) - 1 := by
  have h : ∀ c : Fin N, ∑ c', adj (Gp N) (.inl c) (.inl c') = if 1 ≤ c.val then 1 else 0 :=
    fun c => by
      simp only [adj_Gp_inl_inl hN]
      have := sum_partner (fun _ _ => True) c
      simp only [and_true] at this
      exact this
  simp only [h]
  exact sum_one_le (by obtain ⟨m, rfl⟩ := hN; omega)

/-- `H'` has `(N - 1)/2` core edges, i.e. `N - 1` ordered ones. -/
lemma sum_adj_Hp_core (hN : Odd N) :
    ∑ d, ∑ d', adj (Hp N) (.inl d) (.inl d') = (N : ℝ) - 1 := by
  obtain ⟨m, rfl⟩ := hN
  -- the partner of `d` in `H'` is `N - 1 - d`, which differs from `d` unless `d = m`
  have h : ∀ d : Fin (2 * m + 1),
      ∑ d', adj (Hp (2 * m + 1)) (.inl d) (.inl d') = if d.val ≠ m then 1 else 0 := fun d => by
    simp only [adj_Hp_inl_inl]
    rw [Fintype.sum_eq_single ⟨2 * m - d.val, by omega⟩ fun d' hd' => ite_eq_right fun h =>
      hd' (Fin.ext (by simp only; omega))]
    exact if_congr (by simp only [ne_eq, Fin.ext_iff]; omega) rfl rfl
  simp only [h]
  exact sum_ne_one (fun c => c ≠ m) (by omega) fun c _ => Iff.rfl

/-! ### The cost of the core-core pairs -/

/-- The cost of the core-core pairs if the core vertex `c` of `G'` is mapped to `f(c)` in the first
and to `g(c)` in the second coordinate: `∑_{c,c'} |A_{G'}(c, c') - A_{H'}(f c, g c')|`. -/
def mixCore (N : ℕ) (f g : Fin N → Fin N) : ℝ :=
  ∑ c, ∑ c', |adj (Gp N) (.inl c) (.inl c') - adj (Hp N) (.inl (f c)) (.inl (g c'))|

/-- The number of ordered core edges `(c, c')` of `G'` such that `(f c, g c')` is a core edge of
`H'`. -/
def pres (N : ℕ) (f g : Fin N → Fin N) : ℝ :=
  ∑ c, ∑ c', adj (Gp N) (.inl c) (.inl c') * adj (Hp N) (.inl (f c)) (.inl (g c'))

/-- `pres N f g`, summed over the partners: the ordered core edge `(c, N - c)` of `G'` is preserved
iff `(f(c), g(N - c))` is a core edge of `H'`. -/
lemma pres_eq (hN : Odd N) (f g : Fin N → Fin N) :
    pres N f g = ∑ c, if 1 ≤ c.val ∧
      ((f c).val + (g (partner c)).val + 1 = N ∧ f c ≠ g (partner c)) then 1 else 0 := by
  unfold pres
  simp only [adj_Gp_inl_inl hN, adj_Hp_inl_inl, ite_zero_mul_ite_zero, mul_one]
  exact sum_congr rfl fun c _ =>
    sum_partner (fun c c' => (f c).val + (g c').val + 1 = N ∧ f c ≠ g c') c

/-- The core-core pairs cost `2(N - 1) - 2 · pres N f g`: both cores have `N - 1` ordered edges,
and each preserved one saves two. -/
lemma mixCore_eq (hN : Odd N) (f g : Fin N ≃ Fin N) :
    mixCore N f g = 2 * ((N : ℝ) - 1) - 2 * pres N f g := by
  have habs : ∀ a b : ℝ, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) → |a - b| = a + b - 2 * (a * b) := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
  have hH : ∑ c, ∑ c', adj (Hp N) (.inl (f c)) (.inl (g c')) = (N : ℝ) - 1 :=
    calc ∑ c, ∑ c', adj (Hp N) (.inl (f c)) (.inl (g c'))
        = ∑ c, ∑ d', adj (Hp N) (.inl (f c)) (.inl d') :=
          sum_congr rfl fun c _ => Equiv.sum_comp g fun d' => adj (Hp N) (.inl (f c)) (.inl d')
      _ = ∑ d, ∑ d', adj (Hp N) (.inl d) (.inl d') :=
          Equiv.sum_comp f fun d => ∑ d', adj (Hp N) (.inl d) (.inl d')
      _ = (N : ℝ) - 1 := sum_adj_Hp_core hN
  unfold mixCore pres
  simp only [fun c c' => habs _ _ (adj_eq_zero_or_one (Gp N) (.inl c) (.inl c'))
    (adj_eq_zero_or_one (Hp N) (.inl (f c)) (.inl (g c'))), sum_sub_distrib, sum_add_distrib,
    ← mul_sum, sum_adj_Gp_core hN, hH]
  ring

/-! ### `coreCost` of permutation matrices and of averages of two of them -/

lemma sum_permMat_mul (ρ : Fin N ≃ Fin N) (c : Fin N) (F : Fin N → ℝ) :
    ∑ d, permMat ρ c d * F d = F (ρ c) := by
  rw [Fintype.sum_eq_single (ρ c) fun d hd => by simp [permMat, Ne.symm hd]]
  simp [permMat]

/-- The average `½(P_f + P_g)` of two permutation matrices. -/
noncomputable def avgPerm (f g : Fin N ≃ Fin N) (c d : Fin N) : ℝ :=
  (permMat f c d + permMat g c d) / 2

lemma avgPerm_isDS (f g : Fin N ≃ Fin N) : IsDS (avgPerm f g) where
  nonneg c d := by
    have := (permMat_isDS f).nonneg c d
    have := (permMat_isDS g).nonneg c d
    unfold avgPerm; positivity
  row_sum c := by
    simp only [avgPerm, ← sum_div, sum_add_distrib, (permMat_isDS f).row_sum,
      (permMat_isDS g).row_sum]
    norm_num
  col_sum d := by
    simp only [avgPerm, ← sum_div, sum_add_distrib, (permMat_isDS f).col_sum,
      (permMat_isDS g).col_sum]
    norm_num

lemma sum_avgPerm_mul (f g : Fin N ≃ Fin N) (c : Fin N) (F : Fin N → ℝ) :
    ∑ d, avgPerm f g c d * F d = (F (f c) + F (g c)) / 2 := by
  simp only [avgPerm, add_div, add_mul, sum_add_distrib, div_mul_eq_mul_div, ← sum_div,
    sum_permMat_mul]

/-- `coreCost` with the factors `R(c, d) R(c', d')` in front. -/
lemma coreCost_eq (R : Fin N → Fin N → ℝ) :
    coreCost N R = ∑ c, ∑ d, R c d * ∑ c', ∑ d', R c' d' *
      |adj (Gp N) (.inl c) (.inl c') - adj (Hp N) (.inl d) (.inl d')| := by
  unfold coreCost
  refine sum_congr rfl fun c _ => sum_congr rfl fun d _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c' _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun d' _ => by ring

/-- For a bijection `ρ` of the cores, the core-core pairs cost `mixCore N ρ ρ`. -/
lemma coreCost_permMat (ρ : Fin N ≃ Fin N) : coreCost N (permMat ρ) = mixCore N ρ ρ := by
  rw [coreCost_eq]
  simp only [sum_permMat_mul]
  rfl

/-- For `R = ½(P_f + P_g)`, the core-core pairs cost the average of the four mixed costs. -/
lemma coreCost_avgPerm (f g : Fin N ≃ Fin N) :
    coreCost N (avgPerm f g) =
      (mixCore N f f + mixCore N f g + mixCore N g f + mixCore N g g) / 4 := by
  rw [coreCost_eq]
  simp only [sum_avgPerm_mul]
  unfold mixCore
  simp only [← sum_div, sum_add_distrib]
  ring

end GsimOT.Prop6
