/-
# Combinatorics of the patterns

Paper, App. D.1, the paragraph before Lemma 27 (p. 26, l. 810–818; see also Figure 6 on
p. 26):

> Fix a branch `i ∈ [r]` and consider the sequence `χ_{G_r}(u), χ(v_{i,1}), …, χ(v_{i,ℓ-1}),
> χ_{H_r}(u)` of patterns at times `0, 1, …, ℓ`.  Consecutive patterns differ in exactly one
> coordinate: at time `h ∈ [r]`, the tag `t_{i,h}` is switched on; at time `j(r+1)` for `j ∈ [r]`,
> the bit `b_i` is flipped; at time `j(r+1) + h` for `j ∈ [r-1]` and `h ∈ [r]`, the clock marker
> `c_{j,h}` is switched on; and at time `ℓ - r + h` for `h ∈ [r]`, the tag `t_{i,h}` is switched
> off.

This file proves the facts about patterns used in Lemmas 27 and 28:
* `ham_pat_succ_le_one`: consecutive patterns differ in at most one coordinate;
* `card_change_*`: how often each marker changes along a branch (clock markers once, tags twice
  on their own branch, the bit `b_i` at most `r` times on branch `i`, never on other branches);
* clock levels (`clockLevel`) and their relation to times (`clockLevel_pat_*`), used in the proof
  of Lemma 28.
-/
import GsimOT.Proposition9_LocalEditLowerBound.Construction

open Finset

namespace GsimOT.Prop9

variable {r : ℕ}

/-- Hamming distance of two patterns. -/
def ham (x y : Marker r → Bool) : ℕ := #{z | x z ≠ y z}

/-- Division with remainder by `r + 1`, in the form used below. -/
lemma divmod_of_eq {T a b : ℕ} (hb : b < r + 1) (hT : T = a * (r + 1) + b) :
    T / (r + 1) = a ∧ T % (r + 1) = b :=
  (Nat.div_mod_unique (by omega)).2 ⟨by rw [hT]; ring, hb⟩

lemma ell_sub_r (r : ℕ) : ell r - r = r * (r + 1) := by rw [ell_eq]; omega

/-! ### When does a marker change? -/

lemma change_clock_iff (i : Fin r) (t : ℕ) (j : Fin (r - 1)) (h : Fin r) :
    pat r i t (.clock j h) ≠ pat r i (t + 1) (.clock j h) ↔
      t + 1 = (j.val + 1) * (r + 1) + (h.val + 1) := by
  simp only [pat, ne_eq, decide_eq_decide]
  omega

lemma change_tag_iff (i : Fin r) (t : ℕ) (i' : Fin r) (h : Fin r) :
    pat r i t (.tag i' h) ≠ pat r i (t + 1) (.tag i' h) ↔
      i' = i ∧ (t + 1 = h.val + 1 ∨ t + 1 = ell r - r + (h.val + 1)) := by
  have hh := h.isLt
  have hE : r + 2 ≤ ell r := by unfold ell; nlinarith
  simp only [pat, ne_eq, decide_eq_decide]
  by_cases hi : i' = i
  · simp only [hi, true_and]; omega
  · simp [hi]

lemma change_bit_iff (i : Fin r) (t : ℕ) (i' : Fin r) :
    pat r i t (.bit i') ≠ pat r i (t + 1) (.bit i') ↔ i' = i ∧ (r + 1) ∣ (t + 1) := by
  simp only [pat, ne_eq, decide_eq_decide]
  by_cases hi : i' = i
  · simp only [hi, true_and]
    rw [Nat.succ_div]
    split_ifs with hd <;> simp [hd]; omega
  · simp [hi]

/-- **Consecutive patterns differ in at most one coordinate.** -/
lemma ham_pat_succ_le_one (i : Fin r) {t : ℕ} (ht : t < ell r) :
    ham (pat r i t) (pat r i (t + 1)) ≤ 1 := by
  unfold ham
  rw [Finset.card_le_one]
  -- every changing marker is determined by `q := (t+1)/(r+1)` and `ρ := (t+1) % (r+1)`
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact i.elim0
  have hT : t + 1 ≤ r * (r + 1) + r := by rw [← ell_eq]; omega
  set q := (t + 1) / (r + 1)
  set ρ := (t + 1) % (r + 1)
  -- the three kinds of changes in terms of `q, ρ`
  have hclock : ∀ j h, pat r i t (.clock j h) ≠ pat r i (t + 1) (.clock j h) →
      q = j.val + 1 ∧ ρ = h.val + 1 := by
    intro j h hc
    exact divmod_of_eq (r := r) (by have := h.isLt; omega) ((change_clock_iff i t j h).1 hc)
  have htag : ∀ i' h, pat r i t (.tag i' h) ≠ pat r i (t + 1) (.tag i' h) →
      i' = i ∧ (q = 0 ∨ q = r) ∧ ρ = h.val + 1 := by
    intro i' h hc
    obtain ⟨hi, h1 | h2⟩ := (change_tag_iff i t i' h).1 hc
    · obtain ⟨hq, hρ⟩ := divmod_of_eq (r := r) (T := t + 1) (a := 0) (b := h.val + 1) (by have := h.isLt; omega) (by rw [h1]; ring)
      exact ⟨hi, Or.inl hq, hρ⟩
    · rw [ell_sub_r] at h2
      obtain ⟨hq, hρ⟩ := divmod_of_eq (r := r) (T := t + 1) (a := r) (b := h.val + 1) (by have := h.isLt; omega) (by rw [h2])
      exact ⟨hi, Or.inr hq, hρ⟩
  have hbit : ∀ i', pat r i t (.bit i') ≠ pat r i (t + 1) (.bit i') → i' = i ∧ ρ = 0 := by
    intro i' hc
    obtain ⟨hi, hd⟩ := (change_bit_iff i t i').1 hc
    exact ⟨hi, Nat.mod_eq_zero_of_dvd hd⟩
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  cases a with
  | clock j h =>
    obtain ⟨hq, hρ⟩ := hclock j h ha
    have hj := j.isLt
    cases b with
    | clock j' h' =>
      obtain ⟨hq', hρ'⟩ := hclock j' h' hb
      have : j = j' := Fin.ext (by omega)
      have : h = h' := Fin.ext (by omega)
      subst_vars; rfl
    | tag i' h' =>
      obtain ⟨-, hq' | hq', -⟩ := htag i' h' hb <;> omega
    | bit i' => obtain ⟨-, hρ'⟩ := hbit i' hb; omega
  | tag i₁ h =>
    obtain ⟨hi₁, hq, hρ⟩ := htag i₁ h ha
    cases b with
    | clock j' h' =>
      obtain ⟨hq', -⟩ := hclock j' h' hb
      have := j'.isLt
      omega
    | tag i' h' =>
      obtain ⟨hi', -, hρ'⟩ := htag i' h' hb
      have : h = h' := Fin.ext (by omega)
      subst_vars; rfl
    | bit i' => obtain ⟨-, hρ'⟩ := hbit i' hb; omega
  | bit i₁ =>
    obtain ⟨hi₁, hρ⟩ := hbit i₁ ha
    cases b with
    | clock j' h' => obtain ⟨-, hρ'⟩ := hclock j' h' hb; omega
    | tag i' h' => obtain ⟨-, -, hρ'⟩ := htag i' h' hb; omega
    | bit i' => obtain ⟨hi', -⟩ := hbit i' hb; subst_vars; rfl

/-! ### How often does a marker change along a branch? -/

/-- The number of times marker `z` changes along branch `i` (between times `t` and `t+1`,
`t < ℓ`). -/
def nchg (i : Fin r) (z : Marker r) : ℕ :=
  #{t ∈ Finset.range (ell r) | pat r i t z ≠ pat r i (t + 1) z}

/-- Each clock marker changes (at most) once on every branch. -/
lemma nchg_clock_le (i : Fin r) (j : Fin (r - 1)) (h : Fin r) : nchg i (.clock j h) ≤ 1 := by
  unfold nchg
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, change_clock_iff] at ha hb
  omega

/-- Tags never change on other branches, and change (at most) twice on their own branch. -/
lemma nchg_tag_le (i i' : Fin r) (h : Fin r) :
    nchg i (.tag i' h) ≤ if i' = i then 2 else 0 := by
  unfold nchg
  split_ifs with hi
  · refine (Finset.card_le_card (t := {h.val, ell r - r + h.val}) ?_).trans
      (Finset.card_le_two)
    intro t ht
    simp only [Finset.mem_filter, change_tag_iff] at ht
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ ht
    exact hi ((change_tag_iff i t i' h).1 ht).1

/-- The bit `b_i` never changes on other branches and changes at most `r` times on branch `i`. -/
lemma nchg_bit_le (i i' : Fin r) : nchg i (.bit i') ≤ if i' = i then r else 0 := by
  unfold nchg
  split_ifs with hi
  · -- the change times `t` satisfy `(r+1) ∣ t+1`, and `t + 1 ↦ (t+1)/(r+1) - 1 ∈ [0, r)` is
    -- injective on them
    have hmap : ∀ t ∈ {t ∈ Finset.range (ell r) | pat r i t (.bit i') ≠ pat r i (t + 1) (.bit i')},
        (t + 1) / (r + 1) - 1 ∈ Finset.range r := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_range, change_bit_iff] at ht
      simp only [Finset.mem_range]
      have h1 : t + 1 ≤ r * (r + 1) + r := by rw [← ell_eq]; omega
      have h2 : (t + 1) / (r + 1) ≤ r := by
        have : t + 1 < (r + 1) * (r + 1) := by nlinarith
        exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 this)
      have h3 : 0 < (t + 1) / (r + 1) := Nat.div_pos (Nat.le_of_dvd (by omega) ht.2.2) (by omega)
      omega
    refine (Finset.card_le_card_of_injOn _ hmap ?_).trans (by simp)
    intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_range, change_bit_iff, Set.mem_ofPred_eq] at ha hb
    have ha' := Nat.div_mul_cancel ha.2.2
    have hb' := Nat.div_mul_cancel hb.2.2
    have ha0 : 0 < (a + 1) / (r + 1) := Nat.div_pos (Nat.le_of_dvd (by omega) ha.2.2) (by omega)
    have hb0 : 0 < (b + 1) / (r + 1) := Nat.div_pos (Nat.le_of_dvd (by omega) hb.2.2) (by omega)
    have : (a + 1) / (r + 1) = (b + 1) / (r + 1) := by simp only at hab; omega
    have : a + 1 = b + 1 := by rw [← ha', ← hb', this]
    omega
  · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ ht
    exact hi ((change_bit_iff i t i').1 ht).1

/-- Every marker changes at most `r` times along a single branch (needs `r ≥ 2` for tags). -/
lemma nchg_le (hr : 2 ≤ r) (i : Fin r) (z : Marker r) : nchg i z ≤ r := by
  cases z with
  | clock j h => have := nchg_clock_le i j h; omega
  | tag i' h => have := nchg_tag_le i i' h; split_ifs at this <;> omega
  | bit i' => have := nchg_bit_le i i'; split_ifs at this <;> omega

/-- Summed over all `r` branches, every marker changes at most `r` times: each clock marker once
per branch, each bit `r` times on its own branch, each tag twice on its own branch. -/
lemma sum_nchg_le (hr : 2 ≤ r) (z : Marker r) : ∑ i, nchg i z ≤ r := by
  cases z with
  | clock j h =>
    calc ∑ i, nchg i (.clock j h) ≤ ∑ _i : Fin r, 1 := Finset.sum_le_sum fun i _ => nchg_clock_le i j h
      _ = r := by simp
  | tag i' h =>
    calc ∑ i, nchg i (.tag i' h) ≤ ∑ i : Fin r, if i' = i then 2 else 0 :=
          Finset.sum_le_sum fun i _ => nchg_tag_le i i' h
      _ = 2 := by simp
      _ ≤ r := hr
  | bit i' =>
    calc ∑ i, nchg i (.bit i') ≤ ∑ i : Fin r, if i' = i then r else 0 :=
          Finset.sum_le_sum fun i _ => nchg_bit_le i i'
      _ = r := by simp

/-! ### Clock levels (used in Lemma 28) -/

/-- The clock level `c(x)`: the number of clock markers in the pattern `x`. -/
def clockLevel (x : Marker r → Bool) : ℕ :=
  (Finset.univ.filter fun p : Fin (r - 1) × Fin r => x (.clock p.1 p.2) = true).card

lemma clockLevel_le (x : Marker r → Bool) : clockLevel x ≤ (r - 1) * r := by
  unfold clockLevel
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- Consecutive clock levels differ by at most the Hamming distance. -/
lemma clockLevel_le_add_ham (x y : Marker r → Bool) : clockLevel x ≤ clockLevel y + ham x y := by
  unfold clockLevel ham
  have hsub : (Finset.univ.filter fun p : Fin (r - 1) × Fin r => x (.clock p.1 p.2) = true) ⊆
      (Finset.univ.filter fun p : Fin (r - 1) × Fin r => y (.clock p.1 p.2) = true) ∪
        (Finset.univ.filter fun p : Fin (r - 1) × Fin r => x (.clock p.1 p.2) ≠ y (.clock p.1 p.2)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hp ⊢
    by_cases h : y (.clock p.1 p.2) <;> simp_all
  have hinj : (Finset.univ.filter fun p : Fin (r - 1) × Fin r =>
      x (.clock p.1 p.2) ≠ y (.clock p.1 p.2)).card ≤
      (Finset.univ.filter fun z : Marker r => x z ≠ y z).card := by
    refine Finset.card_le_card_of_injOn (fun p => Marker.clock p.1 p.2) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
      exact hp
    · intro p _ p' _ h
      simp only [Marker.clock.injEq] at h
      exact Prod.ext h.1 h.2
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

lemma clockLevel_pat_zero (i : Fin r) : clockLevel (pat r i 0) = 0 := by
  simp [clockLevel, pat_zero]

lemma clockLevel_pat_ell (hev : Even r) (i : Fin r) : clockLevel (pat r i (ell r)) = (r - 1) * r := by
  simp [clockLevel, pat_ell hev, isClock]

/-- Clock markers in block `≤ a` (paper: `c_{j,h}` with `j ≤ a`) number `min(a, r-1) · r`. -/
lemma card_clock_block_le (a : ℕ) (ha : a ≤ r - 1) :
    (Finset.univ.filter fun p : Fin (r - 1) × Fin r => p.1.val < a).card = a * r := by
  have : (Finset.univ.filter fun p : Fin (r - 1) × Fin r => p.1.val < a) =
      (Finset.univ.filter fun j : Fin (r - 1) => j.val < a) ×ˢ Finset.univ := by
    ext p; simp
  rw [this, Finset.card_product, Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin]
  rw [min_eq_right ha]

/-- If `(j-1) r < c(pat i t) < j r` for some `j ∈ [r-1]`, then `⌊t/(r+1)⌋ = j`. -/
lemma div_eq_of_clockLevel (i : Fin r) (t j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ r - 1)
    (hlo : (j - 1) * r < clockLevel (pat r i t)) (hhi : clockLevel (pat r i t) < j * r) :
    t / (r + 1) = j := by
  unfold clockLevel at hlo hhi
  simp only [pat, decide_eq_true_eq] at hlo hhi
  -- lower bound: `t > j (r+1)`
  have h1 : j * (r + 1) < t := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ.filter fun p : Fin (r - 1) × Fin r =>
        (p.1.val + 1) * (r + 1) + (p.2.val + 1) ≤ t) ⊆
        Finset.univ.filter fun p : Fin (r - 1) × Fin r => p.1.val < j - 1 := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      by_contra hp'
      push Not at hp'
      have : j * (r + 1) < (p.1.val + 1) * (r + 1) + (p.2.val + 1) := by
        have : j ≤ p.1.val + 1 := by omega
        nlinarith
      omega
    have := (Finset.card_le_card hsub).trans_eq (card_clock_block_le (j - 1) (by omega))
    omega
  -- upper bound: `t < (j+1)(r+1)`
  have h2 : t < (j + 1) * (r + 1) := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ.filter fun p : Fin (r - 1) × Fin r => p.1.val < j) ⊆
        Finset.univ.filter fun p : Fin (r - 1) × Fin r =>
          (p.1.val + 1) * (r + 1) + (p.2.val + 1) ≤ t := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have := p.2.isLt
      have : (p.1.val + 1) * (r + 1) ≤ j * (r + 1) := Nat.mul_le_mul_right _ hp
      nlinarith
    have := (card_clock_block_le j hj).symm.trans_le (Finset.card_le_card hsub)
    omega
  exact Nat.div_eq_of_lt_le h1.le h2

/-- In the middle range `0 < c(pat i t) < r(r-1)` all `r` tags of branch `i` are switched on. -/
lemma pat_tag_of_middle (i : Fin r) (t : ℕ) (hlo : 0 < clockLevel (pat r i t))
    (hhi : clockLevel (pat r i t) < (r - 1) * r) (h : Fin r) : pat r i t (.tag i h) = true := by
  -- `t ≥ r + 2`: otherwise no clock is on
  have ht1 : r + 2 ≤ t := by
    by_contra hcon
    push Not at hcon
    apply hlo.ne'
    unfold clockLevel
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _
    simp only [pat, decide_eq_true_eq, not_le]
    nlinarith
  -- `t < r² + r - 1`: otherwise all clocks are on
  have ht2 : t < ell r - r := by
    by_contra hcon
    push Not at hcon
    apply hhi.ne
    unfold clockLevel
    rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    intro p _
    simp only [pat, decide_eq_true_eq]
    rw [ell_sub_r] at hcon
    have := p.1.isLt; have := p.2.isLt
    have : (p.1.val + 1) * (r + 1) ≤ (r - 1) * (r + 1) := Nat.mul_le_mul_right _ (by omega)
    have : (r - 1) * (r + 1) + r ≤ r * (r + 1) := by
      have hr1 : 1 ≤ r := by have := h.isLt; omega
      have : (r - 1) * (r + 1) + (r + 1) = r * (r + 1) := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1]
      omega
    omega
  simp only [pat, true_and, decide_eq_true_eq]
  have := h.isLt
  omega

lemma pat_tag_other (i i' : Fin r) (hi : i' ≠ i) (t : ℕ) (h : Fin r) :
    pat r i t (.tag i' h) = false := by
  simp [pat, hi]

/-- Two middle-range patterns of different branches have Hamming distance at least `r`. -/
lemma ham_ge_of_middle_ne (i i' : Fin r) (hi : i' ≠ i) (t t' : ℕ)
    (hlo : 0 < clockLevel (pat r i t)) (hhi : clockLevel (pat r i t) < (r - 1) * r) :
    r ≤ ham (pat r i t) (pat r i' t') := by
  unfold ham
  have : #(Finset.univ.image fun h : Fin r => (Marker.tag i h : Marker r)) = r := by
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]; simp
  refine le_trans (le_of_eq this.symm) (Finset.card_le_card fun z hz => ?_)
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
  obtain ⟨h, rfl⟩ := hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [pat_tag_of_middle i t hlo hhi h, pat_tag_other i' i (Ne.symm hi)]
  simp

/-- The value of the bit `b_i` in the pattern `pat i t`. -/
lemma pat_bit_self (i : Fin r) (t : ℕ) : pat r i t (.bit i) = decide ((t / (r + 1)) % 2 = 1) := by
  simp [pat]

end GsimOT.Prop9
