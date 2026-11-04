/-
# Lemma 28: every bijection has local cost at least `r`

Paper, Appendix D.1, Lemma 28 (p. 27, l. 838; proof l. 839–859): `d₁(G_r, H_r) ≥ r`.

Proof (paper).  Suppose that `π` is a bijection with `C₁(π) < r`.  By Lemma 22 with `τ := r`,
`π` fixes all markers and permutes `X`.  Hence, for every core vertex `x`, `L_π(x, π(x))` is
the Hamming distance of `χ_{G_r}(x)` and `χ_{H_r}(π(x))`, which is less than `r`.
Starting at `u` in `G_r`, follow `π` until `π^s(u) = u` is reached.  Consider the patterns
`x₀ := χ_{G_r}(u)`, `x_ι := χ(π^ι(u))` (`0 < ι < s`), `x_s := χ_{H_r}(u)`; consecutive patterns
have Hamming distance less than `r`.  Using clock levels one finds indices
`0 < ι₁ - 1 < ⋯ < ι_{r-1} - 1 < s` on a single branch `i` at which the bit `b_i` takes the values
`1, 0, 1, …, 1`, while it is `0` at `0` and at `s`.  So the bit changes at least `r` times along
the walk, and `L_π(b_i, π(b_i)) ≥ r`, a contradiction.

The argument on patterns (everything after "consider the patterns") is the purely combinatorial
`walk_bits`; `lemma28` connects it to bijections of `G_r` and `H_r`.  At a core vertex `x`,
`lemma28` only uses that `L_π(x, π(x))` is at least the Hamming distance of the patterns.
-/
import GsimOT.Proposition8_LocalEditLowerBound.Lemma27_FractionalCost

open Finset

namespace GsimOT.Prop8

variable {r : ℕ}

lemma ham_comm (x y : Marker r → Bool) : ham x y = ham y x := by
  unfold ham; congr 1; ext z; simp [eq_comm]

/-- The number of changes `f ι ≠ f (ι + 1)` of a Boolean sequence for `ι < b`. -/
def nChanges (f : ℕ → Bool) (b : ℕ) : ℕ := #{ι ∈ Finset.range b | f ι ≠ f (ι + 1)}

/-- Counting changes of a Boolean sequence: if `f a ≠ f b` with `a ≤ b`, then there is a change
in `[a, b)`. -/
lemma card_changes_step (f : ℕ → Bool) {a b : ℕ} (hab : a ≤ b) (hf : f a ≠ f b) :
    nChanges f a + 1 ≤ nChanges f b := by
  set N : ℕ → ℕ := nChanges f
  have hsucc : ∀ b, N (b + 1) = N b + if f b ≠ f (b + 1) then 1 else 0 := by
    intro b
    simp only [N, nChanges, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl
  have hmono : ∀ d, N a ≤ N (a + d) := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih => rw [← add_assoc, hsucc]; omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  change N a + 1 ≤ N (a + d)
  induction d with
  | zero => exact absurd rfl hf
  | succ d ih =>
    rw [← add_assoc, hsucc]
    by_cases hd : f (a + d) ≠ f (a + d + 1)
    · rw [ite_eq_left hd]; have := hmono d; omega
    · rw [ite_eq_right hd]
      push Not at hd
      exact ih (by omega) (by rw [hd]; simpa [add_assoc] using hf)

/-- **Lemma 28, combinatorial core.**  Let `x₀, …, x_s` be patterns, each of the form `pat i t`,
with `x₀ = χ_{G_r}(u)`, `x_s = χ_{H_r}(u)`, and consecutive Hamming distances `< r`.  Then for some
branch `i` the bit `b_i` changes at least `r` times along the sequence. -/
theorem walk_bits (hr : 2 ≤ r) (hev : Even r) (s : ℕ) (x : ℕ → Marker r → Bool)
    (hx : ∀ ι ≤ s, ∃ i, ∃ t ≤ ell r, x ι = pat r i t)
    (h0 : ∃ i, x 0 = pat r i 0) (hs : ∃ i, x s = pat r i (ell r))
    (hham : ∀ ι < s, ham (x ι) (x (ι + 1)) < r) :
    ∃ i, r ≤ #{ι ∈ Finset.range s | x ι (.bit i) ≠ x (ι + 1) (.bit i)} := by
  classical
  set C := (r - 1) * r with hC
  have hrC : r ≤ C := by rw [hC]; nlinarith [show 1 ≤ r - 1 by omega]
  set c : ℕ → ℕ := fun ι => clockLevel (x ι) with hc
  have hcle : ∀ ι, c ι ≤ C := fun ι => clockLevel_le _
  have hc0 : c 0 = 0 := by obtain ⟨i, hi⟩ := h0; simp [hc, hi, clockLevel_pat_zero]
  have hcs : c s = C := by obtain ⟨i, hi⟩ := hs; simp [hc, hi, clockLevel_pat_ell hev, hC]
  -- consecutive clock levels differ by less than `r`
  have hup : ∀ ι < s, c (ι + 1) < c ι + r := by
    intro ι hι
    have h1 := clockLevel_le_add_ham (x (ι + 1)) (x ι)
    have h2 := hham ι hι
    rw [ham_comm] at h2
    show clockLevel (x (ι + 1)) < clockLevel (x ι) + r
    omega
  have hdown : ∀ ι < s, c ι < c (ι + 1) + r := by
    intro ι hι
    have h1 := clockLevel_le_add_ham (x ι) (x (ι + 1))
    have h2 := hham ι hι
    show clockLevel (x ι) < clockLevel (x (ι + 1)) + r
    omega
  -- `β`: the first index with full clock level
  have hβex : ∃ β, β ≤ s ∧ c β = C := ⟨s, le_rfl, hcs⟩
  obtain ⟨β, ⟨hβs, hβC⟩, hβmin⟩ : ∃ β, (β ≤ s ∧ c β = C) ∧ ∀ ι < β, c ι < C := by
    refine ⟨Nat.find hβex, Nat.find_spec hβex, fun ι hι => ?_⟩
    have := Nat.find_min hβex hι
    push Not at this
    exact lt_of_le_of_ne (hcle ι) (this (by have := (Nat.find_spec hβex).1; omega))
  -- `α`: the last index `≤ β` with clock level `0`
  obtain ⟨α, hα0, hαβ, hαmax⟩ : ∃ α, c α = 0 ∧ α ≤ β ∧ ∀ ι, α < ι → ι ≤ β → c ι ≠ 0 :=
    ⟨Nat.findGreatest (fun ι => c ι = 0) β,
      Nat.findGreatest_spec (P := fun ι => c ι = 0) (Nat.zero_le β) hc0,
      Nat.findGreatest_le β,
      fun ι h1 h2 => Nat.findGreatest_is_greatest (P := fun ι => c ι = 0) (n := β) h1 h2⟩
  have hαlt : α < β := lt_of_le_of_ne hαβ (fun h => by
    rw [h] at hα0; rw [hα0] at hβC; omega)
  -- middle indices have middle clock level
  have hmid : ∀ ι, α < ι → ι < β → 0 < c ι ∧ c ι < C := fun ι h1 h2 =>
    ⟨Nat.pos_of_ne_zero (hαmax ι h1 h2.le), hβmin ι h2⟩
  -- `α + 1 < β`
  have hα1 : α + 1 < β := by
    have := hup α (by omega)
    rw [hα0] at this
    refine lt_of_le_of_ne (by omega) fun h => ?_
    rw [h, hβC] at this; omega
  -- the branch `i₀` of the walk
  obtain ⟨i₀, t₀, ht₀, hx₀⟩ := hx (α + 1) (by omega)
  have hbranch : ∀ ι, α < ι → ι < β → ∃ t ≤ ell r, x ι = pat r i₀ t := by
    intro ι h1 h2
    induction ι, (show α + 1 ≤ ι by omega) using Nat.le_induction with
    | base => exact ⟨t₀, ht₀, hx₀⟩
    | succ ι hι ih =>
      obtain ⟨t, ht, hxt⟩ := ih (by omega) (by omega)
      obtain ⟨i', t', ht', hxt'⟩ := hx (ι + 1) (by omega)
      refine ⟨t', ht', ?_⟩
      rw [hxt']
      by_contra hne
      have hi : i' ≠ i₀ := fun h => hne (by rw [h])
      have hm := hmid ι (by omega) (by omega)
      have := ham_ge_of_middle_ne i₀ i' hi t t' (by rw [← hxt]; exact hm.1)
        (by rw [← hxt]; exact hm.2)
      rw [← hxt, ← hxt'] at this
      have := hham ι (by omega)
      omega
  -- the bit sequence along the walk
  set f : ℕ → Bool := fun ι => x ι (.bit i₀) with hf
  have hf0 : f 0 = false := by obtain ⟨i, hi⟩ := h0; simp [hf, hi, pat_zero]
  have hfs : f s = false := by obtain ⟨i, hi⟩ := hs; simp [hf, hi, pat_ell hev, isClock]
  -- `ι_j`: the first index in `(α, β]` with clock level `≥ j r`
  have hιex : ∀ j : ℕ, ∃ ι, α < ι ∧ ι ≤ β ∧ (j * r ≤ c ι ∨ ι = β) :=
    fun j => ⟨β, hαlt, le_rfl, Or.inr rfl⟩
  obtain ⟨ιf, hιf_spec, hιf_min⟩ : ∃ ιf : ℕ → ℕ,
      (∀ j, α < ιf j ∧ ιf j ≤ β ∧ (j * r ≤ c (ιf j) ∨ ιf j = β)) ∧
      ∀ j ι, ι < ιf j → ¬ (α < ι ∧ ι ≤ β ∧ (j * r ≤ c ι ∨ ι = β)) :=
    ⟨fun j => Nat.find (hιex j), fun j => Nat.find_spec (hιex j),
      fun j ι h => Nat.find_min (hιex j) h⟩
  have hι_spec : ∀ j, 1 ≤ j → j ≤ r - 1 →
      α < ιf j ∧ ιf j ≤ β ∧ j * r ≤ c (ιf j) := by
    intro j hj1 hj
    obtain ⟨h1, h2, h3⟩ := hιf_spec j
    refine ⟨h1, h2, ?_⟩
    rcases h3 with h3 | h3
    · exact h3
    · rw [h3, hβC, hC]; exact Nat.mul_le_mul_right _ hj
  have hι_min : ∀ j ι, α < ι → ι < ιf j → c ι < j * r := by
    intro j ι h1 h2
    have := hιf_min j ι h2
    push Not at this
    have h3 := this h1 (by have := (hιf_spec j).2.1; omega)
    exact h3.1
  -- `p_j := ι_j - 1`
  have hp : ∀ j, 1 ≤ j → j ≤ r - 1 →
      α < ιf j - 1 ∧ ιf j - 1 < β ∧ f (ιf j - 1) = decide (j % 2 = 1) := by
    intro j hj1 hj
    obtain ⟨h1, h2, h3⟩ := hι_spec j hj1 hj
    have hprev : ιf j - 1 + 1 = ιf j := by omega
    -- `c(p_j) < j r`
    have hlt : c (ιf j - 1) < j * r := by
      by_cases hpα : ιf j - 1 = α
      · rw [hpα, hα0]; positivity
      · exact hι_min j _ (by omega) (by omega)
    -- `c(p_j) > (j - 1) r`
    have hgt : (j - 1) * r < c (ιf j - 1) := by
      have := hup (ιf j - 1) (by omega)
      rw [hprev] at this
      have : j * r = (j - 1) * r + r := by
        obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hj1; simp; ring
      omega
    have hpα : α < ιf j - 1 := by
      by_contra h
      have : ιf j - 1 = α := by omega
      rw [this, hα0] at hgt; omega
    have hpβ : ιf j - 1 < β := by omega
    refine ⟨hpα, hpβ, ?_⟩
    obtain ⟨t, -, hxt⟩ := hbranch _ hpα hpβ
    have hdiv : t / (r + 1) = j := by
      apply div_eq_of_clockLevel i₀ t j hj1 hj
      · rw [← hxt]; exact hgt
      · rw [← hxt]; exact hlt
    simp only [hf, hxt, pat_bit_self, hdiv]
  -- `p_j < p_{j+1}`
  have hpmono : ∀ j, 1 ≤ j → j + 1 ≤ r - 1 → ιf j - 1 ≤ ιf (j + 1) - 1 := by
    intro j hj1 hj
    obtain ⟨h1, h2, -⟩ := hp (j + 1) (by omega) hj
    -- `p_{j+1}` qualifies for `ι_j`
    have hq : j * r ≤ c (ιf (j + 1) - 1) := by
      obtain ⟨h1', h2', h3'⟩ := hι_spec (j + 1) (by omega) hj
      have := hup (ιf (j + 1) - 1) (by omega)
      rw [show ιf (j + 1) - 1 + 1 = ιf (j + 1) by omega] at this
      have : (j + 1) * r = j * r + r := by ring
      omega
    have : ιf j ≤ ιf (j + 1) - 1 := by
      by_contra hcon
      exact hιf_min j _ (by omega) ⟨h1, h2.le, Or.inl hq⟩
    omega
  -- count the changes
  have hcount : ∀ j, 1 ≤ j → j ≤ r - 1 → j ≤ nChanges f (ιf j - 1) := by
    intro j hj1 hj
    induction j, hj1 using Nat.le_induction with
    | base =>
      have hp1 := hp 1 le_rfl hj
      have := card_changes_step f (Nat.zero_le (ιf 1 - 1)) (by rw [hf0, hp1.2.2]; simp)
      have h0 : nChanges f 0 = 0 := by simp [nChanges]
      rw [h0, zero_add] at this
      exact this
    | succ j hj1 ih =>
      have hpj := hp j hj1 (by omega)
      have hpj1 := hp (j + 1) (by omega) hj
      have := card_changes_step f (hpmono j hj1 hj) (by
        rw [hpj.2.2, hpj1.2.2]; simp; omega)
      have := ih (by omega)
      omega
  have hfinal : r ≤ nChanges f s := by
    have hpr := hp (r - 1) (by omega) le_rfl
    have hodd : (r - 1) % 2 = 1 := by
      obtain ⟨k, hk⟩ := hev; omega
    have := card_changes_step f (show ιf (r - 1) - 1 ≤ s by omega)
      (by rw [hpr.2.2, hfs, hodd]; simp)
    have := hcount (r - 1) (by omega) le_rfl
    omega
  exact ⟨i₀, hfinal⟩

/-! ### From bijections to walks -/

lemma sum_Vr_ge_marker (F : Vr r → ℝ) (hF : ∀ a, 0 ≤ F a) :
    ∑ z : Marker r, F (.inl (.marker z)) ≤ ∑ a, F a := by
  rw [Fintype.sum_sum_type, sum_base]
  have h1 : 0 ≤ ∑ x : Core r, F (.inl (.core x)) := Finset.sum_nonneg fun _ _ => hF _
  have h2 : 0 ≤ ∑ y, F (.inr y) := Finset.sum_nonneg fun _ _ => hF _
  linarith

@[simp] lemma adj_Gr_core_marker (x : Core r) (z : Marker r) :
    adj (Gr r) (.inl (.core x)) (.inl (.marker z)) = if chiG x z then 1 else 0 := by
  simp [Gr]
@[simp] lemma adj_Hr_core_marker (x : Core r) (z : Marker r) :
    adj (Hr r) (.inl (.core x)) (.inl (.marker z)) = if chiH x z then 1 else 0 := by
  simp [Hr]
@[simp] lemma adj_Gr_marker_core (x : Core r) (z : Marker r) :
    adj (Gr r) (.inl (.marker z)) (.inl (.core x)) = if chiG x z then 1 else 0 := by
  simp [Gr]
@[simp] lemma adj_Hr_marker_core (x : Core r) (z : Marker r) :
    adj (Hr r) (.inl (.marker z)) (.inl (.core x)) = if chiH x z then 1 else 0 := by
  simp [Hr]

/-- **Lemma 28.** Every bijection `π` of `V(G_r)` has `C₁(π) ≥ r`; hence `d₁(G_r, H_r) ≥ r`. -/
theorem lemma28 (hr : 2 ≤ r) (hev : Even r) (π : Vr r ≃ Vr r) :
    (r : ℝ) ≤ costOneBij (Gr r) (Hr r) π := by
  classical
  by_contra hcon
  push Not at hcon
  -- Lemma 22 (1): `π` fixes the markers and maps `X ∪ M` into itself
  obtain ⟨hfix, hV⟩ := lemma22_bij (G := G0 r) (H := H0 r) (Δ := nX r) (τ := r) (δ := 1)
    markerEnum_injective markerEnum_mono (lock_hyp_deg_G (by omega)) (lock_hyp_deg_H (by omega))
    lock_hyp_delta π hcon
  let πB : Base r → Base r := fun a => (hV a).choose
  have hπB : ∀ a, π (.inl a) = .inl (πB a) := fun a => (hV a).choose_spec
  have hπBm : ∀ z, πB (.marker z) = .marker z := by
    intro z
    obtain ⟨j, hj⟩ := exists_markerEnum z
    have := hfix j
    rw [hj, hπB] at this
    exact Sum.inl_injective this
  have hcore : ∀ x, ∃ y, πB (.core x) = .core y := by
    intro x
    rcases h : πB (.core x) with y | z
    · exact ⟨y, rfl⟩
    · exfalso
      have : π (.inl (.core x)) = π (.inl (.marker z)) := by rw [hπB, hπB, h, hπBm]
      cases π.injective this
  let πc : Core r → Core r := fun x => (hcore x).choose
  have hπc : ∀ x, π (.inl (.core x)) = .inl (.core (πc x)) := fun x => by
    rw [hπB, (hcore x).choose_spec]
  have hπcinj : Function.Injective πc := by
    intro x y h
    have := π.injective (by rw [hπc, hπc, h] : π (.inl (.core x)) = π (.inl (.core y)))
    simpa using this
  let P : Equiv.Perm (Core r) := Equiv.ofBijective πc (Finite.injective_iff_bijective.1 hπcinj)
  have hP : ∀ x, P x = πc x := fun _ => rfl
  -- local costs at core vertices bound the Hamming distances of patterns
  have hhamπ : ∀ x, ham (chiG x) (chiH (P x)) < r := by
    intro x
    have h1 := (localCost_permMat_le_costOneBij (G := Gr r) (H := Hr r) π (.inl (.core x))).trans_lt
      hcon
    rw [hπc] at h1
    have h2 := sum_Vr_ge_marker (fun a => |adj (Gr r) (.inl (.core x)) a -
      adj (Hr r) (.inl (.core (πc x))) (π a)|) (fun _ => abs_nonneg _)
    simp only [hπB, hπBm, adj_Gr_core_marker, adj_Hr_core_marker,
      sum_abs_ind_eq_ham] at h2
    rw [hP]
    exact_mod_cast h2.trans_lt h1
  -- the walk `u, π(u), π²(u), …`
  have hper : ∃ k, 0 < k ∧ (P ^ k) .u = .u :=
    ⟨orderOf P, orderOf_pos P, by rw [pow_orderOf_eq_one]; rfl⟩
  obtain ⟨s, ⟨hs0, hsu⟩, hsmin⟩ : ∃ s, (0 < s ∧ (P ^ s) .u = .u) ∧
      ∀ k, 0 < k → k < s → (P ^ k) .u ≠ .u :=
    ⟨Nat.find hper, Nat.find_spec hper, fun k hk hks h => Nat.find_min hper hks ⟨hk, h⟩⟩
  set y : ℕ → Core r := fun k => (P ^ k) .u with hy
  have hysucc : ∀ k, y (k + 1) = P (y k) := fun k => by
    simp only [hy, pow_succ', Equiv.Perm.mul_apply]
  have hyinj : ∀ a b, a < b → b < s → y a ≠ y b := by
    intro a b hab hbs h
    apply hsmin (b - a) (by omega) (by omega)
    have : (P ^ b) .u = (P ^ a) ((P ^ (b - a)) .u) := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
    apply (P ^ a).injective
    rw [← this]; exact h.symm
  have hyu : ∀ k, 0 < k → k < s → y k ≠ .u := fun k hk hks => hsmin k hk hks
  -- the pattern sequence
  set x : ℕ → Marker r → Bool := fun ι => if ι < s then chiG (y ι) else chiH .u with hxdef
  have i0 : Fin r := ⟨0, by omega⟩
  have hxnext : ∀ ι < s, x (ι + 1) = chiH (P (y ι)) := by
    intro ι hι
    rw [← hysucc]
    by_cases h : ι + 1 < s
    · simp only [hxdef, ite_eq_left h]
      exact chiG_eq_chiH_of_ne_u (hyu _ (by omega) h)
    · have : ι + 1 = s := by omega
      simp [hxdef, this, hy, hsu]
  have hxpat : ∀ ι ≤ s, ∃ i, ∃ t ≤ ell r, x ι = pat r i t := by
    intro ι _
    by_cases h : ι < s
    · simp only [hxdef, ite_eq_left h]
      cases hyι : y ι with
      | u => exact ⟨i0, 0, Nat.zero_le _, by rw [chiG_u, pat_zero]⟩
      | v i k => exact ⟨i, k.val + 1, by have := k.isLt; omega, rfl⟩
    · simp only [hxdef, ite_eq_right h]
      exact ⟨i0, ell r, le_rfl, by rw [chiH_u, pat_ell hev]⟩
  have hx0 : ∃ i, x 0 = pat r i 0 := ⟨i0, by
    simp only [hxdef, ite_eq_left hs0, hy, pow_zero, Equiv.Perm.coe_one, id, chiG_u, pat_zero]⟩
  have hxs : ∃ i, x s = pat r i (ell r) := ⟨i0, by
    simp only [hxdef, lt_irrefl, ite_false, chiH_u, pat_ell hev]⟩
  have hxham : ∀ ι < s, ham (x ι) (x (ι + 1)) < r := by
    intro ι hι
    rw [hxnext ι hι]
    simp only [hxdef, ite_eq_left hι]
    exact hhamπ _
  obtain ⟨i, hi⟩ := walk_bits hr hev s x hxpat hx0 hxs hxham
  -- the bit `b_i` has local cost at least `r`
  have hbit := (localCost_permMat_le_costOneBij (G := Gr r) (H := Hr r) π
    (.inl (.marker (.bit i)))).trans_lt hcon
  rw [hπB, hπBm] at hbit
  have hsub : ∑ ι ∈ Finset.range s,
      |adj (Gr r) (.inl (.marker (.bit i))) (.inl (.core (y ι))) -
        adj (Hr r) (.inl (.marker (.bit i))) (π (.inl (.core (y ι))))| ≤
      ∑ a, |adj (Gr r) (.inl (.marker (.bit i))) a -
        adj (Hr r) (.inl (.marker (.bit i))) (π a)| := by
    rw [← Finset.sum_image (f := fun a => |adj (Gr r) (.inl (.marker (.bit i))) a -
        adj (Hr r) (.inl (.marker (.bit i))) (π a)|)
      (s := Finset.range s) (g := fun ι => (.inl (.core (y ι)) : Vr r)) ?_]
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => abs_nonneg _
    · intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      simp only [Sum.inl.injEq, Base.core.injEq] at hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hyinj a b h hb hab
      · exact hyinj b a h ha hab.symm
  have hterm : ∀ ι ∈ Finset.range s,
      |adj (Gr r) (.inl (.marker (.bit i))) (.inl (.core (y ι))) -
        adj (Hr r) (.inl (.marker (.bit i))) (π (.inl (.core (y ι))))| =
      if x ι (.bit i) ≠ x (ι + 1) (.bit i) then 1 else 0 := by
    intro ι hι
    rw [Finset.mem_range] at hι
    rw [hπc, adj_Gr_marker_core, adj_Hr_marker_core, hxnext ι hι, ← hP]
    simp only [hxdef, ite_eq_left hι]
    cases chiG (y ι) (.bit i) <;> cases chiH (P (y ι)) (.bit i) <;> simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    mul_one] at hsub
  have : (r : ℝ) ≤ #{ι ∈ Finset.range s | x ι (.bit i) ≠ x (ι + 1) (.bit i)} := by
    exact_mod_cast hi
  linarith

end GsimOT.Prop8
