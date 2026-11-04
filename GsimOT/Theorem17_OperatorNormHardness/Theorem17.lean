import GsimOT.Theorem17_OperatorNormHardness.Claim56_SplitMass
import GsimOT.Common.ThreePartition

/-!
# Theorem 17: inapproximability of `d^OT_p`

Theorem 17 of the paper (p. 12, l. 432–433; proof in Appendix G, pp. 54–57, l. 1710–1804). It gives
Theorem 4 (2) (p. 4, l. 135–137); the restriction to maximum degree two for `p = 1` is
Theorem 16.

**Theorem 17.** For `1 ≤ p ≤ ∞` and any `ε > 0`, unless `P = NP`, there is no polynomial-time
approximation algorithm computing `d^OT_p` with multiplicative error guarantee `2^{b(p)} - ε`.

The reduction from Three-Partition takes the paths `F₁` and the cycles of Theorem 16 and attaches
`M` leaves to every vertex (p. 54, l. 1710–1721) (`ThreePartition.graphG`, `ThreePartition.graphH`).

* `ThreePartition.dOT_le_one_of_isYes`: YES-instances satisfy `d^OT_p(G, H) ≤ 1`. The canonical
  bijection creates one mismatch at each end of a path, so its mismatch matrix has absolute row
  and column sums at most `1`, and `‖·‖_p ≤ 1` by the Schur test (paper: p. 55, l. 1733–1737).
* `ThreePartition.lt_dOT_of_not_isYes`: NO-instances satisfy `d^OT_p(G, H) > 2^{b(p)} - ε` if
  `M` satisfies Eq. (46) (p. 56, l. 1774–1775). If neither Claim 55 nor Claim 56 applies, `Q`
  induces a bijection `τ` between the base vertices; some edge of `F₁` is split between two
  cycles, which gives two entries of size `(1 - ε/4)²` in one column of `A^Q` and Corollary 54
  applies (pp. 56–57, l. 1776–1804). The paper fixes `0 < ε* < √2 - 1` (p. 54, l. 1728), so that
  `2^{b(p)} - ε* > 1` (l. 1729–1730); the Lean statement holds for all `0 < ε ≤ 1`, which
  includes this range.
* `ThreePartition.dOT_shift_gap`: the same for arbitrary instances, after the w.l.o.g. shift.

The complexity-theoretic conclusion is not formalized.
-/

open Finset Matrix WithLp
open scoped ENNReal

namespace GsimOT.Hardness

section PermMatrix

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]


variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fintype V] [Fintype W] [DecidableEq V] [Fact (1 ≤ p)] in
/-- The entries of `B_p(G, H, P_π)` are `P_π(x) D(x, y) P_π(y)`. -/
lemma Bpq_permMat (π : V ≃ W) (x y : V × W) :
    Bmat p p G H (permMat π) x y =
      permMat π x.1 x.2 * disc G H x.1 x.2 y.1 y.2 * permMat π y.1 y.2 := by
  have h (z : V × W) (e : ℝ) : powZ (permMat π z.1 z.2) e = permMat π z.1 z.2 := by
    unfold permMat powZ; split_ifs <;> simp_all
  simp only [Bmat, h]

/-- If every vertex has at most one mismatch under `π`, then `‖B_p(G, H, P_π)‖_p ≤ 1`: the
mismatch matrix is a signed partial matching (Schur test). -/
lemma opNorm_Bpq_permMat_le_one (π : V ≃ W)
    (hπ : ∀ v, ∑ v', |adj G v v' - adj H (π v) (π v')| ≤ 1) :
    opNorm p p (Bmat p p G H (permMat π)) ≤ 1 := by
  have hP0 (z : V × W) : 0 ≤ permMat π z.1 z.2 := (permMat_isDS π).nonneg _ _
  have hP1 (z : V × W) : permMat π z.1 z.2 ≤ 1 := (permMat_isDS π).le_one _ _
  have habs (x y : V × W) : |Bmat p p G H (permMat π) x y| =
      permMat π x.1 x.2 * (permMat π y.1 y.2 * |disc G H x.1 x.2 y.1 y.2|) := by
    rw [Bpq_permMat, abs_mul, abs_mul, abs_of_nonneg (hP0 x), abs_of_nonneg (hP0 y)]
    ring
  refine opNorm_le_one_of_sum_abs_le_one (fun x ↦ ?_) fun y ↦ ?_
  · simp only [habs]
    rw [← mul_sum, sum_permMat_mul (f := fun y ↦ |disc G H x.1 x.2 y.1 y.2|)]
    obtain ⟨x1, x2⟩ := x
    by_cases hx : π x1 = x2
    · subst hx
      have : permMat π x1 (π x1) = 1 := by simp [permMat]
      rw [this, one_mul]
      simpa [disc] using hπ x1
    · have : permMat π x1 x2 = 0 := by simp [permMat, hx]
      rw [this, zero_mul]; norm_num
  · simp only [habs]
    have h (x : V × W) : permMat π x.1 x.2 * (permMat π y.1 y.2 * |disc G H x.1 x.2 y.1 y.2|) =
        permMat π y.1 y.2 * (permMat π x.1 x.2 * |disc G H x.1 x.2 y.1 y.2|) := by ring
    simp_rw [h]
    rw [← mul_sum, sum_permMat_mul (f := fun x ↦ |disc G H x.1 x.2 y.1 y.2|)]
    obtain ⟨y1, y2⟩ := y
    by_cases hy : π y1 = y2
    · subst hy
      have : permMat π y1 (π y1) = 1 := by simp [permMat]
      rw [this, one_mul]
      calc ∑ v, |disc G H v (π v) y1 (π y1)|
          = ∑ v, |adj G y1 v - adj H (π y1) (π v)| := by
            refine sum_congr rfl fun v _ ↦ ?_
            rw [disc, adj_symm G, adj_symm H]
        _ ≤ 1 := hπ y1
    · have : permMat π y1 y2 = 0 := by simp [permMat, hy]
      rw [this, zero_mul]; norm_num

end PermMatrix

/-! ### Theorem 17 -/

namespace ThreePartition

variable (I : ThreePartition) (M : ℕ)

/-- The graph `G` of Theorem 17: the paths `F₁` with `M` leaves attached to every vertex. -/
abbrev graphG : SimpleGraph ((Σ i, Fin (I.a i)) ⊕ Σ _ : (Σ i, Fin (I.a i)), Fin M) :=
  addLeaves (pathUnion I.a) fun _ ↦ M

/-- The graph `H` of Theorem 17: `m` cycles on `A` vertices with `M` leaves at every vertex. -/
abbrev graphH : SimpleGraph ((Σ _ : Fin I.m, Fin I.A) ⊕ Σ _ : (Σ _ : Fin I.m, Fin I.A), Fin M) :=
  addLeaves (cycleUnion I.m I.A) fun _ ↦ M

/-- **Theorem 17**, YES-instances: `d^OT_p(G, H) ≤ 1` for all `1 ≤ p ≤ ∞`. The canonical
bijection maps leaves to leaves and creates exactly one mismatch at each end of a path, so the
mismatch matrix is a signed matching. -/
theorem dOT_le_one_of_isYes {p : ℝ≥0∞} [Fact (1 ≤ p)] (h2 : ∀ i, 2 ≤ I.a i) (hI : I.IsYes) :
    dOT p p (I.graphG M) (I.graphH M) ≤ 1 := by
  obtain ⟨σ, hσ⟩ := hI
  have hσ' : ∀ j, ∑ i with σ i = j, I.a i = I.A := fun j ↦ (hσ j).2
  set τ := layoutEquiv σ hσ'
  set π := Equiv.sumCongr τ (Equiv.sigmaCongrLeft (β := fun _ ↦ Fin M) τ)
  refine (iInf_isDS_le (f := fun Q ↦ opNorm p p (Bmat p p (I.graphG M) (I.graphH M) Q))
    (fun _ _ ↦ opNorm_nonneg _ _ _) (permMat_isDS π)).trans ?_
  refine opNorm_Bpq_permMat_le_one _ _ π fun v ↦ ?_
  rw [Fintype.sum_sum_type]
  cases v with
  | inl u =>
    have hleaf : ∑ t : Σ _ : (Σ i, Fin (I.a i)), Fin M,
        |adj (I.graphG M) (.inl u) (.inr t) -
          adj (I.graphH M) (π (.inl u)) (π (.inr t))| = 0 :=
      sum_eq_zero fun t _ ↦ by
        simp [π, Equiv.sigmaCongrLeft_apply, τ.injective.eq_iff]
    have hbase : ∑ u', |adj (I.graphG M) (.inl u) (.inl u') -
        adj (I.graphH M) (π (.inl u)) (π (.inl u'))| =
          (deg (cycleUnion I.m I.A) (τ u) : ℝ) - deg (pathUnion I.a) u := by
      have h (u' : Σ i, Fin (I.a i)) : |adj (I.graphG M) (.inl u) (.inl u') -
          adj (I.graphH M) (π (.inl u)) (π (.inl u'))| =
            adj (cycleUnion I.m I.A) (τ u) (τ u') - adj (pathUnion I.a) u u' := by
        simp only [π, Equiv.sumCongr_apply, Sum.map_inl, adj_addLeaves_inl_inl]
        by_cases hG : (pathUnion I.a).Adj u u'
        · have hH : (cycleUnion I.m I.A).Adj (τ u) (τ u') := layout_adj_cycleUnion σ hσ' hG
          simp only [adj, hG, hH, ite_true]
          norm_num
        · by_cases hH : (cycleUnion I.m I.A).Adj (τ u) (τ u')
          · simp only [adj, hG, hH, ite_true, ite_false]
            norm_num
          · simp only [adj, hG, hH, ite_false]
            norm_num
      simp_rw [h]
      rw [sum_sub_distrib, sum_adj_eq_deg, ← sum_adj_eq_deg (cycleUnion I.m I.A),
        Equiv.sum_comp τ (fun w ↦ adj (cycleUnion I.m I.A) (τ u) w)]
    rw [hleaf, add_zero, hbase, deg_cycleUnion (I.three_le_A_of_mem (h2 u.1))]
    obtain ⟨u', hu'⟩ := exists_pathUnion_adj I.a u (h2 u.1)
    have := one_le_deg (pathUnion I.a) hu'
    linarith
  | inr t =>
    rw [sum_eq_zero fun u' _ ↦ ?_, sum_eq_zero fun t' _ ↦ ?_, add_zero]
    · norm_num
    · simp [π, adj]
    · simp [π, adj, Equiv.sigmaCongrLeft_apply, τ.injective.eq_iff]

/-- A single summand bounds a double sum of nonnegative terms. -/
lemma single_le_sum₂ {α β : Type*} [Fintype α] [Fintype β] {F : α → β → ℝ}
    (hF : ∀ a b, 0 ≤ F a b) (a : α) (b : β) : F a b ≤ ∑ a', ∑ b', F a' b' :=
  (single_le_sum (fun b' _ ↦ hF a b') (mem_univ b)).trans
    (single_le_sum (fun a' _ ↦ sum_nonneg fun b' _ ↦ hF a' b') (mem_univ a))

/-- **Theorem 17**, NO-instances: `d^OT_p(G, H) > 2^{b(p)} - ε` if `M` satisfies Eq. (46) with
`η = ε/8` and `ε' = (ε/8)/(mA - 1)`. Together with `dOT_le_one_of_isYes`, a polynomial-time
`(2^{b(p)} - ε)`-approximation of `d^OT_p` would decide Three-Partition. -/
theorem lt_dOT_of_not_isYes {p : ℝ≥0∞} [Fact (1 ≤ p)] (h3 : ∀ i, 3 ≤ I.a i) (hI : ¬I.IsYes)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hM1 : 2 * (4 / (ε / 8)) ^ 2 + 1 < M)
    (hM2 : 2 * (2 / (ε / 8 / ((I.m * I.A : ℕ) - 1 : ℝ))) ^ 2 + 1 < M) :
    2 ^ bExp p - ε < dOT p p (I.graphG M) (I.graphH M) := by
  set G := I.graphG M
  set H := I.graphH M
  have hm : 0 < I.m := by
    by_contra h
    have h0 : I.m = 0 := by omega
    exact hI ⟨fun i ↦ absurd i.2 (by simp [h0]), fun j ↦ absurd j.2 (by simp [h0])⟩
  have hA : 7 ≤ I.A := by
    have := I.two_mul_lt ⟨0, by omega⟩
    have := h3 ⟨0, by omega⟩
    omega
  set n : ℕ := I.m * I.A
  have hn : 7 ≤ n := le_trans hA (Nat.le_mul_of_pos_left _ hm)
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hcardW : Fintype.card (Σ _ : Fin I.m, Fin I.A) = n := by simp [n]
  set η := ε / 8 with hη_def
  set ε' := ε / 8 / ((n : ℝ) - 1) with hε'_def
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hε' : 0 < ε' := div_pos (by positivity) (by linarith)
  have hb := half_le_bExp p
  have hb1 := bExp_le_one p
  have h2b : (2 : ℝ) ^ bExp p ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hb1
  have h2b1 : (1 : ℝ) ≤ 2 ^ bExp p := Real.one_le_rpow (by norm_num) (by linarith)
  set c := (1 - ε / 4) ^ 2 with hc_def
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hL : 2 ^ bExp p - ε < 2 ^ bExp p * c := by
    rw [hc_def]
    nlinarith [mul_nonneg (sub_nonneg.mpr h2b) hε.le,
      mul_pos (by linarith : (0 : ℝ) < 2 ^ bExp p) (mul_pos hε hε)]
  have hLle : 2 ^ bExp p * c ≤ 2 ^ bExp p := by nlinarith
  set e := Fintype.equivOfCardEq I.card_vertices
  refine lt_of_lt_of_le hL
    (le_iInf_isDS ⟨Equiv.sumCongr e (Equiv.sigmaCongrLeft (β := fun _ ↦ Fin M) e)⟩
      (f := fun Q ↦ opNorm p p (Bmat p p G H Q)) fun Q hQ ↦ ?_)
  have hadjG (v : Σ i, Fin (I.a i)) : ∃ u, (pathUnion I.a).Adj u v :=
    exists_pathUnion_adj I.a v (by have := h3 v.1; omega)
  -- Claim 55
  by_cases hA' : ∃ v, η ≤ ∑ t, Q (.inl v) (.inr t)
  · obtain ⟨v, hv⟩ := hA'
    exact hLle.trans (claim55 hQ (hadjG v) (by positivity) (by rw [hη_def]; linarith) hv hM1).le
  push Not at hA'
  -- Claim 56
  by_cases hB : ∃ v w w', w ≠ w' ∧ ε' ≤ Q (.inl v) (.inl w) ∧ ε' ≤ Q (.inl v) (.inl w')
  · obtain ⟨v, w, w', hww', h1, h2⟩ := hB
    exact hLle.trans (claim56 hQ (hadjG v) hww'
      (card_common_adj_cycleUnion_le_one (by omega) hww') hε' h1 h2 hM2).le
  push Not at hB
  -- every base vertex sends mass `≥ 1 - ε/4` to a single base vertex
  have hf (v : Σ i, Fin (I.a i)) : ∃ w, 1 - ε / 4 ≤ Q (.inl v) (.inl w) := by
    have : Nonempty (Σ _ : Fin I.m, Fin I.A) := ⟨⟨⟨0, hm⟩, ⟨0, by omega⟩⟩⟩
    obtain ⟨w, -, hw⟩ := exists_max_image univ (fun b ↦ Q (.inl v) (.inl b)) univ_nonempty
    refine ⟨w, ?_⟩
    have hsmall (b) (hb : b ∈ univ.erase w) : Q (.inl v) (.inl b) ≤ ε' := by
      by_contra! hb'
      exact absurd (hB v w b (ne_of_mem_erase hb).symm (hb'.le.trans (hw b (mem_univ b))))
        (not_lt.mpr hb'.le)
    have hrow := hQ.row_sum (.inl v)
    rw [Fintype.sum_sum_type, ← add_sum_erase _ _ (mem_univ w)] at hrow
    have h1 : ∑ b ∈ univ.erase w, Q (.inl v) (.inl b) ≤ ε / 8 := by
      calc ∑ b ∈ univ.erase w, Q (.inl v) (.inl b) ≤ ∑ _b ∈ univ.erase w, ε' := sum_le_sum hsmall
        _ = ((n - 1 : ℕ) : ℝ) * ε' := by simp [card_erase_of_mem, hcardW]
        _ = ε / 8 := by
            rw [Nat.cast_sub (by omega), Nat.cast_one, hε'_def]
            field_simp
    have h3' := hA' v
    rw [hη_def] at h3'
    linarith
  choose f hf using hf
  have hfhalf (v) : 1 / 2 < Q (.inl v) (.inl (f v)) := by have := hf v; linarith
  have hf_inj : Function.Injective f := by
    intro v1 v2 h12
    by_contra hne
    have h2 : Q (.inl v1) (.inl (f v1)) + Q (.inl v2) (.inl (f v1)) ≤ 1 := by
      have := hQ.sum_le_one' {.inl v1, .inl v2} (.inl (f v1))
      rwa [sum_pair (by simpa using hne)] at this
    have := hfhalf v1
    have := hfhalf v2
    rw [← h12] at this
    linarith
  set τ := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, I.card_vertices⟩)
  -- as `I` is a NO-instance, some edge of `F₁` is split between two cycles
  have hcross : ∃ u u', (pathUnion I.a).Adj u u' ∧ (f u).1 ≠ (f u').1 := by
    by_contra hcon
    push Not at hcon
    apply hI
    refine I.isYes_of_isDS (permMat_isDS τ) (fun i ↦ (f ⟨i, ⟨0, I.a_pos i⟩⟩).1)
      fun v w hw ↦ ?_
    have hw' : f v = w := by
      by_contra h
      exact hw (by simp [permMat, τ, h])
    rw [← hw']
    exact eq_of_pathUnion_adj I.a (fun v ↦ (f v).1) hcon v
  obtain ⟨u, u', huu', hcr⟩ := hcross
  obtain ⟨v, v', v'', hv', hv'', hne, hcr'⟩ : ∃ v v' v'', (pathUnion I.a).Adj v' v ∧
      (pathUnion I.a).Adj v'' v ∧ v' ≠ v'' ∧ (f v).1 ≠ (f v').1 := by
    rcases exists_other_adj I.a h3 huu' with ⟨u'', h1, h2⟩ | ⟨u'', h1, h2⟩
    · exact ⟨u, u', u'', huu'.symm, h1, h2.symm, hcr⟩
    · exact ⟨u', u, u'', huu', h1, h2.symm, Ne.symm hcr⟩
  have hfc (x) : 1 - ε / 4 ≤ Q (.inl x) (.inl (f x)) := hf x
  have hprod (x : Σ i, Fin (I.a i)) : c ≤ Q (.inl x) (.inl (f x)) * Q (.inl v) (.inl (f v)) := by
    have := hfc x
    have := hfc v
    have : 0 ≤ 1 - ε / 4 := by linarith
    simp only [c, sq]
    exact mul_le_mul (hfc x) (hfc v) (by linarith) (hQ.nonneg _ _)
  have hF (x y y') : 0 ≤ Q (.inl x) y * (1 - adj H y y') * Q (.inl v) y' :=
    mul_nonneg (mul_nonneg (hQ.nonneg _ _) (sub_nonneg.mpr (adj_le_one _ _ _)))
      (hQ.nonneg _ _)
  -- an edge `x v` of `F₁` mapped onto a non-edge gives an entry `≥ c`
  have hentry_adj {x} (hx : (pathUnion I.a).Adj x v)
      (hnx : ¬(cycleUnion I.m I.A).Adj (f x) (f v)) :
      c ≤ |aggMatrix G H Q (.inl x) (.inl v)| := by
    have h := aggMatrix_of_adj G H Q (x := .inl x) (x' := .inl v)
      ((addLeaves_adj_inl_inl).mpr hx)
    have hle := single_le_sum₂ (hF x) (.inl (f x)) (.inl (f v))
    rw [← h] at hle
    have h0 : adj H (.inl (f x)) (.inl (f v)) = 0 := by
      simp only [H, graphH, adj, addLeaves_adj_inl_inl, hnx, ite_false]
    rw [h0, sub_zero, mul_one] at hle
    exact (hprod x).trans (hle.trans (le_abs_self _))
  have hentry1 := hentry_adj hv' fun h ↦ hcr' h.1.symm
  -- a second entry: either `v''` or the preimage of the other cycle neighbour of `f v`
  obtain ⟨x, hxne, hentry2⟩ : ∃ x, x ≠ v' ∧ c ≤ |aggMatrix G H Q (.inl x) (.inl v)| := by
    by_cases hv''f : (cycleUnion I.m I.A).Adj (f v'') (f v)
    · have hdeg : deg (cycleUnion I.m I.A) (f v) = 2 := by
        exact_mod_cast deg_cycleUnion (m := I.m) (by omega) (f v)
      have hcard : 1 < #({w | (cycleUnion I.m I.A).Adj w (f v)} : Finset _) := by
        have hc : ({w | (cycleUnion I.m I.A).Adj w (f v)} : Finset _) =
            ({w | (cycleUnion I.m I.A).Adj (f v) w} : Finset _) := by
          ext w
          simp only [mem_filter, mem_univ, true_and]
          exact (cycleUnion I.m I.A).adj_comm w (f v)
        rw [hc]
        unfold deg at hdeg
        omega
      obtain ⟨ws, hws, hwsne⟩ := exists_mem_ne hcard (f v'')
      have hws' : (cycleUnion I.m I.A).Adj ws (f v) := (mem_filter.mp hws).2
      set x := τ.symm ws
      have hfx : f x = ws := τ.apply_symm_apply ws
      have hxv' : x ≠ v' := fun h ↦ hcr' (by rw [← h, hfx]; exact hws'.1.symm)
      have hxv'' : x ≠ v'' := fun h ↦ hwsne (by rw [← hfx, h])
      have hnadj : ¬(pathUnion I.a).Adj x v := fun h ↦ by
        rcases eq_or_eq_of_pathUnion_adj I.a hv' hv'' hne h with h | h
        · exact hxv' h
        · exact hxv'' h
      refine ⟨x, hxv', ?_⟩
      have h := aggMatrix_of_not_adj G H Q (x := .inl x) (x' := .inl v)
        (fun h ↦ hnadj ((addLeaves_adj_inl_inl).mp h))
      have hle := single_le_sum₂ (F := fun y y' ↦ Q (.inl x) y * adj H y y' *
        Q (.inl v) y') (fun y y' ↦ mul_nonneg (mul_nonneg (hQ.nonneg _ _)
          (adj_nonneg _ _ _)) (hQ.nonneg _ _)) (.inl (f x)) (.inl (f v))
      have h1 : adj H (.inl (f x)) (.inl (f v)) = 1 := by
        simp only [H, graphH, adj, addLeaves_adj_inl_inl, hfx, hws',
          ite_true]
      rw [h1, mul_one] at hle
      rw [h, abs_neg, abs_of_nonneg (sum_nonneg fun y _ ↦ sum_nonneg fun y' _ ↦
        mul_nonneg (mul_nonneg (hQ.nonneg _ _) (adj_nonneg _ _ _)) (hQ.nonneg _ _))]
      exact (hprod x).trans hle
    · exact ⟨v'', Ne.symm hne, hentry_adj hv'' hv''f⟩
  have key := rpow_bExp_mul_le_opNorm_Bpq G H hQ (p := p) (v := .inl v)
    (K := {.inl v', .inl x}) hc0 (by
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hentry1
      · exact hentry2)
  rw [card_pair (by simpa using Ne.symm hxne)] at key
  simpa using key

/-- **Theorem 17** for arbitrary instances (after the w.l.o.g. shift): for `M` as in Eq. (46),
YES-instances give `d^OT_p ≤ 1` and NO-instances give `d^OT_p > 2^{b(p)} - ε`. -/
theorem dOT_shift_gap {p : ℝ≥0∞} [Fact (1 ≤ p)] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hM1 : 2 * (4 / (ε / 8)) ^ 2 + 1 < M)
    (hM2 : 2 * (2 / (ε / 8 / ((I.shift.m * I.shift.A : ℕ) - 1 : ℝ))) ^ 2 + 1 < M) :
    (I.IsYes → dOT p p (I.shift.graphG M) (I.shift.graphH M) ≤ 1) ∧
      (¬I.IsYes → 2 ^ bExp p - ε < dOT p p (I.shift.graphG M) (I.shift.graphH M)) :=
  ⟨fun h ↦ I.shift.dOT_le_one_of_isYes M (fun i ↦ by have := I.four_le_shift_a i; omega)
      (I.shift_isYes_iff.mpr h),
    fun h ↦ I.shift.lt_dOT_of_not_isYes M (fun i ↦ by have := I.four_le_shift_a i; omega)
      (mt I.shift_isYes_iff.mp h) hε hε1 hM1 hM2⟩

end ThreePartition

end GsimOT.Hardness
