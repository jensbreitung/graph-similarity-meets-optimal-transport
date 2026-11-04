import GsimOT.Common.ThreePartition

/-!
# Theorem 16: inapproximability of `d^OT_1`

Theorem 16 of the paper (p. 12, l. 424–425; proof in Appendix G, pp. 51–52, l. 1621–1670). It gives
the case `p = 1` of Theorem 4 (2) (p. 4, l. 135–137).

**Theorem 16.** For any `ε > 0`, unless `P = NP`, there is no polynomial-time approximation
algorithm computing `d^OT_1` with multiplicative error guarantee `2 - ε`, even for graphs of
maximum degree two.

The reduction maps an instance of Three-Partition to `F₁ = pathUnion I.a` (paths on `aᵢ`
vertices) and `F₂ = cycleUnion I.m I.A` (`m` cycles on `A` vertices); both have maximum degree
two. Its correctness is the gap

* `dOTOne_le_of_isYes`: YES-instances satisfy `d^OT_1(F₁, F₂) ≤ 1`;
* `two_le_dOTOne_of_not_isYes`: NO-instances satisfy `d^OT_1(F₁, F₂) ≥ 2`.

`d^OT_1` is `GsimOT.dOTOne` from `GsimOT.Common.Basic`, the definition of Proposition 8 and
Theorem 9, which takes `C₁(Q)` to be the largest local cost on `supp(Q)`. By Eq. (7) this is
`‖B_{1→1}(G, H, Q)‖_{1→1}` (`opNorm_Bpq_one_one_eq_costOne`, `dOT_one_one_eq_dOTOne`).

## Proof

The paper bounds the blowup distance `d^•_1` by looking at permutations of the `k`-blowups and
then uses Theorem 1 (`d^OT_1 = d^•_1`, p. 52, l. 1667). We argue directly with doubly stochastic
matrices, which needs neither; the case distinction is the same. For `Q ∈ DS(V, W)`
(`localCost_eq`)

  `L_Q(v, w) = deg(v) + deg(w) - 2 Q(N(v), N(w))`,

the fractional form of the paper's mismatch count `(2k - ℓ) + (dk - ℓ)` (l. 1661).
If all local costs on `supp(Q)` are `< 2`, then, as `deg(w) = 2` on the cycles,
`Q(N(v), N(w)) > deg(v)/2` for all `(v, w) ∈ supp(Q)`. This forces each row of `Q` into a
single cycle (two cycles would need mass `> deg(v)` on `N(v)`; Case 2, l. 1653–1663, with
`ℓ + ℓ' ≤ dk`) and adjacent vertices into the same cycle (otherwise `Q(N(v), N(w)) ≤ deg(v) - 1`,
so `deg(v) > 2`; Case 1, l. 1645–1652). Counting mass then gives a solution
(`ThreePartition.isYes_of_isDS`; the argument after Eq. (44), l. 1639–1642).

The complexity-theoretic conclusion is not formalized, nor is Proposition 57 (membership in NP).
-/

open Finset

namespace GsimOT.Hardness

section LocalCost

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
  {Q : V → W → ℝ}

/-- `Q(N(v), N(w))`: the mass between the neighbourhoods of `v` and `w`. -/
def nbrMass (Q : V → W → ℝ) (v : V) (w : W) : ℝ :=
  ∑ x : V × W, Q x.1 x.2 * (adj G x.1 v * adj H x.2 w)

/-- `L_Q(v, w) = deg(v) + deg(w) - 2 Q(N(v), N(w))` for `Q ∈ DS(V, W)`. -/
lemma localCost_eq (hQ : IsDS Q) (v : V) (w : W) :
    localCost G H Q v w = deg G v + deg H w - 2 * nbrMass G H Q v w := by
  have h (x : V × W) : Q x.1 x.2 * |disc G H x.1 x.2 v w| =
      Q x.1 x.2 * adj G x.1 v + Q x.1 x.2 * adj H x.2 w -
        2 * (Q x.1 x.2 * (adj G x.1 v * adj H x.2 w)) := by
    simp only [disc, adj]
    split_ifs <;> norm_num
    ring
  rw [localCost_eq_sum_col, ← sum_adj_eq_deg' G v, ← sum_adj_eq_deg' H w]
  unfold nbrMass
  simp_rw [h, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  rw [hQ.sum_mul_fst (fun v' ↦ adj G v' v), hQ.sum_mul_snd (fun w' ↦ adj H w' w)]

end LocalCost

namespace ThreePartition

variable (I : ThreePartition)

/-- **Theorem 16**, YES-instances (p. 51, l. 1626–1632): `d^OT_1(F₁, F₂) ≤ 1`. The
formalisation assumes `aᵢ ≥ 2` for all `i`. -/
theorem dOTOne_le_of_isYes (h2 : ∀ i, 2 ≤ I.a i) (hI : I.IsYes) :
    dOTOne (pathUnion I.a) (cycleUnion I.m I.A) ≤ 1 := by
  obtain ⟨σ, hσ⟩ := hI
  have hσ' : ∀ j, ∑ i with σ i = j, I.a i = I.A := fun j ↦ (hσ j).2
  set G := pathUnion I.a
  set H := cycleUnion I.m I.A
  set π := layoutEquiv σ hσ'
  have hP := permMat_isDS π
  refine (dOTOne_le hP).trans (costOne_le zero_le_one fun v w hvw ↦ ?_)
  have hvw' : π v = w := by
    by_contra h
    exact hvw (by simp [permMat, h])
  have hN : nbrMass G H (permMat π) v w = deg G v := by
    rw [nbrMass, sum_permMat_mul, ← sum_adj_eq_deg' G v]
    refine sum_congr rfl fun u _ ↦ ?_
    by_cases hG : G.Adj u v
    · have hH : H.Adj (π u) w := hvw' ▸ layout_adj_cycleUnion σ hσ' hG
      simp [adj, hG, hH]
    · simp [adj, hG]
  obtain ⟨u, hu⟩ := exists_pathUnion_adj I.a v (h2 v.1)
  have := one_le_deg G hu
  rw [localCost_eq G H hP, deg_cycleUnion (I.three_le_A_of_mem (h2 v.1)), hN]
  linarith

/-- **Theorem 16**, NO-instances (p. 52, l. 1633–1666): `d^OT_1(F₁, F₂) ≥ 2`. -/
theorem two_le_dOTOne_of_not_isYes (hI : ¬I.IsYes) :
    2 ≤ dOTOne (pathUnion I.a) (cycleUnion I.m I.A) := by
  set G := pathUnion I.a
  set H := cycleUnion I.m I.A
  have := Nonempty.intro (Fintype.equivOfCardEq I.card_vertices)
  refine le_dOTOne fun Q hQ ↦ not_lt.mp fun hlt ↦ hI ?_
  -- every `(v, w) ∈ supp(Q)` has local cost `< 2`, i.e. `deg(v) < 2 Q(N(v), N(w))`
  have hloc (v : Σ i, Fin (I.a i)) (w : Σ _ : Fin I.m, Fin I.A) (hvw : Q v w ≠ 0) :
      (deg G v : ℝ) < 2 * nbrMass G H Q v w := by
    have h1 := (localCost_le_costOne hvw).trans_lt hlt
    have hA : 3 ≤ I.A := by
      have := I.two_mul_lt v.1
      have := I.a_pos v.1
      omega
    rw [localCost_eq G H hQ, deg_cycleUnion hA] at h1
    linarith
  -- each row of `Q` is supported on a single cycle
  have hrow (v : Σ i, Fin (I.a i)) (w₁ w₂ : Σ _ : Fin I.m, Fin I.A) (h₁ : Q v w₁ ≠ 0)
      (h₂ : Q v w₂ ≠ 0) : w₁.1 = w₂.1 := by
    by_contra hne
    have e1 := hloc v w₁ h₁
    have e2 := hloc v w₂ h₂
    have : nbrMass G H Q v w₁ + nbrMass G H Q v w₂ ≤ deg G v := by
      unfold nbrMass
      rw [← sum_adj_eq_deg' G v, ← sum_add_distrib, ← hQ.sum_mul_fst (fun u ↦ adj G u v)]
      refine sum_le_sum fun x _ ↦ ?_
      have hb : adj H x.2 w₁ + adj H x.2 w₂ ≤ 1 := by
        simp only [adj]
        split_ifs with hb1 hb2 <;> norm_num
        exact hne (hb1.1.symm.trans hb2.1)
      calc Q x.1 x.2 * (adj G x.1 v * adj H x.2 w₁) +
            Q x.1 x.2 * (adj G x.1 v * adj H x.2 w₂)
          = Q x.1 x.2 * adj G x.1 v *
              (adj H x.2 w₁ + adj H x.2 w₂) := by ring
        _ ≤ Q x.1 x.2 * adj G x.1 v * 1 :=
            mul_le_mul_of_nonneg_left hb (mul_nonneg (hQ.nonneg _ _) (adj_nonneg G _ _))
        _ = Q x.1 x.2 * adj G x.1 v := mul_one _
    linarith
  choose wsel hwsel using hQ.exists_ne_zero
  have hc (v : Σ i, Fin (I.a i)) (w) (hw : Q v w ≠ 0) : w.1 = (wsel v).1 :=
    hrow v w (wsel v) hw (hwsel v)
  -- adjacent vertices of `F₁` are mapped into the same cycle
  have hconst (v v'' : Σ i, Fin (I.a i)) (hvv : G.Adj v'' v) : (wsel v).1 = (wsel v'').1 := by
    by_contra hne
    have e := hloc v (wsel v) (hwsel v)
    have : nbrMass G H Q v (wsel v) ≤ deg G v - 1 := by
      have hdeg : ∑ u, (adj G u v - if u = v'' then adj G u v else 0) = deg G v - 1 := by
        rw [sum_sub_distrib, sum_ite_eq', sum_adj_eq_deg' G v]
        simp [adj, hvv]
      unfold nbrMass
      rw [← hdeg, ← hQ.sum_mul_fst]
      refine sum_le_sum fun x _ ↦ ?_
      by_cases hx : x.1 = v''
      · have hzero : Q x.1 x.2 * (adj G x.1 v * adj H x.2 (wsel v)) = 0 := by
          by_cases hQx : Q x.1 x.2 = 0
          · simp [hQx]
          · have h1 : x.2.1 = (wsel v'').1 := hx ▸ hc x.1 x.2 hQx
            have : ¬H.Adj x.2 (wsel v) := fun hH ↦ hne (hH.1.symm.trans h1)
            simp [adj, this]
        rw [hzero]
        simp [hx]
      · rw [ite_eq_right hx, sub_zero]
        exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (adj_nonneg G _ _)
          (adj_le_one H _ _)) (hQ.nonneg _ _)
    have : (deg G v : ℝ) ≤ 2 := by exact_mod_cast deg_pathUnion_le I.a v
    linarith
  refine I.isYes_of_isDS hQ (fun i ↦ (wsel ⟨i, ⟨0, I.a_pos i⟩⟩).1) fun v w hw ↦ ?_
  rw [hc v w hw]
  exact eq_of_pathUnion_adj I.a (fun v ↦ (wsel v).1) (fun u v huv ↦ (hconst v u huv).symm) v

/-- **Theorem 16** for arbitrary instances (after the w.l.o.g. shift, p. 51, l. 1622–1624):
YES-instances give `d^OT_1 ≤ 1` and NO-instances give `d^OT_1 ≥ 2`. -/
theorem dOTOne_shift_gap :
    (I.IsYes → dOTOne (pathUnion I.shift.a) (cycleUnion I.shift.m I.shift.A) ≤ 1) ∧
      (¬I.IsYes → 2 ≤ dOTOne (pathUnion I.shift.a) (cycleUnion I.shift.m I.shift.A)) :=
  ⟨fun h ↦ I.shift.dOTOne_le_of_isYes (fun i ↦ by have := I.four_le_shift_a i; omega)
      (I.shift_isYes_iff.mpr h),
    fun h ↦ I.shift.two_le_dOTOne_of_not_isYes (mt I.shift_isYes_iff.mp h)⟩

end ThreePartition

end GsimOT.Hardness
