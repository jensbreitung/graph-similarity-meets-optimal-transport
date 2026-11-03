/-
# The minima defining the operator-norm optimal transport distances are attained

Paper, App. A (pp. 14–15, l. 503–510): "All minima in the definitions of the graph distances
are attained. [...] For optimal transport, the coupling polytopes `DS*(V, W)` and `DS(V, W)` are
compact, and the objectives are [...] lower semicontinuous for all operator `p → q`-norms. For the
operator norms, let `(Q*_k)` be a convergent sequence in `DS*(V, W)`. Note that every pair in the
support of `lim_{k→∞} Q*_k` lies in `supp(Q*_k)` for almost all `k`; restricting the weighted
discrepancy matrices to the rows and columns indexed by this support gives convergent matrices and
cannot increase the operator norm. The same argument applies to `DS(V, W)`."

The distances `deltaOTPQ` and `dOT` are defined as infima (Common/OTDistances.lean); this file
shows that the infima are minima, following the argument above.

* `lpNorm_le_of_abs_le`, `opNorm_restrict_le`: restricting a matrix to a set of rows and columns
  does not increase the operator norm.
* `lowerSemicontinuous_opNorm_Bmat`: `Q ↦ ‖B_{p→q}(G, H, Q)‖_{p→q}` is lower semicontinuous
  (restriction to the rows and columns indexed by `supp(Q)`, on which the entries of `B_{p→q}`
  depend continuously on `Q`).
* `isCompact_setOf_isCoupling`: `DS*(V, W)` is compact.
* `exists_deltaOTPQ_eq`, `exists_dOT_eq`: the minima of Eq. (2) and of `d^OT_{p→q}` are attained.

Used by Claim 20 (Theorem 1, App. B, p. 17, l. 573–574), which starts from a minimiser.
-/
import GsimOT.Common.OTDistances
import GsimOT.Common.DoublyStochastic

open Finset Filter Topology Matrix

namespace GsimOT

/-! ### Restricting a matrix does not increase its operator norm -/

section Restrict

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `ℓᵖ` norms are monotone in the absolute values of the entries. -/
lemma lpNorm_le_of_abs_le {p : ENNReal} (hp : 1 ≤ p) {x y : ι → ℝ} (h : ∀ i, |x i| ≤ |y i|) :
    lpNorm p x ≤ lpNorm p y := by
  by_cases hpt : p = ⊤
  · subst hpt
    rw [lpNorm_top, lpNorm_top]
    refine Real.iSup_le (fun i => (h i).trans ?_) (Real.iSup_nonneg fun i => abs_nonneg (y i))
    exact le_ciSup (Set.finite_range fun i => |y i|).bddAbove i
  · have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hpt
    rw [lpNorm_eq_sum hp hpt, lpNorm_eq_sum hp hpt]
    refine Real.rpow_le_rpow (sum_nonneg fun i _ => by positivity)
      (sum_le_sum fun i _ => Real.rpow_le_rpow (abs_nonneg _) (h i) hp0.le) (by positivity)

/-- Restricting a matrix to the rows in `S` and the columns in `T` (setting all other entries to
zero) does not increase the operator `p → q`-norm. -/
lemma opNorm_restrict_le {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) (M : Matrix ι κ ℝ)
    (S : ι → Prop) (T : κ → Prop) [DecidablePred S] [DecidablePred T] :
    opNorm p q (fun i j => if S i ∧ T j then M i j else 0) ≤ opNorm p q M := by
  refine opNorm_le_of_bound hp hq _ (opNorm_nonneg _ _ _) fun x hx => ?_
  -- `R x = D_S (M (D_T x))` with the coordinate projections `D_S`, `D_T`
  set x' : κ → ℝ := fun j => if T j then x j else 0
  have hRx : (fun i j => if S i ∧ T j then M i j else 0 : Matrix ι κ ℝ) *ᵥ x =
      fun i => if S i then (M *ᵥ x') i else 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, x']
    by_cases hi : S i
    · simp only [hi, true_and, ite_true]
      refine sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    · simp [hi]
  have hx' : lpNorm p x' ≤ 1 :=
    (lpNorm_le_of_abs_le hp fun j => by
      simp only [x']; split_ifs <;> simp).trans hx
  rw [hRx]
  calc lpNorm q (fun i => if S i then (M *ᵥ x') i else 0) ≤ lpNorm q (M *ᵥ x') :=
        lpNorm_le_of_abs_le hq fun i => by split_ifs <;> simp
    _ ≤ opNorm p q M * lpNorm p x' := lpNorm_mulVec_le hp hq M x'
    _ ≤ opNorm p q M := mul_le_of_le_one_right (opNorm_nonneg _ _ _) hx'

/-- `|‖A‖ - ‖B‖| ≤ ∑ |A - B|`: the operator norm is continuous. -/
lemma abs_opNorm_sub_le {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) (A B : Matrix ι κ ℝ) :
    |opNorm p q A - opNorm p q B| ≤ ∑ i, ∑ j, |A i j - B i j| := by
  have h1 := opNorm_add_le hp hq B (A - B)
  have h2 := opNorm_add_le hp hq A (B - A)
  have h3 := opNorm_le_sum_abs hp hq (A - B)
  have h4 := opNorm_le_sum_abs hp hq (B - A)
  simp only [add_sub_cancel, Matrix.sub_apply] at h1 h2 h3 h4
  have h5 : ∑ i, ∑ j, |B i j - A i j| = ∑ i, ∑ j, |A i j - B i j| :=
    sum_congr rfl fun i _ => sum_congr rfl fun j _ => abs_sub_comm _ _
  rw [abs_le]
  constructor <;> linarith

/-- The operator norm is continuous on matrices. -/
lemma continuous_opNorm {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Continuous (fun A : ι → κ → ℝ => opNorm p q A) := by
  rw [Metric.continuous_iff]
  intro A ε hε
  -- `∑ |A' - A| < ε` near `A`
  have hT : Tendsto (fun A' : ι → κ → ℝ => ∑ i, ∑ j, |A' i j - A i j|) (𝓝 A) (𝓝 0) := by
    have := tendsto_finsetSum (univ : Finset ι) fun i _ =>
      tendsto_finsetSum (univ : Finset κ) fun j _ =>
        (((continuous_apply j).comp (continuous_apply i)).tendsto A |>.sub_const (A i j)).abs
    simpa using this
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hT.eventually (gt_mem_nhds hε))
  refine ⟨δ, hδ, fun A' hA' => ?_⟩
  rw [Real.dist_eq]
  exact (abs_opNorm_sub_le hp hq A' A).trans_lt (hball hA')

end Restrict

/-! ### Lower semicontinuity of `Q ↦ ‖B_{p→q}(G, H, Q)‖` -/

variable {V W : Type*} [Fintype V] [Fintype W]
variable (p q : ENNReal) (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
  [DecidableRel H.Adj]

omit [Fintype V] [Fintype W] in
/-- `Q ↦ Q(v, w)^a` (convention `0^a = 0`) is continuous at every `Q` with `Q(v, w) ≠ 0`. -/
lemma continuousAt_powZ_apply {Q : V → W → ℝ} {v : V} {w : W} (h : Q v w ≠ 0) (a : ℝ) :
    ContinuousAt (fun Q' : V → W → ℝ => powZ (Q' v w) a) Q := by
  have hc : Continuous (fun Q' : V → W → ℝ => Q' v w) :=
    (continuous_apply w).comp (continuous_apply v)
  have hev : (fun Q' : V → W → ℝ => Q' v w ^ a) =ᶠ[𝓝 Q] fun Q' => powZ (Q' v w) a := by
    filter_upwards [hc.continuousAt.eventually_ne h] with Q' hQ'
    simp [powZ, hQ']
  exact (hc.continuousAt.rpow_const (Or.inl h)).congr hev

omit [Fintype V] [Fintype W] in
/-- The entries of `B_{p→q}(G, H, Q)` vanish outside `supp(Q) × supp(Q)` (convention `0^a = 0`). -/
lemma Bmat_eq_zero_of_not_supp {Q : V → W → ℝ} (a b : V × W)
    (h : ¬ (Q a.1 a.2 ≠ 0 ∧ Q b.1 b.2 ≠ 0)) : Bmat p q G H Q a b = 0 := by
  simp only [not_and_or, not_not] at h
  rcases h with h | h <;> simp [Bmat, h]

/-- **Lower semicontinuity** (App. A, p. 15, l. 505–510): `Q ↦ ‖B_{p→q}(G, H, Q)‖_{p→q}` is
lower semicontinuous. At `Q`, the matrices `B_{p→q}(G, H, Q')` restricted to the rows and columns
indexed by `supp(Q)` depend continuously on `Q'`, their norms are at most `‖B_{p→q}(G, H, Q')‖`,
and at `Q' = Q` the restriction is `B_{p→q}(G, H, Q)` itself. -/
theorem lowerSemicontinuous_opNorm_Bmat {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    LowerSemicontinuous (fun Q : V → W → ℝ => opNorm p q (Bmat p q G H Q)) := by
  classical
  refine lowerSemicontinuous_iff.2 fun Q => lowerSemicontinuousAt_iff.2 fun y hy => ?_
  -- the restriction to the rows and columns indexed by `supp(Q)`
  let R : (V → W → ℝ) → (V × W → V × W → ℝ) := fun Q' a b =>
    if Q a.1 a.2 ≠ 0 ∧ Q b.1 b.2 ≠ 0 then Bmat p q G H Q' a b else 0
  have hRle : ∀ Q', opNorm p q (R Q') ≤ opNorm p q (Bmat p q G H Q') := fun Q' =>
    opNorm_restrict_le hp hq (Bmat p q G H Q') (fun a => Q a.1 a.2 ≠ 0) (fun b => Q b.1 b.2 ≠ 0)
  have hRQ : R Q = Bmat p q G H Q := by
    funext a b
    simp only [R]
    split_ifs with h
    · rfl
    · exact (Bmat_eq_zero_of_not_supp p q G H a b h).symm
  -- `R` is continuous at `Q` (entrywise)
  have hRc : ContinuousAt R Q := by
    refine continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => ?_
    simp only [R]
    split_ifs with h
    · exact ((continuousAt_powZ_apply h.1 _).mul continuousAt_const).mul
        (continuousAt_powZ_apply h.2 _)
    · exact continuousAt_const
  have hc : ContinuousAt (fun Q' => opNorm p q (R Q')) Q :=
    ((continuous_opNorm (ι := V × W) (κ := V × W) hp hq).continuousAt (x := R Q)).comp hRc
  have hy' : y < opNorm p q (R Q) := by rw [hRQ]; exact hy
  have hev : ∀ᶠ Q' in 𝓝 Q, y < opNorm p q (R Q') := hc.eventually (lt_mem_nhds hy')
  exact hev.mono fun Q' hQ' => hQ'.trans_le (hRle Q')

/-! ### Compactness and attainment -/

/-- `DS*(V, W)` is a compact subset of `V → W → ℝ`. -/
lemma isCompact_setOf_isCoupling : IsCompact {Q : V → W → ℝ | IsCoupling Q} := by
  classical
  have hK : IsCompact (Set.univ.pi fun _ : V => Set.univ.pi fun _ : W => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hS : {Q : V → W → ℝ | IsCoupling Q} = (⋂ v, ⋂ w, {Q | 0 ≤ Q v w}) ∩
      ((⋂ v, {Q | ∑ w, Q v w = 1 / (Fintype.card V : ℝ)}) ∩
        ⋂ w, {Q | ∑ v, Q v w = 1 / (Fintype.card W : ℝ)}) := by
    ext Q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨h.nonneg, h.row_sum, h.col_sum⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩
  have hclosed : IsClosed {Q : V → W → ℝ | IsCoupling Q} := by
    rw [hS]
    refine (isClosed_iInter fun v => isClosed_iInter fun w => ?_).inter
      ((isClosed_iInter fun v => ?_).inter (isClosed_iInter fun w => ?_))
    · exact isClosed_le continuous_const (by fun_prop)
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_eq (by fun_prop) continuous_const
  refine hK.of_isClosed_subset hclosed fun Q hQ => ?_
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
  intro v w
  refine ⟨hQ.nonneg v w, ?_⟩
  have h1 : Q v w ≤ ∑ w', Q v w' :=
    single_le_sum (fun w' _ => hQ.nonneg v w') (mem_univ w)
  have h2 : (1 : ℝ) / Fintype.card V ≤ 1 := by
    have : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.2 ⟨v⟩
    exact div_le_one_of_le₀ this (by positivity)
  rw [hQ.row_sum v] at h1
  linarith

/-- **The minimum in Eq. (2) is attained** (App. A, pp. 14–15, l. 503–510): for nonempty `V`, `W`
there is a coupling `Q* ∈ DS*(V, W)` with `‖B_{p→q}(G, H, Q*)‖_{p→q} = δ^OT_{p→q}(G, H)`. -/
theorem exists_deltaOTPQ_eq {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) [Nonempty V]
    [Nonempty W] : ∃ Q, IsCoupling Q ∧ opNorm p q (Bmat p q G H Q) = deltaOTPQ p q G H := by
  have hne : {Q : V → W → ℝ | IsCoupling Q}.Nonempty := by
    refine ⟨fun _ _ => 1 / ((Fintype.card V : ℝ) * Fintype.card W), ?_, ?_, ?_⟩
    · intro _ _; positivity
    · intro _
      have : (Fintype.card W : ℝ) ≠ 0 := by positivity
      have : (Fintype.card V : ℝ) ≠ 0 := by positivity
      simp [Finset.card_univ]
    · intro _
      have : (Fintype.card W : ℝ) ≠ 0 := by positivity
      have : (Fintype.card V : ℝ) ≠ 0 := by positivity
      simp [Finset.card_univ]; field_simp
  obtain ⟨Q, hQ, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne isCompact_setOf_isCoupling
    ((lowerSemicontinuous_opNorm_Bmat G H hp hq).lowerSemicontinuousOn _)
  refine ⟨Q, hQ, le_antisymm ?_ ?_⟩
  · have : Nonempty {Q : V → W → ℝ // IsCoupling Q} := ⟨⟨Q, hQ⟩⟩
    exact le_ciInf fun Q' => hmin Q'.2
  · exact ciInf_le ⟨0, by rintro _ ⟨Q', rfl⟩; exact opNorm_nonneg _ _ _⟩
      (⟨Q, hQ⟩ : {Q : V → W → ℝ // IsCoupling Q})

/-- **The minimum defining `d^OT_{p→q}` is attained** (App. A, p. 15, l. 509–510, "The same
argument applies to `DS(V, W)`"): if `|V| = |W|`, some `Q ∈ DS(V, W)` has
`‖B_{p→q}(G, H, Q)‖_{p→q} = d^OT_{p→q}`. -/
theorem exists_dOT_eq [DecidableEq V] [DecidableEq W] {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hne : Nonempty (V ≃ W)) :
    ∃ Q, IsDS Q ∧ opNorm p q (Bmat p q G H Q) = dOT p q G H := by
  obtain ⟨e⟩ := hne
  obtain ⟨Q, hQ, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (⟨permMat e, permMat_isDS e⟩ : {Q : V → W → ℝ | IsDS Q}.Nonempty) isCompact_setOf_isDS
    ((lowerSemicontinuous_opNorm_Bmat G H hp hq).lowerSemicontinuousOn _)
  refine ⟨Q, hQ, le_antisymm ?_ ?_⟩
  · have : Nonempty {Q : V → W → ℝ // IsDS Q} := ⟨⟨Q, hQ⟩⟩
    exact le_ciInf fun Q' => hmin Q'.2
  · exact ciInf_le ⟨0, by rintro _ ⟨Q', rfl⟩; exact opNorm_nonneg _ _ _⟩
      (⟨Q, hQ⟩ : {Q : V → W → ℝ // IsDS Q})

end GsimOT
