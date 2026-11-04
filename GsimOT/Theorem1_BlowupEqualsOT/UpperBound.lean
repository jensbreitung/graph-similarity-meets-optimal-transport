/-
# The upper bound for couplings with denominator `N` (Eq. (15))

Paper, Appendix B, second part of the proof of Theorem 1 (pp. 18–20, l. 592–638).
The theorem `eq15_of_integral` is Eq. (15) for an arbitrary `ℓ` with `N Q` integral; `eq15` (Claim20.lean) is
the paper's form `ℓ = ks`.

Construction.  With `q(v, w) := N Q(v, w) ∈ ℕ` we have `∑_w q(v, w) = ℓn` and `∑_v q(v, w) = ℓm`.
For each `v` we choose `g₁ v : [ℓn] → W` with fibres `I(v, w)` of size `q(v, w)`, and for each `w`
we choose `g₂ w : [ℓm] → V` with fibres `J(v, w)` of size `q(v, w)`.  Both `V × [ℓn]` and
`W × [ℓm]` are then partitioned into blocks indexed by `V × W` of equal sizes `q(v, w)`
(`{v} × I(v, w)` resp. `{w} × J(v, w)`), and gluing bijections between corresponding blocks
(`Equiv.ofFiberEquiv`) gives the bijection `π` of the paper, `π(v, i) = (w, π_{vw}(i))` for
`i ∈ I(v, w)`.  Eq. (10) then holds, and the averaging argument of the paper gives Eq. (15).
-/
import GsimOT.Theorem1_BlowupEqualsOT.BlockNorms
import GsimOT.Theorem1_BlowupEqualsOT.Definitions

open Finset Matrix

namespace GsimOT

/-- A function `Fin k → α` with prescribed fibre sizes `r a` (where `∑ r a = k`); used to
choose the partitions `I(v, ·)` of `[ℓn]` and `J(·, w)` of `[ℓm]` (Appendix B, p. 18,
l. 597–599). -/
lemma exists_fin_fun_card_fiber {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) (r : α → ℕ)
    (hr : ∑ a, r a = k) : ∃ g : Fin k → α, ∀ a, #{i | g i = a} = r a := by
  let e : Fin k ≃ Σ a, Fin (r a) := Fintype.equivOfCardEq (by simp [hr])
  refine ⟨fun i => (e i).1, fun a => ?_⟩
  rw [Finset.card_eq_sum_ones, Finset.sum_filter,
    Equiv.sum_comp e (fun s => if s.1 = a then 1 else 0), Fintype.sum_sigma]
  rw [Fintype.sum_eq_single a (fun b hb => by simp [hb])]
  simp

/-- The fibre of `(a, c)` under `(x, i) ↦ (x, g x i)` has the size of the fibre of `c` under
`g a`. -/
lemma card_fiber_prod {X Y : Type*} [Fintype X] [DecidableEq X] [DecidableEq Y] {k : ℕ}
    (g : X → Fin k → Y) (a : X) (c : Y) :
    Fintype.card {x : X × Fin k // (x.1, g x.1 x.2) = (a, c)} = #{i | g a i = c} := by
  rw [Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Fintype.sum_prod_type]
  simp [Prod.ext_iff, ite_and]

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- The bijection `π : V × [ℓn] → W × [ℓm]` of Appendix B (proof of Eq. (15), p. 18, l. 597–601):
there is a bijection `π` and a map `c : W × [ℓm] → V` (with `c(w, j) = v` iff `j ∈ J(v, w)`)
such that `π⁻¹(w, j) ∈ {c(w, j)} × [ℓn]` and `|J(v, w)| = q(v, w)`. -/
lemma exists_blowup_bij (k k' : ℕ) (qn : V → W → ℕ)
    (hrow : ∀ v, ∑ w, qn v w = k) (hcol : ∀ w, ∑ v, qn v w = k') :
    ∃ (π : V × Fin k ≃ W × Fin k') (c : W × Fin k' → V),
      (∀ b, (π.symm b).1 = c b) ∧ ∀ v w, #{j | (c j, j.1) = (v, w)} = qn v w := by
  choose g1 hg1 using fun v => exists_fin_fun_card_fiber _ (qn v) (hrow v)
  choose g2 hg2 using fun w => exists_fin_fun_card_fiber _ (fun v => qn v w) (hcol w)
  let f1 : V × Fin k → V × W := fun x => (x.1, g1 x.1 x.2)
  let f2 : W × Fin k' → V × W := fun x => (g2 x.1 x.2, x.1)
  have h1 : ∀ a, Fintype.card {x // f1 x = a} = qn a.1 a.2 := by
    rintro ⟨v, w⟩
    rw [← hg1 v w]
    exact card_fiber_prod g1 v w
  have h2 : ∀ a, Fintype.card {x // f2 x = a} = qn a.1 a.2 := by
    rintro ⟨v, w⟩
    rw [← hg2 w v, ← card_fiber_prod g2 w v]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by
      simp only [f2, Prod.ext_iff]; exact and_comm))
  let e : ∀ a, {x // f1 x = a} ≃ {x // f2 x = a} :=
    fun a => Fintype.equivOfCardEq (by rw [h1, h2])
  refine ⟨Equiv.ofFiberEquiv e, fun x => (f2 x).1, fun x => ?_, fun v w => ?_⟩
  · have := Equiv.ofFiberEquiv_map e ((Equiv.ofFiberEquiv e).symm x)
    rw [Equiv.apply_symm_apply] at this
    show _ = (f2 x).1
    rw [this]
  · rw [← h2 (v, w), Fintype.card_subtype]

/-- Per-block identity used in the chain of equalities in the proof of Eq. (15): if the block of
`a` has `|J(a)| = N·Q(a)` elements, then `∑_{j ∈ J(a)} z(j) = N^t · Q(a)^t · z̄(a)` where
`z̄(a) = (∑_{j ∈ J(a)} z(j)) / |J(a)|^t` (with `0^t = 0` for `Q(a) = 0`). -/
lemma block_sum_eq {α β : Type*} [Fintype β] [DecidableEq α] (b : β → α) (z : β → ℝ) (a : α)
    {N Qa : ℝ} (t : ℝ) (hN : 0 < N) (hQ : 0 ≤ Qa) (hc : (blockCard b a : ℝ) = N * Qa) :
    ∑ j ∈ univ.filter (fun j => b j = a), z j =
      N ^ t * (powZ Qa t * ((∑ j ∈ univ.filter (fun j => b j = a), z j) /
        (blockCard b a : ℝ) ^ t)) := by
  by_cases h0 : blockCard b a = 0
  · have : univ.filter (fun j => b j = a) = ∅ := Finset.card_eq_zero.mp h0
    rw [this]; simp
  · have hQ0 : Qa ≠ 0 := by
      rintro rfl; apply h0; exact_mod_cast (by simpa using hc : (blockCard b a : ℝ) = 0)
    have hQpos : 0 < Qa := lt_of_le_of_ne hQ (Ne.symm hQ0)
    rw [hc, Real.mul_rpow hN.le hQ]
    simp only [powZ, hQ0, ↓reduceIte]
    have h1 : 0 < N ^ t := Real.rpow_pos_of_pos hN t
    have h2 : 0 < Qa ^ t := Real.rpow_pos_of_pos hQpos t
    field_simp

/-- **Eq. (15)** (p. 18, l. 587) for an arbitrary `ℓ` with `N Q` integral. If `Q ∈ DS*(V, W)` and
`N Q(v, w) ∈ ℕ` for all `v, w`, where `N = ℓmn`, then
`δ_{p→q}(G^{•nℓ}, H^{•mℓ}) ≤ ‖B_{p→q}(G, H, Q)‖_{p→q}`.  (In the paper `ℓ = ks`, where `k` is
the least common multiple of the denominators of `Q`; see `eq15`.) -/
theorem eq15_of_integral {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) [Nonempty V] [Nonempty W] (ℓ : ℕ)
    (hℓ : 0 < ℓ) {Q : V → W → ℝ} (hQ : IsCoupling Q)
    (hint : ∀ v w, ∃ k : ℕ,
      ((Fintype.card V * (Fintype.card W * ℓ) : ℕ) : ℝ) * Q v w = k) :
    blowupSeq p q G H ℓ ≤ opNorm p q (Bmat p q G H Q) := by
  have hm : 0 < Fintype.card V := Fintype.card_pos
  have hn : 0 < Fintype.card W := Fintype.card_pos
  choose qn hqn using hint
  have hNpos : (0 : ℝ) < ((Fintype.card V * (Fintype.card W * ℓ) : ℕ) : ℝ) := by positivity
  have hrow : ∀ v, ∑ w, qn v w = Fintype.card W * ℓ := by
    intro v
    have : (∑ w, (qn v w : ℝ)) = ((Fintype.card W * ℓ : ℕ) : ℝ) := by
      simp_rw [← hqn, ← Finset.mul_sum, hQ.row_sum v]
      push_cast
      field_simp
    exact_mod_cast this
  have hcol : ∀ w, ∑ v, qn v w = Fintype.card V * ℓ := by
    intro w
    have : (∑ v, (qn v w : ℝ)) = ((Fintype.card V * ℓ : ℕ) : ℝ) := by
      simp_rw [← hqn, ← Finset.mul_sum, hQ.col_sum w]
      push_cast
      field_simp
    exact_mod_cast this
  obtain ⟨π, c, hπ, hcard⟩ := exists_blowup_bij _ _ qn hrow hcol
  -- `N`, the order of both blowups
  have hcardV : Fintype.card (V × Fin (Fintype.card W * ℓ)) =
      Fintype.card V * (Fintype.card W * ℓ) := by simp
  let N : ℝ := ((Fintype.card V * (Fintype.card W * ℓ) : ℕ) : ℝ)
  -- `M_π = A_{G•}^π - A_{H•}` and the block map `(w, j) ↦ (v, w)` for `j ∈ J(v, w)`
  let M := alignedDiff (blowup G (Fintype.card W * ℓ)) (blowup H (Fintype.card V * ℓ)) π
  let b : W × Fin (Fintype.card V * ℓ) → V × W := fun j => (c j, j.1)
  -- Eq. (10)
  have hM : ∀ j j', M j j' = disc G H (b j).1 (b j).2 (b j').1 (b j').2 := by
    intro j j'
    simp [M, alignedDiff, adj_blowup, hπ, disc, b]
  have hbc : ∀ a, (blockCard b a : ℝ) = N * Q a.1 a.2 := by
    rintro ⟨v, w⟩
    rw [hqn]
    exact_mod_cast hcard v w
  have hd : distPQ p q (blowup G (Fintype.card W * ℓ)) (blowup H (Fintype.card V * ℓ)) ≤
      opNorm p q M :=
    ciInf_le ⟨0, by rintro _ ⟨σ, rfl⟩; exact opNorm_nonneg _ _ _⟩ π
  have hMB : opNorm p q M ≤ N ^ kappa p q * opNorm p q (Bmat p q G H Q) := by
    obtain ⟨xt, yt, hxt, hyt, hEq⟩ := exists_abs_dotProduct_mulVec_eq_opNorm hp hq M
    -- the averaged vectors `x, y ∈ ℝ^{V×W}`
    let x : V × W → ℝ := fun a =>
      (∑ j ∈ univ.filter (fun j => b j = a), xt j) / (blockCard b a : ℝ) ^ (1 - p⁻¹.toReal)
    let y : V × W → ℝ := fun a =>
      (∑ j ∈ univ.filter (fun j => b j = a), yt j) /
        (blockCard b a : ℝ) ^ (1 - (ENNReal.conjExponent q)⁻¹.toReal)
    have hx : lpNorm p x ≤ 1 := (lpNorm_average_le hp b xt).trans hxt
    have hy : lpNorm (ENNReal.conjExponent q) y ≤ 1 :=
      (lpNorm_average_le (one_le_conjExponent hq) b yt).trans hyt
    have hconj : 1 - (ENNReal.conjExponent q)⁻¹.toReal = q⁻¹.toReal := by
      rw [inv_conjExponent_toReal hq]; ring
    let D : V × W → V × W → ℝ := fun a a' => disc G H a.1 a.2 a'.1 a'.2
    have hSy : ∀ a, ∑ j ∈ univ.filter (fun j => b j = a), yt j =
        N ^ q⁻¹.toReal * (powZ (Q a.1 a.2) q⁻¹.toReal * y a) := by
      intro a
      simp only [y, hconj]
      exact block_sum_eq b yt a _ hNpos (hQ.nonneg _ _) (hbc a)
    have hSx : ∀ a, ∑ j ∈ univ.filter (fun j => b j = a), xt j =
        N ^ (1 - p⁻¹.toReal) * (powZ (Q a.1 a.2) (1 - p⁻¹.toReal) * x a) :=
      fun a => block_sum_eq b xt a _ hNpos (hQ.nonneg _ _) (hbc a)
    -- grouping the double sum by blocks (using Eq. (10))
    have step1 : yt ⬝ᵥ (M *ᵥ xt) = ∑ a, ∑ a', D a a' *
        (∑ j ∈ univ.filter (fun j => b j = a), yt j) *
        (∑ j ∈ univ.filter (fun j => b j = a'), xt j) := by
      have e1 : ∀ a a', D a a' * (∑ j ∈ univ.filter (fun j => b j = a), yt j) *
          (∑ j ∈ univ.filter (fun j => b j = a'), xt j) =
          ∑ j ∈ univ.filter (fun j => b j = a), ∑ j' ∈ univ.filter (fun j => b j = a'),
            yt j * (M j j' * xt j') := by
        intro a a'
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j' hj' => ?_
        rw [Finset.mem_filter] at hj hj'
        rw [hM, hj.2, hj'.2]
        ring
      simp_rw [e1]
      rw [dotProduct]
      simp_rw [mulVec, dotProduct, Finset.mul_sum]
      rw [← Finset.sum_fiberwise univ b]
      refine Finset.sum_congr rfl fun a _ => ?_
      symm
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_fiberwise univ b _
    have hkappa : N ^ kappa p q = N ^ q⁻¹.toReal * N ^ (1 - p⁻¹.toReal) := by
      rw [← Real.rpow_add hNpos, kappa]; congr 1; ring
    have key : yt ⬝ᵥ (M *ᵥ xt) = N ^ kappa p q * (y ⬝ᵥ (Bmat p q G H Q *ᵥ x)) := by
      rw [step1, hkappa]
      simp_rw [hSy, hSx]
      simp only [dotProduct, mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
      simp only [Bmat, D]
      ring
    rw [← hEq, key, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hNpos _)]
    exact mul_le_mul_of_nonneg_left (abs_dotProduct_mulVec_le_opNorm hp hq _ x y hx hy)
      (Real.rpow_nonneg hNpos.le _)
  unfold blowupSeq deltaPQ
  rw [hcardV]
  calc N ^ (-kappa p q) * distPQ p q (blowup G (Fintype.card W * ℓ))
        (blowup H (Fintype.card V * ℓ))
      ≤ N ^ (-kappa p q) * (N ^ kappa p q * opNorm p q (Bmat p q G H Q)) :=
        mul_le_mul_of_nonneg_left (hd.trans hMB) (Real.rpow_nonneg hNpos.le _)
    _ = opNorm p q (Bmat p q G H Q) := by
        rw [← mul_assoc, ← Real.rpow_add hNpos]; simp

end GsimOT
