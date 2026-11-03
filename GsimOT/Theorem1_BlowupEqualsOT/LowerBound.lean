/-
# The lower bound `δ^• ≥ δ^OT` (Eqs. (8)–(11))

Paper, App. B, first part of the proof of Theorem 1 (pp. 15–17, l. 516–567).
The theorem `eq13` is Eq. (11).
-/
import GsimOT.Theorem1_BlowupEqualsOT.BlockNorms
import GsimOT.Theorem1_BlowupEqualsOT.Definitions

open Finset

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-! ### Auxiliary identities -/

/-- Summing a function of the block `b j` over `β` is summing over `α` weighted by block sizes. -/
lemma sum_comp_eq_sum_blockCard {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (b : β → α) (f : α → ℝ) : ∑ j, f (b j) = ∑ a, (blockCard b a : ℝ) * f a := by
  rw [← Finset.sum_fiberwise' univ b f]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [blockCard, Finset.sum_const, nsmul_eq_mul]

/-- `t / t^s = t^{1-s}` for `t ≥ 0`, with the convention `0^a = 0` on the right-hand side. -/
lemma div_rpow_self_eq_powZ {t : ℝ} (ht : 0 ≤ t) (s : ℝ) : t / t ^ s = powZ t (1 - s) := by
  rcases ht.eq_or_lt with h | h
  · subst h; simp [powZ]
  · simp only [powZ, h.ne', ite_false]
    rw [Real.rpow_sub h, Real.rpow_one]

/-- `t^s = N^s (t/N)^s` (with the convention `0^s = 0`). -/
lemma powZ_eq_rpow_mul_powZ_div {t N : ℝ} (ht : 0 ≤ t) (hN : 0 < N) (s : ℝ) :
    powZ t s = N ^ s * powZ (t / N) s := by
  rcases ht.eq_or_lt with h | h
  · subst h; simp [powZ]
  · simp only [powZ, h.ne', (div_pos h hN).ne', ite_false]
    rw [Real.div_rpow ht hN.le]
    field_simp

/-! ### The coupling `Q(v,w) = |J(v,w)|/N` -/

section Coupling

variable {k K : ℕ}

/-- The block map `b(w, j) = (v(w,j), w)` on `W × [ℓm]`, where `v(w,j)` is the unique `v` with
`j ∈ J(v, w)`, i.e. `π⁻¹(w, j) ∈ {v} × [ℓn]`.  The block of `(v, w)` is `{w} × J(v, w)`. -/
def blockMap (π : V × Fin K ≃ W × Fin k) (j : W × Fin k) : V × W := ((π.symm j).1, j.1)

/-- `Q(v, w) := |J(v, w)| / N`. -/
noncomputable def couplingOf (π : V × Fin K ≃ W × Fin k) (N : ℝ) (v : V) (w : W) : ℝ :=
  (blockCard (blockMap π) (v, w) : ℝ) / N

/-- `∑_{w} |J(v, w)| = |[ℓn]|`, since `⋃_w I(v,w) = [ℓn]` and `|I(v,w)| = |J(v,w)|`. -/
lemma sum_blockCard_row (π : V × Fin K ≃ W × Fin k) (v : V) :
    ∑ w, (blockCard (blockMap π) (v, w) : ℝ) = K := by
  have h1 : ∀ w, (blockCard (blockMap π) (v, w) : ℝ) =
      ∑ j, if blockMap π j = (v, w) then (1 : ℝ) else 0 := by
    intro w; simp [blockCard, Finset.sum_boole]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ j : W × Fin k, (∑ w, if blockMap π j = (v, w) then (1 : ℝ) else 0) =
      if (π.symm j).1 = v then 1 else 0 := by
    intro j
    simp only [blockMap, Prod.mk.injEq]
    by_cases hv : (π.symm j).1 = v
    · simp [hv]
    · simp [hv]
  simp_rw [h2]
  rw [Equiv.sum_comp π.symm (fun i => if i.1 = v then (1 : ℝ) else 0), Fintype.sum_prod_type]
  simp [apply_ite (fun s : Finset _ => ((#s : ℕ) : ℝ))]

/-- `∑_{v} |J(v, w)| = |[ℓm]|`, since `⋃_v J(v,w) = [ℓm]`. -/
lemma sum_blockCard_col (π : V × Fin K ≃ W × Fin k) (w : W) :
    ∑ v, (blockCard (blockMap π) (v, w) : ℝ) = k := by
  have h1 : ∀ v, (blockCard (blockMap π) (v, w) : ℝ) =
      ∑ j, if blockMap π j = (v, w) then (1 : ℝ) else 0 := by
    intro v; simp [blockCard, Finset.sum_boole]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ j : W × Fin k, (∑ v, if blockMap π j = (v, w) then (1 : ℝ) else 0) =
      if j.1 = w then 1 else 0 := by
    intro j
    simp only [blockMap, Prod.mk.injEq]
    by_cases hw : j.1 = w
    · simp [hw]
    · simp [hw]
  simp_rw [h2]
  rw [Fintype.sum_prod_type]
  simp [apply_ite (fun s : Finset _ => ((#s : ℕ) : ℝ))]

/-- `Q ∈ DS*(V, W)` (proof of Eq. (9)): `∑_{w'} Q(v,w') = ℓn/N = 1/m` and
`∑_{v'} Q(v',w) = ℓm/N = 1/n`. -/
lemma isCoupling_couplingOf [Nonempty V] [Nonempty W] (ℓ : ℕ) (hℓ : 0 < ℓ)
    (π : V × Fin (Fintype.card W * ℓ) ≃ W × Fin (Fintype.card V * ℓ)) :
    IsCoupling (couplingOf π ((Fintype.card V * (Fintype.card W * ℓ) : ℕ) : ℝ)) := by
  have hm : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hl : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  refine ⟨fun v w => ?_, fun v => ?_, fun w => ?_⟩
  · unfold couplingOf; positivity
  · unfold couplingOf
    rw [← Finset.sum_div, sum_blockCard_row]
    push_cast
    field_simp
  · unfold couplingOf
    rw [← Finset.sum_div, sum_blockCard_col]
    push_cast
    field_simp

end Coupling

/-- **Eq. (10)** (p. 15, l. 528). For `j ∈ J(v, w)` and `j' ∈ J(v', w')`,
`M_π((w,j),(w',j')) = D(v, w, v', w')`, i.e. `M_π(j, j') = D(b j, b j')`. -/
lemma alignedDiff_blowup_eq_disc {ℓ : ℕ}
    (π : V × Fin (Fintype.card W * ℓ) ≃ W × Fin (Fintype.card V * ℓ))
    (j j' : W × Fin (Fintype.card V * ℓ)) :
    alignedDiff (blowup G (Fintype.card W * ℓ)) (blowup H (Fintype.card V * ℓ)) π j j' =
      disc G H (blockMap π j).1 (blockMap π j).2 (blockMap π j').1 (blockMap π j').2 := by
  simp [alignedDiff, disc, blockMap]

/-- **Eq. (11)** (p. 15, l. 535) for nonempty `V`, `W`. For every bijection `π` between the
blowups `G^{•nℓ}` and `H^{•mℓ}` the coupling `Q(v,w) = |J(v,w)|/N` satisfies
`‖M_π‖_{p→q} ≥ N^κ ‖B_{p→q}(G, H, Q)‖_{p→q}`, where `N = ℓmn`. -/
theorem eq13 [Nonempty V] [Nonempty W] {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (ℓ : ℕ) (hℓ : 0 < ℓ)
    (π : V × Fin (Fintype.card W * ℓ) ≃ W × Fin (Fintype.card V * ℓ)) :
    ∃ Q, IsCoupling Q ∧
      ((Fintype.card V * (Fintype.card W * ℓ) : ℕ) : ℝ) ^ kappa p q *
          opNorm p q (Bmat p q G H Q) ≤
        opNorm p q (alignedDiff (blowup G (Fintype.card W * ℓ))
          (blowup H (Fintype.card V * ℓ)) π) := by
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ((Fintype.card V * (Fintype.card W * ℓ) : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  rw [← hNdef]
  have hN : 0 < N := by
    rw [hNdef]
    have := Fintype.card_pos (α := V)
    have := Fintype.card_pos (α := W)
    positivity
  refine ⟨couplingOf π N, hNdef ▸ isCoupling_couplingOf ℓ hℓ π, ?_⟩
  -- Lemma 19: optimal test vectors `x, y` for `B`.
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    exists_abs_dotProduct_mulVec_eq_opNorm hp hq (Bmat p q G H (couplingOf π N))
  have hq' := one_le_conjExponent hq
  -- the spread vectors `x̃`, `ỹ`
  obtain ⟨c, hc⟩ : ∃ c, c = blockCard (blockMap π) := ⟨_, rfl⟩
  have hx' := lpNorm_spread_le hp (blockMap π) x
  have hy' := lpNorm_spread_le hq' (blockMap π) y
  rw [← hc] at hx' hy'
  have key := abs_dotProduct_mulVec_le_opNorm hp hq
    (alignedDiff (blowup G (Fintype.card W * ℓ)) (blowup H (Fintype.card V * ℓ)) π)
    _ _ (hx'.trans hx) (hy'.trans hy)
  refine le_trans (le_of_eq ?_) key
  rw [← hxy, ← abs_of_nonneg (Real.rpow_nonneg hN.le (kappa p q)), ← abs_mul]
  congr 1
  -- the chain of equalities at the end of the proof of Eq. (11)
  rw [inv_conjExponent_toReal hq]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, alignedDiff_blowup_eq_disc]
  obtain ⟨b, hb⟩ : ∃ b, b = blockMap π := ⟨_, rfl⟩
  rw [← hb] at hc ⊢
  have hcQ : ∀ a : V × W, couplingOf π N a.1 a.2 = (c a : ℝ) / N := by
    intro a; rw [couplingOf, hc, hb]
  have inner : ∀ j : W × Fin (Fintype.card V * ℓ),
      (∑ j', y (b j) / (c (b j) : ℝ) ^ (1 - q⁻¹.toReal) *
        (disc G H (b j).1 (b j).2 (b j').1 (b j').2 * (x (b j') / (c (b j') : ℝ) ^ p⁻¹.toReal))) =
      ∑ a', (c a' : ℝ) * (y (b j) / (c (b j) : ℝ) ^ (1 - q⁻¹.toReal) *
        (disc G H (b j).1 (b j).2 a'.1 a'.2 * (x a' / (c a' : ℝ) ^ p⁻¹.toReal))) := by
    intro j
    rw [hc, hb]
    exact sum_comp_eq_sum_blockCard (blockMap π) (fun a' => y (blockMap π j) /
      (blockCard (blockMap π) (blockMap π j) : ℝ) ^ (1 - q⁻¹.toReal) *
        (disc G H (blockMap π j).1 (blockMap π j).2 a'.1 a'.2 *
          (x a' / (blockCard (blockMap π) a' : ℝ) ^ p⁻¹.toReal)))
  rw [Finset.sum_congr rfl (fun j _ => inner j)]
  rw [hc, hb, sum_comp_eq_sum_blockCard (blockMap π) (fun a => ∑ a', (blockCard (blockMap π) a' : ℝ) *
      (y a / (blockCard (blockMap π) a : ℝ) ^ (1 - q⁻¹.toReal) *
        (disc G H a.1 a.2 a'.1 a'.2 * (x a' / (blockCard (blockMap π) a' : ℝ) ^ p⁻¹.toReal))))]
  rw [← hb, ← hc]
  simp only [Finset.mul_sum, Bmat]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [hcQ a, hcQ a']
  have hca : (0 : ℝ) ≤ c a := Nat.cast_nonneg _
  have hca' : (0 : ℝ) ≤ c a' := Nat.cast_nonneg _
  have e1 : (c a : ℝ) / (c a : ℝ) ^ (1 - q⁻¹.toReal) = N ^ q⁻¹.toReal * powZ (c a / N) q⁻¹.toReal := by
    rw [div_rpow_self_eq_powZ hca, sub_sub_cancel, powZ_eq_rpow_mul_powZ_div hca hN]
  have e2 : (c a' : ℝ) / (c a' : ℝ) ^ p⁻¹.toReal =
      N ^ (1 - p⁻¹.toReal) * powZ (c a' / N) (1 - p⁻¹.toReal) := by
    rw [div_rpow_self_eq_powZ hca', powZ_eq_rpow_mul_powZ_div hca' hN]
  have hk : N ^ kappa p q = N ^ q⁻¹.toReal * N ^ (1 - p⁻¹.toReal) := by
    rw [← Real.rpow_add hN, kappa]; ring_nf
  symm
  calc (c a : ℝ) * ((c a' : ℝ) * (y a / (c a : ℝ) ^ (1 - q⁻¹.toReal) *
        (disc G H a.1 a.2 a'.1 a'.2 * (x a' / (c a' : ℝ) ^ p⁻¹.toReal))))
      = y a * ((c a : ℝ) / (c a : ℝ) ^ (1 - q⁻¹.toReal)) * disc G H a.1 a.2 a'.1 a'.2 *
          ((c a' : ℝ) / (c a' : ℝ) ^ p⁻¹.toReal) * x a' := by ring
    _ = _ := by rw [e1, e2, hk]; ring

omit [DecidableEq V] [DecidableEq W] in
/-- **Eqs. (8), (9)** (p. 15, l. 517–520). For every `ℓ ≥ 1`,
`δ^OT_{p→q}(G, H) ≤ δ_{p→q}(G^{•nℓ}, H^{•mℓ})`. -/
theorem deltaOTPQ_le_blowupSeq {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) [Nonempty V]
    [Nonempty W] (ℓ : ℕ) (hℓ : 0 < ℓ) :
    deltaOTPQ p q G H ≤ blowupSeq p q G H ℓ := by
  classical
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ((Fintype.card V * (Fintype.card W * ℓ) : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hN : 0 < N := by
    rw [hNdef]
    have := Fintype.card_pos (α := V)
    have := Fintype.card_pos (α := W)
    positivity
  have hcard : (Fintype.card (V × Fin (Fintype.card W * ℓ)) : ℝ) = N := by
    rw [hNdef, Fintype.card_prod, Fintype.card_fin]
  have hbdd : BddBelow (Set.range fun Q : {Q : V → W → ℝ // IsCoupling Q} =>
      opNorm p q (Bmat p q G H Q.1)) :=
    ⟨0, by rintro _ ⟨Q, rfl⟩; exact opNorm_nonneg _ _ _⟩
  have : Nonempty (V × Fin (Fintype.card W * ℓ) ≃ W × Fin (Fintype.card V * ℓ)) :=
    ⟨Fintype.equivOfCardEq (by simp [Fintype.card_prod]; ring)⟩
  -- Eq. (9): `d_{p→q}(G^•, H^•) ≥ N^κ δ^OT_{p→q}(G, H)`
  have h11 : N ^ kappa p q * deltaOTPQ p q G H ≤
      distPQ p q (blowup G (Fintype.card W * ℓ)) (blowup H (Fintype.card V * ℓ)) := by
    refine le_ciInf fun π => ?_
    obtain ⟨Q, hQ, hle⟩ := eq13 (G := G) (H := H) hp hq ℓ hℓ π
    rw [← hNdef] at hle
    refine le_trans ?_ hle
    exact mul_le_mul_of_nonneg_left (ciInf_le hbdd ⟨Q, hQ⟩) (Real.rpow_nonneg hN.le _)
  unfold blowupSeq deltaPQ
  rw [hcard]
  calc deltaOTPQ p q G H = N ^ (-kappa p q) * (N ^ kappa p q * deltaOTPQ p q G H) := by
        rw [← mul_assoc, ← Real.rpow_add hN, neg_add_cancel, Real.rpow_zero, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h11 (Real.rpow_nonneg hN.le _)

end GsimOT
