/-
# Claim 20 and the paper's proof of Eq. (12)

Paper, Appendix B, pp. 17–18, l. 568–591 (converse inequality, Eqs. (12)–(15) and Claim 20).

* `tendsto_opNorm_Bmat_of_supp_eq`: on a fixed support, `Q*_k → Q*_0` implies
  `‖B_{p→q}(G, H, Q*_k)‖ → ‖B_{p→q}(G, H, Q*_0)‖` (proof of Claim 20, l. 576–580).
* `exists_rational_seq_supp_eq`: a sequence of rational couplings `Q*_k` with
  `supp(Q*_k) = supp(Q*_0)` and `Q*_k → Q*_0` (proof of Claim 20, l. 574–576).
* `claim20`: **Claim 20** (l. 573), a rational `Q* ∈ DS*(V, W)` satisfying Eq. (13).
* `exists_denom`, `eq15`: **Eq. (15)**, `δ_{p→q}(G^{•nks}, H^{•mks}) ≤ ‖B_{p→q}(G, H, Q*)‖` for
  every `s ≥ 1`, where `k` clears the denominators of `Q*`.
* `theorem1_of_tendsto`: **Theorem 1 by the paper's argument**: *if* the limit defining
  `δ^•_{p→q}` exists (the paper cites [Gro25] for this, p. 2, l. 44–45), then it equals
  `δ^OT_{p→q}`; the upper bound uses only the subsequence `ℓ = ks`, as in the paper.

Notes on the formalisation.  The paper obtains the rational sequence from "the couplings in
`DS*(V, W)` whose entries outside `S` are zero form a rational polytope" (l. 574–575).  We construct
the sequence explicitly by Birkhoff rounding (`exists_integral_approx_close`, Approximation.lean):
the approximants have denominator `ℓmn`.  The main theorem `theorem1` (Theorem1.lean) uses this
stronger form to prove the existence of the limit instead of citing it; `theorem1_of_tendsto` is
the literal version of the paper's proof.
-/
import GsimOT.Theorem1_BlowupEqualsOT.LowerBound
import GsimOT.Theorem1_BlowupEqualsOT.UpperBound
import GsimOT.Theorem1_BlowupEqualsOT.Approximation
import GsimOT.Common.Attainment

open Finset Filter Topology

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

omit [DecidableEq V] [DecidableEq W] in
/-- Proof of Claim 20 (p. 17, l. 576–580): "On this fixed support, the entries of
`B_{p→q}(G, H, Q*_k)` converge to those of `B_{p→q}(G, H, Q*_0)`, also when `p = 1` or `q = ∞`
[...]. By continuity of the norm, `‖B_{p→q}(G, H, Q*_k)‖ → ‖B_{p→q}(G, H, Q*_0)‖`." -/
theorem tendsto_opNorm_Bmat_of_supp_eq {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {Q₀ : V → W → ℝ} {Q : ℕ → V → W → ℝ} (hsupp : ∀ k v w, Q k v w = 0 ↔ Q₀ v w = 0)
    (hlim : Tendsto Q atTop (𝓝 Q₀)) :
    Tendsto (fun k => opNorm p q (Bmat p q G H (Q k))) atTop
      (𝓝 (opNorm p q (Bmat p q G H Q₀))) := by
  -- the sequence converges within the matrices with the same zero set
  have hlim' : Tendsto Q atTop (𝓝[{Q' | ∀ v w, Q' v w = 0 ↔ Q₀ v w = 0}] Q₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k => hsupp k⟩
  -- entrywise convergence of `B_{p→q}` (`tendsto_powZ_apply`)
  have hB : Tendsto (fun k => Bmat p q G H (Q k)) atTop (𝓝 (Bmat p q G H Q₀)) := by
    refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => ?_
    exact (((tendsto_powZ_apply Q₀ a.1 a.2 q⁻¹.toReal).comp hlim').mul tendsto_const_nhds).mul
      ((tendsto_powZ_apply Q₀ b.1 b.2 (1 - p⁻¹.toReal)).comp hlim')
  exact ((continuous_opNorm (ι := V × W) (κ := V × W) hp hq).tendsto _).comp hB

omit [DecidableEq V] [DecidableEq W] in
/-- Proof of Claim 20 (p. 17, l. 574–576): for every coupling `Q*_0` there is a sequence of
couplings `Q*_k` with rational entries, `supp(Q*_k) = supp(Q*_0)` and `Q*_k → Q*_0`. -/
theorem exists_rational_seq_supp_eq [Nonempty V] [Nonempty W] {Q₀ : V → W → ℝ}
    (hQ₀ : IsCoupling Q₀) :
    ∃ Q : ℕ → V → W → ℝ, (∀ k, IsCoupling (Q k)) ∧ (∀ k v w, ∃ r : ℚ, Q k v w = r) ∧
      (∀ k v w, Q k v w = 0 ↔ Q₀ v w = 0) ∧ Tendsto Q atTop (𝓝 Q₀) := by
  have hδ : ∀ k : ℕ, (0 : ℝ) < 1 / (k + 1) := fun k => by positivity
  choose L hL using fun k : ℕ => exists_integral_approx_close hQ₀ (hδ k)
  choose Q hQ hint hsupp hclose using fun k => hL k (max (L k) 1) (le_max_left _ _)
  refine ⟨Q, hQ, fun k v w => ?_, hsupp, ?_⟩
  · -- `Q k v w = c / N` with `N = mn · max (L k) 1 > 0`
    obtain ⟨c, hc⟩ := hint k v w
    have hN : (0 : ℝ) < ((Fintype.card V * (Fintype.card W * max (L k) 1) : ℕ) : ℝ) := by
      have : 0 < Fintype.card V * (Fintype.card W * max (L k) 1) :=
        Nat.mul_pos Fintype.card_pos (Nat.mul_pos Fintype.card_pos (by omega))
      exact_mod_cast this
    refine ⟨(c : ℚ) / ((Fintype.card V * (Fintype.card W * max (L k) 1) : ℕ) : ℚ), ?_⟩
    rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, eq_div_iff hN.ne', mul_comm]
    exact hc
  · rw [tendsto_pi_nhds]
    intro v
    rw [tendsto_pi_nhds]
    intro w
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
    refine ⟨K, fun k hk => ?_⟩
    rw [Real.dist_eq]
    refine (hclose k v w).trans (lt_of_le_of_lt ?_ hK)
    gcongr

omit [DecidableEq V] [DecidableEq W] in
/-- **Claim 20** (pp. 17–18, l. 573–581). For every `ε > 0` there is a coupling `Q* ∈ DS*(V, W)`
with rational entries such that `‖B_{p→q}(G, H, Q*)‖ ≤ min_{Q*_0} ‖B_{p→q}(G, H, Q*_0)‖ + ε`
(Eq. (13)). As in the paper, the proof starts from a minimiser `Q*_0` (`exists_deltaOTPQ_eq`,
Appendix A), approximates it on its support by rational couplings and uses continuity. -/
theorem claim20 {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) [Nonempty V] [Nonempty W] {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Q, IsCoupling Q ∧ (∀ v w, ∃ r : ℚ, Q v w = r) ∧
      opNorm p q (Bmat p q G H Q) ≤ deltaOTPQ p q G H + ε := by
  obtain ⟨Q₀, hQ₀, hmin⟩ := exists_deltaOTPQ_eq G H hp hq
  obtain ⟨Q, hQ, hrat, hsupp, hlim⟩ := exists_rational_seq_supp_eq hQ₀
  have hT := tendsto_opNorm_Bmat_of_supp_eq (G := G) (H := H) hp hq hsupp hlim
  obtain ⟨k, hk⟩ := (hT.eventually (gt_mem_nhds (lt_add_of_pos_right
    (opNorm p q (Bmat p q G H Q₀)) hε))).exists
  exact ⟨Q k, hQ k, hrat k, by rw [← hmin]; exact hk.le⟩

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- A rational matrix has a common denominator `k ≥ 1`: `k · Q(v, w) ∈ ℕ` for nonnegative `Q`
(the paper takes `k` to be the least common multiple of the denominators, p. 18, l. 584–585). -/
lemma exists_denom [Finite V] [Finite W] {Q : V → W → ℝ} (hQ : ∀ v w, 0 ≤ Q v w)
    (hrat : ∀ v w, ∃ r : ℚ, Q v w = r) :
    ∃ k : ℕ, 0 < k ∧ ∀ v w, ∃ c : ℕ, (k : ℝ) * Q v w = c := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite W
  choose r hr using hrat
  refine ⟨∏ x : V × W, (r x.1 x.2).den, Finset.prod_pos fun x _ => (r x.1 x.2).pos, fun v w => ?_⟩
  set k := ∏ x : V × W, (r x.1 x.2).den
  have hdvd : (r v w).den ∣ k := Finset.dvd_prod_of_mem (fun x : V × W => (r x.1 x.2).den)
    (mem_univ (v, w))
  obtain ⟨d, hd⟩ := hdvd
  -- `k · r = d · num`, a nonnegative integer
  have hnum : 0 ≤ (r v w).num := by
    have : (0 : ℝ) ≤ (r v w : ℝ) := hr v w ▸ hQ v w
    exact Rat.num_nonneg.2 (by exact_mod_cast this)
  refine ⟨d * (r v w).num.toNat, ?_⟩
  have hcast : (((r v w).num.toNat : ℕ) : ℝ) = ((r v w).num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  have hden : ((r v w).den : ℝ) ≠ 0 := by exact_mod_cast (r v w).den_nz
  rw [hr v w, hd]
  push_cast
  rw [hcast, Rat.cast_def]
  field_simp

/-- **Eq. (15)** (p. 18, l. 584–587). If `Q* ∈ DS*(V, W)` and `k · Q*(v, w) ∈ ℕ` for all `v, w`
(e.g. `k` the least common multiple of the denominators), then for every `s ≥ 1`,
`δ_{p→q}(G^{•nks}, H^{•mks}) ≤ ‖B_{p→q}(G, H, Q*)‖_{p→q}`. -/
theorem eq15 {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) [Nonempty V] [Nonempty W]
    {Q : V → W → ℝ} (hQ : IsCoupling Q) {k : ℕ} (hk : 0 < k)
    (hint : ∀ v w, ∃ c : ℕ, (k : ℝ) * Q v w = c) {s : ℕ} (hs : 0 < s) :
    blowupSeq p q G H (k * s) ≤ opNorm p q (Bmat p q G H Q) := by
  refine eq15_of_integral hp hq (k * s) (Nat.mul_pos hk hs) hQ fun v w => ?_
  obtain ⟨c, hc⟩ := hint v w
  refine ⟨Fintype.card V * Fintype.card W * s * c, ?_⟩
  push_cast
  rw [← hc]
  ring

/-- **Theorem 1, following the paper's proof literally** (Appendix B). *Assuming* that the limit
defining `δ^•_{p→q}(G, H)` exists (the paper cites [Gro25], p. 2, l. 44–45), it equals
`δ^OT_{p→q}(G, H)`. Eq. (8): every term is at least `δ^OT` (`deltaOTPQ_le_blowupSeq`, via
Eqs. (9)–(11)). Eqs. (12), (14): for every `ε > 0`, Claim 20 gives a rational `Q*`, and Eq. (15)
bounds the subsequence `ℓ = ks`, whose limit is the same. The main theorem `theorem1` proves the
existence of the limit instead of assuming it. -/
theorem theorem1_of_tendsto {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) [Nonempty V] [Nonempty W]
    {L : ℝ} (hL : Tendsto (blowupSeq p q G H) atTop (𝓝 L)) :
    deltaBlowup p q G H = deltaOTPQ p q G H := by
  rw [deltaBlowup, hL.limUnder_eq]
  apply le_antisymm
  · -- Eqs. (12), (14), (15)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨Q, hQ, hrat, hle⟩ := claim20 (G := G) (H := H) hp hq hε
    obtain ⟨k, hk, hint⟩ := exists_denom hQ.nonneg hrat
    have hsub : Tendsto (fun s => blowupSeq p q G H (k * s)) atTop (𝓝 L) :=
      hL.comp (tendsto_id.const_mul_atTop' hk)
    have hbound : ∀ᶠ s in atTop, blowupSeq p q G H (k * s) ≤ deltaOTPQ p q G H + ε :=
      eventually_atTop.2 ⟨1, fun s hs => (eq15 hp hq hQ hk hint hs).trans hle⟩
    exact le_of_tendsto hsub hbound
  · -- Eq. (8)
    exact ge_of_tendsto hL (eventually_atTop.2 ⟨1, fun ℓ hℓ =>
      deltaOTPQ_le_blowupSeq (G := G) (H := H) hp hq ℓ hℓ⟩)

end GsimOT
