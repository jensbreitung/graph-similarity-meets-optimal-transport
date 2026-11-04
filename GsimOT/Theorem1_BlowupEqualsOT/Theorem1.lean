/-
# Theorem 1: blowup distances equal optimal transport distances

Paper, Section 1, Theorem 1 (p. 3, l. 92): For all `1 ≤ p, q ≤ ∞`, `δ^•_{p→q} = δ^OT_{p→q}`.
(The paper marks blowups with a bomb symbol, written `•` here: `G^{•k}`, `δ^•`; the Lean names
use `blowup`.)

Proof (Appendix B, pp. 15–20, l. 511–638).  Eq. (8) (`deltaOTPQ_le_blowupSeq`, via Eqs. (9)–(11)):
every term of the blowup sequence is at least `δ^OT`.  Eq. (12): for every `ε > 0` take a
near-optimal coupling, approximate it by couplings with denominator `N = ℓmn`
(`exists_integral_approx`, a strengthened Claim 20) and apply Eq. (15) (`eq15_of_integral`, the bound for every
`ℓ` with `N Q` integral).

Formalisation note.  The paper uses that the limit defining `δ^•` exists (it cites [Gro25] for
this, p. 2, l. 44–45) and proves Eq. (15) along the subsequence `ℓ = ks`.  Since our approximation
step works for *every* sufficiently large `ℓ`, we obtain the convergence of the whole sequence, so
the existence of the limit is proved here rather than assumed.  The literal version of the paper's
argument (Claim 20 from a minimiser, Eq. (15) for `ℓ = ks`, existence of the limit as a
hypothesis) is `theorem1_of_tendsto` in Claim20.lean.
-/
import GsimOT.Theorem1_BlowupEqualsOT.LowerBound
import GsimOT.Theorem1_BlowupEqualsOT.UpperBound
import GsimOT.Theorem1_BlowupEqualsOT.Approximation
import GsimOT.Theorem1_BlowupEqualsOT.Claim20

open Finset Filter Topology

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

/-- The uniform coupling `Q(v, w) = 1/(mn)`; in particular `DS*(V, W) ≠ ∅`. -/
lemma isCoupling_uniform [Nonempty V] [Nonempty W] :
    IsCoupling (fun (_ : V) (_ : W) => 1 / ((Fintype.card V : ℝ) * Fintype.card W)) where
  nonneg _ _ := by positivity
  row_sum _ := by
    have : (Fintype.card W : ℝ) ≠ 0 := by positivity
    have : (Fintype.card V : ℝ) ≠ 0 := by positivity
    simp [Finset.card_univ]
  col_sum _ := by
    have : (Fintype.card W : ℝ) ≠ 0 := by positivity
    have : (Fintype.card V : ℝ) ≠ 0 := by positivity
    simp [Finset.card_univ]; field_simp

/-- **Theorem 1 (convergence).** `δ_{p→q}(G^{•nℓ}, H^{•mℓ}) → δ^OT_{p→q}(G, H)` as `ℓ → ∞`;
in particular the limit defining `δ^•_{p→q}` exists. -/
theorem theorem1_tendsto {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) [Nonempty V] [Nonempty W] :
    Tendsto (blowupSeq p q G H) atTop (𝓝 (deltaOTPQ p q G H)) := by
  have hne : Nonempty {Q : V → W → ℝ // IsCoupling Q} := ⟨⟨_, isCoupling_uniform⟩⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- a near-optimal coupling
  obtain ⟨Q, hQ⟩ := exists_lt_of_ciInf_lt
    (f := fun Q : {Q : V → W → ℝ // IsCoupling Q} => opNorm p q (Bmat p q G H Q.1))
    (show deltaOTPQ p q G H < deltaOTPQ p q G H + ε / 2 by linarith)
  -- approximations with denominator `ℓmn`
  obtain ⟨L₀, hL₀⟩ := exists_integral_approx (G := G) (H := H) hp hq Q.2 (half_pos hε)
  refine ⟨max L₀ 1, fun ℓ hℓ => ?_⟩
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le one_pos (le_of_max_le_right hℓ)
  obtain ⟨Q', hQ', hint, hle⟩ := hL₀ ℓ (le_of_max_le_left hℓ)
  have hup := eq15_of_integral (G := G) (H := H) hp hq ℓ hℓ0 hQ' hint
  have hlow := deltaOTPQ_le_blowupSeq (G := G) (H := H) hp hq ℓ hℓ0
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Theorem 1** (p. 3, l. 92). For all `1 ≤ p, q ≤ ∞`, `δ^•_{p→q}(G, H) = δ^OT_{p→q}(G, H)`. -/
theorem theorem1 {p q : ENNReal} (hp : 1 ≤ p) (hq : 1 ≤ q) [Nonempty V] [Nonempty W] :
    deltaBlowup p q G H = deltaOTPQ p q G H :=
  (theorem1_tendsto hp hq).limUnder_eq

end GsimOT
