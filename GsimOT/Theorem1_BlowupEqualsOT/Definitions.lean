/-
# Definitions for Theorem 1: blowups and optimal transport distances for `p → q`-norms

Paper, Section 1 (paragraphs "The Blowup Construction" and "Fractional Alignments and Optimal
Transport", pp. 1–3, l. 36–96; Eq. (1), Eq. (2)), Section 2 and App. A; `κ = κ_{p→q}` and
`s(n) = n^κ` are in App. B (p. 15, l. 513–514). The paper marks blowups with a bomb symbol, written
`•` here: the blowup `G^{•k}` and the blowup distance `δ^•`; the Lean names use `blowup`.

Throughout, `G` is a graph on `V` (order `m = |V|`) and `H` a graph on `W` (order `n = |W|`).

The shared notions `IsCoupling`, `powZ`, `Bmat`, `deltaOTPQ` (Common/OTDistances.lean) and
`kappa`, `alignedDiff`, `distPQ`, `deltaPQ` (Common/AlignedDistances.lean) are used here.

* `blowup G k`        : the blowup `G^{•k}` on `V × [k]`, where `(v,i) ~ (v',i')` iff `v ~ v'`.
* `blowupSeq p q G H ℓ` : `δ_{p→q}(G^{•nℓ}, H^{•mℓ})`.
* `deltaBlowup p q G H` : `δ^•_{p→q}(G, H) = lim_{ℓ→∞} δ_{p→q}(G^{•nℓ}, H^{•mℓ})`.
-/
import GsimOT.Common.OTDistances
import GsimOT.Common.AlignedDistances

open Finset Filter

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- The blowup `G^{•k}` (p. 1, l. 36–37): vertex set `V × [k]`, `(v, i) ~ (v', i')` iff `v ~ v'`
in `G`. -/
def blowup (G : SimpleGraph V) (k : ℕ) : SimpleGraph (V × Fin k) where
  Adj a b := G.Adj a.1 b.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => G.irrefl h⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : DecidableRel (blowup G k).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj a.1 b.1))

@[simp] lemma adj_blowup (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : V × Fin k) :
    adj (blowup G k) a b = adj G a.1 b.1 := by
  simp only [adj]; rfl

section Blowup

variable (p q : ENNReal) (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
  [DecidableRel H.Adj]

/-- `δ_{p→q}(G^{•nℓ}, H^{•mℓ})` with `m = |V|`, `n = |W|`; both blowups have `ℓmn` vertices. -/
noncomputable def blowupSeq (ℓ : ℕ) : ℝ :=
  deltaPQ p q (blowup G (Fintype.card W * ℓ)) (blowup H (Fintype.card V * ℓ))

/-- The blowup distance `δ^•_{p→q}(G, H) = lim_{ℓ→∞} δ_{p→q}(G^{•nℓ}, H^{•mℓ})` (p. 1, l. 41–42). -/
noncomputable def deltaBlowup : ℝ := limUnder atTop (blowupSeq p q G H)

end Blowup

end GsimOT
