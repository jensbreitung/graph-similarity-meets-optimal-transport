/-
# Lemma 30: dependent rounding of Chekuri, Vondrák and Zenklusen (external result)

Paper, App. D.2, Lemma 30 ([CVZ11, Theorem 1.1]) (p. 29, l. 895–898):
Let `q` be a point in the bipartite matching polytope and `γ ∈ (0, 1/2]`.  Then there is a random
matching `M` with `E[1_M] = (1 - γ) q` such that, for every linear statistic
`Z := ∑_e α_e 1[e ∈ M]` with `α_e ∈ [0, 1]`, every `μ ≥ E[Z]` with `μ > 0`, and every `τ ≥ 2`,
`Pr(Z ≥ τ μ) ≤ exp(-μ γ (2τ - 3) / 20)`                                           (Eq. (19))

This is a cited result from the literature and is **not** proved in the paper.  We therefore do
not prove it either; instead we state it as a proposition `CVZRounding` which appears as an
explicit hypothesis of Theorem 9 (and of Lemma 31 and Proposition 32).  No `axiom` is introduced.

Formalisation notes.
* We only need the special case where `q = Q` is a doubly stochastic matrix (a point of the
  perfect matching polytope), which makes the hypothesis weaker (hence safer) than the general
  statement.
* A "random matching" is a finitely supported probability distribution `p` on the finite set
  `Finset (V × W)`, all of whose atoms are matchings.  Expectations and probabilities are the
  corresponding finite sums.
* Apart from this specialisation, the statement is reproduced as given in the paper.
-/
import GsimOT.Common.Basic

open Finset

namespace GsimOT

/-- `M ⊆ V × W` is a matching: no two of its pairs share a vertex. -/
def IsMatching {V W : Type*} (M : Finset (V × W)) : Prop :=
  ∀ e ∈ M, ∀ e' ∈ M, (e.1 = e'.1 ↔ e.2 = e'.2)

/-- The statement of Lemma 30 (CVZ11, Theorem 1.1) specialised to doubly stochastic matrices.

For every `Q ∈ DS(V, W)` and `γ ∈ (0, 1/2]` there is a probability distribution `p` on
subsets `M ⊆ V × W` such that
* every `M` with `p M ≠ 0` is a matching,
* `Pr(e ∈ M) = (1 - γ) Q(e)` for every pair `e`,
* the tail bound (19) holds for every linear statistic with coefficients in `[0, 1]`. -/
def CVZRounding : Prop :=
  ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (Q : V → W → ℝ), IsDS Q → ∀ γ : ℝ, 0 < γ → γ ≤ 1 / 2 →
    ∃ p : Finset (V × W) → ℝ,
      (∀ M, 0 ≤ p M) ∧
      (∑ M, p M = 1) ∧
      (∀ M, p M ≠ 0 → IsMatching M) ∧
      (∀ e : V × W, ∑ M, p M * (if e ∈ M then 1 else 0) = (1 - γ) * Q e.1 e.2) ∧
      (∀ α : V × W → ℝ, (∀ e, 0 ≤ α e ∧ α e ≤ 1) →
        ∀ μ : ℝ, 0 < μ → ∑ M, p M * (∑ e ∈ M, α e) ≤ μ →
        ∀ τ : ℝ, 2 ≤ τ →
          ∑ M, (if τ * μ ≤ ∑ e ∈ M, α e then p M else 0) ≤
            Real.exp (-(μ * γ * (2 * τ - 3)) / 20))

end GsimOT
