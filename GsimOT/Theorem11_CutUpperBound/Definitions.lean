/-
# Definitions for Theorem 11 (cut distance upper bound)

Paper, Section 3.3 (Theorem 11, p. 10) and Appendix E.2 (pp. 32–44).

* `IsThin a Q π`            : the bijection `π` is `a`-thin w.r.t. `Q ∈ DS(V, W)` (Eq. (23)).
* `ThinPermutationTheorem`  : Theorem 35 = [HOG26, Thm. 1.4] (Haqi, Oveis Gharan), a cited result,
                              used as an explicit hypothesis.
* `radAvg F`                : the average `E_{σ ∼ Unif{±1}^b} F(σ)`.
* `ContractionPrinciple`    : the Talagrand contraction lemma, Lemma 43 [LT91, Thm. 4.12] (with
                              `F = id`), a cited result, used as an explicit hypothesis in Lemma 44
                              (and proved in `ContractionPrinciple.lean`).
* `hSupp v R z`             : the support function `h_R(z) = (1/n) ∑_{i,j} R_ij (⟨z, v_ij⟩)_+` of the
                              zonotope `Z_R` (Eq. (33)).
* `rhoSupp v R R'`          : `ρ(R, R') = sup_{z ∈ B_H} |h_R(z) - h_{R'}(z)|` (Eq. (34)).
* `dn n`                    : `d_n = ⌈2 log n⌉ = ⌈log₂(n²)⌉` (Theorem 39, Lemma 48).
-/
import GsimOT.Common.CutNorm

open Finset

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- `π` is `a`-thin w.r.t. `Q` (Eq. (23), p. 32, l. 1014–1015): for all `U = U_V ⊔ U_W ⊆ V ⊔ W`,
the number of pairs `(v, π v)` with exactly one endpoint in `U` is at most `a` times the `Q`-weight
of all pairs `(v, w)` with exactly one endpoint in `U`. For `X = U_V`, `Y = U_W` these are the
pairs in `(X × Ȳ) ∪ (X̄ × Y)` of Eq. (23). -/
def IsThin (a : ℝ) (Q : V → W → ℝ) (π : V ≃ W) : Prop :=
  ∀ (UV : Finset V) (UW : Finset W),
    (#{v | ¬ ((v ∈ UV) ↔ (π v ∈ UW))} : ℝ) ≤
      a * ∑ v, ∑ w, if ¬ ((v ∈ UV) ↔ (w ∈ UW)) then Q v w else 0

/-- **Theorem 35** ([HOG26, Theorem 1.4]; p. 32, l. 1021–1022), used as a hypothesis (and
derived from [RS14] in `FromThinMatching.lean`): there is an absolute constant
`C_thin > 0` such that every `Q ∈ DS(V, W)` admits an `a`-thin bijection with
`a ≤ C_thin ln(2n) ln ln(4n)`. The Lean statement takes `a = C_thin ln(2n) ln ln(4n)`; since
`Q ≥ 0`, an `a'`-thin bijection with `a' ≤ a` is also `a`-thin. -/
def ThinPermutationTheorem : Prop :=
  ∃ Cthin : ℝ, 0 < Cthin ∧ ∀ (V W : Type) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (Q : V → W → ℝ), IsDS Q → Fintype.card V = Fintype.card W →
    ∃ π : V ≃ W, IsThin (Cthin * Real.log (2 * Fintype.card V) *
      Real.log (Real.log (4 * Fintype.card V))) Q π

/-- The Rademacher average `E_{σ ∼ Unif{±1}^b} F(σ)`. -/
noncomputable def radAvg {b : ℕ} (F : (Fin b → ℝ) → ℝ) : ℝ :=
  (∑ s : Fin b → Bool, F (fun a => if s a then 1 else -1)) / 2 ^ b

/-- **Lemma 43** (Talagrand contraction lemma, [LT91, Theorem 4.12] with `F = id`; p. 38,
l. 1186–1188), used as a hypothesis of Lemma 44 and proved in `ContractionPrinciple.lean`: for a
bounded nonempty `T ⊆ ℝ^b` and contractions, i.e. `1`-Lipschitz maps `φ_a` with `φ_a(0) = 0`,
`E_σ sup_{t ∈ T} |∑_a σ_a φ_a(t_a)| ≤ 2 E_σ sup_{t ∈ T} |∑_a σ_a t_a|`. -/
def ContractionPrinciple : Prop :=
  ∀ (b : ℕ) (T : Set (Fin b → ℝ)), Bornology.IsBounded T → T.Nonempty →
    ∀ φ : Fin b → ℝ → ℝ, (∀ a, LipschitzWith 1 (φ a)) → (∀ a, φ a 0 = 0) →
      radAvg (fun σ => ⨆ t : T, |∑ a, σ a * φ a (t.1 a)|) ≤
        2 * radAvg (fun σ => ⨆ t : T, |∑ a, σ a * t.1 a|)

section Zonotope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support function `h_R(z) = (1/n) ∑_{i,j} R_ij (⟨z, v_ij⟩)_+` of the zonotope `Z_R`
(Eq. (33)). -/
noncomputable def hSupp (v : V → W → E) (R : V → W → ℝ) (z : E) : ℝ :=
  (∑ i, ∑ j, R i j * max (inner ℝ z (v i j)) 0) / Fintype.card V

/-- `ρ(R, R') = sup_{z ∈ B_H} |h_R(z) - h_{R'}(z)|` (Eq. (34)). -/
noncomputable def rhoSupp (v : V → W → E) (R R' : V → W → ℝ) : ℝ :=
  ⨆ z : Metric.closedBall (0 : E) 1, |hSupp v R z.1 - hSupp v R' z.1|

end Zonotope

/-- `d_n = ⌈log₂(n²)⌉ = ⌈2 log n⌉` (Theorem 39). -/
def dn (n : ℕ) : ℕ := Nat.clog 2 (n ^ 2)

end GsimOT
