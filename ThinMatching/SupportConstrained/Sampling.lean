/-
# The random sampling step of Algorithm 1 and the hypothesis replacing Lemma 3.6

[HOG26], Section 3.  For a weighted graph `y` on a finite vertex type `W` and `α : ℕ`, Algorithm 1
samples `α` copies of every edge `e` independently with probability `y_e`.  We model this as the
product space `prob (sampleProb y α)` of independent coins indexed by `Sym2 W × Fin α`
(coin `(e, k)` = "the `k`-th copy of `e` is sampled").  Unordered pairs `s(v, v)` on the diagonal
have weight `y(v, v) = 0` and are therefore never sampled (up to a null event).

* `edgeW y e`        : the weight `y_e` of an unordered pair `e : Sym2 W`;
* `edgeTotal y`      : `y(E) = ∑_e y_e`;
* `copies ω e`       : the number of sampled copies of `e` (the multiplicity of `e` in `Y`);
* `sampleCut ω S`    : `Y(δ(S))`, counted with multiplicity;
* `sampleGraph ω`    : the simple graph underlying the sample `Y`;
* `Lemma36`          : the statement of Lemma 3.6 (proof omitted in the paper), used as a
                       hypothesis.
-/
import ThinMatching.Basic
import ThinMatching.SupportConstrained.Prob

open Finset

namespace ThinMatching

section Sampling

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The weight `y_e` of the unordered pair `e`. -/
def edgeW (y : WGraph W) : Sym2 W → ℝ := Sym2.lift ⟨y.w, y.symm⟩

omit [Fintype W] [DecidableEq W] in
@[simp] theorem edgeW_mk (y : WGraph W) (u v : W) : edgeW y s(u, v) = y.w u v := rfl

omit [Fintype W] [DecidableEq W] in
theorem edgeW_nonneg (y : WGraph W) (e : Sym2 W) : 0 ≤ edgeW y e := by
  induction e using Sym2.ind with
  | _ u v => exact y.nonneg u v

/-- `y(E)`, the total weight of the edges. -/
def edgeTotal (y : WGraph W) : ℝ := ∑ e : Sym2 W, edgeW y e

/-- Summing a symmetric function with zero diagonal over unordered pairs counts every ordered pair
`(u, v)` with weight `1/2`. -/
theorem sum_sym2_lift (f : W → W → ℝ) (hf : ∀ u v, f u v = f v u) (hd : ∀ v, f v v = 0) :
    ∑ e : Sym2 W, Sym2.lift ⟨f, hf⟩ e = (∑ u, ∑ v, f u v) / 2 := by
  have hfib : ∑ e : Sym2 W, ∑ p ∈ (Finset.univ : Finset (W × W)) with
      s(p.1, p.2) = e, f p.1 p.2 = ∑ p : W × W, f p.1 p.2 :=
    Finset.sum_fiberwise (Finset.univ : Finset (W × W)) (fun p : W × W => s(p.1, p.2))
      (fun p : W × W => f p.1 p.2)
  rw [eq_div_iff (two_ne_zero' ℝ), ← Finset.sum_product', Finset.univ_product_univ, ← hfib,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.lift_mk]
    by_cases hab : a = b
    · subst hab
      have : (Finset.univ.filter fun p : W × W => s(p.1, p.2) = s(a, a)) = {(a, a)} := by
        ext ⟨p, q⟩; simp
      rw [this, Finset.sum_singleton, hd]; simp [hd]
    · have : (Finset.univ.filter fun p : W × W => s(p.1, p.2) = s(a, b)) = {(a, b), (b, a)} := by
        ext ⟨p, q⟩; simp
      rw [this, Finset.sum_pair (by simp [Ne.symm hab]), hf b a]; ring

/-- The coin probabilities of Algorithm 1: coin `(e, k)` is `true` with probability `y_e`. -/
def sampleProb (y : WGraph W) (α : ℕ) : Sym2 W × Fin α → ℝ := fun i => edgeW y i.1

omit [Fintype W] [DecidableEq W] in
theorem isProbVec_sampleProb (y : WGraph W) (hy : ∀ u v, y.w u v ≤ 1) (α : ℕ) :
    IsProbVec (sampleProb y α) := fun i => by
  refine ⟨edgeW_nonneg y i.1, ?_⟩
  obtain ⟨e, k⟩ := i
  induction e using Sym2.ind with
  | _ u v => exact hy u v

/-- The number of sampled copies of the pair `e` (the multiplicity of `e` in `Y`). -/
def copies {α : ℕ} (ω : Sym2 W × Fin α → Bool) (e : Sym2 W) : ℕ := #{k : Fin α | ω (e, k) = true}

/-- `Y(δ(S))`: the number of sampled edges (with multiplicity) crossing `(S, Sᶜ)`. -/
def sampleCut {α : ℕ} (ω : Sym2 W × Fin α → Bool) (S : Finset W) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, (copies ω s(u, v) : ℝ)

/-- The simple graph underlying the sample `Y`. -/
def sampleGraph {α : ℕ} (ω : Sym2 W × Fin α → Bool) : SimpleGraph W where
  Adj u v := u ≠ v ∧ 0 < copies ω s(u, v)
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

end Sampling

/-- **Lemma 3.6 of [HOG26]** (stated, not proved, in the paper: "the proof goes by a simple
Chernoff bound and a cut-counting argument, see [Asa+17]"), used as a hypothesis.

*Paper:* given `G = (V, E)` and `x : E → ℝ≥0` such that the minimum cut of `(V, E, x)` is at least
`1/(8n)`, sample `α` copies of every edge `e` independently with probability `x_e`, where
`α = c n log n` for a sufficiently large constant `c`; then with high probability
`Y(δ(S)) ≤ O(α) x(δ(S))` for every `S ⊆ V`.

*Formalisation.*  There are absolute constants `c, K > 0` such that for every finite vertex type
`W`, every weighted graph `y` on `W` with `y ≤ 1` (so that the `y_e` are probabilities), every
`N ≥ max(1, |W|)` and every `α ≥ c N ln(2N)` the following holds: if every nonempty proper cut has
`y(δ(S)) ≥ 1/(4N)`, then with probability at least `1 - 1/(4N)` we have
`Y(δ(S)) ≤ K α y(δ(S))` for all `S ⊆ W`.

Choices and why they are harmless:
* `n` of the paper is replaced by a parameter `N ≥ |W|`: in the proof of Theorem 1.3 the lemma is
  applied to the components `G[Cᵢ]` of the trimmed graph with the *global* `n` (threshold
  `ε = 1/(8n) = 1/(4|V|)` and `α = Θ(n log n)` are global).  The proof sketched in the paper
  (Karger: at most `|W|^{2β} ≤ N^{2β}` cuts of weight `≤ β·mincut`; Chernoff: a cut of weight
  `t = β·mincut ≥ β/(4N)` has `P[Y(δ(S)) > e² α t] ≤ exp(-e² α t) ≤ (2N)^{-e² c β/4}`) works
  verbatim with `N` in place of `|W|`.
* `ln(2N)` instead of `log n` avoids `ln 1 = 0`.
* "with high probability" is made explicit as failure probability `≤ 1/(4N)`; the union bound
  above gives failure probability `N^{-Ω(c)}`, so this holds for `c` large enough.  It is what the
  proof of Theorem 1.3 needs: a union bound over the at most `N` components.
* `α` may be any integer `≥ c N ln(2N)` (the paper: "`α = cn log n` for a sufficiently large
  constant `c`"); the same proof applies.
* For `S = ∅` or `S = W` both sides vanish, so "for every `S ⊂ V`" may be read with `⊆`. -/
def Lemma36 : Prop :=
  ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∀ (W : Type) [Fintype W] [DecidableEq W] (y : WGraph W) (N α : ℕ),
      1 ≤ N → Fintype.card W ≤ N → (∀ u v, y.w u v ≤ 1) →
      (∀ S : Finset W, S.Nonempty → S ≠ Finset.univ → 1 / (4 * (N : ℝ)) ≤ cutWeight y S) →
      c * N * Real.log (2 * N) ≤ α →
      prob (sampleProb y α) (fun ω => ∃ S : Finset W, K * α * cutWeight y S < sampleCut ω S)
        ≤ 1 / (4 * (N : ℝ))

end ThinMatching
