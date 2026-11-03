/-
# Theorem 14: upper bound for the spectral distance

Paper, Section 3.4, Theorem 14 and the remark after it (p. 12, l. 397–400), and its proof in
App. F.2 (pp. 46–50).

Structure of the proof (following the paper):
* `Tools.lean`: the spectral norm `‖·‖₂ = ‖·‖_{2→2}` (`opNorm_two_two_eq`), `‖R‖₂ ≤ 1` for doubly
  stochastic `R`, `‖·‖₂ ≤ ‖·‖_F`, the variance identity.
* `RandomBijection.lean`: Eq. (40) (`eq40_le`), Lemma 50, Lemma 51 with Eq. (42), Lemma 52,
  Eqs. (41), (28), (43), the spectral truncation `A′_t`, and the main estimate
  `γ_P ≤ γ_Q + 2t + 2γ_Q h/t` (`exists_bij_norm_le`, `exists_aligned_le`, `exists_aligned_le'`)
  and the choice of `t` (`le_of_forall_threshold`).
* This file: the graph-specific part of the proof of Theorem 14 (p. 49, l. 1526–1532; p. 50,
  l. 1571–1575). We start from an optimal `Q ∈ DS(V, W)` (`exists_dOT_eq`, App. A), so
  `γ_Q = δ^OT_2`. Centring `A′ = A_G - p_G J`, `B′ = A_H - p_G J` changes neither the
  discrepancy (so `B_{2→2}` is unchanged, `discKernel_shift`) nor `A_G^π - A_H` (`aligned_shift`),
  and `‖A′‖_F = n √(p_G (1 - p_G))` (`sum_sq_shiftAdj`).
* Main results: `theorem14` (Theorem 14), `theorem15_h` (the bound `δ₂ ≤ γ_Q + 4√(γ_Q h)` at the
  end of the proof), `theorem15`
  (`δ₂ ≤ min{1, δ^OT_2 + 4√(h δ^OT_2)} ≤ min{1, δ^OT_2 + 2√(2 δ^OT_2)}`, which combines
  `theorem15_h` with `δ₂ ≤ 1`), `theorem15_sqrt` (`δ₂ ≤ (1 + 2√2)√(δ^OT_2)`, p. 12, l. 399, and
  Theorem 2).

Formalisation notes. Instead of assuming `h = √(p_G(1-p_G))` "by symmetry" (l. 1529), both cases
are handled directly (`deltaPQ_le_threshold_G` uses the Frobenius norm of `A′`,
`deltaPQ_le_threshold_H` that of `B′`, after centring both matrices by `p_H`). The bound `δ₂ ≤ 1`
of `theorem15` is proved via `‖·‖₂ ≤ ‖·‖_F ≤ n`, and `δ^OT_2 ≤ 1` (`deltaOTPQ_two_two_le_one`,
used for `theorem15_sqrt`) via the Frobenius norm of `B_{2→2}`.
-/
import GsimOT.Common.OTDistances
import GsimOT.Common.CutNorm
import GsimOT.Common.Attainment
import GsimOT.Theorem15_SpectralUpperBound.RandomBijection

open Finset Matrix
open scoped Matrix.Norms.L2Operator

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- The edge density `p_G = 2|E(G)|/n² = (∑_{v,v'} A_G(v,v'))/n²`. -/
noncomputable def edgeDensity (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (∑ v, ∑ v', adj G v v') / (Fintype.card V : ℝ) ^ 2

/-- The edge density is `p_G = 2|E(G)|/n²`, as in the proof of Theorem 14 (p. 49, l. 1528;
handshake lemma). -/
lemma edgeDensity_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeDensity G = 2 * (#G.edgeFinset : ℝ) / (Fintype.card V : ℝ) ^ 2 := by
  have : ∀ v, ∑ v', adj G v v' = (G.degree v : ℝ) := fun v => by
    rw [sum_adj_eq_deg, deg, ← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_eq_filter]
  unfold edgeDensity
  simp_rw [this]
  rw [← Nat.cast_sum, SimpleGraph.sum_degrees_eq_twice_card_edges]
  push_cast
  ring

variable {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]

namespace Theorem15

/-! ### Shifting the adjacency matrices by the density -/

/-- The shifted adjacency matrix `A_G - p 𝟙𝟙ᵀ`. -/
def shiftAdj (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) : Matrix V V ℝ :=
  fun v v' => adj G v v' - p

lemma shiftAdj_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) :
    (shiftAdj G p).IsHermitian := by
  ext v v'
  simp [shiftAdj, adj_symm G v v']

lemma powZ_half (x : ℝ) : powZ x (1 / 2) = Real.sqrt x := by
  unfold powZ
  split_ifs with h
  · simp [h]
  · rw [Real.sqrt_eq_rpow]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- Shifting does not change the discrepancy, so `B_{2→2}(G, H, Q)` is the kernel of the shifted
matrices. -/
lemma discKernel_shift (p : ℝ) (Q : V → W → ℝ) :
    discKernel (shiftAdj G p) (shiftAdj H p) Q = Bmat 2 2 G H Q := by
  ext a b
  have e : ((2 : ENNReal)⁻¹).toReal = 1 / 2 := by simp
  simp only [discKernel, Bmat, e, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    powZ_half, shiftAdj, disc]
  ring

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- Shifting does not change `A_G^π - A_H`. -/
lemma aligned_shift (p : ℝ) (π : V ≃ W) :
    aligned (shiftAdj G p) (shiftAdj H p) π = alignedDiff G H π := by
  ext w w'
  simp only [aligned, shiftAdj, alignedDiff]
  ring

/-- `‖A_G - p_G‖_F² = n² p_G (1 - p_G)`. -/
lemma sum_sq_shiftAdj (G : SimpleGraph V) [DecidableRel G.Adj] (hn : (Fintype.card V : ℝ) ≠ 0) :
    ∑ i, ∑ k, shiftAdj G (edgeDensity G) i k ^ 2 =
      (Fintype.card V : ℝ) ^ 2 * (edgeDensity G * (1 - edgeDensity G)) := by
  have hsum : ∑ i, ∑ k, adj G i k = edgeDensity G * (Fintype.card V : ℝ) ^ 2 := by
    unfold edgeDensity; field_simp
  have hsq : ∀ i k, adj G i k ^ 2 = adj G i k := fun i k => by
    rcases adj_eq_zero_or_one G i k with h | h <;> rw [h] <;> norm_num
  have e : ∀ i k, shiftAdj G (edgeDensity G) i k ^ 2 =
      adj G i k - 2 * edgeDensity G * adj G i k + edgeDensity G ^ 2 := fun i k => by
    simp only [shiftAdj]
    rw [sub_sq, hsq]
    ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
  rw [hsum]
  ring

/-- `‖A_G - p_G‖_F = n h_G` with `h_G = √(p_G (1 - p_G))`. -/
lemma sqrt_sum_sq_shiftAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : (Fintype.card V : ℝ) ≠ 0) :
    Real.sqrt (∑ i, ∑ k, shiftAdj G (edgeDensity G) i k ^ 2) =
      (Fintype.card V : ℝ) * Real.sqrt (edgeDensity G * (1 - edgeDensity G)) := by
  rw [sum_sq_shiftAdj G hn, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

/-! ### The proof of Theorem 14 for an optimal `Q` -/

omit [Fintype V] [DecidableEq V] [DecidableEq W] in
lemma distPQ_le_opNorm (π : V ≃ W) :
    distPQ 2 2 G H ≤ opNorm 2 2 (alignedDiff G H π) :=
  ciInf_le ⟨0, by rintro _ ⟨π, rfl⟩; exact opNorm_nonneg _ _ _⟩ π

omit [DecidableEq V] [DecidableEq W] in
/-- `δ₂(G, H) = d₂(G, H)/n`. -/
lemma deltaPQ_two_two_eq :
    deltaPQ 2 2 G H = distPQ 2 2 G H / Fintype.card V := by
  rw [deltaPQ, show kappa 2 2 = 1 by simp [kappa], Real.rpow_neg_one, inv_mul_eq_div]

/-- **Main estimate in the paper's normalisation, case `h = h_G`** (p. 50, l. 1572): for every
`Q ∈ DS(V, W)` with `γ_Q = n⁻¹ ‖B_{2→2}(G, H, Q)‖₂` and every `t > 0`,
`δ₂(G, H) ≤ γ_Q + 2t + 2γ_Q h_G / t` with `h_G = √(p_G(1 - p_G))`. As in the paper, `A_G` and
`A_H` are both centred by `p_G` (`A′ = A - p_G J`, `B′ = B - p_G J`), which changes neither
`B_{2→2}` (`discKernel_shift`) nor `A^π - B` (`aligned_shift`), and `‖A′‖_F = n h_G`
(`sqrt_sum_sq_shiftAdj`); the threshold of the spectral truncation is `s = nt`. -/
lemma deltaPQ_le_threshold_G (hcard : Fintype.card V = Fintype.card W)
    (hn : (0 : ℝ) < Fintype.card V) {Q : V → W → ℝ} (hQ : IsDS Q) {t : ℝ} (ht : 0 < t) :
    deltaPQ 2 2 G H ≤ opNorm 2 2 (Bmat 2 2 G H Q) / Fintype.card V + 2 * t +
      2 * (opNorm 2 2 (Bmat 2 2 G H Q) / Fintype.card V) *
        Real.sqrt (edgeDensity G * (1 - edgeDensity G)) / t := by
  obtain ⟨π, hπ⟩ := exists_aligned_le (shiftAdj G (edgeDensity G))
    (shiftAdj H (edgeDensity G)) (shiftAdj_isHermitian G _) hQ hcard
    (mul_pos hn ht : (0 : ℝ) < Fintype.card V * t)
  rw [aligned_shift, discKernel_shift _ Q, sqrt_sum_sq_shiftAdj G hn.ne'] at hπ
  rw [← opNorm_two_two_eq, ← opNorm_two_two_eq] at hπ
  rw [deltaPQ_two_two_eq, div_le_iff₀ hn]
  refine (distPQ_le_opNorm π).trans (hπ.trans (le_of_eq ?_))
  field_simp

/-- The case `h = h_H` (the paper's "by symmetry"): centring by `p_H` and using the Frobenius
norm of `B′`. -/
lemma deltaPQ_le_threshold_H (hcard : Fintype.card V = Fintype.card W)
    (hn : (0 : ℝ) < Fintype.card V) {Q : V → W → ℝ} (hQ : IsDS Q) {t : ℝ} (ht : 0 < t) :
    deltaPQ 2 2 G H ≤ opNorm 2 2 (Bmat 2 2 G H Q) / Fintype.card V + 2 * t +
      2 * (opNorm 2 2 (Bmat 2 2 G H Q) / Fintype.card V) *
        Real.sqrt (edgeDensity H * (1 - edgeDensity H)) / t := by
  have hW : (Fintype.card W : ℝ) = Fintype.card V := by rw [hcard]
  obtain ⟨π, hπ⟩ := exists_aligned_le' (shiftAdj G (edgeDensity H))
    (shiftAdj H (edgeDensity H)) (shiftAdj_isHermitian H _) hQ hcard
    (mul_pos hn ht : (0 : ℝ) < Fintype.card V * t)
  rw [aligned_shift, discKernel_shift _ Q, sqrt_sum_sq_shiftAdj H (hW ▸ hn.ne'), hW] at hπ
  rw [← opNorm_two_two_eq, ← opNorm_two_two_eq] at hπ
  rw [deltaPQ_two_two_eq, div_le_iff₀ hn]
  refine (distPQ_le_opNorm π).trans (hπ.trans (le_of_eq ?_))
  field_simp

/-- Choice of `t` (p. 50, l. 1573–1575): for every `Q ∈ DS(V, W)`,
`δ₂(G, H) ≤ γ_Q + 4√(γ_Q h)` with `h = min{√(p_G(1-p_G)), √(p_H(1-p_H))}`. -/
lemma deltaPQ_le_of_isDS (hcard : Fintype.card V = Fintype.card W)
    (hn : (0 : ℝ) < Fintype.card V) {Q : V → W → ℝ} (hQ : IsDS Q) :
    deltaPQ 2 2 G H ≤ opNorm 2 2 (Bmat 2 2 G H Q) / Fintype.card V +
      4 * Real.sqrt (opNorm 2 2 (Bmat 2 2 G H Q) / Fintype.card V *
        min (Real.sqrt (edgeDensity G * (1 - edgeDensity G)))
          (Real.sqrt (edgeDensity H * (1 - edgeDensity H)))) := by
  have hC : 0 ≤ opNorm 2 2 (Bmat 2 2 G H Q) / Fintype.card V :=
    div_nonneg (opNorm_nonneg _ _ _) hn.le
  rcases min_choice (Real.sqrt (edgeDensity G * (1 - edgeDensity G)))
    (Real.sqrt (edgeDensity H * (1 - edgeDensity H))) with h | h <;> rw [h]
  · exact le_of_forall_threshold hC (Real.sqrt_nonneg _) fun t ht =>
      deltaPQ_le_threshold_G hcard hn hQ ht
  · exact le_of_forall_threshold hC (Real.sqrt_nonneg _) fun t ht =>
      deltaPQ_le_threshold_H hcard hn hQ ht

/-- `δ₂ ≤ 1`: all entries of `A_G^π - A_H` lie in `[-1, 1]`, so `‖A_G^π - A_H‖₂ ≤ ‖·‖_F ≤ n`. -/
lemma distPQ_le_card (hcard : Fintype.card V = Fintype.card W) :
    distPQ 2 2 G H ≤ Fintype.card V := by
  obtain ⟨e⟩ : Nonempty (V ≃ W) := ⟨Fintype.equivOfCardEq hcard⟩
  refine (distPQ_le_opNorm e).trans ?_
  rw [opNorm_two_two_eq]
  refine (l2_norm_le_frobenius _).trans ?_
  have h : ∑ i, ∑ j, alignedDiff G H e i j ^ 2 ≤ (Fintype.card V : ℝ) ^ 2 := by
    calc ∑ i, ∑ j, alignedDiff G H e i j ^ 2 ≤ ∑ _i : W, ∑ _j : W, (1 : ℝ) :=
          sum_le_sum fun i _ => sum_le_sum fun j _ => by
            have := abs_adj_sub_adj_le_one G H (e.symm i) (e.symm j) i j
            rw [alignedDiff, ← sq_abs]
            nlinarith [abs_nonneg (adj G (e.symm i) (e.symm j) - adj H i j)]
      _ = (Fintype.card V : ℝ) ^ 2 := by simp [hcard, sq]
  calc Real.sqrt _ ≤ Real.sqrt ((Fintype.card V : ℝ) ^ 2) := Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_sq (Nat.cast_nonneg _)

end Theorem15

open Theorem15

lemma kappa_two_two : kappa 2 2 = 1 := by simp [kappa]

omit [DecidableEq V] [DecidableEq W] in
lemma deltaOTPQ_two_two_nonneg : 0 ≤ deltaOTPQ 2 2 G H :=
  Real.iInf_nonneg fun _ => opNorm_nonneg _ _ _

omit [DecidableEq V] [DecidableEq W] in
/-- `h = min{√(p_G(1-p_G)), √(p_H(1-p_H))} ≤ 1/2`, since `x(1-x) ≤ 1/4`. -/
lemma min_sqrt_density_le_half :
    min (Real.sqrt (edgeDensity G * (1 - edgeDensity G)))
      (Real.sqrt (edgeDensity H * (1 - edgeDensity H))) ≤ 1 / 2 := by
  refine (min_le_left _ _).trans ?_
  calc Real.sqrt (edgeDensity G * (1 - edgeDensity G)) ≤ Real.sqrt ((1 / 2) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (edgeDensity G - 1 / 2)])
    _ = 1 / 2 := Real.sqrt_sq (by norm_num)

omit [DecidableEq V] [DecidableEq W] in
/-- `4√(hδ) ≤ 2√(2δ)`, since `h ≤ 1/2` (p. 50, l. 1575). -/
lemma four_sqrt_le (δ : ℝ) (hδ : 0 ≤ δ) :
    4 * Real.sqrt (min (Real.sqrt (edgeDensity G * (1 - edgeDensity G)))
        (Real.sqrt (edgeDensity H * (1 - edgeDensity H))) * δ) ≤ 2 * Real.sqrt (2 * δ) := by
  have hh0 : 0 ≤ min (Real.sqrt (edgeDensity G * (1 - edgeDensity G)))
      (Real.sqrt (edgeDensity H * (1 - edgeDensity H))) := by positivity
  have hh := min_sqrt_density_le_half (G := G) (H := H)
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero, mul_pow, mul_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  nlinarith

/-- `‖B_{2→2}(G, H, Q)‖₂ ≤ ∑_{v,w} Q(v, w)` for `Q ≥ 0`, via the Frobenius norm (all entries of
the discrepancy lie in `[-1, 1]`). -/
lemma opNorm_Bmat_le_sum {Q : V → W → ℝ} (h0 : ∀ v w, 0 ≤ Q v w) :
    opNorm 2 2 (Bmat 2 2 G H Q) ≤ ∑ v, ∑ w, Q v w := by
  rw [← discKernel_shift 0 Q, opNorm_two_two_eq]
  set S := ∑ v, ∑ w, Q v w with hSdef
  have hS : 0 ≤ S := sum_nonneg fun v _ => sum_nonneg fun w _ => h0 v w
  have hentry : ∀ a b : V × W, discKernel (shiftAdj G 0) (shiftAdj H 0) Q a b ^ 2 ≤
      Q a.1 a.2 * Q b.1 b.2 := fun a b => by
    simp only [discKernel, shiftAdj, sub_zero]
    rw [mul_pow, mul_pow, Real.sq_sqrt (h0 _ _), Real.sq_sqrt (h0 _ _)]
    have hd : (adj G a.1 b.1 - adj H a.2 b.2) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).2 (abs_adj_sub_adj_le_one G H _ _ _ _)
    have := mul_nonneg (h0 a.1 a.2) (h0 b.1 b.2)
    nlinarith
  have hsum : ∑ a : V × W, Q a.1 a.2 = S := by rw [Fintype.sum_prod_type]
  refine (l2_norm_le_frobenius _).trans ?_
  calc Real.sqrt (∑ a, ∑ b, discKernel (shiftAdj G 0) (shiftAdj H 0) Q a b ^ 2)
      ≤ Real.sqrt (S ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        calc _ ≤ ∑ a : V × W, ∑ b : V × W, Q a.1 a.2 * Q b.1 b.2 :=
              sum_le_sum fun a _ => sum_le_sum fun b _ => hentry a b
          _ = S ^ 2 := by rw [← Finset.sum_mul_sum, hsum, sq]
    _ = S := Real.sqrt_sq hS

/-- `δ₂(G, H) ≤ 1`: all entries of `A_G^π - A_H` lie in `[-1, 1]`. This is the bound `δ₂ ≤ 1` in
`theorem15`. -/
lemma deltaPQ_two_two_le_one
    (hcard : Fintype.card V = Fintype.card W) : deltaPQ 2 2 G H ≤ 1 := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · rw [deltaPQ_two_two_eq (G := G) (H := H), h0, Nat.cast_zero, div_zero]; norm_num
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hpos
  rw [deltaPQ_two_two_eq (G := G) (H := H), div_le_one hn]
  exact distPQ_le_card hcard

/-- `δ^OT_2(G, H) ≤ 1`, used after Theorem 14 (p. 12, l. 399: "As `δ^OT_2 ≤ 1`"): for every
coupling `Q*`, `‖B_{2→2}(G, H, Q*)‖₂ ≤ ∑ Q* ≤ 1`. -/
lemma deltaOTPQ_two_two_le_one : deltaOTPQ 2 2 G H ≤ 1 := by
  rcases isEmpty_or_nonempty {Q : V → W → ℝ // IsCoupling Q} with h | ⟨⟨Q, hQc⟩⟩
  · rw [deltaOTPQ, Real.iInf_of_isEmpty]; norm_num
  refine (ciInf_le (f := fun Q : {Q : V → W → ℝ // IsCoupling Q} =>
    opNorm 2 2 (Bmat 2 2 G H Q.1)) ⟨0, by rintro _ ⟨Q, rfl⟩; exact opNorm_nonneg _ _ _⟩ ⟨Q, hQc⟩).trans ?_
  refine (opNorm_Bmat_le_sum (G := G) (H := H) hQc.nonneg).trans ?_
  simp only [hQc.row_sum, sum_const, card_univ, nsmul_eq_mul]
  rw [mul_one_div]
  exact div_self_le_one _

/-- **The bound at the end of the proof of Theorem 14** (p. 50, l. 1573–1574):
`δ₂(G, H) ≤ δ^OT_2 + 4√(h δ^OT_2)` with `h = min{√(p_G(1-p_G)), √(p_H(1-p_H))}`. As in the paper
(p. 49, l. 1526), we start from an optimal `Q ∈ DS(V, W)` (`exists_dOT_eq`), so that
`γ_Q = δ^OT_2(G, H)`. -/
theorem theorem15_h (hcard : Fintype.card V = Fintype.card W) :
    deltaPQ 2 2 G H ≤ deltaOTPQ 2 2 G H + 4 * Real.sqrt (min
        (Real.sqrt (edgeDensity G * (1 - edgeDensity G)))
        (Real.sqrt (edgeDensity H * (1 - edgeDensity H))) * deltaOTPQ 2 2 G H) := by
  have hδ := deltaOTPQ_two_two_nonneg (G := G) (H := H)
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · -- empty graphs: `δ₂ = 0`
    rw [deltaPQ_two_two_eq (G := G) (H := H), h0, Nat.cast_zero, div_zero]
    positivity
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast hpos
  have : Nonempty V := Fintype.card_pos_iff.1 hpos
  obtain ⟨Q, hQ, hopt⟩ := exists_dOT_eq G H (p := 2) (q := 2) (by norm_num) (by norm_num)
    ⟨Fintype.equivOfCardEq hcard⟩
  have hrel := deltaOTPQ_eq_dOT 2 2 G H (by norm_num) (by norm_num) hcard
  rw [kappa_two_two, Real.rpow_neg_one] at hrel
  have hγ : opNorm 2 2 (Bmat 2 2 G H Q) / Fintype.card V = deltaOTPQ 2 2 G H := by
    rw [hrel, hopt, inv_mul_eq_div]
  have h := deltaPQ_le_of_isDS (G := G) (H := H) hcard hn hQ
  rw [hγ, mul_comm (deltaOTPQ 2 2 G H)] at h
  exact h

/-- **Theorem 14** (p. 12, l. 397–398). For all graphs `G, H` of the same order,
`δ₂(G, H) ≤ δ^OT_2(G, H) + 2√(2 δ^OT_2(G, H))`. As in the paper, this follows from `theorem15_h`
and `h ≤ 1/2` (`four_sqrt_le`). -/
theorem theorem14 (hcard : Fintype.card V = Fintype.card W) :
    deltaPQ 2 2 G H ≤ deltaOTPQ 2 2 G H + 2 * Real.sqrt (2 * deltaOTPQ 2 2 G H) := by
  have h := four_sqrt_le (G := G) (H := H) _ (deltaOTPQ_two_two_nonneg (G := G) (H := H))
  linarith [theorem15_h (G := G) (H := H) hcard]

/-- **Theorem 14 with the bound of its proof and `min{1, ·}`.** For graphs `G, H` of the same
order with edge densities `p_G, p_H` and `h = min{√(p_G(1-p_G)), √(p_H(1-p_H))}`,
`δ_2(G, H) ≤ min{1, δ^OT_2 + 4√(h δ^OT_2)} ≤ min{1, δ^OT_2 + 2√(2 δ^OT_2)}`.
This combines the bound `theorem15_h` at the end of the proof of Theorem 14 with
`δ₂ ≤ 1` (`deltaPQ_two_two_le_one`) and `h ≤ 1/2` (`four_sqrt_le`); it implies Theorem 14
(`theorem14`, `δ_2 ≤ δ^OT_2 + 2√(2 δ^OT_2)`). -/
theorem theorem15 (hcard : Fintype.card V = Fintype.card W) :
    deltaPQ 2 2 G H ≤ min 1 (deltaOTPQ 2 2 G H + 4 * Real.sqrt (min
        (Real.sqrt (edgeDensity G * (1 - edgeDensity G)))
        (Real.sqrt (edgeDensity H * (1 - edgeDensity H))) * deltaOTPQ 2 2 G H)) ∧
    min 1 (deltaOTPQ 2 2 G H + 4 * Real.sqrt (min
        (Real.sqrt (edgeDensity G * (1 - edgeDensity G)))
        (Real.sqrt (edgeDensity H * (1 - edgeDensity H))) * deltaOTPQ 2 2 G H)) ≤
      min 1 (deltaOTPQ 2 2 G H + 2 * Real.sqrt (2 * deltaOTPQ 2 2 G H)) :=
  ⟨le_min (deltaPQ_two_two_le_one hcard) (theorem15_h hcard),
    min_le_min_left _ (add_le_add le_rfl (four_sqrt_le (G := G) (H := H) _ deltaOTPQ_two_two_nonneg))⟩

/-- **Consequence of Theorem 14** (p. 12, l. 399, and the `δ₂` part of Theorem 2, p. 3, l. 119):
`δ_2 ≤ (1 + 2√2) √(δ^OT_2)`. As in the paper: `δ^OT_2 ≤ 1` gives `δ^OT_2 ≤ √(δ^OT_2)`. -/
theorem theorem15_sqrt (hcard : Fintype.card V = Fintype.card W) :
    deltaPQ 2 2 G H ≤ (1 + 2 * Real.sqrt 2) * Real.sqrt (deltaOTPQ 2 2 G H) := by
  have h := theorem14 (G := G) (H := H) hcard
  have hδ := deltaOTPQ_two_two_nonneg (G := G) (H := H)
  have h1 := deltaOTPQ_two_two_le_one (G := G) (H := H)
  have hs := Real.sqrt_nonneg (deltaOTPQ 2 2 G H)
  have hsq := Real.sq_sqrt hδ
  have hle : deltaOTPQ 2 2 G H ≤ Real.sqrt (deltaOTPQ 2 2 G H) := by
    have : Real.sqrt (deltaOTPQ 2 2 G H) ≤ 1 := Real.sqrt_le_one.mpr h1
    nlinarith
  have e : Real.sqrt (2 * deltaOTPQ 2 2 G H) = Real.sqrt 2 * Real.sqrt (deltaOTPQ 2 2 G H) :=
    Real.sqrt_mul (by norm_num) _
  rw [e] at h
  nlinarith

end GsimOT
