/-
# Lemma 48 and Theorem 39: additive rounding (Appendix E.2.2, pp. 40–43)

Theorem 39 (p. 36, l. 1112–1114; proof p. 43, l. 1357–1361) and Lemma 48 (p. 43, l. 1339–1341;
proof l. 1342–1354).

* Properties of `ρ`: pseudometric and Eq. (35) (`rhoSupp_triangle`, `rhoSupp_convex`).
* Eq. (3) with Carathéodory, `N ≤ n²` (`exists_perm_decomp`).
* **Lemma 48**: binary-tree merging (`merge_aux`, `lemma48`).
* **Theorem 39** (`theorem39`): Lemma 45, Lemma 48 and Corollary 46 with `t = √(20 d_n) n^{-1/6}`.
-/
import GsimOT.Theorem11_CutUpperBound.Corollary46_SpectralTruncation
import GsimOT.Theorem11_CutUpperBound.Lemma47_MergingPermutations

open Finset

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W]

section RhoProps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma abs_hSupp_le (v : V → W → E) (R : V → W → ℝ) {z : E} (hz : ‖z‖ ≤ 1) :
    |hSupp v R z| ≤ (∑ i, ∑ j, |R i j| * ‖v i j‖) / Fintype.card V := by
  unfold hSupp
  rw [abs_div, Nat.abs_cast]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_))
  rw [abs_mul]
  gcongr
  calc |max (inner ℝ z (v i j)) 0| ≤ max |inner ℝ z (v i j)| |0| := abs_max_le_max_abs_abs
    _ = |inner ℝ z (v i j)| := by simp
    _ ≤ ‖z‖ * ‖v i j‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * ‖v i j‖ := by gcongr
    _ = ‖v i j‖ := one_mul _

instance closedBall_nonempty' : Nonempty (Metric.closedBall (0 : E) 1) :=
  ⟨⟨0, by simp⟩⟩

lemma rhoSupp_bdd (v : V → W → E) (R R' : V → W → ℝ) :
    BddAbove (Set.range fun z : Metric.closedBall (0 : E) 1 =>
      |hSupp v R z.1 - hSupp v R' z.1|) := by
  refine ⟨(∑ i, ∑ j, |R i j| * ‖v i j‖) / Fintype.card V +
    (∑ i, ∑ j, |R' i j| * ‖v i j‖) / Fintype.card V, ?_⟩
  rintro _ ⟨z, rfl⟩
  have hz : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
  exact (abs_sub _ _).trans (add_le_add (abs_hSupp_le v R hz) (abs_hSupp_le v R' hz))

lemma le_rhoSupp_ball (v : V → W → E) (R R' : V → W → ℝ) {z : E} (hz : ‖z‖ ≤ 1) :
    |hSupp v R z - hSupp v R' z| ≤ rhoSupp v R R' :=
  le_ciSup (f := fun z : Metric.closedBall (0 : E) 1 => |hSupp v R z.1 - hSupp v R' z.1|)
    (rhoSupp_bdd v R R') ⟨z, mem_closedBall_zero_iff.mpr hz⟩

lemma rhoSupp_le_of {v : V → W → E} {R R' : V → W → ℝ} {c : ℝ}
    (h : ∀ z : E, ‖z‖ ≤ 1 → |hSupp v R z - hSupp v R' z| ≤ c) : rhoSupp v R R' ≤ c :=
  ciSup_le fun z => h z.1 (mem_closedBall_zero_iff.mp z.2)

lemma rhoSupp_triangle (v : V → W → E) (A B C : V → W → ℝ) :
    rhoSupp v A C ≤ rhoSupp v A B + rhoSupp v B C :=
  rhoSupp_le_of fun _ hz => (abs_sub_le _ _ _).trans
    (add_le_add (le_rhoSupp_ball v A B hz) (le_rhoSupp_ball v B C hz))

lemma rhoSupp_self_le (v : V → W → E) (A : V → W → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    rhoSupp v A A ≤ c :=
  rhoSupp_le_of fun _ _ => by simpa using hc

lemma hSupp_lin (v : V → W → E) (a b : ℝ) (A B : V → W → ℝ) (z : E) :
    hSupp v (fun i j => a * A i j + b * B i j) z = a * hSupp v A z + b * hSupp v B z := by
  unfold hSupp
  rw [mul_div_assoc', mul_div_assoc', ← add_div]
  congr 1
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

lemma rhoSupp_convex (v : V → W → E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (A A' B B' : V → W → ℝ) :
    rhoSupp v (fun i j => a * A i j + b * B i j) (fun i j => a * A' i j + b * B' i j) ≤
      a * rhoSupp v A A' + b * rhoSupp v B B' := by
  refine rhoSupp_le_of fun z hz => ?_
  rw [hSupp_lin, hSupp_lin]
  calc |a * hSupp v A z + b * hSupp v B z - (a * hSupp v A' z + b * hSupp v B' z)|
      = |a * (hSupp v A z - hSupp v A' z) + b * (hSupp v B z - hSupp v B' z)| := by ring_nf
    _ ≤ |a * (hSupp v A z - hSupp v A' z)| + |b * (hSupp v B z - hSupp v B' z)| :=
        abs_add_le _ _
    _ = a * |hSupp v A z - hSupp v A' z| + b * |hSupp v B z - hSupp v B' z| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * rhoSupp v A A' + b * rhoSupp v B B' := by
        gcongr
        · exact le_rhoSupp_ball v A A' hz
        · exact le_rhoSupp_ball v B B' hz

end RhoProps

variable [DecidableEq V] [DecidableEq W]

section Merge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The normalised convex combination `(∑_{a ∈ s} w_a P_{π_a}) / (∑_{a ∈ s} w_a)`. -/
noncomputable def combo {ι : Type*} (π : ι → V ≃ W) (w : ι → ℝ) (s : Finset ι) :
    V → W → ℝ :=
  fun i j => (∑ a ∈ s, w a * permMat (π a) i j) / ∑ a ∈ s, w a

omit [DecidableEq V] in
lemma combo_singleton_case (v : V → W → E) {ι : Type*} (π : ι → V ≃ W) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) {s : Finset ι} (hs : s.Nonempty) (hs1 : #s ≤ 1) {c : ℝ}
    (hc : 0 ≤ c) : ∃ π' : V ≃ W, rhoSupp v (permMat π') (combo π w s) ≤ c := by
  have hs1' : #s = 1 := by have := hs.card_pos; omega
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs1'
  refine ⟨π a, ?_⟩
  have : combo π w {a} = permMat (π a) := by
    funext i j
    simp only [combo, Finset.sum_singleton]
    field_simp [(hw a).ne']
  rw [this]
  exact rhoSupp_self_le _ _ hc

/-- Merging along a binary tree of height `k` (proof of Lemma 48, p. 43, l. 1344–1354): a convex
combination of at most `2^k` permutation matrices `P_s` (positive weights) is approximated within
`k η₀`, `η₀ = 20 M n^{-1/3}` (Lemma 47), by a single permutation matrix. The tree splits the index
set into two halves at every node (instead of padding with leaves of weight zero), so every inner
node has two children of positive weight. The induction step is the paper's: triangle inequality,
Lemma 47 and Eq. (35). -/
lemma merge_aux (hCP : ContractionPrinciple) (v : V → W → E) {M : ℝ}
    (hM : ∀ i j, ‖v i j‖ ≤ M) (hcard : Fintype.card V = Fintype.card W)
    (hη : 0 ≤ 20 * M * (Fintype.card V : ℝ) ^ (-(1 / 3 : ℝ)))
    {ι : Type*} (π : ι → V ≃ W) (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    ∀ (k : ℕ) (s : Finset ι), s.Nonempty → #s ≤ 2 ^ k →
      ∃ π' : V ≃ W, rhoSupp v (permMat π') (combo π w s) ≤
        k * (20 * M * (Fintype.card V : ℝ) ^ (-(1 / 3 : ℝ))) := by
  classical
  intro k
  induction k with
  | zero =>
    intro s hs hsk
    exact combo_singleton_case v π w hw hs (by simpa using hsk) (by simp)
  | succ k ih =>
    intro s hs hsk
    by_cases h1 : #s ≤ 1
    · exact combo_singleton_case v π w hw hs h1 (by positivity)
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (s := s) (n := #s / 2)
      (Nat.div_le_self _ _)
    have hsd : #(s \ t) = #s - #t := Finset.card_sdiff_of_subset hts
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have ht : t.Nonempty := Finset.card_pos.mp (by omega)
    have hst : (s \ t).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨π1, h1'⟩ := ih t ht (by omega)
    obtain ⟨π2, h2'⟩ := ih (s \ t) hst (by omega)
    have hΛ1 : 0 < ∑ a ∈ t, w a := Finset.sum_pos (fun i _ => hw i) ht
    have hΛ2 : 0 < ∑ a ∈ s \ t, w a := Finset.sum_pos (fun i _ => hw i) hst
    have hθ0 : 0 ≤ (∑ a ∈ s \ t, w a) / (∑ a ∈ t, w a + ∑ a ∈ s \ t, w a) := by positivity
    have hθ1 : (∑ a ∈ s \ t, w a) / (∑ a ∈ t, w a + ∑ a ∈ s \ t, w a) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    obtain ⟨π', hπ'⟩ := lemma47 hCP v hM hcard π1 π2 hθ0 hθ1
    refine ⟨π', ?_⟩
    have hsplit : combo π w s = fun i j =>
        (1 - (∑ a ∈ s \ t, w a) / (∑ a ∈ t, w a + ∑ a ∈ s \ t, w a)) * combo π w t i j +
        (∑ a ∈ s \ t, w a) / (∑ a ∈ t, w a + ∑ a ∈ s \ t, w a) * combo π w (s \ t) i j := by
      funext i j
      simp only [combo]
      rw [← Finset.sum_sdiff hts (f := w), ← Finset.sum_sdiff hts]
      field_simp
      ring
    rw [hsplit]
    calc _ ≤ _ := rhoSupp_triangle v _ _ _
      _ ≤ 20 * M * (Fintype.card V : ℝ) ^ (-(1 / 3 : ℝ)) +
          ((1 - (∑ a ∈ s \ t, w a) / (∑ a ∈ t, w a + ∑ a ∈ s \ t, w a)) *
              (k * (20 * M * (Fintype.card V : ℝ) ^ (-(1 / 3 : ℝ)))) +
            (∑ a ∈ s \ t, w a) / (∑ a ∈ t, w a + ∑ a ∈ s \ t, w a) *
              (k * (20 * M * (Fintype.card V : ℝ) ^ (-(1 / 3 : ℝ))))) := by
          refine add_le_add hπ' ((rhoSupp_convex v (by linarith) hθ0 _ _ _ _).trans ?_)
          gcongr
      _ = _ := by push_cast; ring

end Merge

/-- **Eq. (3)** (Birkhoff) with Carathéodory's theorem [Sch86] (proof of Lemma 48, p. 43,
l. 1342–1344):
`Q` is a convex combination of `N ≤ n²` permutation matrices with positive weights. -/
lemma exists_perm_decomp {Q : V → W → ℝ} (hQ : IsDS Q) (hcard : Fintype.card V = Fintype.card W)
    (hn : 0 < Fintype.card V) :
    ∃ (m : ℕ) (π : Fin m → V ≃ W) (w : Fin m → ℝ), (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      (∀ a b, ∑ i, w i * permMat (π i) a b = Q a b) ∧ m ≤ Fintype.card V ^ 2 := by
  let e : V ≃ W := Fintype.equivOfCardEq hcard
  let Mx : Matrix V V ℝ := fun a b => Q a (e b)
  have hM : Mx ∈ doublyStochastic ℝ V := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun a b => hQ.nonneg _ _, fun a => ?_, fun b => hQ.col_sum _⟩
    simpa [Mx] using (Equiv.sum_comp e (fun b => Q a b)).trans (hQ.row_sum a)
  obtain ⟨wt, hwt0, hwt1, hwtM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hmem : Q ∈ convexHull ℝ (Set.range (permMat : (V ≃ W) → V → W → ℝ)) := by
    have hQe : Q = ∑ σ, wt σ • permMat (σ.trans e) := by
      funext a b
      have := congrFun (congrFun hwtM a) (e.symm b)
      simp only [Mx, Equiv.apply_symm_apply] at this
      rw [← this]
      simp [Finset.sum_apply, Matrix.sum_apply, permMat, Equiv.Perm.permMatrix,
        Equiv.eq_symm_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases h : e (σ a) = b <;> simp [h]
    rw [hQe]
    exact (convex_convexHull ℝ _).sum_mem (fun σ _ => hwt0 σ) hwt1
      (fun σ _ => subset_convexHull ℝ _ ⟨_, rfl⟩)
  obtain ⟨ι, _, z, wι, hzr, hai, hwpos, hwsum, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hmem
  choose π hπ using fun i => hzr ⟨i, rfl⟩
  have hmass : ∀ i, ∑ a, ∑ b, z i a b = Fintype.card V := fun i => by
    rw [← hπ i]; exact (permMat_isDS _).sum_sum
  have hli : LinearIndependent ℝ z := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h2 : ∑ a, ∑ b, (∑ i ∈ s, g i • z i) a b = (∑ i ∈ s, g i) * Fintype.card V := by
      calc ∑ a, ∑ b, (∑ i ∈ s, g i • z i) a b = ∑ a, ∑ b, ∑ i ∈ s, g i * z i a b := by
            simp [Finset.sum_apply]
        _ = ∑ a, ∑ i ∈ s, ∑ b, g i * z i a b :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ i ∈ s, ∑ a, ∑ b, g i * z i a b := Finset.sum_comm
        _ = ∑ i ∈ s, g i * Fintype.card V := Finset.sum_congr rfl fun i _ => by
            rw [← hmass i, Finset.mul_sum]; simp_rw [Finset.mul_sum]
        _ = (∑ i ∈ s, g i) * Fintype.card V := (Finset.sum_mul _ _ _).symm
    rw [hg] at h2
    have hsum : ∑ i ∈ s, g i = 0 := by
      simp only [Pi.zero_apply, Finset.sum_const_zero] at h2
      have hn' : (Fintype.card V : ℝ) ≠ 0 := by positivity
      exact (mul_eq_zero.mp h2.symm).resolve_right hn'
    exact (affineIndependent_iff.mp hai) s g hsum hg i hi
  have hcardι := hli.fintype_card_le_finrank
  rw [Module.finrank_pi_fintype] at hcardι
  simp only [Module.finrank_pi, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hcardι
  let f := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => π (f.symm i), fun i => wι (f.symm i), fun i => hwpos _, ?_,
    fun a b => ?_, ?_⟩
  · rw [← hwsum]; exact Equiv.sum_comp f.symm wι
  · rw [← hwz]
    simp only [hπ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Equiv.sum_comp f.symm (fun i => wι i * z i a b)
  · rw [sq]; nth_rw 2 [hcard]; exact hcardι

/-- **Lemma 48.** For `n ≥ 2`, `d_n = ⌈2 log₂ n⌉` and every `Q ∈ DS(V, W)` there is a permutation
matrix `P` with `ρ(P, Q) ≤ 20 M d_n n^{-1/3}` (for any vectors `v_ij` with `‖v_ij‖ ≤ M`). -/
theorem lemma48 (hCP : ContractionPrinciple) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : V → W → E) {M : ℝ} (hM : ∀ i j, ‖v i j‖ ≤ M)
    (hcard : Fintype.card V = Fintype.card W) (hn : 2 ≤ Fintype.card V) {Q : V → W → ℝ}
    (hQ : IsDS Q) :
    ∃ π : V ≃ W, rhoSupp v (permMat π) Q ≤
      20 * M * dn (Fintype.card V) * (Fintype.card V : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hn0 : 0 < Fintype.card V := by omega
  obtain ⟨m, π, w, hw, hw1, hQ', hm⟩ := exists_perm_decomp hQ hcard hn0
  obtain ⟨i0⟩ : Nonempty V := Fintype.card_pos_iff.mp hn0
  obtain ⟨j0⟩ : Nonempty W := Fintype.card_pos_iff.mp (hcard ▸ hn0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM i0 j0)
  have hη : 0 ≤ 20 * M * (Fintype.card V : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ.nonempty_of_sum_ne_zero (by rw [hw1]; norm_num)
  obtain ⟨π', h⟩ := merge_aux hCP v hM hcard hη π w hw (dn (Fintype.card V)) Finset.univ hne
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hm.trans (Nat.le_pow_clog one_lt_two _))
  have hQeq : combo π w Finset.univ = Q := by
    funext a b; simp only [combo]; rw [hw1, div_one, hQ']
  rw [hQeq] at h
  exact ⟨π', h.trans (le_of_eq (by ring))⟩

/-- **Theorem 39.** For `n ≥ 2` and every `Q ∈ DS(V, W)` there is a permutation matrix `P` with
`ζ_P ≤ ζ_Q + 36 √(d_n) n^{-1/6}`, `d_n = ⌈2 log₂ n⌉`. Here `ζ_R = epsR A B R`, for symmetric `A, B`
with entries in `[0, 1]` (e.g. adjacency matrices) and `|V| = |W| = n`. -/
theorem theorem39 (hCP : ContractionPrinciple) (A : Matrix V V ℝ) (B : Matrix W W ℝ)
    (hA : A.IsSymm) (hB : B.IsSymm)
    (hA01 : ∀ i k, 0 ≤ A i k ∧ A i k ≤ 1) (hB01 : ∀ j l, 0 ≤ B j l ∧ B j l ≤ 1)
    (hcard : Fintype.card V = Fintype.card W) (hn : 2 ≤ Fintype.card V) {Q : V → W → ℝ}
    (hQ : IsDS Q) :
    ∃ π : V ≃ W, epsR A B (permMat π) ≤
      epsR A B Q + 36 * Real.sqrt (dn (Fintype.card V)) * (Fintype.card V : ℝ) ^ (-(1 / 6 : ℝ)) := by
  have hn0 : 0 < Fintype.card V := by omega
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn0
  obtain ⟨x, hx⟩ : ∃ x, x = (Fintype.card V : ℝ) ^ (-(1 / 6 : ℝ)) := ⟨_, rfl⟩
  have hxpos : 0 < x := hx ▸ Real.rpow_pos_of_pos hnpos _
  have hx3 : (Fintype.card V : ℝ) ^ (-(1 / 3 : ℝ)) = x ^ 2 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (dn (Fintype.card V) : ℝ) := ⟨_, rfl⟩
  have hd1 : 1 ≤ d := by
    have : 0 < dn (Fintype.card V) := Nat.clog_pos one_lt_two (by nlinarith)
    rw [hd]; exact_mod_cast this
  obtain ⟨t, htdef⟩ : ∃ t, t = Real.sqrt (20 * d) * x := ⟨_, rfl⟩
  have ht : 0 < t := by
    rw [htdef]; exact mul_pos (Real.sqrt_pos.mpr (by linarith)) hxpos
  -- Lemma 45 for this `t`; Lemma 48; Corollary 46 with `P = P_π`
  obtain ⟨v, T, hv, hT, h30⟩ := lemma45 A B hA hB hA01 hB01 hcard ht
  obtain ⟨π, hπ⟩ := lemma48 hCP v hv hcard hn hQ
  refine ⟨π, (corollary46 v T hv hT h30 (permMat_isDS π) hQ).trans ?_⟩
  rw [hx3, ← hd] at hπ
  rw [← hx, ← hd]
  have hρ : 2 * Real.sqrt 2 / t * rhoSupp v (permMat π) Q ≤
      2 * Real.sqrt 2 / t * (20 * Real.sqrt 2 * d * x ^ 2) := by gcongr
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have ht2 : t * t = 20 * d * x ^ 2 := by
    rw [htdef]
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 20 * d by linarith)
    linear_combination x ^ 2 * this
  have key : 2 * Real.sqrt 2 / t * (20 * Real.sqrt 2 * d * x ^ 2) = 4 * t := by
    rw [div_mul_eq_mul_div, div_eq_iff ht.ne']
    linear_combination (40 * d * x ^ 2) * h2 - 4 * ht2
  have hs20 : Real.sqrt 20 ≤ 9 / 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 20 by norm_num), Real.sqrt_nonneg 20]
  have htd : t = Real.sqrt 20 * Real.sqrt d * x := by
    rw [htdef, Real.sqrt_mul (by norm_num)]
  have h8 : 8 * t ≤ 36 * Real.sqrt d * x := by
    rw [htd]
    have : 0 ≤ Real.sqrt d * x := mul_nonneg (Real.sqrt_nonneg _) hxpos.le
    nlinarith
  linarith

end GsimOT
