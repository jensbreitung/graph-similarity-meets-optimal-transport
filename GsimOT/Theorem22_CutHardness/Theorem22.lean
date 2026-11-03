import GsimOT.Theorem22_CutHardness.Claim56_LeafMass
import GsimOT.Theorem22_CutHardness.Claim57_SplitMass
import GsimOT.Theorem22_CutHardness.Claim58_WrongVertex
import GsimOT.Theorem22_CutHardness.Claim59_NearIdentity
import GsimOT.Theorem22_CutHardness.BaseGraphs

/-!
# Theorem 18: hardness of approximating `d^OT_□`

Theorem 18 of the paper (p. 13, l. 443–444; proof in App. G, pp. 57–62, l. 1826–1988): for every
`ε > 0`, unless `P = NP`, there is no polynomial-time approximation algorithm computing `d^OT_□`
with multiplicative error guarantee `17/16 - ε`. This is Theorem 4 (3) (p. 4, l. 138–139).

The reduction from MaxCut takes, for a graph `F` on `n` vertices and `m` edges, base graphs `G'`,
`H'` on `n' = 2m + n` vertices with `‖A_{G'} - A_{H'}‖_□ = 2 · maxcut(F)` under the canonical
bijection (`BaseGraphs.lean`) and attaches `ℓᵢ = i (n² + n) k` leaves to the `i`-th vertex of both
graphs (p. 57, l. 1826–1834). For fixed `δ ∈ (0, 1)` and `k = ⌈1600 n⁶/δ⌉` (p. 62, l. 1977),
`2(1 - δ) · maxcut(F) ≤ d^OT_□(G, H) ≤ 2 · maxcut(F)` (l. 1982–1983); the case `δ = 1/34` is
Eq. (47) (p. 58, l. 1838), `(33/17) · maxcut(F) ≤ d^OT_□(G, H) ≤ 2 · maxcut(F)`.

* `dOTCut_addLeaves_le`, `le_dOTCut_addLeaves`: the upper and the lower bound, with the paper's
  constants, for base graphs with the properties used in the paper (as hypotheses: `n' ≤ n²`,
  degrees at most `n - 1`, `‖A_{G'} - A_{H'}‖_□ = 2c` with `1 ≤ c ≤ n²/4`).
* `maxcut_dOTCut_bounds_paper`: the complete reduction exactly as in the paper, with the base graphs
  of `BaseGraphs.lean`, `n = |V(F)|` and `k = ⌈1600 n⁶/δ⌉`; the three properties are proved here
  (`card_adj_anG_le`, `card_adj_anH_le`, `two_mul_card_edge_add_le`, `four_mul_maxcut_le`).
  `maxcut_dOTCut_bounds_eq47` is Eq. (47), the case `δ = 1/34`.
* `maxcut_dOTCut_bounds`: the same with `n'` in place of `n` in the leaf counts (which needs
  neither the degree bound nor `n' ≤ n²`).

The complexity-theoretic conclusion (via [Hås01], p. 58, l. 1840–1843 and p. 62, l. 1984–1988)
and the polynomial size of `G`, `H` (l. 1977–1981) are not formalised.
-/

open Finset

namespace GsimOT.Hardness

/-! ### The upper bound -/

section Upper

/-- The canonical alignment: `‖B(G, H, P_id)‖_□ ≤ ‖A_G - A_H‖_□`. -/
lemma cutNorm_B_refl_le {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    cutNorm (B G H (permMat (Equiv.refl V))) ≤ cutNorm (adj G - adj H) := by
  refine cutNorm_le _ fun S' T' ↦ ?_
  set D := adj G - adj H
  have hinj (U : Finset (V × V)) :
      Set.InjOn Prod.fst (↑(U.filter fun x : V × V ↦ x.1 = x.2) : Set (V × V)) := by
    intro x hx y hy hxy
    have hx' := (mem_filter.mp (mem_coe.mp hx)).2
    have hy' := (mem_filter.mp (mem_coe.mp hy)).2
    exact Prod.ext hxy (hx'.symm.trans (hxy.trans hy'))
  have hB (x y : V × V) : B G H (permMat (Equiv.refl V)) x y =
      if x.1 = x.2 then (if y.1 = y.2 then D x.1 y.1 else 0) else 0 := by
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    simp only [B, disc, permMat, Equiv.refl_apply, D, Pi.sub_apply]
    by_cases h1 : x1 = x2
    · subst h1
      by_cases h2 : y1 = y2
      · subst h2; simp
      · simp [h2]
    · simp [h1]
  have hsum : ∑ x ∈ S', ∑ y ∈ T', B G H (permMat (Equiv.refl V)) x y =
      ∑ v ∈ (S'.filter fun x ↦ x.1 = x.2).image Prod.fst,
        ∑ v' ∈ (T'.filter fun y ↦ y.1 = y.2).image Prod.fst, D v v' := by
    rw [sum_image (hinj S'), sum_filter]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [sum_image (hinj T'), sum_filter]
    by_cases hx : x.1 = x.2
    · simp only [hB, hx, ite_true]
    · simp only [hB, hx, ite_false, sum_const_zero]
  rw [hsum]
  exact abs_sum_le_cutNorm _ _ _

/-- Attaching the same leaves to both graphs does not change `A_G - A_H` on the base. -/
lemma cutNorm_addLeaves_sub_le {β : Type*} [Fintype β] [DecidableEq β] (G' H' : SimpleGraph β)
    [DecidableRel G'.Adj] [DecidableRel H'.Adj] (ℓ : β → ℕ) :
    cutNorm (adj (addLeaves G' ℓ) - adj (addLeaves H' ℓ)) ≤
      cutNorm (adj G' - adj H') := by
  refine cutNorm_le _ fun S T ↦ ?_
  have hsum : ∑ x ∈ S, ∑ y ∈ T, (adj (addLeaves G' ℓ) - adj (addLeaves H' ℓ)) x y =
      ∑ b ∈ S.toLeft, ∑ b' ∈ T.toLeft, (adj G' - adj H') b b' := by
    conv_lhs => rw [← toLeft_disjSum_toRight (u := S)]
    rw [sum_disjSum]
    rw [sum_eq_zero (s := S.toRight) fun t _ ↦ sum_eq_zero fun y _ ↦ by
      simp [Pi.sub_apply, adj, addLeaves_adj_inr_iff], add_zero]
    refine sum_congr rfl fun b _ ↦ ?_
    conv_lhs => rw [← toLeft_disjSum_toRight (u := T)]
    rw [sum_disjSum, sum_eq_zero (s := T.toRight) fun t _ ↦ by simp [Pi.sub_apply], add_zero]
    exact sum_congr rfl fun b' _ ↦ by simp [Pi.sub_apply]
  rw [hsum]
  exact abs_sum_le_cutNorm _ _ _

end Upper

/-! ### The lower bound -/

section Theorem22

variable {n' : ℕ} {G' H' : SimpleGraph (Fin n')} [DecidableRel G'.Adj] [DecidableRel H'.Adj]

/-- The number `ℓᵢ = i (n² + n) k` of leaves attached to the `i`-th base vertex (the paper
numbers the vertices from `1`, we from `0`). -/
def leafCount (n k : ℕ) (i : Fin n') : ℕ := (i + 1) * ((n ^ 2 + n) * k)

/-- Upper bound: `d^OT_□(G, H) ≤ ‖A_{G'} - A_{H'}‖_□ = 2 · maxcut(F)` (p. 58, l. 1839–1840:
`d^OT_□ ≤ d_□`, and the canonical bijection). -/
theorem dOTCut_addLeaves_le (ℓ : Fin n' → ℕ) :
    dOTCut (addLeaves G' ℓ) (addLeaves H' ℓ) ≤ cutNorm (adj G' - adj H') :=
  (iInf_isDS_le (f := fun Q ↦ cutNorm (B (addLeaves G' ℓ) (addLeaves H' ℓ) Q))
    (fun _ _ ↦ cutNorm_nonneg _) (permMat_isDS (Equiv.refl _))).trans
    ((cutNorm_B_refl_le _ _).trans (cutNorm_addLeaves_sub_le _ _ _))

/-- Lower bound: for `0 < δ < 1` and base graphs `G', H'` on `n' ≤ n²` vertices with degrees at
most `n - 1` and `‖A_{G'} - A_{H'}‖_□ = 2c` (`c = maxcut(F)`, so `1 ≤ c ≤ n²/4`), attaching
`ℓᵢ = i (n² + n) k` leaves with `k = ⌈1600 n⁶/δ⌉` gives `d^OT_□(G, H) ≥ 2(1 - δ) c`. This is the
case distinction of the paper (Claims 58–61) with its choice `α = δ/(200 n⁴)`, `η = α/2`,
`τ = α/(4n²)` and `k` (pp. 61–62, l. 1966–1977). -/
theorem le_dOTCut_addLeaves (n : ℕ) (hn : 1 ≤ n) (hn' : n' ≤ n ^ 2)
    (hdG : ∀ b, #{x | G'.Adj x b} ≤ n - 1) (hdH : ∀ b, #{x | H'.Adj x b} ≤ n - 1) {c : ℝ}
    (hc : cutNorm (adj G' - adj H') = 2 * c) (hc1 : 1 ≤ c) (hcn : 4 * c ≤ n ^ 2) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    2 * (1 - δ) * c ≤ dOTCut (addLeaves G' (leafCount n ⌈1600 * (n : ℝ) ^ 6 / δ⌉₊))
      (addLeaves H' (leafCount n ⌈1600 * (n : ℝ) ^ 6 / δ⌉₊)) := by
  set k := ⌈1600 * (n : ℝ) ^ 6 / δ⌉₊
  set ℓ : Fin n' → ℕ := leafCount n k
  set M := (n ^ 2 + n) * k
  have hM : ∀ b, M ≤ ℓ b := fun b ↦ by
    simp only [ℓ, leafCount, M]
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  -- numerical facts
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hnR
  have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hnR
  have hn6 : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ hnR
  have hn7 : (n : ℝ) ≤ (n : ℝ) ^ 7 := by
    calc (n : ℝ) = n * 1 := (mul_one _).symm
      _ ≤ n * (n : ℝ) ^ 6 := by gcongr
      _ = (n : ℝ) ^ 7 := by ring
  -- `δ k ≥ 1600 n⁶`, hence `k ≥ 1600 n⁶` and `δ M ≥ 1600 n⁶ (n² + n)`
  have hδk : 1600 * (n : ℝ) ^ 6 ≤ δ * k := by
    have := Nat.le_ceil (1600 * (n : ℝ) ^ 6 / δ)
    rw [div_le_iff₀ hδ0] at this
    linarith
  have hk : 1600 * (n : ℝ) ^ 6 ≤ k := by
    have : δ * (k : ℝ) ≤ k := mul_le_of_le_one_left (Nat.cast_nonneg k) hδ1.le
    linarith
  have hMR : (M : ℝ) = ((n : ℝ) ^ 2 + n) * k := by simp [M]
  have hδM : 1600 * (n : ℝ) ^ 8 + 1600 * (n : ℝ) ^ 7 ≤ δ * M := by
    have h := mul_le_mul_of_nonneg_left hδk (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 + n)
    rw [hMR]
    nlinarith
  have hdR : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub hn, Nat.cast_one]
  have hn'R : ((Fintype.card (Fin n') : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [Fintype.card_fin]; exact_mod_cast hn'
  set α : ℝ := δ / (200 * (n : ℝ) ^ 4)
  set τ : ℝ := α / (4 * (n : ℝ) ^ 2)
  have hα0 : 0 < α := by positivity
  have hα1 : α ≤ 1 / 200 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hτ0 : 0 < τ := by positivity
  -- it suffices to show `‖B‖_□ ≥ n²/2 ≥ 2c` or `‖B‖_□ ≥ 2c - δ/100`
  have hbig {x : ℝ} (hx : (n : ℝ) ^ 2 / 2 ≤ x) : 2 * (1 - δ) * c ≤ x := by
    nlinarith [mul_pos hδ0 (by linarith : (0 : ℝ) < c)]
  refine le_iInf_isDS ⟨Equiv.refl _⟩
    (f := fun Q ↦ cutNorm (B (addLeaves G' ℓ) (addLeaves H' ℓ) Q)) fun Q hQ ↦ ?_
  -- Claim 58: a base vertex sends mass `η = α/2` to leaves
  by_cases hA : ∃ v, α / 2 ≤ ∑ t, Q (.inl v) (.inr t)
  · obtain ⟨v, hv⟩ := hA
    refine hbig ((le_trans ?_ (claim56 hQ hM (by positivity) hv)))
    have : α / 2 * ((M : ℝ) - 2) / 4 = δ * ((M : ℝ) - 2) / (1600 * (n : ℝ) ^ 4) := by
      simp only [α]; field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith
  push Not at hA
  -- Claim 59: a base vertex sends mass `τ` to two base vertices
  by_cases hB : ∃ v w w', w ≠ w' ∧ τ ≤ Q (.inl v) (.inl w) ∧ τ ≤ Q (.inl v) (.inl w')
  · obtain ⟨v, w, w', hww', h1, h2⟩ := hB
    refine hbig ((le_trans ?_ (claim57 hQ hM hdH hww' hτ0.le h1 h2)))
    have : τ * ((M : ℝ) - 2 * ((n - 1 : ℕ) : ℝ)) / 2 =
        δ * ((M : ℝ) - 2 * ((n - 1 : ℕ) : ℝ)) / (1600 * (n : ℝ) ^ 6) := by
      simp only [τ, α]; field_simp; ring
    rw [this, le_div_iff₀ (by positivity), hdR]
    have hδn : δ * ((n : ℝ) - 1) ≤ (n : ℝ) - 1 :=
      mul_le_of_le_one_left (by linarith) hδ1.le
    nlinarith
  push Not at hB
  -- otherwise every base vertex sends mass `≥ 1 - α` to a single base vertex
  have hf (v : Fin n') : ∃ w, 1 - α ≤ Q (.inl v) (.inl w) := by
    obtain ⟨w, -, hw⟩ := exists_max_image univ (fun b ↦ Q (.inl v) (.inl b)) ⟨v, mem_univ v⟩
    refine ⟨w, ?_⟩
    have hsmall (b : Fin n') (hb : b ∈ univ.erase w) : Q (.inl v) (.inl b) ≤ τ := by
      by_contra! hb'
      exact absurd (hB v w b (ne_of_mem_erase hb).symm (hb'.le.trans (hw b (mem_univ b))))
        (not_lt.mpr hb'.le)
    have hrow := hQ.row_sum (.inl v)
    rw [Fintype.sum_sum_type, ← add_sum_erase _ _ (mem_univ w)] at hrow
    have h1 : ∑ b ∈ univ.erase w, Q (.inl v) (.inl b) ≤ (n' - 1 : ℕ) * τ := by
      calc ∑ b ∈ univ.erase w, Q (.inl v) (.inl b) ≤ ∑ _b ∈ univ.erase w, τ := sum_le_sum hsmall
        _ = (n' - 1 : ℕ) * τ := by simp [card_erase_of_mem]
    have h2 : ((n' - 1 : ℕ) : ℝ) * τ ≤ α / 2 := by
      have : ((n' - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
        rw [Fintype.card_fin] at hn'R; exact le_trans (by exact_mod_cast Nat.sub_le n' 1) hn'R
      calc ((n' - 1 : ℕ) : ℝ) * τ ≤ (n : ℝ) ^ 2 * τ := by gcongr
        _ = α / 4 := by simp only [τ]; field_simp
        _ ≤ α / 2 := by linarith
    have h3 := hA v
    linarith
  choose f hf using hf
  by_cases hC : ∃ i, f i ≠ i
  · -- Claim 60: some `vᵢ` is mapped to `w_{f i}` with `f i ≠ i`
    obtain ⟨i, hi⟩ := hC
    have hgap {a b : Fin n'} (hab : a < b) : (M : ℝ) ≤ (ℓ b : ℝ) - ℓ a := by
      have : ℓ a + M ≤ ℓ b := by
        simp only [ℓ, leafCount, M]
        have : (a : ℕ) + 1 + 1 ≤ b + 1 := by have := Fin.lt_def.mp hab; omega
        calc (a + 1) * ((n ^ 2 + n) * k) + (n ^ 2 + n) * k = (a + 1 + 1) * ((n ^ 2 + n) * k) := by
              ring
          _ ≤ (b + 1) * ((n ^ 2 + n) * k) := Nat.mul_le_mul_right _ this
      have : ((ℓ a + M : ℕ) : ℝ) ≤ ℓ b := by exact_mod_cast this
      push_cast at this
      linarith
    have hfin {x : ℝ} (hx : (M : ℝ) ≤ x) : (n : ℝ) ^ 2 / 2 ≤ (1 - α) * (x - ((n - 1 : ℕ) : ℝ)) := by
      rw [hdR]
      have : (n : ℝ) ^ 2 ≤ (M : ℝ) - n := by
        have h := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ k)
          (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 + n)
        rw [hMR]
        linarith
      nlinarith
    refine hbig ?_
    rcases lt_or_gt_of_ne hi with h | h
    · exact (hfin (hgap h)).trans (claim58' hQ hdH (by linarith) (hf i))
    · exact (hfin (hgap h)).trans (claim58 hQ hdG (by linarith) (hf i))
  · -- Claim 61: `Q` is close to the canonical bijection
    push Not at hC
    have h59 := claim59 (G' := G') (H' := H') (ℓ := ℓ) hQ hα0.le fun i ↦ by
      simpa [hC i] using hf i
    rw [hc] at h59
    have : 2 * α * ((Fintype.card (Fin n') : ℕ) : ℝ) ^ 2 ≤ δ / 100 := by
      calc 2 * α * ((Fintype.card (Fin n') : ℕ) : ℝ) ^ 2 ≤ 2 * α * ((n : ℝ) ^ 2) ^ 2 := by
            gcongr
        _ = δ / 100 := by simp only [α]; field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hc1 hδ0.le]

end Theorem22

/-! ### Reindexing and the complete reduction -/

section Reduction

/-- A graph on `W` transported to `V` along `e : V ≃ W`. -/
def reindexGraph {V W : Type*} (G : SimpleGraph W) (e : V ≃ W) : SimpleGraph V := G.comap e

instance {V W : Type*} (G : SimpleGraph W) [DecidableRel G.Adj] (e : V ≃ W) :
    DecidableRel (reindexGraph G e).Adj := fun x y ↦
  inferInstanceAs (Decidable (G.Adj (e x) (e y)))

/-- The cut norm is invariant under reindexing rows and columns by the same bijection. -/
lemma cutNorm_submatrix_equiv {X X' : Type*} [Fintype X] [Fintype X'] [DecidableEq X]
    [DecidableEq X'] (M : Matrix X X ℝ) (e : X' ≃ X) :
    cutNorm (M.submatrix e e) = cutNorm M := by
  apply le_antisymm
  · refine cutNorm_le _ fun S T ↦ ?_
    have := abs_sum_le_cutNorm M (S.map e.toEmbedding) (T.map e.toEmbedding)
    simpa [sum_map] using this
  · refine cutNorm_le _ fun S T ↦ ?_
    have := abs_sum_le_cutNorm (M.submatrix e e) (S.map e.symm.toEmbedding)
      (T.map e.symm.toEmbedding)
    simpa [sum_map] using this

/-- In any simple graph, a vertex has at most `|V| - 1` neighbours. -/
lemma card_adj_le_card_sub_one {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (b : V) : #{x | G.Adj x b} ≤ Fintype.card V - 1 := by
  classical
  calc #{x | G.Adj x b} ≤ #(univ.erase b) :=
        card_le_card fun x hx ↦ mem_erase.mpr ⟨G.ne_of_adj (mem_filter.mp hx).2, mem_univ x⟩
    _ = Fintype.card V - 1 := by rw [card_erase_of_mem (mem_univ b), card_univ]

variable {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]

/-- The number `n' = 2m + n` of base vertices. -/
abbrev nBase : ℕ := Fintype.card ((Edge F × Bool) ⊕ Fin n)

/-- The base graph `G'` with vertex set `Fin n'`. -/
noncomputable def baseG : SimpleGraph (Fin (nBase F)) :=
  reindexGraph (anG F) (Fintype.equivFin ((Edge F × Bool) ⊕ Fin n)).symm

/-- The base graph `H'` with vertex set `Fin n'`. -/
noncomputable def baseH : SimpleGraph (Fin (nBase F)) :=
  reindexGraph (anH F) (Fintype.equivFin ((Edge F × Bool) ⊕ Fin n)).symm

noncomputable instance : DecidableRel (baseG F).Adj :=
  inferInstanceAs (DecidableRel
    (reindexGraph (anG F) (Fintype.equivFin ((Edge F × Bool) ⊕ Fin n)).symm).Adj)
noncomputable instance : DecidableRel (baseH F).Adj :=
  inferInstanceAs (DecidableRel
    (reindexGraph (anH F) (Fintype.equivFin ((Edge F × Bool) ⊕ Fin n)).symm).Adj)

lemma cutNorm_baseG_sub_baseH :
    cutNorm (adj (baseG F) - adj (baseH F)) = 2 * maxcut F := by
  rw [← cutNorm_anG_sub_anH F,
    ← cutNorm_submatrix_equiv (adj (anG F) - adj (anH F) : Matrix _ _ ℝ)
      (Fintype.equivFin ((Edge F × Bool) ⊕ Fin n)).symm]
  congr 1

/-- The leaf counts of the reduction with `n'` in place of `n`: `ℓᵢ = i (n'² + n') k` with
`k = ⌈1600 n'⁶/δ⌉`. -/
noncomputable abbrev leavesF (δ : ℝ) : Fin (nBase F) → ℕ :=
  leafCount (nBase F) ⌈1600 * (nBase F : ℝ) ^ 6 / δ⌉₊

/-- **Theorem 18** (correctness of the reduction from MaxCut), variant with `n' = |V(G')|` in
place of `n = |V(F)|` in the leaf counts: for `0 < δ < 1` and a graph `F` with an edge, the
graphs `G, H` obtained from the base graphs `G', H'` by attaching `ℓᵢ` leaves satisfy
`2(1 - δ) · maxcut(F) ≤ d^OT_□(G, H) ≤ 2 · maxcut(F)`. -/
theorem maxcut_dOTCut_bounds {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hF : ∃ u v, F.Adj u v) :
    2 * (1 - δ) * (maxcut F : ℝ) ≤
        dOTCut (addLeaves (baseG F) (leavesF F δ)) (addLeaves (baseH F) (leavesF F δ)) ∧
      dOTCut (addLeaves (baseG F) (leavesF F δ)) (addLeaves (baseH F) (leavesF F δ)) ≤
        2 * maxcut F := by
  obtain ⟨u, v, huv⟩ := hF
  -- the edge `uv` is cut by `{min u v}`
  have hm1 : 1 ≤ maxcut F := by
    rcases lt_or_gt_of_ne (F.ne_of_adj huv) with h | h
    · have : 1 ≤ cutSize F {u} :=
        card_pos.mpr ⟨⟨(u, v), h, huv⟩, by simp [(Fin.ne_of_lt h).symm]⟩
      exact this.trans (cutSize_le_maxcut F _)
    · have : 1 ≤ cutSize F {v} :=
        card_pos.mpr ⟨⟨(v, u), h, huv.symm⟩, by simp [(Fin.ne_of_lt h).symm]⟩
      exact this.trans (cutSize_le_maxcut F _)
  have hmaxm : maxcut F ≤ Fintype.card (Edge F) :=
    Finset.sup_le fun C _ ↦ card_le_univ _
  have hcard : nBase F = 2 * Fintype.card (Edge F) + n := by
    simp only [nBase, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    ring
  have hn : 1 ≤ nBase F := by
    have : 1 ≤ Fintype.card (Edge F) := hm1.trans hmaxm
    omega
  refine ⟨le_dOTCut_addLeaves (nBase F) hn (Nat.le_self_pow two_ne_zero _)
    (fun b ↦ by simpa using card_adj_le_card_sub_one (baseG F) b)
    (fun b ↦ by simpa using card_adj_le_card_sub_one (baseH F) b)
    (cutNorm_baseG_sub_baseH F) (by exact_mod_cast hm1) ?_ hδ0 hδ1, ?_⟩
  · have h1 : (maxcut F : ℝ) ≤ Fintype.card (Edge F) := by exact_mod_cast hmaxm
    have h2 : ((nBase F : ℕ) : ℝ) = 2 * Fintype.card (Edge F) + n := by
      rw [hcard]; push_cast; ring
    have h3 : (1 : ℝ) ≤ Fintype.card (Edge F) := by exact_mod_cast hm1.trans hmaxm
    rw [h2]
    nlinarith
  · rw [← cutNorm_baseG_sub_baseH F]
    exact dOTCut_addLeaves_le _

end Reduction

/-! ### The construction with the paper's leaf counts -/

section PaperLeaves

/-- Reindexing a graph does not change neighbourhood sizes. -/
lemma card_adj_reindexGraph {V W : Type*} [Fintype V] [Fintype W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (e : V ≃ W) (b : V) :
    #{x | (reindexGraph G e).Adj x b} = #{y | G.Adj y (e b)} := by
  rw [← card_map e.toEmbedding]
  congr 1
  ext y
  simp only [mem_map, mem_filter, mem_univ, true_and, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hy; exact ⟨e.symm y, by simpa [reindexGraph] using hy, by simp⟩

/-- A neighbourhood bound in a bipartite graph `bipGraph P` on `R ⊕ C`: if every `r` has at
most one neighbour, `C` has at least two elements, and `r ↦ g r` is injective on the
neighbours of `c` and avoids `c`, then every vertex has at most `|C| - 1` neighbours. -/
lemma card_adj_bipGraph_le {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]
    (P : R → C → Prop) [DecidableRel P] (hC : 2 ≤ Fintype.card C)
    (h1 : ∀ r c c', P r c → P r c' → c = c') (g : R → C)
    (hg : ∀ c r r', P r c → P r' c → g r = g r' → r = r') (hgc : ∀ r c, P r c → g r ≠ c)
    (b : R ⊕ C) : #{x | (bipGraph P).Adj x b} ≤ Fintype.card C - 1 := by
  classical
  cases b with
  | inl r =>
    have : #{x | (bipGraph P).Adj x (.inl r)} ≤ 1 := by
      rw [card_le_one]
      intro x hx y hy
      simp only [mem_filter, mem_univ, true_and] at hx hy
      cases x with
      | inl _ => exact absurd hx bipGraph_adj_inl_inl
      | inr c =>
        cases y with
        | inl _ => exact absurd hy bipGraph_adj_inl_inl
        | inr c' => rw [h1 r c c' hx hy]
    omega
  | inr c =>
    have hsub : ({x | (bipGraph P).Adj x (.inr c)} : Finset (R ⊕ C)) =
        ({r | P r c} : Finset R).map Function.Embedding.inl := by
      ext x
      cases x <;> simp
    rw [hsub, card_map, ← card_univ, ← card_erase_of_mem (mem_univ c)]
    refine card_le_card_of_injOn g (fun r hr ↦ ?_) fun r hr r' hr' h ↦ ?_
    · have hr := (mem_filter.mp hr).2
      exact mem_erase.mpr ⟨hgc r c hr, mem_univ _⟩
    · exact hg c r r' (mem_filter.mp hr).2 (mem_filter.mp hr').2 h

variable {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]

omit [DecidableRel F.Adj] in
/-- An edge `uv` with `u < v` is determined by its endpoints `{u, v}`. -/
lemma edge_eq_of_endpoints {e e' : Edge F} {a b : Fin n}
    (he : (e.1.1 = a ∧ e.1.2 = b) ∨ (e.1.1 = b ∧ e.1.2 = a))
    (he' : (e'.1.1 = a ∧ e'.1.2 = b) ∨ (e'.1.1 = b ∧ e'.1.2 = a)) : e = e' := by
  revert he he'
  obtain ⟨⟨u, v⟩, huv, -⟩ := e
  obtain ⟨⟨u', v'⟩, huv', -⟩ := e'
  intro he he'
  simp only at he he' huv huv'
  apply Subtype.ext
  simp only [Prod.mk.injEq]
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd (huv.trans huv') (lt_irrefl _)

/-- The base graph `G'` of [AN06, Prop. 3.2] has maximum degree at most `n - 1` (proofs of
Claims 59 and 60, p. 59, l. 1885–1892 and p. 60, l. 1921–1922). -/
lemma card_adj_anG_le (hn : 2 ≤ n) (b) : #{x | (anG F).Adj x b} ≤ n - 1 := by
  have := card_adj_bipGraph_le (C := Fin n)
    (fun r c ↦ (r.2 = true ∧ c = r.1.1.1) ∨ (r.2 = false ∧ c = r.1.1.2)) (by simpa using hn)
    (fun r c c' h h' ↦ by
      rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rcases h' with ⟨h2, rfl⟩ | ⟨h2, rfl⟩ <;>
        simp_all)
    (fun r ↦ if r.2 then r.1.1.2 else r.1.1.1)
    (fun c r r' h h' hg ↦ by
      obtain ⟨e, s⟩ := r
      obtain ⟨e', s'⟩ := r'
      have hs : s = s' := by
        rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rcases h' with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;>
          simp_all only [ite_true, ite_false, Bool.false_eq_true] <;>
          exact absurd (e.2.1.trans (h3 ▸ hg ▸ e'.2.1)) (lt_irrefl _)
      subst hs
      refine Prod.ext (edge_eq_of_endpoints F (a := c) (b := if s then e.1.2 else e.1.1)
        ?_ ?_) rfl
      · cases s <;> simp_all
      · cases s <;> simp_all)
    (fun r c h ↦ by
      rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> simp only [h1, ite_true, ite_false,
        Bool.false_eq_true]
      · exact r.1.2.1.ne'
      · exact r.1.2.1.ne)
    b
  rw [Fintype.card_fin] at this
  convert this using 3
  exact Iff.rfl

/-- The same for `H'`. -/
lemma card_adj_anH_le (hn : 2 ≤ n) (b) : #{x | (anH F).Adj x b} ≤ n - 1 := by
  have := card_adj_bipGraph_le (C := Fin n)
    (fun r c ↦ (r.2 = true ∧ c = r.1.1.2) ∨ (r.2 = false ∧ c = r.1.1.1)) (by simpa using hn)
    (fun r c c' h h' ↦ by
      rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rcases h' with ⟨h2, rfl⟩ | ⟨h2, rfl⟩ <;>
        simp_all)
    (fun r ↦ if r.2 then r.1.1.1 else r.1.1.2)
    (fun c r r' h h' hg ↦ by
      obtain ⟨e, s⟩ := r
      obtain ⟨e', s'⟩ := r'
      have hs : s = s' := by
        rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> rcases h' with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;>
          simp_all only [ite_true, ite_false, Bool.false_eq_true] <;>
          exact absurd (e.2.1.trans (h3 ▸ hg ▸ e'.2.1)) (lt_irrefl _)
      subst hs
      refine Prod.ext (edge_eq_of_endpoints F (a := c) (b := if s then e.1.1 else e.1.2)
        ?_ ?_) rfl
      · cases s <;> simp_all
      · cases s <;> simp_all)
    (fun r c h ↦ by
      rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> simp only [h1, ite_true, ite_false,
        Bool.false_eq_true]
      · exact r.1.2.1.ne
      · exact r.1.2.1.ne')
    b
  rw [Fintype.card_fin] at this
  convert this using 3
  exact Iff.rfl

/-- `n' = 2m + n ≤ n²` (p. 62, l. 1969): the signed edges inject into the ordered pairs of
distinct vertices. -/
lemma two_mul_card_edge_add_le : 2 * Fintype.card (Edge F) + n ≤ n ^ 2 := by
  classical
  let g : Edge F × Bool → Fin n × Fin n := fun r ↦ if r.2 then r.1.1 else r.1.1.swap
  have hinj : Set.InjOn g ↑(univ : Finset (Edge F × Bool)) := by
    rintro ⟨⟨⟨u, v⟩, huv, hF⟩, s⟩ hr ⟨⟨⟨u', v'⟩, huv', hF'⟩, s'⟩ hr' h
    simp only [g] at h huv huv'
    cases s <;> cases s' <;> simp only [ite_true, Bool.false_eq_true, ite_false,
      Prod.swap_prod_mk, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
    · rfl
    · exact absurd (huv.trans huv') (lt_irrefl _)
    · exact absurd (huv.trans huv') (lt_irrefl _)
    · rfl
  have hmaps : ∀ r ∈ (univ : Finset (Edge F × Bool)), g r ∈ (univ : Finset (Fin n)).offDiag := by
    rintro ⟨⟨⟨u, v⟩, huv, -⟩, s⟩ -
    cases s <;> simp [g, huv.ne, huv.ne']
  have h := card_le_card_of_injOn g hmaps hinj
  rw [offDiag_card, card_univ, Fintype.card_prod, Fintype.card_bool, card_univ,
    Fintype.card_fin] at h
  have : n ≤ n * n := Nat.le_mul_self n
  rw [sq]
  omega

/-- `4 · maxcut(F) ≤ n²` (p. 59, l. 1880): a vertex set `C` cuts at most
`|C| · |V(F) \ C| ≤ n²/4` edges. -/
lemma four_mul_maxcut_le : 4 * maxcut F ≤ n ^ 2 := by
  classical
  have hcut (C : Finset (Fin n)) : 4 * cutSize F C ≤ n ^ 2 := by
    let g : Edge F → Fin n × Fin n := fun e ↦ if e.1.1 ∈ C then e.1 else e.1.swap
    have hmaps : ∀ e ∈ ({e : Edge F | (e.1.1 ∈ C ↔ e.1.2 ∉ C)} : Finset (Edge F)),
        g e ∈ C ×ˢ Cᶜ := by
      intro e he
      simp only [mem_filter, mem_univ, true_and] at he
      by_cases hu : e.1.1 ∈ C <;> simp_all [g]
    have hinj : Set.InjOn g ↑({e : Edge F | (e.1.1 ∈ C ↔ e.1.2 ∉ C)} : Finset (Edge F)) := by
      rintro ⟨⟨u, v⟩, huv, hF⟩ he ⟨⟨u', v'⟩, huv', hF'⟩ he' h
      simp only [g] at h huv huv'
      apply Subtype.ext
      by_cases hu : u ∈ C <;> by_cases hu' : u' ∈ C <;>
        simp only [hu, hu', ite_true, ite_false, Prod.swap_prod_mk, Prod.mk.injEq] at h <;>
        obtain ⟨rfl, rfl⟩ := h
      · rfl
      · exact absurd (huv.trans huv') (lt_irrefl _)
      · exact absurd (huv.trans huv') (lt_irrefl _)
      · rfl
    have h := card_le_card_of_injOn g hmaps hinj
    unfold cutSize
    rw [card_product, card_compl, Fintype.card_fin] at h
    have hC : #C ≤ n := by simpa using card_le_univ C
    have : 4 * (#C * (n - #C)) ≤ n ^ 2 := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hC
      have hd' : n - #C = d := by omega
      rw [hd', show n ^ 2 = (#C + d) ^ 2 from congrArg (· ^ 2) hd]
      nlinarith [sq_nonneg ((#C : ℤ) - d)]
    exact (Nat.mul_le_mul_left 4 h).trans this
  obtain ⟨C, -, hC⟩ := exists_mem_eq_sup (univ : Finset (Finset (Fin n))) univ_nonempty
    (cutSize F)
  rw [maxcut, hC]
  exact hcut C

/-- The leaf counts of the paper, `ℓᵢ = i (n² + n) k` with `n = |V(F)|` and `k = ⌈1600 n⁶/δ⌉`
(p. 57, l. 1833, and p. 62, l. 1977). -/
noncomputable abbrev leavesPaper (δ : ℝ) : Fin (nBase F) → ℕ :=
  leafCount n ⌈1600 * (n : ℝ) ^ 6 / δ⌉₊

/-- **Theorem 18** (correctness of the reduction from MaxCut), exactly as in the paper: for
`0 < δ < 1` and a graph `F` on `n` vertices with an edge, the graphs `G, H` obtained from the
base graphs `G', H'` by attaching `ℓᵢ = i (n² + n) k` leaves with `k = ⌈1600 n⁶/δ⌉` to the `i`-th
base vertex satisfy `2(1 - δ) · maxcut(F) ≤ d^OT_□(G, H) ≤ 2 · maxcut(F)` (p. 62, l. 1983). -/
theorem maxcut_dOTCut_bounds_paper {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hF : ∃ u v, F.Adj u v) :
    2 * (1 - δ) * (maxcut F : ℝ) ≤
        dOTCut (addLeaves (baseG F) (leavesPaper F δ)) (addLeaves (baseH F) (leavesPaper F δ)) ∧
      dOTCut (addLeaves (baseG F) (leavesPaper F δ)) (addLeaves (baseH F) (leavesPaper F δ)) ≤
        2 * maxcut F := by
  obtain ⟨u, v, huv⟩ := hF
  have hn : 2 ≤ n := by
    have h1 := u.2
    have h2 := v.2
    have : (u : ℕ) ≠ v := fun h ↦ F.ne_of_adj huv (Fin.ext h)
    omega
  have hm1 : 1 ≤ maxcut F := by
    rcases lt_or_gt_of_ne (F.ne_of_adj huv) with h | h
    · have : 1 ≤ cutSize F {u} :=
        card_pos.mpr ⟨⟨(u, v), h, huv⟩, by simp [(Fin.ne_of_lt h).symm]⟩
      exact this.trans (cutSize_le_maxcut F _)
    · have : 1 ≤ cutSize F {v} :=
        card_pos.mpr ⟨⟨(v, u), h, huv.symm⟩, by simp [(Fin.ne_of_lt h).symm]⟩
      exact this.trans (cutSize_le_maxcut F _)
  have hcard : nBase F = 2 * Fintype.card (Edge F) + n := by
    simp only [nBase, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    ring
  refine ⟨le_dOTCut_addLeaves n (by omega) (hcard ▸ two_mul_card_edge_add_le F)
    (fun b ↦ ?_) (fun b ↦ ?_) (cutNorm_baseG_sub_baseH F) (by exact_mod_cast hm1)
    (by exact_mod_cast four_mul_maxcut_le F) hδ0 hδ1, ?_⟩
  · have h : #{x | (baseG F).Adj x b} = #{x | (reindexGraph (anG F)
        (Fintype.equivFin ((Edge F × Bool) ⊕ Fin n)).symm).Adj x b} := rfl
    rw [h, card_adj_reindexGraph]
    exact card_adj_anG_le F hn _
  · have h : #{x | (baseH F).Adj x b} = #{x | (reindexGraph (anH F)
        (Fintype.equivFin ((Edge F × Bool) ⊕ Fin n)).symm).Adj x b} := rfl
    rw [h, card_adj_reindexGraph]
    exact card_adj_anH_le F hn _
  · rw [← cutNorm_baseG_sub_baseH F]
    exact dOTCut_addLeaves_le _

/-- **Eq. (47)** (p. 58, l. 1838): `(33/17) · maxcut(F) ≤ d^OT_□(G, H) ≤ 2 · maxcut(F)` for a graph
`F` with an edge, the case `δ = 1/34` of `maxcut_dOTCut_bounds_paper` (`k = ⌈1600 · 34 · n⁶⌉`). -/
theorem maxcut_dOTCut_bounds_eq47 (hF : ∃ u v, F.Adj u v) :
    33 / 17 * (maxcut F : ℝ) ≤ dOTCut (addLeaves (baseG F) (leavesPaper F (1 / 34)))
        (addLeaves (baseH F) (leavesPaper F (1 / 34))) ∧
      dOTCut (addLeaves (baseG F) (leavesPaper F (1 / 34)))
        (addLeaves (baseH F) (leavesPaper F (1 / 34))) ≤ 2 * maxcut F := by
  obtain ⟨h1, h2⟩ := maxcut_dOTCut_bounds_paper F (δ := 1 / 34) (by norm_num) (by norm_num) hF
  exact ⟨by linarith, h2⟩

end PaperLeaves

end GsimOT.Hardness
