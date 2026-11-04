/-
# Lemma 24: the fractional alignment

Paper, Appendix C.1, Lemma 24 (p. 22, l. 707; proof pp. 22–23, l. 708–725):
`d^OT_ed(G, H) ≤ 3N + 1`.

Proof (paper).  Let `π₋, π₊ ∈ Bij(V, W)` be the compliant bijections with `π₋(v_i) = w_{i-1}` and
`π₊(v_i) = w_{i+1}`, and `Q := ½(P_{π₋} + P_{π₊})`.  By Lemma 22 the cost can be computed on `G'`
and `H'`.  Pairs of markers contribute nothing, and as `ℓ(v_i, π₋(v_i)) = ℓ(v_i, π₊(v_i)) = 1`,
Lemma 23 gives `2N` from the core-marker pairs.  Each core edge of `G'` is preserved with
probability `½`, giving `(N - 1)/2`, and the same holds for `H'`; the isolated core vertices `v₀`
and `w_N` cost at most one each.  In total, `C_ed(Q) ≤ 2N + (N - 1) + 2 = 3N + 1`.

Formalisation notes.
* With the identification `v_i ↔ w_{i+1}`, `π₊` is the identity on the core vertices and `π₋` maps
  the core vertex `c` to `c - 1 (mod N)` (`predCore`).
* `costEdit_witness`: `C_ed(Q) = 3N`, hence Lemma 24 (`lemma24`).  The core-marker pairs cost
  `2N` (Lemma 23 and `sum_ell_witness`) and the core-core pairs
  `¼ (2(N - 1) + 2 + 2 + 2(N - 1)) = N` (`coreCost_witness`); the four terms are the cases
  `(π₊, π₊)`, `(π₊, π₋)`, `(π₋, π₊)`, `(π₋, π₋)` for the two vertices of a pair.  The two mixed
  cases cost `2` each: the exceptional edge `{v_{N-1}, v_{N+1}}`, whose endpoints are both mapped
  to `w_N`, and the pair `(v₀, v₀)`, which is mapped onto the core edge `{w_{2N-1}, w₁}`
  (Figure 5).
-/
import GsimOT.Proposition5_EditLowerBound.CoreEdges

open Finset

namespace GsimOT.Prop5

variable {N : ℕ}

/-! ### The bijection `π₋` on the core vertices -/

/-- `c ↦ c - 1 (mod N)`: the core part of `π₋`, as `π₋(v_{2c}) = w_{2c-1}` is the core vertex
`c - 1` of `H'` (and `w_{2N-1}` the core vertex `N - 1`). -/
def predCore (N : ℕ) : Fin N ≃ Fin N where
  toFun c := ⟨if c.val = 0 then N - 1 else c.val - 1, by have := c.isLt; split_ifs <;> omega⟩
  invFun c := ⟨if c.val = N - 1 then 0 else c.val + 1, by have := c.isLt; split_ifs <;> omega⟩
  left_inv c := by
    have := c.isLt
    apply Fin.ext
    simp only
    split_ifs <;> omega
  right_inv c := by
    have := c.isLt
    apply Fin.ext
    simp only
    split_ifs at * <;> omega

lemma predCore_val (c : Fin N) :
    (predCore N c).val = if c.val = 0 then N - 1 else c.val - 1 := rfl

/-! ### The cost of the core-core pairs -/

/-- `(π₊, π₊)`: no core edge is preserved. -/
lemma pres_id_id (hN : Odd N) : pres N (Equiv.refl (Fin N)) (Equiv.refl (Fin N)) = 0 := by
  rw [pres_eq hN]
  refine sum_eq_zero fun c _ => ite_eq_right fun ⟨hc, h1, _⟩ => ?_
  have := partner_val hc
  simp only [Equiv.refl_apply] at h1
  omega

/-- `(π₋, π₋)`: no core edge is preserved. -/
lemma pres_pred_pred (hN : Odd N) : pres N (predCore N) (predCore N) = 0 := by
  rw [pres_eq hN]
  refine sum_eq_zero fun c _ => ite_eq_right fun ⟨hc, h1, _⟩ => ?_
  have := partner_val hc
  have := c.isLt
  rw [predCore_val, predCore_val] at h1
  split_ifs at h1 <;> omega

/-- `(π₊, π₋)`: all core edges `{c, N - c}` but the exceptional one `{v_{N-1}, v_{N+1}}`
(`2c + 1 = N`) are preserved. -/
lemma pres_id_pred (hN : Odd N) (h3 : 3 ≤ N) :
    pres N (Equiv.refl (Fin N)) (predCore N) = N - 2 := by
  obtain ⟨m, hm⟩ := hN
  rw [pres_eq ⟨m, hm⟩, ← sum_ne_two (fun c => 1 ≤ c ∧ c ≠ m) (a := m) (by omega) (by omega)
    fun c _ => Iff.rfl]
  refine sum_congr rfl fun c _ => if_congr ?_ rfl rfl
  have := c.isLt
  simp only [Equiv.refl_apply, ne_eq, Fin.ext_iff, predCore_val]
  by_cases hc : 1 ≤ c.val
  · have := partner_val hc
    split_ifs <;> omega
  · omega

/-- `(π₋, π₊)`: all core edges `{c, N - c}` but the exceptional one (`2c = N + 1`) are
preserved. -/
lemma pres_pred_id (hN : Odd N) (h3 : 3 ≤ N) :
    pres N (predCore N) (Equiv.refl (Fin N)) = N - 2 := by
  obtain ⟨m, hm⟩ := hN
  rw [pres_eq ⟨m, hm⟩, ← sum_ne_two (fun c => 1 ≤ c ∧ c ≠ m + 1) (a := m + 1) (by omega)
    (by omega) fun c _ => Iff.rfl]
  refine sum_congr rfl fun c _ => if_congr ?_ rfl rfl
  have := c.isLt
  simp only [Equiv.refl_apply, ne_eq, Fin.ext_iff, predCore_val]
  by_cases hc : 1 ≤ c.val
  · have := partner_val hc
    split_ifs <;> omega
  · omega

/-! ### The witness `Q = ½(P_{π₋} + P_{π₊})` -/

/-- `Q` restricted to the core vertices: `½(P_{π₊} + P_{π₋})`. -/
noncomputable def Rwit (N : ℕ) : Fin N → Fin N → ℝ := avgPerm (Equiv.refl (Fin N)) (predCore N)

/-- **The fractional alignment `Q = ½(P_{π₋} + P_{π₊})`** of Lemma 24; it is compliant. -/
noncomputable def Qwit (N : ℕ) : VN N → VN N → ℝ := extendId (extMarkers (Rwit N))

lemma Rwit_isDS : IsDS (Rwit N) := avgPerm_isDS _ _

lemma Qwit_isDS : IsDS (Qwit N) := extendId_isDS (extMarkers_isDS Rwit_isDS)

/-- `ℓ(v_i, π₊(v_i)) = 1`. -/
lemma ell_self (c : Fin N) : ell c c = 1 := by
  have := c.isLt
  simp only [ell, posG, posH, cycDist]
  omega

/-- `ℓ(v_i, π₋(v_i)) = 1`. -/
lemma ell_predCore (c : Fin N) : ell c (predCore N c) = 1 := by
  have := c.isLt
  simp only [ell, posG, posH, cycDist, predCore_val]
  split_ifs <;> omega

/-- The core-core pairs cost `N` under `Q`. -/
lemma coreCost_witness (hN : Odd N) (h3 : 3 ≤ N) : coreCost N (Rwit N) = N := by
  rw [Rwit, coreCost_avgPerm, mixCore_eq hN, mixCore_eq hN, mixCore_eq hN, mixCore_eq hN,
    pres_id_id hN, pres_pred_pred hN, pres_id_pred hN h3, pres_pred_id hN h3]
  ring

/-- The core-marker pairs: `∑ Q(v_i, w_j) ℓ(v_i, w_j) = N`. -/
lemma sum_ell_witness : ∑ c, ∑ d, Rwit N c d * ell c d = N := by
  simp only [Rwit, sum_avgPerm_mul, Equiv.refl_apply, ell_self, ell_predCore]
  norm_num

/-- `C_ed(Q) = 3N`: the exact cost of the witness of Lemma 24. -/
theorem costEdit_witness (hN : Odd N) (h3 : 3 ≤ N) :
    costEdit (GN N) (HN N) (Qwit N) = 3 * N := by
  rw [Qwit, lemma23 Rwit_isDS, coreCost_witness hN h3, sum_ell_witness]
  ring

/-- **Lemma 24.** `d^OT_ed(G, H) ≤ 3N + 1`. -/
theorem lemma24 (hN : Odd N) (h3 : 3 ≤ N) : dOTEdit (GN N) (HN N) ≤ 3 * N + 1 :=
  calc dOTEdit (GN N) (HN N) ≤ costEdit (GN N) (HN N) (Qwit N) := dOTEdit_le Qwit_isDS
    _ = 3 * N := costEdit_witness hN h3
    _ ≤ 3 * N + 1 := by linarith

end GsimOT.Prop5
