/-
# Doubly stochastic matrices: further facts

Facts about `DS(V, W)` (`IsDS` in `GsimOT.Common.Basic`) that several proofs share:

* `IsDS.exists_ne_zero`: every row has a nonzero entry;
* `IsDS.sum_mul_fst`, `IsDS.sum_mul_snd`, `IsDS.sum_mul_mul_fst`, `IsDS.sum_mul_mul_snd`: sums over
  `V × W` against `Q` that collapse by the row and column sums;
* `sum_permMat_mul`: a sum over `V × W` against `P_π` collapses to a sum over `V`;
* `isCompact_setOf_isDS`: `DS(V, W)` is compact;
* `iInf_isDS_le`, `le_iInf_isDS`: bounds for an infimum over `DS(V, W)`, the form of all
  optimal-transport distances (`dOTOne`, `dOTEdit`, `dOTCut`, `dOT`).
* `mass Q S T = Q(S, T)`: partial sums, with bounds by `#S` and `#T`, the bound on the number of
  rows with large mass in a column set (`card_mul_le_of_lt_mass`) and the averaging bound
  `abs_sub_sum_mul_mul_le`.
-/
import GsimOT.Common.Basic

open Finset

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W]

namespace IsDS

variable {Q : V → W → ℝ}

/-- Every row of a doubly stochastic matrix has a nonzero entry. -/
lemma exists_ne_zero (hQ : IsDS Q) (v : V) : ∃ w, Q v w ≠ 0 := by
  by_contra! h
  simpa [h] using hQ.row_sum v

/-- `∑_{(v,w)} Q(v,w) h(v) = ∑_v h(v)`. -/
lemma sum_mul_fst (hQ : IsDS Q) (h : V → ℝ) : ∑ x : V × W, Q x.1 x.2 * h x.1 = ∑ v, h v := by
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun v _ => ?_
  rw [← sum_mul, hQ.row_sum, one_mul]

/-- `∑_{(v,w)} Q(v,w) h(w) = ∑_w h(w)`. -/
lemma sum_mul_snd (hQ : IsDS Q) (h : W → ℝ) : ∑ x : V × W, Q x.1 x.2 * h x.2 = ∑ w, h w := by
  simp only [Fintype.sum_prod_type]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  rw [← sum_mul, hQ.col_sum, one_mul]

/-- `∑_{v,w,v',w'} Q(v,w) f(v,v') Q(v',w') = ∑_{v,v'} f(v,v')`. -/
lemma sum_mul_mul_fst (hQ : IsDS Q) (f : V → V → ℝ) :
    ∑ x : V × W, ∑ y : V × W, Q x.1 x.2 * f x.1 y.1 * Q y.1 y.2 = ∑ v, ∑ v', f v v' := by
  have h (x : V × W) :
      ∑ y : V × W, Q x.1 x.2 * f x.1 y.1 * Q y.1 y.2 = Q x.1 x.2 * ∑ v', f x.1 v' := by
    rw [← hQ.sum_mul_fst (f x.1), mul_sum]
    exact sum_congr rfl fun y _ => by ring
  simp_rw [h]
  exact hQ.sum_mul_fst fun v => ∑ v', f v v'

/-- `∑_{v,w,v',w'} Q(v,w) g(w,w') Q(v',w') = ∑_{w,w'} g(w,w')`. -/
lemma sum_mul_mul_snd (hQ : IsDS Q) (g : W → W → ℝ) :
    ∑ x : V × W, ∑ y : V × W, Q x.1 x.2 * g x.2 y.2 * Q y.1 y.2 = ∑ w, ∑ w', g w w' := by
  have h (x : V × W) :
      ∑ y : V × W, Q x.1 x.2 * g x.2 y.2 * Q y.1 y.2 = Q x.1 x.2 * ∑ w', g x.2 w' := by
    rw [← hQ.sum_mul_snd (g x.2), mul_sum]
    exact sum_congr rfl fun y _ => by ring
  simp_rw [h]
  exact hQ.sum_mul_snd fun w => ∑ w', g w w'

end IsDS

/-- A sum over `V × W` against `P_π` collapses to a sum over `V`. -/
lemma sum_permMat_mul [DecidableEq W] (π : V ≃ W) (f : V × W → ℝ) :
    ∑ x : V × W, permMat π x.1 x.2 * f x = ∑ v, f (v, π v) := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun v _ => ?_
  simp [permMat]

/-- `DS(V, W)` is a compact subset of `V → W → ℝ`. -/
lemma isCompact_setOf_isDS : IsCompact {Q : V → W → ℝ | IsDS Q} := by
  classical
  have hK : IsCompact (Set.univ.pi fun _ : V => Set.univ.pi fun _ : W => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hS : {Q : V → W → ℝ | IsDS Q} = (⋂ v, ⋂ w, {Q | 0 ≤ Q v w}) ∩
      ((⋂ v, {Q | ∑ w, Q v w = 1}) ∩ ⋂ w, {Q | ∑ v, Q v w = 1}) := by
    ext Q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨h.nonneg, h.row_sum, h.col_sum⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩
  have hclosed : IsClosed {Q : V → W → ℝ | IsDS Q} := by
    rw [hS]
    refine (isClosed_iInter fun v => isClosed_iInter fun w => ?_).inter
      ((isClosed_iInter fun v => ?_).inter (isClosed_iInter fun w => ?_))
    · exact isClosed_le continuous_const (by fun_prop)
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_eq (by fun_prop) continuous_const
  refine hK.of_isClosed_subset hclosed fun Q hQ => ?_
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
  exact fun v w => ⟨hQ.nonneg v w, hQ.le_one v w⟩

/-- An infimum over `DS(V, W)` of a nonnegative function is at most each of its values. -/
lemma iInf_isDS_le {f : (V → W → ℝ) → ℝ} (hf : ∀ Q, IsDS Q → 0 ≤ f Q) {Q : V → W → ℝ}
    (hQ : IsDS Q) : ⨅ Q : {Q : V → W → ℝ // IsDS Q}, f Q.1 ≤ f Q :=
  ciInf_le ⟨0, by rintro _ ⟨Q, rfl⟩; exact hf Q.1 Q.2⟩ (⟨Q, hQ⟩ : {Q : V → W → ℝ // IsDS Q})

/-- A lower bound for all values is a lower bound for an infimum over `DS(V, W)`, which is
nonempty if there is a bijection `V ≃ W`. -/
lemma le_iInf_isDS (hne : Nonempty (V ≃ W)) {f : (V → W → ℝ) → ℝ} {c : ℝ}
    (h : ∀ Q, IsDS Q → c ≤ f Q) : c ≤ ⨅ Q : {Q : V → W → ℝ // IsDS Q}, f Q.1 := by
  classical
  obtain ⟨π⟩ := hne
  have : Nonempty {Q : V → W → ℝ // IsDS Q} := ⟨⟨permMat π, permMat_isDS π⟩⟩
  exact le_ciInf fun Q => h Q.1 Q.2

/-! ### Partial sums of doubly stochastic matrices -/

section Mass

variable {Q : V → W → ℝ}

/-- `Q(S, T) = ∑_{s ∈ S, t ∈ T} Q(s, t)`. -/
def mass (Q : V → W → ℝ) (S : Finset V) (T : Finset W) : ℝ := ∑ s ∈ S, ∑ t ∈ T, Q s t

lemma mass_nonneg (hQ : IsDS Q) (S : Finset V) (T : Finset W) : 0 ≤ mass Q S T :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ hQ.nonneg _ _

lemma IsDS.sum_le_one (hQ : IsDS Q) (v : V) (T : Finset W) : ∑ t ∈ T, Q v t ≤ 1 := by
  rw [← hQ.row_sum v]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ T) fun _ _ _ ↦ hQ.nonneg _ _

lemma IsDS.sum_le_one' (hQ : IsDS Q) (S : Finset V) (w : W) : ∑ s ∈ S, Q s w ≤ 1 := by
  rw [← hQ.col_sum w]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ S) fun _ _ _ ↦ hQ.nonneg _ _

lemma mass_le_card_left (hQ : IsDS Q) (S : Finset V) (T : Finset W) : mass Q S T ≤ #S := by
  calc mass Q S T ≤ ∑ _s ∈ S, (1 : ℝ) := sum_le_sum fun s _ ↦ hQ.sum_le_one s T
    _ = #S := by simp

lemma mass_le_card_right (hQ : IsDS Q) (S : Finset V) (T : Finset W) : mass Q S T ≤ #T := by
  have h : mass Q S T = ∑ t ∈ T, ∑ s ∈ S, Q s t := sum_comm
  rw [h]
  calc ∑ t ∈ T, ∑ s ∈ S, Q s t ≤ ∑ _t ∈ T, (1 : ℝ) := sum_le_sum fun t _ ↦ hQ.sum_le_one' S t
    _ = #T := by simp

lemma mass_univ_left (hQ : IsDS Q) (T : Finset W) : mass Q univ T = #T := by
  have h : mass Q univ T = ∑ t ∈ T, ∑ s, Q s t := sum_comm
  rw [h]
  simp [hQ.col_sum]

lemma mass_univ_right (hQ : IsDS Q) (S : Finset V) : mass Q S univ = #S := by
  simp [mass, hQ.row_sum]

/-- Few rows carry much mass into `T`: `δ · #{x ∈ U | Q(x, T) > δ} ≤ #T`. -/
lemma card_mul_le_of_lt_mass (hQ : IsDS Q) (U : Finset V) (T : Finset W) (δ : ℝ) :
    #{x ∈ U | δ < ∑ t ∈ T, Q x t} * δ ≤ #T := by
  calc (#{x ∈ U | δ < ∑ t ∈ T, Q x t} : ℝ) * δ = ∑ _x ∈ {x ∈ U | δ < ∑ t ∈ T, Q x t}, δ := by
        simp
    _ ≤ ∑ x ∈ {x ∈ U | δ < ∑ t ∈ T, Q x t}, ∑ t ∈ T, Q x t :=
        sum_le_sum fun x hx ↦ (mem_filter.mp hx).2.le
    _ ≤ mass Q univ T :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦
          sum_nonneg fun _ _ ↦ hQ.nonneg _ _
    _ = #T := mass_univ_left hQ T

/-- If `Q(s, s') Q(t, t') ≥ p`, then the `Q ⊗ Q`-average of `h` is `(1 - p)`-close to
`h(s', t')` for every `h` with values in `[0, 1]`. -/
lemma abs_sub_sum_mul_mul_le (hQ : IsDS Q) (s t : V) (s' t' : W) (h : W → W → ℝ)
    (h0 : ∀ w w', 0 ≤ h w w') (h1 : ∀ w w', h w w' ≤ 1) :
    |h s' t' - ∑ w, ∑ w', Q s w * Q t w' * h w w'| ≤ 1 - Q s s' * Q t t' := by
  classical
  set X := ∑ w, ∑ w', Q s w * Q t w' * h w w'
  set p := Q s s' * Q t t'
  have hsingle (F : W → W → ℝ) (hF : ∀ w w', 0 ≤ F w w') : F s' t' ≤ ∑ w, ∑ w', F w w' :=
    (single_le_sum (fun w' _ ↦ hF s' w') (mem_univ t')).trans
      (single_le_sum (fun w _ ↦ sum_nonneg fun w' _ ↦ hF w w') (mem_univ s'))
  have hone : ∑ w, ∑ w', Q s w * Q t w' = 1 := by
    rw [← sum_mul_sum, hQ.row_sum, hQ.row_sum, one_mul]
  have hX1 : p * h s' t' ≤ X :=
    hsingle (fun w w' ↦ Q s w * Q t w' * h w w') fun w w' ↦
      mul_nonneg (mul_nonneg (hQ.nonneg _ _) (hQ.nonneg _ _)) (h0 w w')
  have hX2 : p * (1 - h s' t') ≤ 1 - X := by
    have := hsingle (fun w w' ↦ Q s w * Q t w' * (1 - h w w')) fun w w' ↦
      mul_nonneg (mul_nonneg (hQ.nonneg _ _) (hQ.nonneg _ _)) (sub_nonneg.mpr (h1 w w'))
    have heq : ∑ w, ∑ w', Q s w * Q t w' * (1 - h w w') = 1 - X := by
      simp only [mul_sub, mul_one, sum_sub_distrib, hone, X]
    simpa [heq] using this
  have hp0 : 0 ≤ p := mul_nonneg (hQ.nonneg _ _) (hQ.nonneg _ _)
  have hp1 : p ≤ 1 := by
    nlinarith [hQ.le_one s s', hQ.le_one t t', hQ.nonneg s s', hQ.nonneg t t']
  have hh0 := h0 s' t'
  have hh1 := h1 s' t'
  rw [abs_le]
  constructor <;> nlinarith

end Mass

end GsimOT
