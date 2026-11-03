/-
# Lemma 4.5: cut values bound discrepancies

[HOG26], Lemma 4.5.

* Bipartite case: from the degree constraints `x(S_L, R) = |S_L|` and `x(L, S_R) = |S_R|`,
  `||S_L| − |S_R|| = |x(S_L, R) − x(L, S_R)| ≤ x(δ(S))` (as in the paper).
* General case: the paper invokes the odd-set constraint of `PM(G)`.  Here `x ∈ PM(G)` is by
  definition a convex combination of perfect matchings, so we only need the easy direction: every
  perfect matching crosses an odd set at least once (`one_le_crossCount_of_odd`), and
  `x(δ(S)) = ∑_M c_M |M ∩ δ(S)|`.
-/
import ThinMatching.Basic

open Finset

namespace ThinMatching

/-- **Lemma 4.5 (bipartite).** For a fractional perfect matching `x` of a bipartite graph and
`S = S_L ∪ S_R`, `x(δ(S)) ≥ Δ_bip(S) = ||S_L| − |S_R||`. -/
theorem lemma45_bip {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {x : L → R → ℝ} (hx : IsFracPMBip x) (SL : Finset L) (SR : Finset R) :
    |(#SL : ℝ) - #SR| ≤ bipCutWeight x SL SR := by
  -- degree constraints: `|S_L| = x(S_L, R)` and `|S_R| = x(L, S_R)`
  have hL : (#SL : ℝ) = ∑ l, ∑ r, if l ∈ SL then x l r else 0 := by
    calc (#SL : ℝ) = ∑ l ∈ SL, ∑ r, x l r := by simp [hx.row_sum]
      _ = ∑ l, if l ∈ SL then ∑ r, x l r else 0 := by rw [Finset.sum_ite_mem, univ_inter]
      _ = _ := by refine Finset.sum_congr rfl fun l _ => ?_; split_ifs <;> simp
  have hR : (#SR : ℝ) = ∑ l, ∑ r, if r ∈ SR then x l r else 0 := by
    rw [Finset.sum_comm]
    calc (#SR : ℝ) = ∑ r ∈ SR, ∑ l, x l r := by simp [hx.col_sum]
      _ = ∑ r, if r ∈ SR then ∑ l, x l r else 0 := by rw [Finset.sum_ite_mem, univ_inter]
      _ = _ := by refine Finset.sum_congr rfl fun l _ => ?_; split_ifs <;> simp
  rw [hL, hR, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  have := hx.nonneg l r
  split_ifs <;> simp_all [abs_of_nonneg]

/-- A fixed-point-free involution maps no odd set into itself: every perfect matching crosses
an odd set `S` at least once. -/
theorem one_le_crossCount_of_odd {V : Type*} [Fintype V] [DecidableEq V] (M : PerfectMatching V)
    {S : Finset V} (hS : Odd #S) : 1 ≤ crossCount M S := by
  by_contra h
  have h0 : ∀ v ∈ S, M.1 v ∈ S := by
    intro v hv
    by_contra hv'
    exact h (Nat.one_le_iff_ne_zero.2 (Finset.card_ne_zero.2 ⟨v, by simp [hv, hv']⟩))
  -- pair up the elements of `S` by `M` to see that `|S|` is even
  have hsum : ∑ _v ∈ S, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun v _ => M.1 v) (fun v _ => by decide)
      (fun v _ _ => (M.2 v).2) (fun v hv => h0 v hv) (fun v _ => (M.2 v).1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact (Nat.not_even_iff_odd.2 hS) ((ZMod.natCast_eq_zero_iff_even).1 hsum)

/-- `x(δ(S)) = ∑_M c_M |M ∩ δ(S)|` for `x = ∑_M c_M 1_M`. -/
theorem cutWeight_eq_sum_crossCount {V : Type*} [Fintype V] [DecidableEq V] {x : WGraph V}
    (c : PerfectMatching V → ℝ)
    (hc : ∀ u v, x.w u v = ∑ M, c M * (if M.1 u = v then (1 : ℝ) else 0)) (S : Finset V) :
    cutWeight x S = ∑ M, c M * crossCount M S := by
  have key : ∀ M : PerfectMatching V, ∀ u,
      ∑ v ∈ Sᶜ, c M * (if M.1 u = v then (1 : ℝ) else 0) = c M * (if M.1 u ∉ S then 1 else 0) := by
    intro M u
    rw [← Finset.mul_sum, Finset.sum_ite_eq, if_congr Finset.mem_compl rfl rfl]
  unfold cutWeight crossCount
  simp_rw [hc]
  calc ∑ u ∈ S, ∑ v ∈ Sᶜ, ∑ M, c M * (if M.1 u = v then (1 : ℝ) else 0)
      = ∑ u ∈ S, ∑ M, ∑ v ∈ Sᶜ, c M * (if M.1 u = v then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ M, ∑ u ∈ S, ∑ v ∈ Sᶜ, c M * (if M.1 u = v then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ M, c M * #{v ∈ S | M.1 v ∉ S} := by
        refine Finset.sum_congr rfl fun M _ => ?_
        simp_rw [key, ← Finset.mul_sum]
        rw [Finset.card_filter, Nat.cast_sum]
        congr 1
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> simp

/-- **Lemma 4.5 (general).** For `x ∈ PM(G)` and `S` of odd size, `x(δ(S)) ≥ 1 = Δ_non-bip(S)`. -/
theorem lemma45 {V : Type*} [Fintype V] [DecidableEq V] {x : WGraph V} (hx : IsFracPM x)
    {S : Finset V} (hS : Odd #S) : 1 ≤ cutWeight x S := by
  obtain ⟨c, hc0, hc1, hc⟩ := hx
  rw [cutWeight_eq_sum_crossCount c hc S, ← hc1]
  refine Finset.sum_le_sum fun M _ => ?_
  have : (1 : ℝ) ≤ crossCount M S := by exact_mod_cast one_le_crossCount_of_odd M hS
  nlinarith [hc0 M]

end ThinMatching
