/-
# Tutte witnesses (Definition 3.3, Lemma 3.4) and the cut `F` of Lemma 3.5

[HOG26], Section 3.

*Encoding of Tutte witnesses.*  A Tutte witness `(U, {O₁, …, O_q})` (pairwise disjoint nonempty
odd subsets of `V \ U`, `q > |U|`) is encoded by a labelling `L : V → Option V`:
`U = L⁻¹(none)`, and the *classes* `cls L r = L⁻¹(some r)` (`r : V`) partition `V \ U`; the `Oᵢ` are
the classes of odd size and the remaining set `R = V \ (U ∪ ⋃ Oᵢ)` is the union of the classes of
even size.  `IsTutteWitness L` says that there are more odd classes than vertices in `U`.  The
paper's union bound runs over the witnesses that can be *violated* by the sample, i.e. those
produced by Tutte's theorem, whose sets are the connected components of `H - U`; these are exactly
encoded as above (`exists_witness_of_no_pm`: the classes are the components of `H - U`, the even
ones forming `R`), so it suffices to count labellings.

*Lemma 3.4* (`card_witnesses_le`): there are at most `(|V| + 1)^{|V|}` labellings, hence at most
that many witnesses (the paper: `(2n + 1)^{2n}` for `|V| = 2n`).

*The set `F`.*  `F = ⋃ᵢ δ(Oᵢ) \ δ(U)` is the set of pairs `{a, b}` with `a, b ∉ U` in different
classes, one of which is odd (`crossF`, `witnessF`).  If the `Oᵢ` are unions of connected components
of `H - U` (in particular for the witness given by Tutte's theorem) then `H` has no edge in `F`.

*Inequality (1).*  The paper shows `x(F) ≥ 1/2` from the odd-set and degree constraints of `PM(G)`.
Since `IsFracPM x` is a convex combination of perfect matchings we argue directly on each perfect
matching `M`: each odd `Oᵢ` has a vertex matched outside `Oᵢ`; if no `M`-edge lay in `F` these
vertices would all be matched into `U`, injectively, so `q ≤ |U|`.  Hence every perfect matching
has an edge in `F` and `x(F) ≥ 1` (`one_le_witnessF_weight`), slightly stronger than the paper's
`x(F) ≥ 1/2`.
-/
import ThinMatching.SupportConstrained.Sampling

open Finset

namespace ThinMatching

section Witness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class `L⁻¹(some r)` of the labelling `L`. -/
def cls (L : V → Option V) (r : V) : Finset V := {v | L v = some r}

/-- The set `U = L⁻¹(none)` of the witness encoded by `L`. -/
def witU (L : V → Option V) : Finset V := {v | L v = none}

/-- The labels of the odd classes `O₁, …, O_q`. -/
def oddLabels (L : V → Option V) : Finset V := {r | Odd #(cls L r)}

/-- **Definition 3.3 (Tutte witness)**, encoded by a labelling: `q > |U|`. -/
def IsTutteWitness (L : V → Option V) : Prop := #(witU L) < #(oddLabels L)

/-- `{a, b} ∈ F = ⋃ᵢ δ(Oᵢ) \ δ(U)`: `a, b ∉ U` lie in different classes, one of which is odd. -/
def crossF (L : V → Option V) (a b : V) : Prop :=
  ∃ r s, L a = some r ∧ L b = some s ∧ r ≠ s ∧ (r ∈ oddLabels L ∨ s ∈ oddLabels L)

theorem crossF_symm {L : V → Option V} {a b : V} (h : crossF L a b) : crossF L b a := by
  obtain ⟨r, s, h1, h2, h3, h4⟩ := h
  exact ⟨s, r, h2, h1, Ne.symm h3, h4.symm⟩

open Classical in
/-- The set `F` of unordered pairs. -/
noncomputable def witnessF (L : V → Option V) : Finset (Sym2 V) :=
  (Finset.univ.filter fun p : V × V => crossF L p.1 p.2).image fun p => s(p.1, p.2)

theorem mem_witnessF {L : V → Option V} {a b : V} :
    s(a, b) ∈ witnessF L ↔ crossF L a b := by
  classical
  unfold witnessF
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨p, q, h, he⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact crossF_symm h
  · intro h; exact ⟨a, b, h, rfl⟩

/-- Membership in `F` for an arbitrary unordered pair. -/
theorem exists_of_mem_witnessF {L : V → Option V} {e : Sym2 V} (he : e ∈ witnessF L) :
    ∃ a b, e = s(a, b) ∧ crossF L a b := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, b, rfl, mem_witnessF.1 he⟩

open Classical in
/-- **Lemma 3.4 (counting Tutte witnesses).**  There are at most `(|V| + 1)^{|V|}` Tutte
witnesses. -/
theorem card_witnesses_le :
    #(Finset.univ.filter fun L : V → Option V => IsTutteWitness L) ≤
      (Fintype.card V + 1) ^ Fintype.card V := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Fintype.card_option]

/-- A perfect matching maps no odd set into itself. -/
theorem exists_mem_map_notMem_of_odd (M : PerfectMatching V) {S : Finset V} (hS : Odd #S) :
    ∃ v ∈ S, M.1 v ∉ S := by
  by_contra h
  push Not at h
  have hsum : ∑ _v ∈ S, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun v _ => M.1 v) (fun v _ => by decide)
      (fun v _ _ => (M.2 v).2) (fun v hv => h v hv) (fun v _ => (M.2 v).1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact (Nat.not_even_iff_odd.2 hS) ((ZMod.natCast_eq_zero_iff_even).1 hsum)

/-- Every perfect matching has an edge in `F` (this gives inequality (1) of Lemma 3.5). -/
theorem exists_crossF_of_isTutteWitness (M : PerfectMatching V) {L : V → Option V}
    (hL : IsTutteWitness L) : ∃ v, crossF L v (M.1 v) := by
  by_contra hno
  push Not at hno
  -- every odd class contains a vertex matched into `U`
  have key : ∀ r ∈ oddLabels L, ∃ v ∈ cls L r, M.1 v ∈ witU L := by
    intro r hr
    obtain ⟨v, hv, hv'⟩ := exists_mem_map_notMem_of_odd M
      (by simpa [oddLabels] using hr : Odd #(cls L r))
    refine ⟨v, hv, ?_⟩
    have hLv : L v = some r := by simpa [cls] using hv
    simp only [witU, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw : L (M.1 v) with _ | s
    · rfl
    · exfalso
      have hrs : r ≠ s := by
        rintro rfl; exact hv' (by simp [cls, hw])
      exact hno v ⟨r, s, hLv, hw, hrs, Or.inl hr⟩
  choose! g hg1 hg2 using key
  have : #(oddLabels L) ≤ #(witU L) := by
    refine Finset.card_le_card_of_injOn (fun r => M.1 (g r)) (fun r hr => hg2 r hr) ?_
    intro r hr r' hr' h
    have h' : g r = g r' := M.1.injective h
    have e1 : L (g r) = some r := by simpa [cls] using hg1 r hr
    have e2 : L (g r') = some r' := by simpa [cls] using hg1 r' hr'
    rw [h'] at e1; rw [e1] at e2; exact Option.some_injective _ e2
  exact absurd hL (not_lt.2 this)

/-- **Inequality (1) of Lemma 3.5** (strengthened): for `x ∈ PM(G)` and a Tutte witness,
`x(F) ≥ 1`. -/
theorem one_le_witnessF_weight {x : WGraph V} (hx : IsFracPM x) {L : V → Option V}
    (hL : IsTutteWitness L) : 1 ≤ ∑ e ∈ witnessF L, edgeW x e := by
  obtain ⟨c, hc0, hc1, hc⟩ := hx
  -- the indicator of `M` on unordered pairs
  have hsymm : ∀ (M : PerfectMatching V) (u v : V),
      (if M.1 u = v then (1 : ℝ) else 0) = if M.1 v = u then 1 else 0 := by
    intro M u v
    have : M.1 u = v ↔ M.1 v = u :=
      ⟨fun h => by rw [← h]; exact (M.2 u).1, fun h => by rw [← h]; exact (M.2 v).1⟩
    simp only [this]
  let ind : PerfectMatching V → Sym2 V → ℝ := fun M => Sym2.lift ⟨fun u v => if M.1 u = v then 1
    else 0, hsymm M⟩
  have hxe : ∀ e, edgeW x e = ∑ M, c M * ind M e := by
    intro e
    induction e using Sym2.ind with
    | _ u v => simp [ind, hc u v]
  have hind : ∀ M, 1 ≤ ∑ e ∈ witnessF L, ind M e := by
    intro M
    obtain ⟨v, hv⟩ := exists_crossF_of_isTutteWitness M hL
    have hmem : s(v, M.1 v) ∈ witnessF L := mem_witnessF.2 hv
    have hnn : ∀ e ∈ witnessF L, 0 ≤ ind M e := by
      intro e _
      induction e using Sym2.ind with
      | _ a b => simp only [ind, Sym2.lift_mk]; split_ifs <;> norm_num
    calc (1 : ℝ) = ind M s(v, M.1 v) := by simp [ind]
      _ ≤ _ := Finset.single_le_sum hnn hmem
  calc (1 : ℝ) = ∑ M, c M * 1 := by simp [hc1]
    _ ≤ ∑ M, c M * ∑ e ∈ witnessF L, ind M e :=
        Finset.sum_le_sum fun M _ => mul_le_mul_of_nonneg_left (hind M) (hc0 M)
    _ = ∑ e ∈ witnessF L, edgeW x e := by
        simp_rw [hxe, Finset.mul_sum]
        exact Finset.sum_comm

/-- **Tutte's theorem (Theorem 2.4), in the form used in Lemma 3.5.**  If the graph `H` has no
perfect matching then there is a Tutte witness `L` such that `H` has no edge in `F`.  (The classes
of `L` are the connected components of `H - U` for a Tutte violator `U`.) -/
theorem exists_witness_of_no_pm (H : SimpleGraph V)
    (h : ¬ ∃ M : PerfectMatching V, ∀ v, H.Adj v (M.1 v)) :
    ∃ L : V → Option V, IsTutteWitness L ∧ ∀ a b, crossF L a b → ¬ H.Adj a b := by
  classical
  -- `H` has no perfect matching in the sense of Mathlib
  have hno : ¬ ∃ M : H.Subgraph, M.IsPerfectMatching := by
    rintro ⟨M, hM⟩
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hM
    choose σ hσ huniq using hM
    have hinv : Function.Involutive σ := fun v => (huniq (σ v) v (hσ v).symm).symm
    refine h ⟨⟨Function.Involutive.toPerm σ hinv, fun v => ⟨hinv v, fun hv => ?_⟩⟩,
      fun v => M.adj_sub (hσ v)⟩
    have h1 := M.adj_sub (hσ v)
    simp only [Function.Involutive.coe_toPerm] at hv
    rw [hv] at h1
    exact H.irrefl h1
  obtain ⟨u, hu⟩ : ∃ u, H.IsTutteViolator u := by
    by_contra hc; push Not at hc; exact hno (SimpleGraph.tutte.2 hc)
  -- the graph `H - U` and its components
  let G' := ((⊤ : H.Subgraph).deleteVerts u).coe
  have hmemv : ∀ v, v ∉ u → v ∈ ((⊤ : H.Subgraph).deleteVerts u).verts := fun v hv => by
    simp [hv]
  have hsurj : ∀ c : G'.ConnectedComponent, ∃ w, G'.connectedComponentMk w = c :=
    fun c => c.ind fun w => ⟨w, rfl⟩
  choose rep0 hrep0 using hsurj
  let rep : G'.ConnectedComponent → V := fun c => (rep0 c).1
  have hrep : Function.Injective rep := fun c d hcd => by
    rw [← hrep0 c, ← hrep0 d, Subtype.ext hcd]
  let comp : ∀ v, v ∉ u → G'.ConnectedComponent := fun v hv =>
    G'.connectedComponentMk ⟨v, hmemv v hv⟩
  let L : V → Option V := fun v => if hv : v ∈ u then none else some (rep (comp v hv))
  have hLsome : ∀ v r, L v = some r ↔ ∃ hv : v ∉ u, rep (comp v hv) = r := fun v r => by
    by_cases hv : v ∈ u <;> simp [L, hv]
  -- the class of `rep c` is the support of `c`
  have hcls : ∀ c : G'.ConnectedComponent, #(cls L (rep c)) = c.supp.ncard := by
    intro c
    rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective c.supp Subtype.val_injective]
    congr 1
    ext v
    simp only [cls, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hLsome,
      Set.mem_image, SimpleGraph.ConnectedComponent.mem_supp_iff]
    constructor
    · rintro ⟨hv, hc⟩
      exact ⟨⟨v, hmemv v hv⟩, hrep hc, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hv : w.1 ∉ u := by
        have := w.2; simp at this; exact this
      exact ⟨hv, congrArg rep (by rw [← hw])⟩
  refine ⟨L, ?_, ?_⟩
  · -- the number of odd classes exceeds `|U|`
    unfold IsTutteWitness
    have hU : #(witU L) = u.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext v
      by_cases hv : v ∈ u <;> simp [witU, L, hv]
    have hodd : G'.oddComponents.ncard ≤ #(oddLabels L) := by
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard_of_injOn rep (fun c hc => ?_) (hrep.injOn) (Finset.finite_toSet _)
      simp only [oddLabels, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hcls]
      exact hc
    unfold SimpleGraph.IsTutteViolator at hu
    rw [hU]
    exact lt_of_lt_of_le hu hodd
  · -- `H` has no edge in `F`
    rintro a b ⟨r, s, hr, hs, hrs, -⟩ hab
    obtain ⟨ha, rfl⟩ := (hLsome a r).1 hr
    obtain ⟨hb, rfl⟩ := (hLsome b s).1 hs
    apply hrs
    congr 1
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [G', hab, ha, hb]

end Witness

end ThinMatching
