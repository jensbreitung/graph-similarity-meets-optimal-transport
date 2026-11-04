/-
# Lemma 43: the Talagrand contraction lemma [LT91, Theorem 4.12] (p. 38)

Lemma 43 (p. 38, l. 1186–1188) is a cited result (the paper refers to [LT91, Theorem 4.12] for a
proof, l. 1182–1185); we prove it (`contractionPrinciple`), discharging the hypothesis
`ContractionPrinciple` of Lemma 44 and hence of Theorem 39 and Theorem 11 (`theorem11`).

Proof outline:
1. A two-point lemma: `sup (u + x) + sup (u - x) ≤ sup (u + y) + sup (u - y)` whenever
   `|x t - x t'| ≤ |y t - y t'|`.
2. Talagrand's comparison theorem (without absolute values),
   `E sup_t ∑ σ_a x_a(t) ≤ E sup_t ∑ σ_a y_a(t)`, by replacing one coordinate at a time
   (pairing each sign vector with the one obtained by flipping the current coordinate).
3. The version with absolute values and factor `2`, by adding the point `0` to `T`
   and using the symmetry `σ ↦ -σ`.
-/
import GsimOT.Theorem11_CutUpperBound.Definitions

open Finset

namespace GsimOT

namespace ContractionAux

/-- The sign vector associated with `s : ι → Bool`. -/
noncomputable def sgn {ι : Type*} (s : ι → Bool) (a : ι) : ℝ := if s a then 1 else -1

lemma abs_sgn {ι : Type*} (s : ι → Bool) (a : ι) : |sgn s a| = 1 := by
  unfold sgn; split <;> simp

lemma bddAbove_of_abs_le {T : Type*} (f : T → ℝ) (M : ℝ) (h : ∀ t, |f t| ≤ M) :
    BddAbove (Set.range f) :=
  ⟨M, by rintro _ ⟨t, rfl⟩; exact (le_abs_self _).trans (h t)⟩

lemma abs_sum_sgn_le {ι : Type*} (s : Finset ι) (σ v : ι → ℝ) (hσ : ∀ a, |σ a| ≤ 1) (M : ℝ)
    (hv : ∀ a, |v a| ≤ M) : |∑ a ∈ s, σ a * v a| ≤ ∑ _a ∈ s, M := by
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul]
  calc |σ a| * |v a| ≤ 1 * M :=
        mul_le_mul (hσ a) (hv a) (abs_nonneg _) zero_le_one
    _ = M := one_mul M

/-- The two-point lemma. -/
lemma two_point {T : Type*} [Nonempty T] (u x y : T → ℝ) (Mu My : ℝ)
    (hu : ∀ t, |u t| ≤ Mu) (hy : ∀ t, |y t| ≤ My)
    (hxy : ∀ t t', |x t - x t'| ≤ |y t - y t'|) :
    (⨆ t, (u t + x t)) + (⨆ t, (u t - x t)) ≤ (⨆ t, (u t + y t)) + (⨆ t, (u t - y t)) := by
  have hb1 : BddAbove (Set.range fun t => u t + y t) :=
    bddAbove_of_abs_le _ (Mu + My) fun t =>
      (abs_add_le _ _).trans (add_le_add (hu t) (hy t))
  have hb2 : BddAbove (Set.range fun t => u t - y t) :=
    bddAbove_of_abs_le _ (Mu + My) fun t =>
      (abs_sub _ _).trans (add_le_add (hu t) (hy t))
  have key : ∀ t t', (u t + x t) + (u t' - x t') ≤
      (⨆ t, (u t + y t)) + (⨆ t, (u t - y t)) := by
    intro t t'
    have h1 := hxy t t'
    rcases le_total (y t') (y t) with h | h
    · have e : |y t - y t'| = y t - y t' := abs_of_nonneg (by linarith)
      have := le_ciSup hb1 t
      have := le_ciSup hb2 t'
      have := le_abs_self (x t - x t')
      linarith
    · have e : |y t - y t'| = y t' - y t := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      have := le_ciSup hb1 t'
      have := le_ciSup hb2 t
      have := le_abs_self (x t - x t')
      linarith
  have : ∀ t, u t + x t ≤ ((⨆ t, (u t + y t)) + (⨆ t, (u t - y t))) - ⨆ t, (u t - x t) := by
    intro t
    have : (⨆ t, (u t - x t)) ≤
        ((⨆ t, (u t + y t)) + (⨆ t, (u t - y t))) - (u t + x t) :=
      ciSup_le fun t' => by have := key t t'; linarith
    linarith
  have := ciSup_le this
  linarith

lemma sgn_not {ι : Type*} (s : ι → Bool) (a : ι) : sgn (fun a => !s a) a = - sgn s a := by
  unfold sgn; cases h : s a <;> simp [h]

/-- One step of the comparison theorem: replace coordinate `c`. -/
lemma step {b : ℕ} {T : Type*} [Nonempty T] (c : Fin b) (z w : Fin b → T → ℝ) (M : ℝ)
    (hz : ∀ a t, |z a t| ≤ M) (hwz : ∀ a, a ≠ c → w a = z a)
    (hc : ∀ t t', |w c t - w c t'| ≤ |z c t - z c t'|) :
    ∑ s : Fin b → Bool, (⨆ t, ∑ a, sgn s a * w a t) ≤
      ∑ s : Fin b → Bool, (⨆ t, ∑ a, sgn s a * z a t) := by
  classical
  let flip : Equiv.Perm (Fin b → Bool) :=
    Function.Involutive.toPerm (fun s => Function.update s c (!(s c)))
      (by intro s; funext a; by_cases h : a = c <;> simp [h])
  have hflip : ∀ F : (Fin b → Bool) → ℝ, ∑ s, F s = ∑ s, F (flip s) := fun F =>
    (Equiv.sum_comp flip F).symm
  have hflip_apply : ∀ s, flip s = Function.update s c (!(s c)) := fun s => rfl
  have hsgn_ne : ∀ s a, a ≠ c → sgn (flip s) a = sgn s a := by
    intro s a h
    simp [hflip_apply, sgn, h]
  have hsgn_c : ∀ s, sgn (flip s) c = - sgn s c := by
    intro s
    simp only [hflip_apply, sgn, Function.update_self]
    cases s c <;> simp
  have pt : ∀ s, (⨆ t, ∑ a, sgn s a * w a t) + (⨆ t, ∑ a, sgn (flip s) a * w a t) ≤
      (⨆ t, ∑ a, sgn s a * z a t) + (⨆ t, ∑ a, sgn (flip s) a * z a t) := by
    intro s
    have hsplit : ∀ (σ : Fin b → ℝ) (v : Fin b → T → ℝ) t,
        ∑ a, σ a * v a t = σ c * v c t + ∑ a ∈ univ.erase c, σ a * v a t := fun σ v t =>
      (Finset.add_sum_erase _ _ (mem_univ c)).symm
    have herase : ∀ (σ : Fin b → ℝ) (hσ : ∀ a, a ≠ c → σ a = sgn s a) t,
        ∑ a ∈ univ.erase c, σ a * w a t = ∑ a ∈ univ.erase c, sgn s a * z a t := by
      intro σ hσ t
      refine Finset.sum_congr rfl fun a ha => ?_
      have hac := ne_of_mem_erase ha
      rw [hσ a hac, hwz a hac]
    have herase' : ∀ (σ : Fin b → ℝ) (hσ : ∀ a, a ≠ c → σ a = sgn s a) t,
        ∑ a ∈ univ.erase c, σ a * z a t = ∑ a ∈ univ.erase c, sgn s a * z a t := by
      intro σ hσ t
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hσ a (ne_of_mem_erase ha)]
    have e1 : ∀ t, ∑ a, sgn s a * w a t =
        (∑ a ∈ univ.erase c, sgn s a * z a t) + sgn s c * w c t := by
      intro t; rw [hsplit, herase _ (fun _ _ => rfl), add_comm]
    have e2 : ∀ t, ∑ a, sgn (flip s) a * w a t =
        (∑ a ∈ univ.erase c, sgn s a * z a t) - sgn s c * w c t := by
      intro t; rw [hsplit, herase _ (hsgn_ne s), hsgn_c]; ring
    have e3 : ∀ t, ∑ a, sgn s a * z a t =
        (∑ a ∈ univ.erase c, sgn s a * z a t) + sgn s c * z c t := by
      intro t; rw [hsplit, add_comm]
    have e4 : ∀ t, ∑ a, sgn (flip s) a * z a t =
        (∑ a ∈ univ.erase c, sgn s a * z a t) - sgn s c * z c t := by
      intro t; rw [hsplit, herase' _ (hsgn_ne s), hsgn_c]; ring
    simp only [e1, e2, e3, e4]
    exact two_point (fun t => ∑ a ∈ univ.erase c, sgn s a * z a t)
      (fun t => sgn s c * w c t) (fun t => sgn s c * z c t) (∑ _a ∈ univ.erase c, M) M
      (fun t => abs_sum_sgn_le _ _ _ (fun a => (abs_sgn s a).le) M (fun a => hz a t))
      (fun t => by rw [abs_mul, abs_sgn, one_mul]; exact hz c t)
      (fun t t' => by
        rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_sgn, one_mul, one_mul]; exact hc t t')
  have h1 := hflip (fun s => ⨆ t, ∑ a, sgn s a * w a t)
  have h2 := hflip (fun s => ⨆ t, ∑ a, sgn s a * z a t)
  have h3 := Finset.sum_le_sum (s := univ) fun s _ => pt s
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h3
  linarith

/-- Talagrand's comparison theorem (without absolute values). -/
lemma comparison {b : ℕ} {T : Type*} [Nonempty T] (x y : Fin b → T → ℝ) (M : ℝ)
    (hx : ∀ a t, |x a t| ≤ M) (hy : ∀ a t, |y a t| ≤ M)
    (hxy : ∀ a t t', |x a t - x a t'| ≤ |y a t - y a t'|) :
    ∑ s : Fin b → Bool, (⨆ t, ∑ a, sgn s a * x a t) ≤
      ∑ s : Fin b → Bool, (⨆ t, ∑ a, sgn s a * y a t) := by
  classical
  have key : ∀ A : Finset (Fin b),
      ∑ s : Fin b → Bool, (⨆ t, ∑ a, sgn s a * (if a ∈ A then x a else y a) t) ≤
        ∑ s : Fin b → Bool, (⨆ t, ∑ a, sgn s a * y a t) := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | insert c A hcA ih =>
      refine le_trans (step c (fun a => if a ∈ A then x a else y a)
        (fun a => if a ∈ insert c A then x a else y a) M ?_ ?_ ?_) ih
      · intro a t
        by_cases h : a ∈ A
        · simp only [h, ↓reduceIte]; exact hx a t
        · simp only [h, ↓reduceIte]; exact hy a t
      · intro a hac
        simp [Finset.mem_insert, hac]
      · intro t t'
        simp only [Finset.mem_insert, true_or, ↓reduceIte, hcA, ↓reduceIte]
        exact hxy c t t'
  simpa using key univ

end ContractionAux

/-- **Lemma 43** (Talagrand contraction lemma, [LT91, Theorem 4.12], with `F = id`). -/
theorem contractionPrinciple : ContractionPrinciple := by
  intro b T hT hne φ hφ hφ0
  classical
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (hT.insert 0)
  have : Nonempty (insert (0 : Fin b → ℝ) T : Set (Fin b → ℝ)) :=
    ⟨⟨0, Set.mem_insert _ _⟩⟩
  have : Nonempty T := hne.to_subtype
  have hcoord : ∀ t ∈ insert (0 : Fin b → ℝ) T, ∀ a, |t a| ≤ R := fun t ht a => by
    have := (norm_le_pi_norm t a).trans (hR t ht)
    rwa [Real.norm_eq_abs] at this
  have hphi : ∀ a r, |φ a r| ≤ |r| := by
    intro a r
    have := (hφ a).dist_le_mul r 0
    simpa [Real.dist_eq, hφ0] using this
  have hT0 : ∀ t : T, t.1 ∈ insert (0 : Fin b → ℝ) T := fun t => Set.mem_insert_of_mem _ t.2
  -- bounds
  have hbY : ∀ (s : Fin b → Bool) (t : Fin b → ℝ), t ∈ insert (0 : Fin b → ℝ) T →
      |∑ a, ContractionAux.sgn s a * φ a (t a)| ≤ ∑ _a : Fin b, R := fun s t ht =>
    ContractionAux.abs_sum_sgn_le _ _ _ (fun a => (ContractionAux.abs_sgn s a).le) R
      (fun a => (hphi a _).trans (hcoord t ht a))
  have hbX : ∀ (s : Fin b → Bool) (t : Fin b → ℝ), t ∈ insert (0 : Fin b → ℝ) T →
      |∑ a, ContractionAux.sgn s a * t a| ≤ ∑ _a : Fin b, R := fun s t ht =>
    ContractionAux.abs_sum_sgn_le _ _ _ (fun a => (ContractionAux.abs_sgn s a).le) R
      (fun a => hcoord t ht a)
  -- comparison on `T ∪ {0}`
  have cmp := ContractionAux.comparison (T := (insert (0 : Fin b → ℝ) T : Set (Fin b → ℝ)))
    (fun a t => φ a (t.1 a)) (fun a t => t.1 a) R
    (fun a t => (hphi a _).trans (hcoord t.1 t.2 a)) (fun a t => hcoord t.1 t.2 a)
    (fun a t t' => by
      have := (hφ a).dist_le_mul (t.1 a) (t'.1 a)
      simpa [Real.dist_eq] using this)
  -- Step A
  have hA : ∀ s : Fin b → Bool,
      (⨆ t : T, |∑ a, ContractionAux.sgn s a * φ a (t.1 a)|) ≤
        (⨆ t : (insert (0 : Fin b → ℝ) T : Set (Fin b → ℝ)),
            ∑ a, ContractionAux.sgn s a * φ a (t.1 a)) +
        (⨆ t : (insert (0 : Fin b → ℝ) T : Set (Fin b → ℝ)),
            ∑ a, ContractionAux.sgn (fun a => !s a) a * φ a (t.1 a)) := by
    intro s
    have hb1 := ContractionAux.bddAbove_of_abs_le
      (fun t : (insert (0 : Fin b → ℝ) T : Set (Fin b → ℝ)) =>
        ∑ a, ContractionAux.sgn s a * φ a (t.1 a)) _ (fun t => hbY s t.1 t.2)
    have hb2 := ContractionAux.bddAbove_of_abs_le
      (fun t : (insert (0 : Fin b → ℝ) T : Set (Fin b → ℝ)) =>
        ∑ a, ContractionAux.sgn (fun a => !s a) a * φ a (t.1 a)) _
      (fun t => hbY _ t.1 t.2)
    have hneg : ∀ t : Fin b → ℝ, ∑ a, ContractionAux.sgn (fun a => !s a) a * φ a (t a) =
        -∑ a, ContractionAux.sgn s a * φ a (t a) := by
      intro t
      simp only [ContractionAux.sgn_not, neg_mul, Finset.sum_neg_distrib]
    have h0 : ∑ a, ContractionAux.sgn s a * φ a ((0 : Fin b → ℝ) a) = 0 := by
      simp [hφ0]
    have hz1 := le_ciSup hb1 ⟨0, Set.mem_insert _ _⟩
    have hz2 := le_ciSup hb2 ⟨0, Set.mem_insert _ _⟩
    simp only [hneg, h0, neg_zero] at hz1 hz2
    simp only [hneg]
    refine ciSup_le fun t => abs_le.2 ⟨?_, ?_⟩
    · have := le_ciSup hb2 ⟨t.1, hT0 t⟩
      simp only [hneg] at this
      linarith
    · have := le_ciSup hb1 ⟨t.1, hT0 t⟩
      simp only at this
      linarith
  -- Step B: symmetry
  have hB : ∑ s : Fin b → Bool, (⨆ t : (insert (0 : Fin b → ℝ) T : Set (Fin b → ℝ)),
        ∑ a, ContractionAux.sgn (fun a => !s a) a * φ a (t.1 a)) =
      ∑ s : Fin b → Bool, (⨆ t : (insert (0 : Fin b → ℝ) T : Set (Fin b → ℝ)),
        ∑ a, ContractionAux.sgn s a * φ a (t.1 a)) :=
    Equiv.sum_comp (Function.Involutive.toPerm (fun s : Fin b → Bool => fun a => !s a)
      (by intro s; funext a; simp))
      (fun s => ⨆ t : (insert (0 : Fin b → ℝ) T : Set (Fin b → ℝ)),
        ∑ a, ContractionAux.sgn s a * φ a (t.1 a))
  -- Step D
  have hD : ∀ s : Fin b → Bool,
      (⨆ t : (insert (0 : Fin b → ℝ) T : Set (Fin b → ℝ)),
          ∑ a, ContractionAux.sgn s a * t.1 a) ≤
        ⨆ t : T, |∑ a, ContractionAux.sgn s a * t.1 a| := by
    intro s
    have hb := ContractionAux.bddAbove_of_abs_le
      (fun t : T => |∑ a, ContractionAux.sgn s a * t.1 a|) _
      (fun t => by rw [abs_abs]; exact hbX s t.1 (hT0 t))
    refine ciSup_le fun t => ?_
    rcases t with ⟨t, ht⟩
    rcases ht with rfl | ht
    · obtain ⟨t0, ht0⟩ := hne
      have := le_ciSup hb ⟨t0, ht0⟩
      have := abs_nonneg (∑ a, ContractionAux.sgn s a * t0 a)
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at *
      linarith
    · exact (le_abs_self _).trans (le_ciSup hb ⟨t, ht⟩)
  have hAs := Finset.sum_le_sum (s := univ) fun s _ => hA s
  have hDs := Finset.sum_le_sum (s := univ) fun s _ => hD s
  rw [Finset.sum_add_distrib, hB] at hAs
  have main : ∑ s : Fin b → Bool, (⨆ t : T, |∑ a, ContractionAux.sgn s a * φ a (t.1 a)|) ≤
      2 * ∑ s : Fin b → Bool, (⨆ t : T, |∑ a, ContractionAux.sgn s a * t.1 a|) := by
    linarith
  unfold radAvg
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right main (by positivity)

end GsimOT
