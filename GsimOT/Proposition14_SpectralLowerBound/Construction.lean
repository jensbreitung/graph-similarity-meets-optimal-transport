/-
# The graphs `G_r` and `H_r` of Proposition 13

Paper, Section 3.4 (Proposition 13, p. 11), App. F.1 (the construction, p. 45, l. 1399–1411) and
Figure 7 (p. 45).

Fix `r ≥ 1`. Both graphs live on the common vertex set `V = X ∪ M` with
* the *core* `X = {u} ∪ {v_{i,k} | i ∈ [2r], 0 ≤ k ≤ r}`, represented by
  `Core r = Option (Fin (2r) × Fin (r+1))` (`none = u`, `some (i, k) = v_{i,k}`, branches indexed
  from `0`), and
* the *markers* `M = C ∪ T_1 ∪ ⋯ ∪ T_{2r}`, represented by `Marker r = Fin r ⊕ (Fin (2r) × Fin r)`:
  `inl j` is the clock `c_{j+1}` and `inr (i, t)` is the tag `t_{i,t+1}` of branch `i`.

In both graphs `N(v_{i,k}) = T_i ∪ {c_1, …, c_k}`; `u` is isolated in `G_r` and adjacent to all
clocks in `H_r`; there are no further edges. `|V| = 4r² + 3r + 1`, `u` is isolated in `G_r`, and
`H_r` has minimum degree at least `r`.
-/
import GsimOT.Common.OTDistances

open Finset

namespace GsimOT.Prop14

/-! ## Vertices -/

/-- Core vertices: `none` is `u`, `some (i, k)` is `v_{i,k}`. -/
abbrev Core (r : ℕ) := Option (Fin (2 * r) × Fin (r + 1))

/-- Markers: `inl j` is the clock `c_{j+1}`, `inr (i, t)` is the tag `t_{i,t+1}`. -/
abbrev Marker (r : ℕ) := Fin r ⊕ (Fin (2 * r) × Fin r)

/-- The common vertex set `V = X ∪ M` of `G_r` and `H_r`. -/
abbrev Vtx (r : ℕ) := Core r ⊕ Marker r

lemma card_Vtx (r : ℕ) : Fintype.card (Vtx r) = 4 * r ^ 2 + 3 * r + 1 := by
  simp only [Fintype.card_sum, Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
  ring

/-! ## The graphs -/

/-- Adjacency between a core vertex and a marker; `b = false` for `G_r`, `b = true` for `H_r`. -/
def cm (r : ℕ) (b : Bool) : Core r → Marker r → Bool
  | none, .inl _ => b
  | none, .inr _ => false
  | some (_, k), .inl j => decide (j.val < k.val)
  | some (i, _), .inr (i', _) => decide (i' = i)

/-- Adjacency of the graph (bipartite between core and markers). -/
def adjB (r : ℕ) (b : Bool) : Vtx r → Vtx r → Bool
  | .inl x, .inr m => cm r b x m
  | .inr m, .inl x => cm r b x m
  | _, _ => false

lemma adjB_symm (r : ℕ) (b : Bool) (x y : Vtx r) : adjB r b x y = adjB r b y x := by
  cases x <;> cases y <;> rfl

lemma adjB_self (r : ℕ) (b : Bool) (x : Vtx r) : adjB r b x x = false := by
  cases x <;> rfl

/-- The common shape of `G_r` (`b = false`) and `H_r` (`b = true`). -/
def graph (r : ℕ) (b : Bool) : SimpleGraph (Vtx r) where
  Adj x y := adjB r b x y = true
  symm := ⟨fun x y h => by rw [adjB_symm]; exact h⟩
  loopless := ⟨fun x h => by rw [adjB_self] at h; exact Bool.false_ne_true h⟩

/-- The graph `G_r` of Proposition 13: `u` is isolated. -/
def Gr (r : ℕ) : SimpleGraph (Vtx r) := graph r false

/-- The graph `H_r` of Proposition 13: `u` is adjacent to all clocks. -/
def Hr (r : ℕ) : SimpleGraph (Vtx r) := graph r true

instance (r : ℕ) : DecidableRel (Gr r).Adj := fun a b =>
  inferInstanceAs (Decidable (adjB r false a b = true))

instance (r : ℕ) : DecidableRel (Hr r).Adj := fun a b =>
  inferInstanceAs (Decidable (adjB r true a b = true))

/-! ## Adjacency entries -/

/-- Real core–marker adjacency. -/
def cmR (r : ℕ) (b : Bool) (x : Core r) (m : Marker r) : ℝ := if cm r b x m then 1 else 0

lemma adj_Gr (r : ℕ) (x y : Vtx r) :
    adj (Gr r) x y = if adjB r false x y = true then 1 else 0 := rfl

lemma adj_Hr (r : ℕ) (x y : Vtx r) :
    adj (Hr r) x y = if adjB r true x y = true then 1 else 0 := rfl

@[simp] lemma adj_Gr_inl_inl (r : ℕ) (x y : Core r) : adj (Gr r) (.inl x) (.inl y) = 0 := rfl
@[simp] lemma adj_Hr_inl_inl (r : ℕ) (x y : Core r) : adj (Hr r) (.inl x) (.inl y) = 0 := rfl
@[simp] lemma adj_Gr_inr_inr (r : ℕ) (m m' : Marker r) : adj (Gr r) (.inr m) (.inr m') = 0 := rfl
@[simp] lemma adj_Hr_inr_inr (r : ℕ) (m m' : Marker r) : adj (Hr r) (.inr m) (.inr m') = 0 := rfl
@[simp] lemma adj_Gr_inl_inr (r : ℕ) (x : Core r) (m : Marker r) :
    adj (Gr r) (.inl x) (.inr m) = cmR r false x m := rfl
@[simp] lemma adj_Hr_inl_inr (r : ℕ) (x : Core r) (m : Marker r) :
    adj (Hr r) (.inl x) (.inr m) = cmR r true x m := rfl
@[simp] lemma adj_Gr_inr_inl (r : ℕ) (x : Core r) (m : Marker r) :
    adj (Gr r) (.inr m) (.inl x) = cmR r false x m := rfl
@[simp] lemma adj_Hr_inr_inl (r : ℕ) (x : Core r) (m : Marker r) :
    adj (Hr r) (.inr m) (.inl x) = cmR r true x m := rfl

@[simp] lemma cmR_none_inl (r : ℕ) (b : Bool) (j : Fin r) :
    cmR r b none (.inl j) = if b then 1 else 0 := by cases b <;> rfl
@[simp] lemma cmR_none_inr (r : ℕ) (b : Bool) (p : Fin (2 * r) × Fin r) :
    cmR r b none (.inr p) = 0 := rfl
@[simp] lemma cmR_some_inl (r : ℕ) (b : Bool) (i : Fin (2 * r)) (k : Fin (r + 1)) (j : Fin r) :
    cmR r b (some (i, k)) (.inl j) = if j.val < k.val then 1 else 0 := by
  simp [cmR, cm]
@[simp] lemma cmR_some_inr (r : ℕ) (b : Bool) (i : Fin (2 * r)) (k : Fin (r + 1))
    (i' : Fin (2 * r)) (t : Fin r) :
    cmR r b (some (i, k)) (.inr (i', t)) = if i' = i then 1 else 0 := by
  simp [cmR, cm]

/-- Branch vertices have the same neighbourhood in `G_r` and `H_r`. -/
lemma cmR_some_eq (r : ℕ) (v : Fin (2 * r) × Fin (r + 1)) (m : Marker r) :
    cmR r false (some v) m = cmR r true (some v) m := by
  obtain ⟨i, k⟩ := v
  rcases m with j | ⟨i', t⟩ <;> simp

/-- `u` is isolated in `G_r`. -/
@[simp] lemma adj_Gr_u (r : ℕ) (y : Vtx r) : adj (Gr r) (.inl none) y = 0 := by
  rcases y with y | j | p <;> simp

/-! ## Degrees -/

lemma le_deg_of_injective {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (y : V) {r : ℕ} (f : Fin r → V) (hf : Function.Injective f)
    (h : ∀ t, G.Adj y (f t)) : r ≤ deg G y := by
  unfold deg
  calc r = (univ.image f).card := by rw [card_image_of_injective _ hf]; simp
    _ ≤ _ := card_le_card (by
        intro v hv
        simp only [mem_image, mem_univ, true_and] at hv
        obtain ⟨t, rfl⟩ := hv
        simpa using h t)

/-- `H_r` has minimum degree at least `r`. -/
lemma le_deg_Hr (r : ℕ) (y : Vtx r) : r ≤ deg (Hr r) y := by
  rcases y with (_ | ⟨i, k⟩) | j | ⟨i, t₀⟩
  · exact le_deg_of_injective _ _ (fun t => .inr (.inl t)) (fun a b h => by simpa using h)
      fun t => rfl
  · exact le_deg_of_injective _ _ (fun t => .inr (.inr (i, t))) (fun a b h => by simpa using h)
      fun t => by show adjB r true _ _ = true; simp [adjB, cm]
  · exact le_deg_of_injective _ _ (fun t => .inl (some (⟨t.val, by omega⟩, Fin.last r)))
      (fun a b h => by simpa [Fin.ext_iff] using h)
      fun t => by show adjB r true _ _ = true; simp [adjB, cm]
  · exact le_deg_of_injective _ _ (fun t => .inl (some (i, t.castSucc)))
      (fun a b h => by simpa using h)
      fun t => by show adjB r true _ _ = true; simp [adjB, cm]

end GsimOT.Prop14
