/-
# Lemma 25 and Claim 26: every bijection costs at least `4N - 2`

Paper, App. C.1, Lemma 25 (p. 23, l. 726; proof pp. 23–24, l. 727–753) with Claim 26 (p. 24,
l. 737; proof l. 738–749): `d_ed(G, H) ≥ 4N - 2`.

Proof (paper).  Let `π ∈ Bij(V, W)`.  If `C_ed(π) ≥ τ = 4N - 1` there is nothing to prove.
Otherwise Lemma 22 implies that `π` fixes every marker and maps `S_G` onto `S_H`; we may assume
that `π` is compliant, as replacing its action on the clique by the identity cannot increase the
cost.  Let `d_i ∈ {-N + 2, -N + 4, …, N}` be the signed displacement of `v_i`, i.e.
`π(v_i) = w_{(i + d_i) mod 2N}`.  Then `ℓ(v_i, π(v_i)) = |d_i|`, so by Lemma 23 the core-marker
pairs contribute `2U` with `U := ∑ |d_i|`.  Let `k` be the number of core edges of `G'` that `π`
maps onto core edges of `H'`.

* **Claim 26.** `U ≥ N + 2k`.  If some `d_i = N`, then `U ≥ N + (N - 1) ≥ N + 2k`.  Otherwise all
  `d_i ∈ (-N, N)`.  As `π` maps the even positions onto the odd ones, `∑ d_i ≡ N (mod 2N)`, so
  `|∑ d_i| ≥ N`.  For a preserved core edge `{v_i, v_{i'}}`, `d_i + d_{i'} = 0` and
  `|d_i| + |d_{i'}| ≥ 2`.  With `S` the set of endpoints of the preserved edges,
  `U ≥ 2k + |∑_{v_i ∉ S} d_i| = 2k + |∑ d_i| ≥ 2k + N`.
* Both cores have `(N - 1)/2` edges, of which exactly `k` are preserved, so their ordered pairs
  contribute `2(N - 1 - 2k)`, and `C_ed(π) ≥ 2(N - 1 - 2k) + 2U ≥ 4N - 2`.

Formalisation notes.
* Instead of replacing `π` on the clique by the identity, we drop the pairs involving the clique
  from the sum `C_ed(π) = ∑_{v,v'} |A_G(v, v') - A_H(π v, π v')|` (`costEditBij_restrict`); what
  remains is the cost of the compliant bijection w.r.t. `(G', H')`.
* `π` maps the core vertex `c` to `ρ(c)` (`restrictInl`, applied twice).  The displacement of
  `v_{2c}` is `disp ρ c ∈ (-N, N]`, with `ℓ(v_{2c}, π(v_{2c})) = |disp ρ c|` (`ell_eq_abs_disp`).
* `2k = pres N ρ ρ` is the number of preserved *ordered* core edges.  The set `S` consists of the
  `c ≥ 1` whose partner edge `{c, N - c}` is preserved, and `∑_{c ∈ S} d_c = 0` is proved with the
  involution `c ↦ N - c` on `S`.
-/
import GsimOT.Proposition6_EditLowerBound.CoreEdges

open Finset

namespace GsimOT.Prop6

variable {N : ℕ}

/-! ### Restricting a bijection -/

/-- A permutation of `α ⊕ β` that maps `α` into `α` restricts to a permutation of `α`. -/
noncomputable def restrictInl {α β : Type*} [Finite α] (π : (α ⊕ β) ≃ (α ⊕ β))
    (h : ∀ a, ∃ a', π (.inl a) = .inl a') : α ≃ α :=
  Equiv.ofBijective (fun a => (h a).choose) (Finite.injective_iff_bijective.1 fun a b hab =>
    Sum.inl_injective (π.injective
      (((h a).choose_spec.trans (congrArg Sum.inl hab)).trans (h b).choose_spec.symm)))

lemma restrictInl_spec {α β : Type*} [Finite α] (π : (α ⊕ β) ≃ (α ⊕ β))
    (h : ∀ a, ∃ a', π (.inl a) = .inl a') (a : α) : π (.inl a) = .inl (restrictInl π h a) :=
  (h a).choose_spec

/-- Dropping the pairs that involve the clique: the cost of `π` w.r.t. `(G, H)` is at least the cost
of its restriction `σ` to `V(G')` w.r.t. `(G', H')`. -/
lemma costEditBij_restrict (π : VN N ≃ VN N) (σ : Base N ≃ Base N)
    (hσ : ∀ b, π (.inl b) = .inl (σ b)) :
    costEditBij (Gp N) (Hp N) σ ≤ costEditBij (GN N) (HN N) π := by
  -- a sum of nonnegative terms over `V(G') ⊕ K` is at least the sum over `V(G')`
  have hinl : ∀ F : VN N → ℝ, (∀ x, 0 ≤ F x) → ∑ b, F (.inl b) ≤ ∑ x, F x := fun F hF => by
    rw [Fintype.sum_sum_type (f := F)]
    exact le_add_of_nonneg_right (sum_nonneg fun _ _ => hF _)
  rw [costEditBij_eq, costEditBij_eq]
  calc ∑ b, ∑ b', |adj (Gp N) b b' - adj (Hp N) (σ b) (σ b')|
      = ∑ b, ∑ b', |adj (GN N) (.inl b) (.inl b') - adj (HN N) (π (.inl b)) (π (.inl b'))| := by
        simp only [hσ, GN, HN, adj_lock_inl_inl]
    _ ≤ ∑ b, ∑ x', |adj (GN N) (.inl b) x' - adj (HN N) (π (.inl b)) (π x')| :=
        sum_le_sum fun b _ => hinl (fun x' => |adj (GN N) (.inl b) x' -
          adj (HN N) (π (.inl b)) (π x')|) fun _ => abs_nonneg _
    _ ≤ ∑ x, ∑ x', |adj (GN N) x x' - adj (HN N) (π x) (π x')| :=
        hinl (fun x => ∑ x', |adj (GN N) x x' - adj (HN N) (π x) (π x')|)
          fun _ => sum_nonneg fun _ _ => abs_nonneg _

/-- The cost of a compliant bijection, which maps the core by `ρ`, w.r.t. `(G', H')`: the core-core
pairs cost `mixCore N ρ ρ` and the core-marker pairs `2 ∑ ℓ(v_{2c}, π(v_{2c}))` (Lemma 23). -/
lemma costEditBij_sumCongr (ρ : Fin N ≃ Fin N) :
    costEditBij (Gp N) (Hp N) (ρ.sumCongr (Equiv.refl (Fin N))) =
      mixCore N ρ ρ + 2 * ∑ c, (ell c (ρ c) : ℝ) := by
  rw [costEditBij, ← extMarkers_permMat, costEdit_extMarkers, coreCost_permMat]
  simp only [sum_permMat_mul]

/-! ### Displacements -/

/-- The signed displacement `d ∈ (-N, N]` of `v_{2c}` under a bijection that maps the core vertex
`c` to `ρ(c)`, i.e. `π(v_{2c}) = w_{(2c + d) mod 2N}`. -/
def disp (ρ : Fin N ≃ Fin N) (c : Fin N) : ℤ :=
  if (2 * (ρ c).val + 1 - 2 * c.val : ℤ) ≤ -N then 2 * (ρ c).val + 1 - 2 * c.val + 2 * N
  else if (N : ℤ) < 2 * (ρ c).val + 1 - 2 * c.val then 2 * (ρ c).val + 1 - 2 * c.val - 2 * N
  else 2 * (ρ c).val + 1 - 2 * c.val

/-- `ℓ(v_{2c}, π(v_{2c})) = |d_c|`. -/
lemma ell_eq_abs_disp (ρ : Fin N ≃ Fin N) (c : Fin N) : (ell c (ρ c) : ℤ) = |disp ρ c| := by
  have := c.isLt
  have := (ρ c).isLt
  rcases abs_cases (disp ρ c) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> unfold disp at * <;>
    simp only [ell, cycDist, posG, posH] <;> split_ifs at * <;> omega

/-- `d_c` is odd, so `|d_c| ≥ 1`. -/
lemma one_le_ell (ρ : Fin N ≃ Fin N) (c : Fin N) : 1 ≤ ell c (ρ c) := by
  have := c.isLt
  have := (ρ c).isLt
  simp only [ell, cycDist, posG, posH]
  omega

/-- `d_c` differs from `2ρ(c) + 1 - 2c` by a multiple of `2N`. -/
lemma disp_eq (ρ : Fin N ≃ Fin N) (c : Fin N) :
    ∃ e : ℤ, disp ρ c = 2 * (ρ c).val + 1 - 2 * c.val + 2 * N * e := by
  unfold disp
  split_ifs
  · exact ⟨1, by ring⟩
  · exact ⟨-1, by ring⟩
  · exact ⟨0, by ring⟩

/-- `∑ d_c ≡ N (mod 2N)`, as `π` maps the even positions bijectively onto the odd ones. -/
lemma sum_disp (ρ : Fin N ≃ Fin N) : ∃ e : ℤ, ∑ c, disp ρ c = N + 2 * N * e := by
  choose e he using disp_eq ρ
  refine ⟨∑ c, e c, ?_⟩
  have hρ : ∑ c : Fin N, ((ρ c : ℕ) : ℤ) = ∑ c : Fin N, ((c : ℕ) : ℤ) :=
    Equiv.sum_comp ρ fun c : Fin N => ((c : ℕ) : ℤ)
  simp only [he, sum_add_distrib, sum_sub_distrib, ← mul_sum, hρ, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- `|∑ d_c| ≥ N`. -/
lemma sum_disp_ge (ρ : Fin N ≃ Fin N) :
    (N : ℤ) ≤ ∑ c, disp ρ c ∨ ∑ c, disp ρ c ≤ -N := by
  obtain ⟨e, he⟩ := sum_disp ρ
  rw [he]
  rcases le_or_gt 0 e with h | h
  · left; nlinarith
  · right; nlinarith

/-! ### Claim 26 -/

/-- The core edge `{c, N - c}` of `G'` (`c ≥ 1`) is mapped onto a core edge of `H'`. -/
def Preserved (ρ : Fin N ≃ Fin N) (c : Fin N) : Prop :=
  1 ≤ c.val ∧ ((ρ c).val + (ρ (partner c)).val + 1 = N ∧ ρ c ≠ ρ (partner c))

instance (ρ : Fin N ≃ Fin N) : DecidablePred (Preserved ρ) := fun c => by
  unfold Preserved; infer_instance

lemma partner_partner {c : Fin N} (hc : 1 ≤ c.val) : partner (partner c) = c := by
  have := c.isLt
  have h1 := partner_val hc
  exact Fin.ext (by rw [partner_val (by omega), h1]; omega)

/-- `2k = #S`: `pres N ρ ρ` counts the vertices `c ∈ S`. -/
lemma pres_eq_card (hN : Odd N) (ρ : Fin N ≃ Fin N) :
    pres N ρ ρ = #{c | Preserved ρ c} := by
  rw [pres_eq hN, sum_boole]
  rfl

/-- For a preserved edge `{c, N - c}` with displacements in `(-N, N)`, `d_c + d_{N-c} = 0`. -/
lemma disp_add_disp_partner (ρ : Fin N ≃ Fin N) {c : Fin N} (hc : Preserved ρ c)
    (h1 : disp ρ c ≠ N) (h2 : disp ρ (partner c) ≠ N) :
    disp ρ c + disp ρ (partner c) = 0 := by
  obtain ⟨hc1, hsum, -⟩ := hc
  have := partner_val hc1
  have := c.isLt
  have := (ρ c).isLt
  have := (ρ (partner c)).isLt
  unfold disp at *
  split_ifs at * <;> omega

/-- **Claim 26.** `U ≥ N + 2k`, where `U = ∑ ℓ(v_{2c}, π(v_{2c}))` and `2k = pres N ρ ρ` is the
number of preserved ordered core edges. -/
theorem claim31 (hN : Odd N) (ρ : Fin N ≃ Fin N) :
    (N : ℝ) + pres N ρ ρ ≤ ∑ c, (ell c (ρ c) : ℝ) := by
  rw [pres_eq_card hN]
  have hN1 : 1 ≤ N := by obtain ⟨m, rfl⟩ := hN; omega
  -- work in `ℤ`
  suffices h : (N : ℤ) + #{c | Preserved ρ c} ≤ ∑ c, (ell c (ρ c) : ℤ) by exact_mod_cast h
  have hge : ∀ c, disp ρ c ≤ ell c (ρ c) ∧ -disp ρ c ≤ ell c (ρ c) := fun c => by
    rw [ell_eq_abs_disp]; exact ⟨le_abs_self _, neg_le_abs _⟩
  have hone : ∀ c, (1 : ℤ) ≤ ell c (ρ c) := fun c => by exact_mod_cast one_le_ell ρ c
  -- `S ⊆ {c ≥ 1}`, so `2k ≤ N - 1`
  have hS : (#{c | Preserved ρ c} : ℤ) ≤ N - 1 := by
    have : #{c | Preserved ρ c} ≤ #{c : Fin N | c ≠ ⟨0, by omega⟩} :=
      card_le_card fun c hc => by
        simp only [mem_filter, mem_univ, true_and] at hc ⊢
        exact fun h => by rw [h] at hc; exact absurd hc.1 (by simp)
    rw [filter_ne' univ, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at this
    omega
  by_cases hN' : ∃ c₀, disp ρ c₀ = N
  · -- some displacement is `N`: `U ≥ N + (N - 1)`
    obtain ⟨c₀, hc₀⟩ := hN'
    rw [← add_sum_erase _ _ (mem_univ c₀)]
    have h1 : (N : ℤ) ≤ ell c₀ (ρ c₀) := by have := (hge c₀).1; omega
    have h2 : ((univ.erase c₀).card : ℤ) ≤ ∑ c ∈ univ.erase c₀, (ell c (ρ c) : ℤ) := by
      rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact sum_le_sum fun c _ => hone c
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, Nat.cast_sub hN1,
      Nat.cast_one] at h2
    omega
  · -- all displacements in `(-N, N)`
    push Not at hN'
    -- `∑_{c ∈ S} d_c = 0`: pair `c` with its partner `N - c`
    have hS0 : ∑ c ∈ univ.filter (Preserved ρ), disp ρ c = 0 := by
      refine sum_involution (fun c _ => partner c) (fun c hc => ?_) (fun c hc _ => ?_)
        (fun c hc => ?_) (fun c hc => ?_)
      · simp only [mem_filter, mem_univ, true_and] at hc
        exact disp_add_disp_partner ρ hc (hN' c) (hN' _)
      · simp only [mem_filter, mem_univ, true_and] at hc
        intro h
        have := partner_val hc.1
        have := congrArg Fin.val h
        obtain ⟨m, rfl⟩ := hN
        omega
      · simp only [mem_filter, mem_univ, true_and] at hc ⊢
        obtain ⟨hc1, hsum, hne⟩ := hc
        have := c.isLt
        have h1 := partner_val hc1
        refine ⟨by omega, ?_, ?_⟩ <;> rw [partner_partner hc1]
        · omega
        · exact Ne.symm hne
      · simp only [mem_filter, mem_univ, true_and] at hc
        exact partner_partner hc.1
    -- split `U` into the vertices in `S` and the others
    rw [← sum_filter_add_sum_filter_not univ (Preserved ρ)]
    have h1 : (#{c | Preserved ρ c} : ℤ) ≤ ∑ c ∈ univ with Preserved ρ c, (ell c (ρ c) : ℤ) := by
      rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact sum_le_sum fun c _ => hone c
    have hsplit := sum_filter_add_sum_filter_not univ (Preserved ρ) (disp ρ)
    rw [hS0, zero_add] at hsplit
    have h2 : ∑ c ∈ univ.filter (fun c => ¬Preserved ρ c), disp ρ c ≤
        ∑ c ∈ univ.filter (fun c => ¬Preserved ρ c), (ell c (ρ c) : ℤ) :=
      sum_le_sum fun c _ => (hge c).1
    have h3 : -∑ c ∈ univ.filter (fun c => ¬Preserved ρ c), disp ρ c ≤
        ∑ c ∈ univ.filter (fun c => ¬Preserved ρ c), (ell c (ρ c) : ℤ) := by
      rw [← sum_neg_distrib]
      exact sum_le_sum fun c _ => (hge c).2
    rcases sum_disp_ge ρ with h | h <;> linarith

/-! ### Lemma 25 -/

/-- **Lemma 25.** Every bijection `π ∈ Bij(V, W)` satisfies `C_ed(π) ≥ 4N - 2`. -/
theorem lemma30_bij (hN : Odd N) (π : VN N ≃ VN N) :
    (4 * N - 2 : ℝ) ≤ costEditBij (GN N) (HN N) π := by
  have hN1 : 1 ≤ N := by obtain ⟨m, rfl⟩ := hN; omega
  by_cases hπ : costEditBij (GN N) (HN N) π < ((4 * N - 1 : ℕ) : ℝ)
  swap
  · push Not at hπ
    have : ((4 * N - 1 : ℕ) : ℝ) = 4 * N - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    linarith
  -- Lemma 22: `π` fixes every marker and maps `V(G')` onto itself
  obtain ⟨hfix, hV⟩ := lemma27_bij_edit (G := Gp N) (H := Hp N) markerEnum_injective
    markerEnum_mono (deg_Gp_le hN) deg_Hp_le markerEnum_deg π hπ
  set σ := restrictInl π hV with hσdef
  have hσ : ∀ b, π (.inl b) = .inl (σ b) := restrictInl_spec π hV
  have hσz : ∀ r, σ (.inr r) = .inr r := fun r => by
    obtain ⟨j, hj⟩ := exists_markerEnum r
    have := hfix j
    rw [hj, hσ] at this
    exact Sum.inl_injective this
  -- so `π` maps the core of `G'` onto the core of `H'`, by `ρ`
  have hcore : ∀ c, ∃ d, σ (.inl c) = .inl d := fun c => by
    rcases h : σ (.inl c) with d | r
    · exact ⟨d, rfl⟩
    · rw [← hσz r] at h
      exact absurd (σ.injective h) (by simp)
  set ρ := restrictInl σ hcore with hρdef
  have hρ : ∀ c, σ (.inl c) = .inl (ρ c) := restrictInl_spec σ hcore
  have hσρ : σ = ρ.sumCongr (Equiv.refl (Fin N)) := by
    ext b
    rcases b with c | r
    · simp [hρ]
    · simp [hσz]
  -- `C_ed(π) ≥ 2(N - 1 - 2k) + 2U ≥ 4N - 2`
  have h1 := costEditBij_restrict π σ hσ
  rw [hσρ, costEditBij_sumCongr, mixCore_eq hN] at h1
  have h2 := claim31 hN ρ
  linarith

/-- **Lemma 25.** `d_ed(G, H) ≥ 4N - 2`. -/
theorem lemma30 (hN : Odd N) : (4 * N - 2 : ℝ) ≤ dEdit (GN N) (HN N) :=
  le_dEdit fun π => lemma30_bij hN π

end GsimOT.Prop6
