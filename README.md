# Graph Similarity Meets Optimal Transport — Lean 4 formalisation

This repository contains a machine-checked formalisation, in [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4), of results from the paper

> J. Breitung, T. Gervens, M. Grohe. *Graph Similarity Meets Optimal Transport.*
> ([`Graph_Similarity_Meets_Optimal_Transport.pdf`](Graph_Similarity_Meets_Optimal_Transport.pdf))

The proofs follow the arguments of the paper step by step. Every result lives in its own folder,
and all results share one set of common definitions.

## Status

Formalised: **Theorem 1** (blowup distances equal optimal transport distances, for all operator
`p → q`-norms), the lower bound `4/3` and the upper bound `2` for the **edit distance** `d_ed`
(Proposition 5, Theorem 6), the results on the **local edit distance** `d₁` (the distance induced by
the operator `1 → 1`-norm), the **cut distance** `d_□` and the **spectral distance** `d₂` of
Section 3, and the **hardness results** of Section 4. The thin matching theorem of [HOG26]
(Theorem 35), used for Theorem 11, is formalised in a separate library (see below).

Statement, equation, appendix and page numbers refer to the paper. The table gives the Lean
declarations and the folder of every result; [`docs/NUMBERING.md`](docs/NUMBERING.md) lists the files
and declarations of all numbered statements and equations.

| Result (paper) | Statement | Lean | Folder | Correspondence | Status |
|---|---|---|---|---|---|
| **Theorem 1** (p. 3, Appendix B) | `δ^•_{p→q} = δ^OT_{p→q}` for all `1 ≤ p, q ≤ ∞`; the limit defining the blowup distance `δ^•` exists | `GsimOT.theorem1`, `GsimOT.theorem1_tendsto` | [`GsimOT/Theorem1_BlowupEqualsOT`](GsimOT/Theorem1_BlowupEqualsOT) | [PDF](GsimOT/Theorem1_BlowupEqualsOT/Theorem1_correspondence.pdf) | ✅ fully proved |
| **Proposition 5** (p. 6, Appendix C.1) and **Theorem 3 (1)** | for odd `N ≥ 3`: `d_ed(G, H) ≥ 4N − 2` and `d_ed^OT(G, H) ≤ 3N + 1`; `δ_ed ≥ (4/3 − ε)·δ_ed^OT` | `GsimOT.Prop5.proposition5`, `GsimOT.Prop5.proposition5_delta`, `GsimOT.Prop5.theorem3_item1` | [`GsimOT/Proposition5_EditLowerBound`](GsimOT/Proposition5_EditLowerBound) | [PDF](GsimOT/Proposition5_EditLowerBound/Proposition5_correspondence.pdf) | ✅ fully proved |
| **Theorem 6** (p. 7, Appendix C.2) and the `δ_ed` part of **Theorem 2** | `∑ᵢ λᵢ C_ed(πᵢ) ≤ 2·C_ed(Q)` for `Q = ∑ᵢ λᵢ P_{πᵢ}`; `d_ed ≤ 2·d_ed^OT`, `δ_ed ≤ 2·δ_ed^OT` | `GsimOT.theorem6`, `GsimOT.theorem6_dEdit`, `GsimOT.theorem2_edit` | [`GsimOT/Theorem6_EditUpperBound`](GsimOT/Theorem6_EditUpperBound) | [PDF](GsimOT/Theorem6_EditUpperBound/Theorem6_correspondence.pdf) | ✅ fully proved |
| **Proposition 8** (p. 7, Appendix D.1) and **Theorem 3 (2)** | for even `r ≥ 2`: `d₁(G_r, H_r) = r`, `d₁^OT(G_r, H_r) = 1`, `\|V(G_r)\| = Θ(r³)` | `GsimOT.Prop8.proposition8`, `GsimOT.Prop8.theorem3_item2` | [`GsimOT/Proposition8_LocalEditLowerBound`](GsimOT/Proposition8_LocalEditLowerBound) | [PDF](GsimOT/Proposition8_LocalEditLowerBound/Proposition8_correspondence.pdf) | ✅ fully proved |
| **Theorem 9** (p. 9, Appendix D.2) and the `δ₁` part of **Theorem 2** | `δ₁ ≤ 15·√(δ₁^OT · ln(4/δ₁^OT))` | `GsimOT.theorem9` | [`GsimOT/Theorem9_LocalEditUpperBound`](GsimOT/Theorem9_LocalEditUpperBound) | [PDF](GsimOT/Theorem9_LocalEditUpperBound/Theorem9_correspondence.pdf) | ✅ proved, assuming the cited Lemma 30 (see below) |
| **Proposition 10** (p. 9, Appendix E.1) and **Theorem 3 (3)** | graphs on 145 vertices with `d_□(G, H) = 8` and `d_□^OT(G, H) ≤ 4`; moreover `d_□^OT(G, H) = 4` (p. 10: the Lean certificate cited in the paper), so `δ_□ = 2·δ_□^OT` | `GsimOT.Prop10.proposition10`, `GsimOT.Prop10.dOTCut_eq_four`, `GsimOT.Prop10.theorem3_item3` | [`GsimOT/Proposition10_CutLowerBound`](GsimOT/Proposition10_CutLowerBound) | [PDF](GsimOT/Proposition10_CutLowerBound/Proposition10_correspondence.pdf) | ✅ fully proved |
| **Theorem 11** (p. 10, Appendix E.2) and the `δ_□` part of **Theorem 2** | `δ_□^OT ≤ δ_□ ≤ C·δ_□^OT ln(e/δ_□^OT) ln(e ln(e/δ_□^OT))`; `δ_□ ≤ C_α (δ_□^OT)^α` for every `α < 1`, i.e. `δ_□ ≤ C_ε (δ_□^OT)^{1−ε}` for every `ε > 0` | `GsimOT.theorem11_of_rackeShah`, `GsimOT.theorem11_power_lt_one_of_rackeShah`, `GsimOT.theorem2_cut_of_rackeShah` (from the `_of_thin` versions) | [`GsimOT/Theorem11_CutUpperBound`](GsimOT/Theorem11_CutUpperBound) | [PDF](GsimOT/Theorem11_CutUpperBound/Theorem11_correspondence.pdf) | ✅ proved, assuming only the tree-cut sparsifier theorem [RS14] (through the formalisation of Theorem 35 = [HOG26, Thm. 1.4], see below) |
| **Proposition 12** (p. 11, Appendix F) | `δ_□ ≤ δ₂ ≤ 2√δ_□` | `GsimOT.proposition12` | [`GsimOT/Proposition12_CutVsSpectral`](GsimOT/Proposition12_CutVsSpectral) | [PDF](GsimOT/Proposition12_CutVsSpectral/Proposition12_correspondence.pdf) | ✅ fully proved |
| **Proposition 13** (p. 11, Appendix F.1) and **Theorem 3 (4)** | `d₂(G_r, H_r) = √r`, `1/(2√2) ≤ d₂^OT(G_r, H_r) ≤ 1`; no bound `δ₂ ≤ C (δ₂^OT)^α` for `α > 3/4` | `GsimOT.Prop13.proposition13`, `GsimOT.Prop13.theorem3_item4`, `GsimOT.Prop13.no_power_bound` | [`GsimOT/Proposition13_SpectralLowerBound`](GsimOT/Proposition13_SpectralLowerBound) | [PDF](GsimOT/Proposition13_SpectralLowerBound/Proposition13_correspondence.pdf) | ✅ fully proved |
| **Theorem 14** (p. 12, Appendix F.2) and the `δ₂` part of **Theorem 2** | `δ₂ ≤ δ₂^OT + 2√(2δ₂^OT)` and `δ₂ ≤ (1 + 2√2)√δ₂^OT`; `theorem14_min` proves the sharper `δ₂ ≤ min{1, δ₂^OT + 4√(h δ₂^OT)}` | `GsimOT.theorem14`, `GsimOT.theorem14_min`, `GsimOT.theorem14_sqrt` | [`GsimOT/Theorem14_SpectralUpperBound`](GsimOT/Theorem14_SpectralUpperBound) | [PDF](GsimOT/Theorem14_SpectralUpperBound/Theorem14_correspondence.pdf) | ✅ fully proved |
| **Theorem 15** (p. 12, Appendix G) | `d_ed^OT(F₁, F₂) ≤ 4m` iff the Three-Partition instance is a YES-instance | `GsimOT.Hardness.ThreePartition.dOTEdit_le_iff` | [`GsimOT/Theorem15_EditHardness`](GsimOT/Theorem15_EditHardness) | [PDF](GsimOT/Theorem15_EditHardness/Theorem15_correspondence.pdf) | ✅ reduction fully proved (see below) |
| **Theorem 16** (p. 12, Appendix G) | YES-instances: `d₁^OT(F₁, F₂) ≤ 1`; NO-instances: `d₁^OT(F₁, F₂) ≥ 2` | `GsimOT.Hardness.ThreePartition.dOTOne_le_of_isYes`, `GsimOT.Hardness.ThreePartition.two_le_dOTOne_of_not_isYes` | [`GsimOT/Theorem16_LocalEditHardness`](GsimOT/Theorem16_LocalEditHardness) | [PDF](GsimOT/Theorem16_LocalEditHardness/Theorem16_correspondence.pdf) | ✅ reduction fully proved (see below) |
| **Theorem 17** (p. 12, Appendix G) with Lemma 53, Corollary 54, Claims 55, 56 | YES-instances: `d_p^OT(G, H) ≤ 1`; NO-instances: `d_p^OT(G, H) > 2^{b(p)} − ε`, for all `1 ≤ p ≤ ∞` | `GsimOT.Hardness.ThreePartition.dOT_le_one_of_isYes`, `GsimOT.Hardness.ThreePartition.lt_dOT_of_not_isYes` | [`GsimOT/Theorem17_OperatorNormHardness`](GsimOT/Theorem17_OperatorNormHardness) | [PDF](GsimOT/Theorem17_OperatorNormHardness/Theorem17_correspondence.pdf) | ✅ reduction fully proved (see below) |
| **Theorem 18** (p. 13, Appendix G) with Eq. (47), Claims 58–61 | for every `0 < δ < 1` and every graph `F` with an edge: `2(1 − δ)·maxcut(F) ≤ d_□^OT(G, H) ≤ 2·maxcut(F)`; for `δ = 1/34` this is Eq. (47), `(33/17)·maxcut(F) ≤ d_□^OT(G, H)` | `GsimOT.Hardness.maxcut_dOTCut_bounds_paper`, `GsimOT.Hardness.maxcut_dOTCut_bounds_eq47` | [`GsimOT/Theorem18_CutHardness`](GsimOT/Theorem18_CutHardness) | [PDF](GsimOT/Theorem18_CutHardness/Theorem18_correspondence.pdf) | ✅ reduction fully proved (see below) |
| Shared notions, ℓᵖ/operator norms, Lemma 19, Observation 21, Lemma 22, Lemma 29, Eqs. (3) and (7), attainment of the minima (Appendix A), edit distance, the graphs of Section 4 | — | `GsimOT.*` | [`GsimOT/Common`](GsimOT/Common) | [PDF](GsimOT/Common/Common_correspondence.pdf) | ✅ fully proved |

Each folder contains a PDF with a table that matches every statement of the paper (with its page
number) to the corresponding Lean declaration (with file and line), followed by notes on the
formalisation, and a proof overview `<Name>_overview.pdf` that explains the structure of the Lean proof.

**Hardness results.** For Theorems 15, 16, 17 and 18 the Lean statements are the correctness of
the reductions: for the constructed graphs, YES-instances have a small and NO-instances a large
distance (for Theorem 18: `d_□^OT` is within a factor `1 − δ` of `2·maxcut(F)`). The complexity side
(polynomial running time, NP-hardness of Three-Partition, Håstad's bound for MaxCut) is not
formalised. These results and the graphs of their reductions are in the namespace `GsimOT.Hardness`.

**Trusted base.** The build script checks that no `sorry` and no `axiom` occur, and prints the
axioms used by every main result. Only the standard axioms `propext`, `Classical.choice` and
`Quot.sound` appear.

**Lemma 30 and Theorem 35 are hypotheses, not axioms.** Theorem 9 relies on the dependent rounding
theorem of Chekuri, Vondrák and Zenklusen (paper: Lemma 30, [CVZ11, Thm. 1.1]), and Theorem 11 on the
thin-permutation theorem of Haqi and Oveis Gharan (paper: Theorem 35, [HOG26, Thm. 1.4]). The paper
cites both results without proving them. Here they are the propositions `GsimOT.CVZRounding`
([`Lemma30_DependentRounding.lean`](GsimOT/Theorem9_LocalEditUpperBound/Lemma30_DependentRounding.lean))
and `GsimOT.ThinPermutationTheorem`
([`Definitions.lean`](GsimOT/Theorem11_CutUpperBound/Definitions.lean)), which are explicit
arguments `hCVZ` of `GsimOT.theorem9` and `hThin` of `GsimOT.theorem11_of_thin`. The statements
follow the paper; Lemma 30 is specialised to doubly stochastic matrices (the only case used). The
contraction principle [LT91] (Lemma 43), which the paper also cites, is proved. Theorem 35 is
moreover *derived* from the formalisation of [HOG26] (see below), so Theorem 11 also holds assuming
only the tree-cut sparsifier theorem [RS14].

### The thin matching paper [HOG26] (separate library `ThinMatching/`)

Theorem 35 of the paper is [HOG26, Theorem 1.4] (A. Haqi, S. Oveis Gharan, *On Thin Perfect Matchings
up to Polylogarithmic Factors*, [arXiv:2606.01330](https://arxiv.org/abs/2606.01330)). It is
formalised in the separate Lean library [`ThinMatching/`](ThinMatching), which imports only Mathlib
and is independent of `GsimOT`. Correspondence: [`ThinMatching/HOG26_correspondence.pdf`](ThinMatching/HOG26_correspondence.pdf);
proof overview: [`ThinMatching/HOG26_overview.pdf`](ThinMatching/HOG26_overview.pdf).

| [HOG26] | Lean | Status |
|---|---|---|
| Lemma 1.2 (linear lower bound in the support) | `ThinMatching.lemma12` | ✅ fully proved |
| Theorem 1.3 (support-constrained `O(n log n)`-thin matching) | `ThinMatching.theorem13_support` | ✅ proved, assuming Lemma 3.6 (`Lemma36`; its proof is omitted in [HOG26]) |
| Theorem 1.4 (relaxed `O(log n log log n)`-thin matching, bipartite and general), with Prop. 4.3, Lemmas 4.5, 4.6 | `ThinMatching.theorem14_bip`, `ThinMatching.theorem14` | ✅ proved, assuming the tree-cut sparsifier theorem of Räcke–Shah [RS14] (`RackeShahTheorem`, cited in [HOG26] as Theorem 2.2) |
| Corollary 1.6 (metric distortion) | — | not formalised (application, needs [ACR23]) |

The bridge [`GsimOT/Theorem11_CutUpperBound/FromThinMatching.lean`](GsimOT/Theorem11_CutUpperBound/FromThinMatching.lean)
derives `GsimOT.ThinPermutationTheorem` from Theorem 1.4, so **Theorem 11 holds assuming only [RS14]**
(`GsimOT.theorem11_of_rackeShah`).

## Checking the proofs

### Requirements

* Linux, macOS or WSL with `git`, `curl` and `bash`
* about 6 GB of free disk space (for the prebuilt Mathlib library)
* at least 8 GB of RAM
* an internet connection for the first build

Lean and Mathlib are pinned in [`lean-toolchain`](lean-toolchain) (Lean `v4.35.0`) and
[`lakefile.toml`](lakefile.toml) / [`lake-manifest.json`](lake-manifest.json) (Mathlib `v4.35.0`),
so everyone checks the proofs against exactly the same versions.

### One command

```bash
git clone https://github.com/jensbreitung/graph-similarity-meets-optimal-transport.git
cd graph-similarity-meets-optimal-transport
bash build.sh --install-elan      # or just: bash build.sh   if elan/lake is already installed
```

`build.sh`:

1. finds the Lean toolchain manager [elan](https://github.com/leanprover/elan), or installs it
   with `--install-elan`;
2. downloads the prebuilt Mathlib cache (`lake exe cache get`; skip with `--no-cache`);
3. builds the library, which checks every proof (`lake build`);
4. checks that the sources contain no `sorry`, `admit` or `axiom`;
5. runs [`scripts/CheckAxioms.lean`](scripts/CheckAxioms.lean), which prints the axioms of the main
   results, and fails if anything other than `propext`, `Classical.choice` and `Quot.sound`
   appears;
6. with `--docs`, regenerates the correspondence and proof overview PDFs (needs `python3` and
   `pdflatex`).

The first run takes a few minutes, mostly to download Mathlib. After that, `lake build` finishes
in about a minute.

### By hand

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh  # install elan
lake exe cache get                       # download prebuilt Mathlib
lake build                               # check all proofs
lake env lean scripts/CheckAxioms.lean   # print the axioms of the main results
```

You can also build a single result, e.g. `lake build GsimOT.Theorem9_LocalEditUpperBound.Theorem9`.

### Interactively

Open the repository folder in VS Code with the
[Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) (after
`lake exe cache get`). Opening any `.lean` file starts the local Lean server, which checks the file
and shows the proof state at the cursor.

## Repository layout

Every result folder also contains `<Name>_correspondence.{tex,pdf}` (the correspondence table) and
`<Name>_overview.{tex,pdf}` (the proof overview).

```
GsimOT.lean                                  root module; imports everything
GsimOT/
├── Common/                                  shared notions and shared lemmas
│   ├── Basic.lean                           A_G, deg, DS(V,W), P_π, L_Q, C₁, d₁, d₁^OT, δ₁, δ₁^OT
│   ├── OperatorNorm.lean                    ℓᵖ norms, ‖·‖_{p→q}, Hölder, Lemma 19
│   ├── AlignedDistances.lean                A_G^π − A_H, d_{p→q}, δ_{p→q}
│   ├── CutNorm.lean                         ‖·‖_□, C_□, d_□, d_□^OT, δ_□, δ_□^OT, ζ_Q
│   ├── Birkhoff.lean                        Eq. (3): supp(Q) contains a bijection
│   ├── BirkhoffDecomposition.lean           Eq. (3): Q is a convex combination of the P_π
│   ├── Observation21_DegreeBound.lean       Observation 21
│   ├── DoublyStochastic.lean                DS(V,W): sums against Q, partial sums Q(S, T), compactness
│   ├── EditDistance.lean                    C_ed, d_ed, d_ed^OT, δ_ed, δ_ed^OT
│   ├── Attainment.lean                      the minima of Appendix A are attained
│   ├── Leaves.lean                          Section 4: attaching leaves
│   ├── Lemma22_LockingMarkers.lean          Lemma 22 (for • = 1)
│   ├── Lemma22_LockingMarkersEdit.lean      Lemma 22 (for • = ed)
│   ├── Lemma29_Integrality.lean             ρ_H and Lemma 29
│   ├── MatrixNorms.lean                     ‖·‖_ed = ‖·‖_(1), C_ed = ‖B‖_ed, Eq. (7)
│   ├── OTDistances.lean                     DS*, 0⁰ = 0, B, B_{p→q}, δ^OT_{p→q}, d^OT_{p→q}
│   ├── PathsAndCycles.lean                  Section 4: disjoint unions of paths and of cycles
│   └── ThreePartition.lean                  Section 4: Three-Partition instances and solutions
├── Theorem1_BlowupEqualsOT/                 Theorem 1
│   ├── Definitions.lean                     blowups, δ^•
│   ├── BlockNorms.lean                      norms of spread / averaged test vectors
│   ├── LowerBound.lean                      Eqs. (8)–(11)
│   ├── UpperBound.lean                      Eq. (15)
│   ├── Approximation.lean                   approximating couplings by denominator-ℓmn couplings
│   ├── Claim20.lean                         Claim 20, Eqs. (13), (15) along ℓ = ks
│   └── Theorem1.lean                        Theorem 1
├── Proposition5_EditLowerBound/             Proposition 5 (lower bound 4/3 for the edit distance)
│   ├── Construction.lean                    G', H' (core, markers, semicircles), G, H via Lemma 22
│   ├── Lemma23_MarkerCost.lean              ℓ, Lemma 23
│   ├── CoreEdges.lean                       the core edges; cost of the core-core pairs
│   ├── Lemma24_FractionalCost.lean          Q = ½(P_{π₋} + P_{π₊}), Lemma 24
│   ├── Lemma25_BijectionCost.lean           displacements, Claim 26, Lemma 25
│   └── Proposition5.lean                    Proposition 5, Theorem 3 (1)
├── Theorem6_EditUpperBound/                 Theorem 6 (upper bound for the edit distance)
│   ├── TraceFormula.lean                    Eq. (17); Frobenius identities, steps (a)–(g)
│   └── Theorem6.lean                        Theorem 6 (Appendix C.2), Theorem 2 for δ_ed
├── Proposition8_LocalEditLowerBound/        Proposition 8 (lower bound)
│   ├── Construction.lean                    markers, core, patterns, G⁰_r, H⁰_r
│   ├── Patterns.lean                        consecutive patterns, change counts, clock levels
│   ├── LockedGraphs.lean                    G_r, H_r via Lemma 22; the shifts σ_i
│   ├── Lemma27_FractionalCost.lean          Lemma 27: Q_r and C₁(Q_r) ≤ 1; C₁(σ_i) ≤ r
│   ├── Lemma28_BijectionCost.lean           Lemma 28 (walk argument)
│   └── Proposition8.lean                    Lemma 27, Proposition 8, Theorem 3 (2)
├── Theorem9_LocalEditUpperBound/            Theorem 9 (upper bound)
│   ├── Lemma30_DependentRounding.lean       statement of Lemma 30 (hypothesis)
│   ├── Lemma31_GoodMatching.lean            Lemma 31
│   ├── PathCutting.lean                     cutting paths into blocks and closing them
│   ├── Proposition32_Rounding.lean          Proposition 32
│   └── Theorem9.lean                        Theorem 9
├── Proposition10_CutLowerBound/             Proposition 10 (lower bound for the cut distance)
│   ├── Construction.lean                    the graphs G, H on 145 vertices
│   ├── Lemma33_BijectionCost.lean           Lemma 33: d_□(G, H) = 8
│   ├── Lemma34_FractionalCost.lean          Lemma 34: d_□^OT(G, H) ≤ 4
│   ├── OptimalAlignment.lean                d_□^OT(G, H) ≥ 4: the Lean certificate cited on p. 10
│   └── Proposition10.lean                   Proposition 10, d_□^OT(G, H) = 4, Theorem 3 (3)
├── Theorem11_CutUpperBound/                 Theorem 11 (upper bound for the cut distance)
│   ├── Definitions.lean                     thinness (Eq. (23)), Theorem 35 [HOG26], zonotopes
│   ├── Theorem38_ThinRounding.lean          E.2.1: Lemmas 36, 37, Eq. (26), Theorem 38
│   ├── Corollary46_SpectralTruncation.lean  E.2.2: Eq. (22), Lemmas 40, 41, 45, Corollary 46
│   ├── ContractionPrinciple.lean            Lemma 43 [LT91]
│   ├── Lemma47_MergingPermutations.lean     Lemmas 42, 44 and 47
│   ├── Theorem39_AdditiveRounding.lean      Lemma 48, Theorem 39
│   ├── Theorem11.lean                       E.2.3: Eq. (39), Theorem 11
│   └── FromThinMatching.lean                Theorem 35 from [HOG26, Thm. 1.4] (ThinMatching), Theorem 11 assuming [RS14]
├── Proposition12_CutVsSpectral/             Proposition 12 (cut distance vs. spectral distance)
│                                            └── Proposition12.lean
├── Proposition13_SpectralLowerBound/        Proposition 13 (lower bound for the spectral distance)
│   ├── Construction.lean                    the graphs G_r, H_r
│   ├── SpectralDistance.lean                d₂(G_r, H_r) = √r
│   ├── Lemma49.lean                         Lemma 49: r/√n ≤ d₂^OT(G_r, H_r) ≤ 1
│   └── Proposition13.lean                   Proposition 13, Theorem 3 (4)
├── Theorem14_SpectralUpperBound/            Theorem 14 (upper bound for the spectral distance)
│   ├── Tools.lean                           spectral-norm tools
│   ├── RandomBijection.lean                 γ_Q, Lemmas 50–52, Eqs. (40)–(43)
│   └── Theorem14.lean                       Theorem 14
├── Theorem15_EditHardness/                  Theorem 15 (hardness of d_ed^OT)
│                                            └── Theorem15.lean
├── Theorem16_LocalEditHardness/             Theorem 16 (hardness of d₁^OT)
│                                            └── Theorem16.lean
├── Theorem17_OperatorNormHardness/          Theorem 17 (hardness of d_p^OT)
│   ├── OperatorPNorms.lean                  ℓ^p norms, Schur test, Corollary 54 for symmetric matrices
│   ├── Lemma53_AggregatedMatrix.lean        Lemma 53
│   ├── Corollary54_ColumnBound.lean         Corollary 54
│   ├── Claim55_LeafMass.lean                Claim 55
│   ├── Claim56_SplitMass.lean               Claim 56
│   └── Theorem17.lean                       Theorem 17
└── Theorem18_CutHardness/                   Theorem 18 (hardness of approximating d_□^OT)
    ├── ProductSums.lean                     entry sums of B(G, H, Q) over products of sets
    ├── Claim58_LeafMass.lean                Claim 58
    ├── Claim59_SplitMass.lean               Claim 59
    ├── Claim60_WrongVertex.lean             Claim 60
    ├── Claim61_NearIdentity.lean            Claim 61
    ├── BaseGraphs.lean                      the base graphs G', H' from the [AN06] matrix
    └── Theorem18.lean                       Theorem 18 and Eq. (47)
ThinMatching.lean                            root module of the [HOG26] library
ThinMatching/                                formalisation of [HOG26] (independent library, imports only Mathlib)
├── Basic.lean, TreeSparsifier.lean, Load.lean   graphs, matchings, thinness, tree-cut sparsifiers, loads
├── LowerBound.lean                          Lemma 1.2
├── Discrepancy.lean, LoadVsCut.lean         Lemma 4.5, Proposition 4.3
├── TreePairing.lean                         Lemma 4.6 (Algorithm 2)
├── Theorem14.lean                           Theorem 1.4
├── SupportConstrained.lean, SupportConstrained/   Theorem 1.3 (trimming, sampling, Tutte witnesses, Lemma 3.5)
└── HOG26_correspondence.{tex,pdf}, HOG26_overview.{tex,pdf}
docs/NUMBERING.md                            every numbered statement and equation of the paper with its Lean files
scripts/
├── CheckAxioms.lean                         #print axioms for all main results
├── gen_correspondence.py                    generates the correspondence documents
├── build_overviews.py                       compiles the proof overviews
└── overview_preamble.tex, overview_template.tex   shared preamble and template of the proof overviews
build.sh                                     build-and-check script
```

### Conventions

* Graphs are Mathlib `SimpleGraph`s on finite types `V`, `W` (with decidable adjacency). `G` lives
  on `V` and `H` on `W`, as in the paper.
* `adj G v v' ∈ {0, 1}` is the adjacency matrix with real entries, and
  `localCost G H Q v w = ∑_{v',w'} |A_G(v,v') − A_H(w,w')| · Q(v',w')` is `L_Q(v,w)`.
* `costOne G H Q = max_{(v,w) ∈ supp Q} L_Q(v,w)` is `C₁(Q)` (Eq. (7)); `dOne` and `dOTOne` are the
  minimum over bijections and the infimum over `DS(V,W)`; `deltaOne` and `deltaOTOne` divide by `n`.
* `costEdit G H Q = ∑_{v,w,v',w'} |A_G(v,v') − A_H(w,w')| · Q(v,w) · Q(v',w')` is `C_ed(Q)`;
  `dEdit` and `dOTEdit` are the minimum over bijections and the infimum over `DS(V,W)`;
  `deltaEdit` and `deltaOTEdit` divide by `n²`.
* `B G H Q` and `Bmat p q G H Q` (`Common/OTDistances.lean`) are `B(G,H,Q)` and `B_{p→q}(G,H,Q)`;
  `entrywiseNorm` (`Common/MatrixNorms.lean`, the paper's `‖·‖_ed = ‖·‖_(1)`), `cutNorm`
  (`Common/CutNorm.lean`) and `opNorm p q` (`Common/OperatorNorm.lean`) are the norms; `dOTCut`,
  `dOT p q` and `deltaOTPQ p q` are `d_□^OT`, `d_{p→q}^OT` and `δ_{p→q}^OT`. Each notion has exactly
  one definition, shared by all results. Eq. (7) is `dOT_one_one_eq_dOTOne`, and
  `costEdit_eq_entrywiseNorm_B` gives `C_ed(Q) = ‖B(G,H,Q)‖_ed`. The Section 4 results and their
  gadgets (`Common/PathsAndCycles.lean`, `Common/ThreePartition.lean`, `Common/Leaves.lean`) are in
  the namespace `GsimOT.Hardness`.
* The result folders depend only on `GsimOT/Common`, never on each other.