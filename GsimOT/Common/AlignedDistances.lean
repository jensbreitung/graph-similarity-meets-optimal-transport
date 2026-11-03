/-
# Distances of aligned graphs of the same order for operator norms

Paper, Section 1 (pp. 1–3), Section 2 (p. 5) and App. B (p. 15).

* `kappa p q`        : `κ_{p→q} = 1/q + 1 - 1/p` (App. B, p. 15, l. 513).
* `alignedDiff G H π`: `A_G^π - A_H` for a bijection `π : V ≃ W`, where `A_G^π(π v, π v') = A_G(v, v')`,
  i.e. `A_G^π` is `A_G` with rows and columns permuted according to `π` (p. 1, l. 9–10).
* `distPQ p q G H`   : `d_{p→q}(G, H) = min_π ‖A_G^π - A_H‖_{p→q}` over `π ∈ Bij(V, W)` (graphs of
  the same order; p. 1, l. 7–9; Section 2, p. 5, l. 175, 186–187).
* `deltaPQ p q G H`  : `δ_{p→q}(G, H) = N^{-κ} d_{p→q}(G, H)` with `N = |V|`, i.e. `d_{p→q}`
  normalised by `s(N) = N^{1/q+1-1/p} = N^κ` (p. 1, l. 21–28; p. 3, l. 88–90; App. B, p. 15,
  l. 513–514).
-/
import GsimOT.Common.Basic
import GsimOT.Common.OperatorNorm

namespace GsimOT

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- `κ_{p→q} = 1/q + 1 - 1/p` (App. B, p. 15, l. 513). -/
noncomputable def kappa (p q : ENNReal) : ℝ := q⁻¹.toReal + 1 - p⁻¹.toReal

section Graphs

variable (p q : ENNReal) (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
  [DecidableRel H.Adj]

/-- `A_G^π - A_H ∈ ℝ^{W×W}` where `A_G^π(π v, π v') = A_G(v, v')`. -/
def alignedDiff (π : V ≃ W) : Matrix W W ℝ := fun w w' =>
  adj G (π.symm w) (π.symm w') - adj H w w'

/-- `d_{p→q}(G, H) = min_{π ∈ Bij(V,W)} ‖A_G^π - A_H‖_{p→q}`. -/
noncomputable def distPQ : ℝ := ⨅ π : V ≃ W, opNorm p q (alignedDiff G H π)

/-- `δ_{p→q}(G, H) = N^{-κ} d_{p→q}(G, H)` with `N = |V|`, the normalisation by
`s(N) = N^{1/q+1-1/p}` (p. 3, l. 88–90; App. B, p. 15, l. 513–514). -/
noncomputable def deltaPQ : ℝ := (Fintype.card V : ℝ) ^ (-kappa p q) * distPQ p q G H

end Graphs

end GsimOT
