/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Path.Planar
import LeanPool.JacobianDiffgeo.Path.LocalPrimitive
import LeanPool.JacobianDiffgeo.Path.Chain
import LeanPool.JacobianDiffgeo.Path.Continuation
import LeanPool.JacobianDiffgeo.Path.Bridge
import LeanPool.JacobianDiffgeo.Path.HomotopySquare
import LeanPool.JacobianDiffgeo.Path.Periods
import LeanPool.JacobianDiffgeo.Path.Perturb

/-!
# paths-and-integrals (CC6): integration of holomorphic 1-forms along continuous paths

API summary (see `docs/design/paths-and-integrals.md`), namespace `RS`. NO measure-theoretic
integration on `X`; the only integration is planar (interval integrals, via the single-chart
bridge). The definition is by chain continuation (Forster 10.9), not the universal cover.

* **Planar layer** (`Path/Planar.lean`, no manifold imports — reused by `dbar-solvability`,
  `residue-calculus`, `monodromy`, `abel-weak-solutions`):
  `RS.exists_hasDerivAt_ball` (disk primitive with prescribed value, Morera via mathlib's
  `HasPrimitives.lean`), `RS.eventuallyEq_of_hasDerivAt_eq` (local uniqueness of primitives),
  `RS.Convex.isPathConnected_diff_countable` (convex-minus-countable is path-connected),
  `RS.exists_homotopy_range_subset_of_convex` (affine rel-endpoint homotopy inside a convex set).
* **The central predicate** (`Path/LocalPrimitive.lean`): `RS.IsPrimitiveAlongMap K η F s` — near
  every `a ∈ s`, `F` factors as `g ∘ e ∘ K` for a maximal-atlas chart `e` at `K a` and a planar
  local primitive `g` of `coeffIn e η`. Core API: `.mono`, `.add_const`, `.congr`, `.congr_map`,
  `.continuousOn`, `.comp` (restriction along a continuous reparametrization of the parameter
  space), `.rechart` (re-chart the local data; the workhorse), `.sub_eq_sub` (uniqueness up to a
  constant on a preconnected parameter set), `.glue` (junction gluing along a preconnected
  overlap), `RS.isPrimitiveAlongMap_of_ball` (constant-chart primitive on a set mapped into one
  chart-ball — the reusable "cell primitive" atom).
* **Chart chains** (`Path/Chain.lean`): `RS.ChartChain γ` (a Lebesgue-number chart-ball
  subdivision of `[0,1]` adapted to `γ`), `RS.exists_chartChain`.
* **Existence, `pathIntegral`, path algebra, linearity** (`Path/Continuation.lean`):
  `RS.IsPrimitiveAlong γ η F := IsPrimitiveAlongMap γ.extend η F univ`,
  `RS.exists_isPrimitiveAlong` (chain-continuation existence), `RS.pathIntegral γ η`,
  `RS.IsPrimitiveAlong.pathIntegral_eq` (well-definedness: `pathIntegral γ η = F 1 - F 0` for
  *any* primitive `F`). Path algebra: `RS.pathIntegral_refl/symm/trans/reparam/cast`
  (reparametrization invariance needs no monotonicity). Linearity:
  `RS.pathIntegral_add/smul/zero_form`, `RS.pathIntegralₗ : Form1 X →ₗ[ℂ] ℂ`.
* **The bridge to honest integrals** (`Path/Bridge.lean`): `RS.pathIntegral_eq_intervalIntegral`
  (single-chart C¹ bridge to the classical `∫ coeff · (chart∘γ)'`; `circleIntegral`/
  `curveIntegral` specializations are owned downstream by residue-calculus/planar-stokes-atoms),
  `RS.pathIntegral_mdifferential` (continuous-path FTC: `∫_γ df = f(y) - f(x)`).
* **Homotopy invariance — the 2D grid** (`Path/HomotopySquare.lean`): `RS.gridK`, `RS.GridChain`,
  `RS.exists_gridChain`, `RS.exists_primitive_along_square` (primitive along a clamped continuous
  square, via mathlib's `exists_monotone_Icc_subset_open_cover_unitInterval_prod_self`).
  Consequences: `RS.pathIntegral_congr_homotopic` (rel-endpoint homotopy invariance),
  `RS.pathIntegralQ` (descent to `Path.Homotopic.Quotient`, with `.mk`/`.trans` lemmas),
  `RS.pathIntegral_congr_freeHomotopic` (free/basepoint-moving homotopy invariance of periods),
  `RS.pathIntegral_eq_of_simplyConnected`, `RS.period_eq_zero_of_homotopic_refl`.
* **Periods** (`Path/Periods.lean`): `RS.period γ η := pathIntegral γ η` on based loops
  `Path x x`, with `RS.period_trans/symm/refl/congr_homotopic/conj` (basepoint-independence along
  a connecting path) and `RS.periodVector` (w.r.t. a `Module.Basis` of `Form1 X`) with its
  `_trans/_symm/_refl` lemmas — the exact ingredients `jacobian-construction`'s
  `AddSubgroup.closure (Set.range (periodVector b))` recipe needs (CC9; the period subgroup
  itself is *not* defined here).
* **Loop perturbation off a finite set** (`Path/Perturb.lean`): `RS.nonempty_open_diff_finite`,
  `RS.exists_homotopic_avoiding_of_ball` (single-chart-ball base case), and the general
  multi-chart statements `RS.exists_homotopic_avoiding` / `RS.Loop.exists_homotopic_avoiding` —
  a path (loop) with endpoints (basepoint) off a finite set `S` is homotopic rel endpoints to
  one whose range avoids `S`. Proved by downward induction along a `ChartChain` with fresh
  breakpoints inserted off `S` in chart-ball overlaps and the truncation-splitting
  reparametrization homotopy (design risk R4, discharged).

No `T2Space`/`CompactSpace`/`ConnectedSpace` anywhere in this unit (compactness of `[0,1]`/
`[0,1]²` does all the work). No dependency on `Jacobian.Surface` (the `chartAt`-chart trick in
the bridge/FTC lemma removes the only candidate dependency).
-/
