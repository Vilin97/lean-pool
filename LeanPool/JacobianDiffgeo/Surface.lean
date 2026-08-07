/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Surface.Bridges
import LeanPool.JacobianDiffgeo.Surface.RealSmooth
import LeanPool.JacobianDiffgeo.Surface.ChartedSpaceKit
import LeanPool.JacobianDiffgeo.Surface.Identity
import LeanPool.JacobianDiffgeo.Surface.InverseFunction

/-!
# surfaces-and-charts: foundation unit for Riemann surfaces (namespace `RS`)

API summary (see `docs/design/surfaces-and-charts.md`):

* **Bridges**: `contMDiffAt_iff_analyticAt` / `contMDiffAt_iff_contDiffAt_extChartAt`
  (`f : X → ℂ`, no side conditions), Banach-target `contMDiffAt_iff_analyticAt_comp`,
  two-chart `contMDiffAt_iff_analyticAt_writtenInExtChartAt` and the recentered
  `contMDiffAt_iff_analyticAt_inChartAt` (`f : X → Y`, with `ContinuousAt`), chart-invariance
  `contMDiffAt_iff_analyticAt_of_mem_source`, set version
  `contMDiffOn_iff_analyticOnNhd_of_subset_source`.
* **RealSmooth (CC7)**: `instance isManifoldRealOfComplex : IsManifold 𝓘(ℝ, ℂ) ω X` (hence
  every `n`, unlocking `exists_smoothPartitionOfUnity` on compact T2 surfaces); `rfl` facts
  `extChartAt_real_eq`, `writtenInExtChartAt_real_eq`; holomorphic ⇒ real-`C^n`
  (`contMDiff_real_of_holomorphic` and friends).
* **ChartedSpaceKit**: `chartedSpaceOfFamily`, `isManifold_of_analyticOn_transitions`,
  `isManifold_of_family` — build `ChartedSpace ℂ Z` + `IsManifold 𝓘(ℂ) ω Z` from a chart
  family (for projective-line and jacobian-construction).
* **Identity**: `eventually_eq_or_eventually_ne` (dichotomy), identity theorem
  `eq_of_frequently_eq` / `eq_of_eqOn_of_accPt`, isolated fibers
  `eventually_ne_of_not_const`, `isOpenMap_of_not_const`, `surjective_of_not_const`;
  also `map_extChartAt_nhdsNE` and the instance `(𝓝[≠] x).NeBot`.
* **InverseFunction**: holomorphic IFT `exists_openPartialHomeomorph_of_deriv_ne_zero`
  (+ `_of_mfderiv_ne_zero`, `mfderiv_ne_zero_iff_deriv_ne_zero`,
  `map_nhds_eq_of_deriv_ne_zero`).
-/
