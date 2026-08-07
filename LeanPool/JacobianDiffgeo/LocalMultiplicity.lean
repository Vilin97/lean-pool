/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.LocalMultiplicity.KthRoot
import LeanPool.JacobianDiffgeo.LocalMultiplicity.PlanarNormalForm
import LeanPool.JacobianDiffgeo.LocalMultiplicity.ChartBridge
import LeanPool.JacobianDiffgeo.LocalMultiplicity.Multiplicity
import LeanPool.JacobianDiffgeo.LocalMultiplicity.AdaptedCharts
import LeanPool.JacobianDiffgeo.LocalMultiplicity.Composition

/-!
# local-multiplicity (CC4): local multiplicity of holomorphic maps (namespace `RS`)

API summary (see `docs/design/local-multiplicity.md`):

* **Definition**: `multiplicityENat F x : ℕ∞` is `analyticOrderAt (inChartAt F x) (chartAt ℂ x x)`
  (`⊤` iff holomorphic and locally constant, junk `0` if not holomorphic);
  `multiplicity F x : ℕ` is its `toNat`; `IsRamifiedAt F x ↔ 2 ≤ multiplicity F x`.
* **Basic API** (`Multiplicity.lean`): junk lemmas, `one_le_multiplicity`, `natCast_multiplicity`,
  chart invariance `analyticOrderAt_charts_eq_multiplicityENat`, isolated fibres
  (`eventually_ne`, `exists_nhds_fiber_eq_singleton`), CC3 bridges
  `meromorphicOrderAt_chart_sub` / `meromorphicOrderAt_chart_of_eq_zero`.
* **Adapted charts** (Forster 2.1): `AdaptedChartsAt F x k` (centered maximal-atlas charts with
  round-ball targets in which `F` is `z ↦ z ^ k`); existence `exists_adaptedChartsAt` with
  `k = multiplicity F x` and source shrinkable into any neighborhood; `image_source`,
  `eqOn_symm`, `multiplicity_eq`.
* **Composition**: `multiplicity(ENat)_comp` (`mult (G ∘ F) x = mult G (F x) * mult F x`),
  `multiplicity(ENat)_comp_chart_symm`; `multiplicity_eq_one_iff_injOn`,
  `exists_openPartialHomeomorph_of_multiplicity_eq_one`, `isRamifiedAt_iff_not_injOn`,
  `eventually_multiplicity_eq_one` (ramification is isolated).
* **Planar layer**: `AnalyticAt.exists_pow_eq` (k-th root), `AnalyticAt.exists_normal_form`
  (`f = f z₀ + φ ^ k`, also packaged), `analyticOrderAt_left_comp_sub`, `image_pow_ball`;
  `ChartBridge.lean` has `inChartAt`, transitions (`analyticAt_transition`,
  `trans_mem_maximalAtlas`, `mem_contDiffGroupoid_iff_analytic`, `map_nhdsNE`) and a local
  `LMCompat` copy of the CC7 holomorphy bridge (canonical version: `Jacobian.Surface`).
-/
