/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.ProjectiveLine.Inversion
import LeanPool.JacobianDiffgeo.ProjectiveLine.Charts
import LeanPool.JacobianDiffgeo.ProjectiveLine.Holomorphy
import LeanPool.JacobianDiffgeo.ProjectiveLine.Sphere
import LeanPool.JacobianDiffgeo.ProjectiveLine.GenusZero

/-!
# projective-line (CC5): the Riemann sphere `ℙ¹ := OnePoint ℂ`

API summary (see `docs/design/projective-line.md`). Everything lives in `namespace RS.P1` unless
noted; `open scoped RS.P1` for the notation `ℙ¹ := OnePoint ℂ` (doc-only, no challenge statement
needs it).

* **Inversion** (`Inversion.lean`): `inversion : OnePoint ℂ → OnePoint ℂ` (`z ↦ z⁻¹`, `∞ ↦ 0`,
  `0 ↦ ∞`), `inversion_involutive`, `inversion_eq_infty_iff`, `continuous_inversion`,
  `inversionHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ`.
* **Charts** (`Charts.lean`): `coeChart`/`invChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ` (junk
  `coeChart ∞ = 0`, `invChart` unconditionally `↑z ↦ z⁻¹`); `instChartedSpace : ChartedSpace ℂ
  (OnePoint ℂ)` and `instIsManifold : IsManifold 𝓘(ℂ) ω (OnePoint ℂ)`; simp facts `chartAt_coe`,
  `chartAt_infty`, `atlas_eq`, `coeChart_mem_maximalAtlas`/`invChart_mem_maximalAtlas`; basepoints
  via `Nontrivial (OnePoint ℂ)`; `CompactSpace`/`T2Space`/`ConnectedSpace`/no-isolated-points
  instances (all `inferInstance`, guarded by `example`s).
* **Holomorphy transfer kit** (`Holomorphy.lean`, standing variable `{Z} [ChartedSpace ℂ Z]
  [IsManifold 𝓘(ℂ) ω Z]`, no compactness/connectedness): `contMDiff_coe` (`ℂ → ℙ¹` holomorphic),
  `ContMDiffAt.onePointCoe`/`ContMDiff.onePointCoe` (no-poles lift), the chart-iff lemmas
  `contMDiffAt_iff_analyticAt_of_ne_infty`/`_of_eq_infty`, the **pole constructor**
  `contMDiffAt_of_pole` (planar; the pre-`ℳ X` atom for meromorphic-and-divisors), the converse
  `meromorphicAt_coeChart_comp`, and `contMDiff_inversion`/`inversionDiffeomorph` (inversion is a
  biholomorphic involution).
* **Sphere** (`Sphere.lean`): `homeoSphere : OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ
  (Fin 3)) 1` — the exact sphere model used by the challenge's `genus_eq_zero_iff_homeo`.
* **Genus zero** (`GenusZero.lean`): `form1_eq_zero`, `Subsingleton (RS.Form1 (OnePoint ℂ))`,
  `finrank_form1`, and the root-level `RS.genus_onePoint : genus (OnePoint ℂ) = 0`.

Downstream consumers: genus-zero-headline (`homeoSphere` + `RS.genus_onePoint` + the standing
instances), mapping-degree/meromorphic-trace (the chart API + `inversionDiffeomorph` +
basepoints), meromorphic-and-divisors (`contMDiffAt_of_pole` + `ContMDiffAt.onePointCoe` as the
two atoms for the future `ℳ.toP1` bridge, junk-value contract `coeChart ∞ = 0`).
-/

/-- The Riemann sphere, as the one-point compactification of `ℂ`. -/
scoped[RS.P1] notation "ℙ¹" => OnePoint ℂ
