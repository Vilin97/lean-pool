/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/

import LeanPool.SardMoreira.ContDiff
import LeanPool.SardMoreira.ContDiffMoreiraHolder
import LeanPool.SardMoreira.ContinuousMultilinearMap
import LeanPool.SardMoreira.Chart
import LeanPool.SardMoreira.ChartEstimates
import LeanPool.SardMoreira.ImplicitFunction
import LeanPool.SardMoreira.LebesgueDensity
import LeanPool.SardMoreira.LinearAlgebra
import LeanPool.SardMoreira.LocalEstimates
import LeanPool.SardMoreira.MainTheorem
import LeanPool.SardMoreira.MeasureBallSemicontinuous
import LeanPool.SardMoreira.MeasureComap
import LeanPool.SardMoreira.MeasureNNReal
import LeanPool.SardMoreira.NormedSpace
import LeanPool.SardMoreira.OuterMeasureDeriv
import LeanPool.SardMoreira.ToMathlib
import LeanPool.SardMoreira.Topology
import LeanPool.SardMoreira.UnifDoublingCover
import LeanPool.SardMoreira.Unused
import LeanPool.SardMoreira.UpperLowerSemicontinuous
import LeanPool.SardMoreira.WithRPowDist

/-!
# Moreira's version of Sard's theorem

Source: url:https://github.com/urkud/SardMoreira
Authors: Yury G. Kudryashov
Status: verified
Main declarations: `dimH_image_le_sardMoreiraBound_of_finrank_le`
Tags: analysis, measure-theory, sard-theorem, hausdorff-measure
MSC: 28A78, 58C25
-/

/-!
## Mathematical overview

Moreira's strengthening of Sard's theorem on the Hausdorff dimension
of the critical-value set of a sufficiently differentiable map.

## Main results

- `hausdorffMeasure_sardMoreiraBound_image_null_of_finrank_le` —
  Hausdorff measure vanishing for the image of a set whose derivative
  rank is bounded by `p`.
- `dimH_image_le_sardMoreiraBound_of_finrank_le` — the corresponding
  Hausdorff-dimension bound for critical-value images.
- `ContDiffMoreiraHolderAt` — the pointwise `C^{k+α}` predicate
  (function is `C^k` at a point and the `k`-th derivative is locally
  Hölder of exponent `α`).
- `WithRPowDist` — metric-space wrapper giving `dist x y ^ α` as the
  metric, used to apply Vitali covering arguments to product spaces
  with mixed scaling.
-/
