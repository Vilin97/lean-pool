/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import LeanPool.SardMoreira.ContDiff
public import LeanPool.SardMoreira.ContDiffMoreiraHolder
public import LeanPool.SardMoreira.ContinuousMultilinearMap
public import LeanPool.SardMoreira.Chart
public import LeanPool.SardMoreira.ChartEstimates
public import LeanPool.SardMoreira.ImplicitFunction
public import LeanPool.SardMoreira.LebesgueDensity
public import LeanPool.SardMoreira.LinearAlgebra
public import LeanPool.SardMoreira.LocalEstimates
public import LeanPool.SardMoreira.MainTheorem
public import LeanPool.SardMoreira.MeasureBallSemicontinuous
public import LeanPool.SardMoreira.MeasureComap
public import LeanPool.SardMoreira.MeasureNNReal
public import LeanPool.SardMoreira.NormedSpace
public import LeanPool.SardMoreira.OuterMeasureDeriv
public import LeanPool.SardMoreira.ToMathlib
public import LeanPool.SardMoreira.Topology
public import LeanPool.SardMoreira.UnifDoublingCover
public import LeanPool.SardMoreira.Unused
public import LeanPool.SardMoreira.UpperLowerSemicontinuous
public import LeanPool.SardMoreira.WithRPowDist

/-!
# Moreira's version of Sard's theorem

Source: doi:10.5565/PUBLMAT_45101_06
Authors: Yury G. Kudryashov
Status: verified
Main declarations: `dimH_image_le_sardMoreiraBound_of_finrank_le`
Tags: analysis, measure-theory, sard-theorem, hausdorff-measure
MSC: 28A78, 58C25
-/

@[expose] public section

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
