/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Examples.RandomMatrix.AttentionFeatureGramOperatorNormUsage
import LeanPool.HighDimProb.Examples.RandomMatrix.EmpiricalFisherOperatorNormUsage
import LeanPool.HighDimProb.Examples.RandomMatrix.LoRAAdapterSubspaceCovarianceUsage
import LeanPool.HighDimProb.Examples.RandomMatrix.NTKGramUsage
import LeanPool.HighDimProb.Examples.RandomMatrix.NaturalTroppPipelineUsage
import LeanPool.HighDimProb.Examples.RandomMatrix.RandomFeatureKernelUsage
import LeanPool.HighDimProb.Examples.RandomMatrix.RankOneMatrixBernsteinPipelineUsage
import LeanPool.HighDimProb.Examples.RandomMatrix.SampleCovarianceTailUsage

/-!
# RandomMatrix statement routes

This example index is intentionally thin. It adds no mathematical facts and no
new assumptions. It groups existing example-level statements by theorem family:
sample covariance, rank-one covariance/Gram sums, operator-norm tails, TraceExp
bookkeeping, and hardbone statement targets.

The focused files below contain the full assumptions and theorem statements.
This file only keeps the route names discoverable and build-checked.
-/

namespace HighDimProb.Examples.RandomMatrix.StatementRoutes

open HighDimProb.Examples.RandomMatrix.SampleCovarianceTailUsage
open HighDimProb.Examples.RandomMatrix.EmpiricalFisherOperatorNormUsage
open HighDimProb.Examples.RandomMatrix.RandomFeatureKernelUsage
open HighDimProb.Examples.RandomMatrix.NTKGramUsage
open HighDimProb.Examples.RandomMatrix.RankOneMatrixBernsteinPipelineUsage
open HighDimProb.Examples.RandomMatrix.AttentionFeatureGramOperatorNormUsage
open HighDimProb.Examples.RandomMatrix.LoRAAdapterSubspaceCovarianceUsage
open HighDimProb.Examples.RandomMatrix.NaturalTroppPipelineUsage

/-!
## Sample covariance

This section indexes bounded-row covariance tail routes. The example-level
bundles expose row-norm, variance-proxy, positive-side, and negative-side
obligations without creating another core sample-covariance API.
-/

/-!
## Rank-one covariance and Gram routes

These examples show how rank-one feature or gradient covariance summands feed
the shared Matrix Bernstein wrappers. Example-specific names stay in examples;
reusable matrix facts stay in core.
-/

/-!
## Structured covariance operator-norm routes

These wrappers use the same core positive- and negative-side Matrix Bernstein
assumptions. The example-specific vocabulary remains in examples until repeated
proof obligations justify a core abstraction.
-/

/-!
## Natural TraceExp/Tropp bookkeeping

These examples index prefix/state bookkeeping around the lower-level TraceExp
statements. They do not prove Lieb, Golden-Thompson, CFC, or full Matrix
Bernstein.
-/

end HighDimProb.Examples.RandomMatrix.StatementRoutes
