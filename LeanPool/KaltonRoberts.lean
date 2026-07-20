/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

import LeanPool.KaltonRoberts.Defs
import LeanPool.KaltonRoberts.Numerical
import LeanPool.KaltonRoberts.Collections
import LeanPool.KaltonRoberts.Lemmas
import LeanPool.KaltonRoberts.Pipeline
import LeanPool.KaltonRoberts.PipelineEps
import LeanPool.KaltonRoberts.EpsilonRecombination
import LeanPool.KaltonRoberts.MainTheorem

/-!
# Halving the Kalton-Roberts upper bound

Source: arxiv:2606.06807, url:https://github.com/boonsuan/KaltonRoberts
Authors: Ho Boon Suan
Status: verified
Main declarations: `KaltonRoberts.KR_constant_lt`
Tags: functional-analysis, finitely-additive-measures, kalton-roberts
MSC: 46B20, 28A12, 05C35
-/
