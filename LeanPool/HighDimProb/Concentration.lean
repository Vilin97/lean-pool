/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Concentration.Basic
import LeanPool.HighDimProb.Concentration.Markov
import LeanPool.HighDimProb.Concentration.Chebyshev
import LeanPool.HighDimProb.Concentration.LayerCake
import LeanPool.HighDimProb.Concentration.OrliczToTail
import LeanPool.HighDimProb.Concentration.TailToOrlicz
import LeanPool.HighDimProb.Concentration.Implications
import LeanPool.HighDimProb.Concentration.MomentImplications
import LeanPool.HighDimProb.Concentration.MGF
import LeanPool.HighDimProb.Concentration.MaxScale
import LeanPool.HighDimProb.Concentration.SubGaussianSums
import LeanPool.HighDimProb.Concentration.SubExponentialSums
import LeanPool.HighDimProb.Concentration.Bernstein
import LeanPool.HighDimProb.Concentration.RademacherSums
import LeanPool.HighDimProb.Concentration.Hoeffding

/-!
# Concentration branch

Experimental aggregate for scalar tail concentration foundations.

Verified Wikipedia reference:
* Concentration inequality:
  https://en.wikipedia.org/wiki/Concentration_inequality
-/
