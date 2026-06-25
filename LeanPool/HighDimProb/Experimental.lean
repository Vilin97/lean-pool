/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Vector
import LeanPool.HighDimProb.Geometry
import LeanPool.HighDimProb.Concentration
import LeanPool.HighDimProb.Distributions
import LeanPool.HighDimProb.RandomMatrix
import LeanPool.HighDimProb.LimitTheorems
import LeanPool.HighDimProb.Process
import LeanPool.HighDimProb.SignalRecovery
import LeanPool.HighDimProb.Tactic

/-!
# Experimental HighDimProb modules

This aggregate exposes APIs that are useful for development and documentation
but are not yet part of the stable `import LeanPool.HighDimProb` surface.

Use this module when you want the current high-dimensional work-in-progress
surface:

* vector, geometry, process, limit-theorem, and signal-recovery scaffolds;
* scalar concentration branches that are still outside the stable root;
* random-matrix APIs whose mathematical boundary is still being refined.

The experimental boundary is especially important for theorem wrappers that
still carry proof-route assumptions such as explicit primitive hypotheses,
variance-proxy bounds, trace-MGF providers, CFC/Tropp assumptions, or
operator-norm bridge assumptions. Those declarations can be documented and
tested here while the assumptions are gradually removed or identified as the
right mathematical boundary.

Stable APIs should be imported through `HighDimProb`. Experimental APIs should
be imported through a focused branch, such as `HighDimProb.RandomMatrix`, or
through this aggregate when broad work-in-progress access is intended.
-/
