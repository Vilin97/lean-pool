/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Nets

/-!
# Nets usage examples
-/

namespace HighDimProb

example {α : Type*} [PseudoMetricSpace α] (s net : Set α) (ε : ℝ) :
    IsEpsilonNet s net ε =
      Metric.IsCover (epsilonRadius ε) s net :=
  rfl

end HighDimProb
