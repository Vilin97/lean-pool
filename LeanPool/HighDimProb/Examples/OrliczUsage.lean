/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Orlicz

/-!
# Orlicz usage examples
-/

namespace HighDimProb

example (p : ℕ) (x : ℝ) :
    psiPower p x = Real.exp (|x| ^ p) - 1 :=
  rfl

end HighDimProb
