/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomVector

/-!
# Random vector usage examples
-/

namespace HighDimProb

example {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : RandomVector Ω n) (i : Fin n) (ω : Ω) :
    coordinate X i ω = X ω i :=
  rfl

end HighDimProb
