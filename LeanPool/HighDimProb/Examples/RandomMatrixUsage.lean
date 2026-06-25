/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.RandomMatrix

/-!
# Random matrix usage examples
-/

namespace HighDimProb

example {Omega : Type*} [MeasurableSpace Omega] {m n : Nat}
    (A : RandomMatrix Omega m n) (i : Fin m) (j : Fin n) (omega : Omega) :
    matrixEntry A i j omega = A omega i j :=
  rfl

end HighDimProb
