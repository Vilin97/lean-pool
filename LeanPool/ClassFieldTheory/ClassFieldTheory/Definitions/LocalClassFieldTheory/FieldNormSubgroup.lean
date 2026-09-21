/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormHom
/-!
# The subgroup of field norms
-/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The subgroup `N_{L/K}(Lˣ)` of nonzero field norms. -/
def fieldNormSubgroup
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    Subgroup Kˣ :=
  (fieldNormHom K L).range

end ClassFieldTheory
