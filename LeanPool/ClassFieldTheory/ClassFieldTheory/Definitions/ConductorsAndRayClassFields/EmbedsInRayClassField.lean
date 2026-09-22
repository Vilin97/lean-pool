/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
/-!
# Embedding into a ray class field
-/

namespace ClassFieldTheory

universe u v

/-- A finite extension embeds into a ray class field for `m`.  The existential
formulation avoids making a global choice of ray class field. -/
def EmbedsInRayClassField
    (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [Algebra K L]
    (m : RayClassModulus K) : Prop :=
  ∃ R : RayClassFieldRealization K m,
    Nonempty (L →ₐ[K] R.extension)

end ClassFieldTheory
