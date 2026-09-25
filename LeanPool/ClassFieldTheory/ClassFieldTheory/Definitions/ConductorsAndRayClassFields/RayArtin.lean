/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
/-!
# The ray Artin map
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory.RayClassFieldRealization

universe u

/-- The Frobenius-normalized ray Artin map. -/
def rayArtin
    {K : Type u} [Field K] [NumberField K]
    {m : RayClassModulus K}
    (R : RayClassFieldRealization K m) :
    RayClassGroup m →* (R.extension ≃ₐ[K] R.extension) :=
  R.artinEquiv.toMonoidHom

end ClassFieldTheory.RayClassFieldRealization
