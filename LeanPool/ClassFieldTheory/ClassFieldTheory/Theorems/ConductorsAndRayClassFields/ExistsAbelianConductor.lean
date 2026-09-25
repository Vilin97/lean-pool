/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.EmbedsInRayClassFieldIffConductorLe
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
/-!
# Existence of the abelian conductor

The conductor of a finite abelian extension is the least modulus whose ray
class field contains that extension. The older theorem name
`embedsInRayClassField_iff_conductor_le` remains available for compatibility;
its conclusion is an existence statement, so this name reflects its type.
-/

@[expose] public section

namespace ClassFieldTheory

/-- A finite abelian extension of number fields has a conductor. -/
theorem exists_abelianConductor
    (K : Type) [Field K] [NumberField K]
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] :
    ∃ c : RayClassModulus K, IsAbelianConductor K L c :=
  embedsInRayClassField_iff_conductor_le K L

end ClassFieldTheory
