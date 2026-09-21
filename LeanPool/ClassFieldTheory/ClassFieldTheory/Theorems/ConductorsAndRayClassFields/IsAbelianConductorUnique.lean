/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
/-!
# Uniqueness of the conductor

A finite abelian extension has at most one modulus that characterizes exactly
the ray class fields containing it.
-/

namespace ClassFieldTheory

universe u v

/-- The least modulus characterized by ray-class-field containment is unique. -/
theorem IsAbelianConductor.unique
    {K : Type u} [Field K] [NumberField K]
    {L : Type v} [Field L] [NumberField L] [Algebra K L]
    {c d : RayClassModulus K}
    (hc : IsAbelianConductor K L c)
    (hd : IsAbelianConductor K L d) : c = d := by
  apply le_antisymm
  · exact (hc d).mp ((hd d).mpr le_rfl)
  · exact (hd c).mp ((hc c).mpr le_rfl)

end ClassFieldTheory
