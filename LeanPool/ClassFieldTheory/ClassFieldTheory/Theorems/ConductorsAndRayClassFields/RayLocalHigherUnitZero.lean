/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic
/-!
# The zeroth local higher-unit group
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace ClassFieldTheory

universe u

open NumberField IsDedekindDomain

/-- At depth zero the local higher-unit group is the full group of
integral units, not the full multiplicative group of the local field. -/
theorem rayLocalHigherUnitGroup_zero
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    rayLocalHigherUnitGroup v 0 =
      (v.adicCompletionIntegers K).units := by
  change RayClass.localHigherUnitGroup v 0 =
    (v.adicCompletionIntegers K).units
  exact RayClass.localHigherUnitGroup_zero v

end ClassFieldTheory
