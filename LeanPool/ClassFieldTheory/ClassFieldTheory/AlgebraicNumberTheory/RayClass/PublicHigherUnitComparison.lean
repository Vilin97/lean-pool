/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic
/-!
# Comparison of public and idelic higher-unit groups

The reader-facing higher-unit group agrees with the group used in the
existing ray-class and idelic implementation. Keep this definitional
comparison at the boundary between the two APIs.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

/-- The public local higher-unit group is the same subgroup as the one used
by the existing ray-class implementation. -/
theorem rayLocalHigherUnitGroup_eq_rayClass
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    rayLocalHigherUnitGroup v n = RayClass.localHigherUnitGroup v n := by
  rfl

end ClassFieldTheory
