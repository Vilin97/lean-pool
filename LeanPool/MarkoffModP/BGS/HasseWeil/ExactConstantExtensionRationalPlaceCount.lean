/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZetaDegreeIndexOne
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneAffineHasseWeilFromZeta

/-!
# Rational-place count of an exact constant extension

The packaged exact constant-extension count at level one is definitionally
the complete rational-place count of the scalar-extended function field.
This small bridge keeps the instance choices used by the global splitting
formula explicit.
-/

namespace BGS.HasseWeil

noncomputable section

variable (C S N : Type*) [Field C] [Fintype C]
  [DecidableEq C] [DecidableEq (RatFunc C)]
  [Field S] [Fintype S]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
  [Field N] [Algebra (RatFunc C) N]
  [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]

local instance rationalCountBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance rationalCountBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The packaged level-one exact-extension count is the complete rational
place count of the extended function field. -/
theorem exactConstantExtensionClosedPlaceExtensionCount_one_eq_rationalPlaceCount
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) :
    exactConstantExtensionClosedPlaceExtensionCount C S N hExact 1 =
      (by
        let E := ExactConstantExtension C N S
        letI : Field E := exactConstantExtensionField C N S hExact
        letI : Algebra (RatFunc S) E :=
          ratFuncExactConstantExtensionAlgebra C S N hExact
        letI : SMul (RatFunc S) E := Algebra.toSMul
        letI : Module (RatFunc S) E := Algebra.toModule
        letI : FiniteDimensional (RatFunc S) E :=
          finiteDimensional_over_extendedRatFunc C S N hExact
        letI : Algebra.IsSeparable (RatFunc S) E :=
          isSeparable_over_extendedRatFunc C S N hExact
        letI : DecidableEq S := Classical.decEq S
        letI : DecidableEq (RatFunc S) := Classical.decEq (RatFunc S)
        exact finiteExtensionRationalPlaceCount S E) := by
  classical
  let E := ExactConstantExtension C N S
  let : Field E := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) E := Algebra.toSMul
  let : Module (RatFunc S) E := Algebra.toModule
  let : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S) E :=
    isSeparable_over_extendedRatFunc C S N hExact
  change exactConstantExtensionClosedPlaceExtensionCount
      C S N hExact 1 = finiteExtensionRationalPlaceCount S E
  rw [exactConstantExtensionClosedPlaceExtensionCount_eq_classical_decidableEq]
  exact finiteExtensionClosedPlaceExtensionCount_one_eq_rationalPlaceCount
    S E

end

end BGS.HasseWeil
