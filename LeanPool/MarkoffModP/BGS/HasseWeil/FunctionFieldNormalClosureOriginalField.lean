/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionPlaceAlgEquiv
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionClosedPlaceAlgEquiv
import LeanPool.MarkoffModP.BGS.HasseWeil.FunctionFieldNormalClosure

/-!
# The original field inside its chosen normal closure

The chosen embedding of a finite separable function field into its normal
closure has a field range.  This file names that intermediate field, records
the tautological algebra equivalence with the original presentation, and
transports exact constants and rational-place counts across it.
-/

namespace BGS.HasseWeil

noncomputable section

variable (K F : Type*) [Field K] [Field F]
  [Algebra (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- The embedded copy of the original function field inside its chosen
normal closure. -/
abbrev FunctionFieldNormalClosureOriginalField :
    IntermediateField (RatFunc K) (FunctionFieldNormalClosure K F) :=
  (functionFieldToNormalClosure K F).fieldRange

/-- The original presentation is equivalent, over `K(X)`, to its embedded
copy in the normal closure. -/
noncomputable def functionFieldNormalClosureOriginalFieldAlgEquiv :
    F ≃ₐ[RatFunc K] FunctionFieldNormalClosureOriginalField K F :=
  (functionFieldToNormalClosure K F).equivFieldRange

/-- The normal closure is finite over the embedded original field. -/
noncomputable instance
    functionFieldNormalClosure_finiteDimensional_over_originalField :
    FiniteDimensional (FunctionFieldNormalClosureOriginalField K F)
      (FunctionFieldNormalClosure K F) := by
  exact Module.Finite.right (RatFunc K)
    (FunctionFieldNormalClosureOriginalField K F)
    (FunctionFieldNormalClosure K F)

/-- The normal closure remains Galois after replacing the rational base by
the embedded original field. -/
noncomputable instance functionFieldNormalClosure_isGalois_over_originalField :
    IsGalois (FunctionFieldNormalClosureOriginalField K F)
      (FunctionFieldNormalClosure K F) :=
  IsGalois.tower_top_of_isGalois (RatFunc K)
    (FunctionFieldNormalClosureOriginalField K F)
    (FunctionFieldNormalClosure K F)

section Constants

variable [Algebra K F] [IsScalarTower K (RatFunc K) F]

local instance originalFieldImageConstantAlgebra :
    Algebra K (FunctionFieldNormalClosureOriginalField K F) :=
  RingHom.toAlgebra
    ((algebraMap (RatFunc K)
      (FunctionFieldNormalClosureOriginalField K F)).comp
        (algebraMap K (RatFunc K)))

local instance originalFieldImageConstantTower :
    IsScalarTower K (RatFunc K)
      (FunctionFieldNormalClosureOriginalField K F) :=
  IsScalarTower.of_algebraMap_eq'
    (R := K) (S := RatFunc K)
      (A := FunctionFieldNormalClosureOriginalField K F) rfl

/-- Exactness of the constant field is unchanged when the original function
field is replaced by its embedded image in the normal closure. -/
theorem functionFieldNormalClosureOriginalField_algebraicClosure_eq_bot
    (hExact : algebraicClosure K F = (⊥ : IntermediateField K F)) :
    algebraicClosure K (FunctionFieldNormalClosureOriginalField K F) =
      (⊥ : IntermediateField K
        (FunctionFieldNormalClosureOriginalField K F)) := by
  let e : F ≃ₐ[K] FunctionFieldNormalClosureOriginalField K F :=
    (functionFieldNormalClosureOriginalFieldAlgEquiv K F).restrictScalars K
  have hmap := algebraicClosure.map_eq_of_algEquiv e
  rw [hExact] at hmap
  simpa only [IntermediateField.map_bot] using hmap.symm

end Constants

section Places

variable [DecidableEq K] [DecidableEq (RatFunc K)]

/-- The original presentation and its embedded normal-closure image have the
same complete rational-place count. -/
theorem functionFieldNormalClosureOriginalField_rationalPlaceCount_eq :
    finiteExtensionRationalPlaceCount K F =
      finiteExtensionRationalPlaceCount K
        (FunctionFieldNormalClosureOriginalField K F) :=
  finiteExtensionRationalPlaceCount_eq_of_algEquiv K F
    (FunctionFieldNormalClosureOriginalField K F)
    (functionFieldNormalClosureOriginalFieldAlgEquiv K F)

end Places

section ClosedPlaces

variable [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)]

/-- The entire closed-place extension-count sequence is unchanged when the
original presentation is replaced by its image in the normal closure. -/
theorem
    functionFieldNormalClosureOriginalField_closedPlaceExtensionCount_eq
    (r : ℕ) :
    finiteExtensionClosedPlaceExtensionCount K F r =
      finiteExtensionClosedPlaceExtensionCount K
        (FunctionFieldNormalClosureOriginalField K F) r :=
  finiteExtensionClosedPlaceExtensionCount_eq_of_algEquiv K F
    (FunctionFieldNormalClosureOriginalField K F)
    (functionFieldNormalClosureOriginalFieldAlgEquiv K F) r

end ClosedPlaces

end

end BGS.HasseWeil
