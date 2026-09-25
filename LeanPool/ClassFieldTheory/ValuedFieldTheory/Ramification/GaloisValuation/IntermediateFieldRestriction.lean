/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Basic
/-!
# Restriction between normal intermediate fields

This module packages the canonical restriction map between two intermediate
fields in a common ambient extension without requiring callers to install the
auxiliary algebra and scalar-tower instances.
-/

@[expose] public section

noncomputable section

namespace RamificationTheory

universe u v

variable {K : Type u} {Omega : Type v}
  [Field K] [Field Omega] [Algebra K Omega]

/-- Restriction `Gal(F/K) → Gal(E/K)` for two intermediate fields `E ≤ F`
in one ambient extension. -/
noncomputable def intermediateFieldRestrictNormalHom
    (E F : IntermediateField K Omega) (hEF : E ≤ F) [Normal K E] :
    (F ≃ₐ[K] F) →* (E ≃ₐ[K] E) := by
  letI : Algebra E F :=
    RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  exact AlgEquiv.restrictNormalHom E

/-- Evaluation of the canonical intermediate-field restriction after both
sides are included in the common ambient field. -/
theorem intermediateFieldRestrictNormalHom_apply_val
    (E F : IntermediateField K Omega) (hEF : E ≤ F) [Normal K E]
    (sigma : F ≃ₐ[K] F) (x : E) :
    E.val (intermediateFieldRestrictNormalHom E F hEF sigma x) =
      F.val (sigma (IntermediateField.inclusion hEF x)) := by
  let : Algebra E F :=
    RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  have h := AlgEquiv.restrictNormal_commutes sigma E x
  exact congrArg F.val h

end RamificationTheory
