/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedField
/-!
# The completed theta-intertwining theorem: the canonical base algebra on the fixed field

This light leaf names the base algebra already determined by the completed
Frobenius action.  Naming it prevents repeated fallback searches through
generic scalar-action instances in later norm calculations.
-/

noncomputable section


open scoped LaurentSeries PowerSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

noncomputable local instance equalCharacteristicFixedFieldAlgebraBaseAlgebra
    (F : LocalField K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedFrobeniusFixedBaseAlgebra F

noncomputable local instance equalCharacteristicFixedFieldAlgebraLevelAlgebra
    (F : LocalField K) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedFrobeniusFixedLevelAlgebra F n

local instance equalCharacteristicFixedFieldAlgebraScalarTower
    (F : LocalField K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The completed Frobenius fixed field, viewed only as a subring of the
completed level.  This lightweight projection lets ring-homomorphism
consumers avoid reconstructing the ambient Laurent-base algebra. -/
noncomputable def equalCharacteristicCompletedFrobeniusFixedFieldSubring
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Subring (equalCharacteristicCompletedLevelField F n) :=
  (equalCharacteristicCompletedFrobeniusFixedField F a n).toSubring

/-- The canonical `k((T))`-algebra structure on the completed theta-intertwining theorem fixed field. -/
@[reducible]
noncomputable def equalCharacteristicCompletedFrobeniusFixedFieldAlgebra
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedFrobeniusFixedField F a n) :=
  Subalgebra.algebra
    (equalCharacteristicCompletedFrobeniusFixedField F a n).toSubalgebra

/-- The scalar action induced by the canonical `k((T))`-algebra structure on
the completed Frobenius fixed field.  Naming it lets downstream files reuse
the same structure without asking typeclass search to unfold the fixed field. -/
@[reducible]
noncomputable def equalCharacteristicCompletedFrobeniusFixedFieldSMul
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    SMul F.residueField⸨X⸩
      (equalCharacteristicCompletedFrobeniusFixedField F a n) :=
  @Algebra.toSMul _ _ _ _
    (equalCharacteristicCompletedFrobeniusFixedFieldAlgebra F a n)

/-- The module structure induced by the canonical `k((T))`-algebra structure
on the completed Frobenius fixed field. -/
@[reducible]
noncomputable def equalCharacteristicCompletedFrobeniusFixedFieldModule
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Module F.residueField⸨X⸩
      (equalCharacteristicCompletedFrobeniusFixedField F a n) :=
  @Algebra.toModule _ _ _ _
    (equalCharacteristicCompletedFrobeniusFixedFieldAlgebra F a n)

end EqualCharacteristic
end LubinTate
