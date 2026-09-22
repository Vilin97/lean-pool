/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
import Mathlib.RingTheory.Norm.Basic
/-!
# Transport of finite-extension norm subgroups

Compatible field equivalences carry the actual group of field norms to the
actual group of field norms.  This is the norm comparison needed when finite
local class-field theory is transported to a small representative.
-/

noncomputable section

namespace ClassFieldTheory

universe u v w x

variable {F : Type u} {M : Type v} {F' : Type w} {M' : Type x}
  [Field F] [Field M] [Field F'] [Field M']
  [Algebra F M] [Algebra F' M']
  [FiniteDimensional F M] [FiniteDimensional F' M']

omit [FiniteDimensional F M] [FiniteDimensional F' M'] in
/-- The field-norm homomorphisms commute with compatible field equivalences. -/
theorem fieldNormHom_map_ringEquiv
    (eF : F ≃+* F') (eM : M ≃+* M')
    (he : (algebraMap F' M').comp eF.toRingHom =
      eM.toRingHom.comp (algebraMap F M))
    (y : Mˣ) :
    (Units.mapEquiv eF.toMulEquiv) (fieldNormHom F M y) =
      fieldNormHom F' M' (Units.mapEquiv eM.toMulEquiv y) := by
  apply Units.ext
  change eF (Algebra.norm F (y : M)) =
    Algebra.norm F' (eM (y : M))
  rw [Algebra.norm_eq_of_equiv_equiv eF eM he]
  exact eF.apply_symm_apply _

/-- The image of a field-norm subgroup under a base-field equivalence is
exactly the norm subgroup of the transported extension. -/
theorem fieldNormSubgroup_map_ringEquiv
    (eF : F ≃+* F') (eM : M ≃+* M')
    (he : (algebraMap F' M').comp eF.toRingHom =
      eM.toRingHom.comp (algebraMap F M)) :
    (fieldNormSubgroup F M).map
        (Units.mapEquiv eF.toMulEquiv).toMonoidHom =
      fieldNormSubgroup F' M' := by
  ext z
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨Units.mapEquiv eM.toMulEquiv x,
      (fieldNormHom_map_ringEquiv eF eM he x).symm⟩
  · rintro ⟨x, rfl⟩
    let y := (Units.mapEquiv eM.toMulEquiv).symm x
    refine ⟨fieldNormHom F M y, ⟨y, rfl⟩, ?_⟩
    change (Units.mapEquiv eF.toMulEquiv) (fieldNormHom F M y) =
      fieldNormHom F' M' x
    simpa only [y, MulEquiv.apply_symm_apply] using
      fieldNormHom_map_ringEquiv eF eM he y

end ClassFieldTheory
