/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.RationalComplexification
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import Mathlib.FieldTheory.Galois.Abelian
/-!
# Complexification of a number field

This module forms the actual compositum with the rational fourth-root field
and proves that restriction to the rational cyclotomic factor is faithful.
-/

@[expose] public section

open scoped IsMulCommutative
open AlgebraicNumberTheory NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance]
  rationalComplexificationCyclotomicField_isAbelianGalois

open scoped Classical in
private def rationalComplexificationAmbientField :
    IntermediateField ℚ (SeparableClosure ℚ) := by
  letI : Algebra ℚ KummerTheory.rationalCyclotomicField :=
    DivisionRing.toRatAlgebra
  exact IntermediateField.lift rationalComplexificationCyclotomicField

open scoped Classical in
private noncomputable def rationalComplexificationAmbientEquiv :
    rationalComplexificationCyclotomicField ≃ₐ[ℚ]
      rationalComplexificationAmbientField := by
  letI : Algebra ℚ KummerTheory.rationalCyclotomicField :=
    DivisionRing.toRatAlgebra
  exact IntermediateField.liftAlgEquiv
    rationalComplexificationCyclotomicField

variable (F : Type*) [Field F] [NumberField F]

open scoped Classical in
/-- The actual compositum of the chosen copy of `F` with the rational
complexification field inside `SeparableClosure ℚ`. -/
def numberFieldComplexification :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  numberFieldInRationalSeparableClosure F ⊔
    rationalComplexificationAmbientField

open scoped Classical in
/-- The complexification inside the rational separable closure carries its rational algebra
structure. -/
@[reducible]
noncomputable local instance
    numberFieldComplexificationRationalAlgebra :
    Algebra ℚ (numberFieldComplexification F) :=
  (numberFieldComplexification F).algebra'

attribute [local instance] numberFieldComplexificationRationalAlgebra

open scoped Classical in
noncomputable instance numberFieldComplexification_finiteDimensional :
    FiniteDimensional ℚ (numberFieldComplexification F) := by
  let :
      FiniteDimensional ℚ
        rationalComplexificationAmbientField :=
    rationalComplexificationAmbientEquiv.toLinearEquiv.finiteDimensional
  exact
    IntermediateField.finiteDimensional_sup
      (numberFieldInRationalSeparableClosure F)
      rationalComplexificationAmbientField

open scoped Classical in
noncomputable instance numberFieldComplexification_numberField :
    NumberField (numberFieldComplexification F) :=
  NumberField.of_module_finite ℚ (numberFieldComplexification F)

open scoped Classical in
/-- The chosen embedding of `F` into its actual complexification. -/
noncomputable def numberFieldComplexificationEmbedding :
    F →ₐ[ℚ] numberFieldComplexification F :=
  (numberFieldSeparableClosureEmbedding F).codRestrict
    (numberFieldComplexification F).toSubalgebra
    (fun x =>
      (show numberFieldInRationalSeparableClosure F ≤
          numberFieldComplexification F from le_sup_left)
        (show numberFieldSeparableClosureEmbedding F x ∈
            numberFieldInRationalSeparableClosure F from
          (AlgHom.mem_fieldRange).mpr ⟨x, rfl⟩))

open scoped Classical in
/-- The rational fourth-root cyclotomic field embedded into the
complexification of `F`. -/
noncomputable def rationalComplexificationCompositumEmbedding :
    rationalComplexificationCyclotomicField →ₐ[ℚ]
      numberFieldComplexification F :=
  (IntermediateField.inclusion le_sup_right).comp
    rationalComplexificationAmbientEquiv.toAlgHom

open scoped Classical in
noncomputable instance numberFieldComplexificationAlgebra :
    Algebra F (numberFieldComplexification F) :=
  (numberFieldComplexificationEmbedding F).toRingHom.toAlgebra

open scoped Classical in
/-- The scalar action belonging to the chosen embedding of `F` into its
complexification.  Naming it prevents typeclass search from finding a
definitionally different action through the ambient intermediate field. -/
noncomputable instance numberFieldComplexificationSmul :
    SMul F (numberFieldComplexification F) :=
  (numberFieldComplexificationAlgebra F).toSMul

open scoped Classical in
noncomputable instance rationalComplexificationCompositumAlgebra :
    Algebra rationalComplexificationCyclotomicField
      (numberFieldComplexification F) :=
  (rationalComplexificationCompositumEmbedding F).toRingHom.toAlgebra

open scoped Classical in
/-- The scalar action induced by the actual fourth-root-field embedding.
Declaring it directly prevents instance search from exploring unrelated
intermediate-field algebra structures. -/
noncomputable instance rationalComplexificationCompositumSmul :
    SMul rationalComplexificationCyclotomicField
      (numberFieldComplexification F) :=
  (rationalComplexificationCompositumAlgebra F).toSMul

open scoped Classical in
instance numberFieldComplexification_scalarTower :
    IsScalarTower ℚ F (numberFieldComplexification F) :=
  IsScalarTower.of_algebraMap_eq'
    (numberFieldComplexificationEmbedding F).comp_algebraMap.symm

open scoped Classical in
instance rationalComplexificationCompositum_scalarTower :
    IsScalarTower ℚ rationalComplexificationCyclotomicField
      (numberFieldComplexification F) :=
  IsScalarTower.of_algebraMap_eq'
    (rationalComplexificationCompositumEmbedding F).comp_algebraMap.symm

open scoped Classical in
noncomputable instance
    numberFieldComplexification_finiteDimensional_over_base :
    FiniteDimensional F (numberFieldComplexification F) :=
  FiniteDimensional.right ℚ F (numberFieldComplexification F)

open scoped Classical in
/-- Restriction from `F(μ₄)/F` to the rational fourth-root
cyclotomic factor. -/
noncomputable def numberFieldComplexificationRestriction :
    Gal(numberFieldComplexification F/F) →*
      Gal(rationalComplexificationCyclotomicField/ℚ) :=
  IntermediateField.restrictRestrictAlgEquivMapHom
    ℚ rationalComplexificationCyclotomicField F
      (numberFieldComplexification F)

open scoped Classical in
private def numberFieldComplexificationBaseLayer :
    IntermediateField ℚ (numberFieldComplexification F) :=
  (numberFieldInRationalSeparableClosure F).restrict
    (show numberFieldInRationalSeparableClosure F ≤
        numberFieldComplexification F from
      le_sup_left)

open scoped Classical in
private def numberFieldComplexificationCyclotomicLayer :
    IntermediateField ℚ (numberFieldComplexification F) :=
  rationalComplexificationAmbientField.restrict
    (show
      rationalComplexificationAmbientField ≤
          numberFieldComplexification F from
      le_sup_right)

open scoped Classical in
/-- The base layer inside the complexification carries its rational algebra structure. -/
@[reducible]
noncomputable local instance
    numberFieldComplexificationBaseLayerRationalAlgebra :
    Algebra ℚ (numberFieldComplexificationBaseLayer F) :=
  (numberFieldComplexificationBaseLayer F).algebra'

attribute [local instance] numberFieldComplexificationBaseLayerRationalAlgebra

open scoped Classical in
/-- The cyclotomic layer inside the complexification carries its rational algebra structure. -/
@[reducible]
noncomputable local instance
    numberFieldComplexificationCyclotomicLayerRationalAlgebra :
    Algebra ℚ (numberFieldComplexificationCyclotomicLayer F) :=
  (numberFieldComplexificationCyclotomicLayer F).algebra'

attribute [local instance] numberFieldComplexificationCyclotomicLayerRationalAlgebra

open scoped Classical in
private noncomputable def numberFieldComplexificationBaseEquiv :
    F ≃ₐ[ℚ] numberFieldComplexificationBaseLayer F :=
  (numberFieldSeparableClosureEmbedding F).equivFieldRange.trans
    (IntermediateField.restrictAlgEquiv le_sup_left)

open scoped Classical in
private noncomputable def numberFieldComplexificationCyclotomicEquiv :
    rationalComplexificationCyclotomicField ≃ₐ[ℚ]
      numberFieldComplexificationCyclotomicLayer F :=
  rationalComplexificationAmbientEquiv.trans
    (IntermediateField.restrictAlgEquiv le_sup_right)

open scoped Classical in
private noncomputable local instance
    numberFieldComplexificationCyclotomicLayer_isAbelianGalois :
    IsAbelianGalois ℚ
      (numberFieldComplexificationCyclotomicLayer F) :=
  IsAbelianGalois.of_algHom
    (numberFieldComplexificationCyclotomicEquiv F).symm.toAlgHom

attribute [local instance] numberFieldComplexificationCyclotomicLayer_isAbelianGalois

open scoped Classical in
private noncomputable local instance
    numberFieldComplexificationCyclotomicLayer_isGalois :
    IsGalois ℚ (numberFieldComplexificationCyclotomicLayer F) :=
  (numberFieldComplexificationCyclotomicLayer_isAbelianGalois
    F).toIsGalois

attribute [local instance] numberFieldComplexificationCyclotomicLayer_isGalois

open scoped Classical in
private noncomputable local instance
    numberFieldComplexificationCyclotomicLayer_normal :
    Normal ℚ (numberFieldComplexificationCyclotomicLayer F) :=
  (numberFieldComplexificationCyclotomicLayer_isGalois
    F).to_normal

attribute [local instance] numberFieldComplexificationCyclotomicLayer_normal

open scoped Classical in
private theorem numberFieldComplexificationLayers_sup :
    numberFieldComplexificationCyclotomicLayer F ⊔
        numberFieldComplexificationBaseLayer F =
      ⊤ := by
  apply IntermediateField.lift_injective
    (numberFieldComplexification F)
  rw [numberFieldComplexificationCyclotomicLayer,
    numberFieldComplexificationBaseLayer,
    IntermediateField.lift_sup,
    IntermediateField.lift_restrict,
    IntermediateField.lift_restrict,
    IntermediateField.lift_top]
  exact sup_comm _ _

open scoped Classical in
private theorem numberFieldComplexificationBaseEquiv_algebraMap
    (x : F) :
    algebraMap F (numberFieldComplexification F) x =
      algebraMap (numberFieldComplexificationBaseLayer F)
        (numberFieldComplexification F)
        (numberFieldComplexificationBaseEquiv F x) := by
  apply Subtype.ext
  rfl

open scoped Classical in
private noncomputable def numberFieldComplexificationChangeBase :
    Gal(numberFieldComplexification F/F) →*
      Gal(numberFieldComplexification F/numberFieldComplexificationBaseLayer F) where
  toFun σ :=
    { σ.toRingEquiv with
      commutes' := by
        intro y
        have hy :
            algebraMap F (numberFieldComplexification F)
                ((numberFieldComplexificationBaseEquiv F).symm y) =
              algebraMap (numberFieldComplexificationBaseLayer F)
                (numberFieldComplexification F) y := by
          have hy' :=
            numberFieldComplexificationBaseEquiv_algebraMap F
              ((numberFieldComplexificationBaseEquiv F).symm y)
          rw [(numberFieldComplexificationBaseEquiv F).apply_symm_apply]
            at hy'
          exact hy'
        rw [← hy]
        change
          σ (algebraMap F (numberFieldComplexification F)
              ((numberFieldComplexificationBaseEquiv F).symm y)) =
            algebraMap F (numberFieldComplexification F)
              ((numberFieldComplexificationBaseEquiv F).symm y)
        exact σ.commutes _ }
  map_one' := rfl
  map_mul' _ _ := rfl

open scoped Classical in
private theorem numberFieldComplexificationChangeBase_injective :
    Function.Injective (numberFieldComplexificationChangeBase F) := by
  intro σ τ hστ
  apply AlgEquiv.ext
  intro x
  exact congrArg
    (fun f :
      Gal(numberFieldComplexification F/numberFieldComplexificationBaseLayer F) => f x)
    hστ

open scoped Classical in
private noncomputable def numberFieldComplexificationLayerRestriction :
    Gal(numberFieldComplexification F/numberFieldComplexificationBaseLayer F) →*
      Gal(numberFieldComplexificationCyclotomicLayer F/ℚ) := by
  letI : IsGalois ℚ (numberFieldComplexificationCyclotomicLayer F) :=
    numberFieldComplexificationCyclotomicLayer_isGalois F
  letI : Normal ℚ (numberFieldComplexificationCyclotomicLayer F) :=
    numberFieldComplexificationCyclotomicLayer_normal F
  exact
    IntermediateField.restrictRestrictAlgEquivMapHom
      ℚ (numberFieldComplexificationCyclotomicLayer F)
        (numberFieldComplexificationBaseLayer F)
        (numberFieldComplexification F)

open scoped Classical in
private theorem numberFieldComplexificationLayerRestriction_injective :
    Function.Injective
      (numberFieldComplexificationLayerRestriction F) := by
  let : IsGalois ℚ (numberFieldComplexificationCyclotomicLayer F) :=
    numberFieldComplexificationCyclotomicLayer_isGalois F
  let : Normal ℚ (numberFieldComplexificationCyclotomicLayer F) :=
    numberFieldComplexificationCyclotomicLayer_normal F
  exact
    IntermediateField.restrictRestrictAlgEquivMapHom_injective
      (numberFieldComplexificationCyclotomicLayer F)
      (numberFieldComplexificationBaseLayer F)
      (numberFieldComplexificationLayers_sup F)

open scoped Classical in
private noncomputable def numberFieldComplexificationTransportCyclotomic :
    Gal(rationalComplexificationCyclotomicField/ℚ) →*
      Gal(numberFieldComplexificationCyclotomicLayer F/ℚ) :=
  (AlgEquiv.autCongr
    (numberFieldComplexificationCyclotomicEquiv F)).toMonoidHom

open scoped Classical in
private theorem numberFieldComplexificationRestriction_commutes
    (σ : Gal(numberFieldComplexification F/F)) :
    numberFieldComplexificationTransportCyclotomic F
        (numberFieldComplexificationRestriction F σ) =
      numberFieldComplexificationLayerRestriction F
        (numberFieldComplexificationChangeBase F σ) := by
  let : IsGalois ℚ (numberFieldComplexificationCyclotomicLayer F) :=
    numberFieldComplexificationCyclotomicLayer_isGalois F
  let : Normal ℚ (numberFieldComplexificationCyclotomicLayer F) :=
    numberFieldComplexificationCyclotomicLayer_normal F
  apply AlgEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ :=
    (numberFieldComplexificationCyclotomicEquiv F).surjective x
  apply Subtype.ext
  have hraw :
      (numberFieldComplexificationCyclotomicEquiv F
          (numberFieldComplexificationRestriction F σ y) :
        numberFieldComplexification F) =
        σ (numberFieldComplexificationCyclotomicEquiv F y :
          numberFieldComplexification F) := by
    change
      algebraMap rationalComplexificationCyclotomicField
          (numberFieldComplexification F)
          (numberFieldComplexificationRestriction F σ y) =
        σ (algebraMap rationalComplexificationCyclotomicField
          (numberFieldComplexification F) y)
    change
      algebraMap rationalComplexificationCyclotomicField
          (numberFieldComplexification F)
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ
              (numberFieldComplexification F) σ)
            rationalComplexificationCyclotomicField) y) =
        (MulSemiringAction.toAlgEquiv ℚ
          (numberFieldComplexification F) σ)
          (algebraMap rationalComplexificationCyclotomicField
            (numberFieldComplexification F) y)
    exact
      AlgEquiv.restrictNormal_commutes
        (MulSemiringAction.toAlgEquiv ℚ
          (numberFieldComplexification F) σ)
        rationalComplexificationCyclotomicField y
  have hrestrict :
      (numberFieldComplexificationLayerRestriction F
          (numberFieldComplexificationChangeBase F σ)
          (numberFieldComplexificationCyclotomicEquiv F y) :
        numberFieldComplexification F) =
        numberFieldComplexificationChangeBase F σ
          (numberFieldComplexificationCyclotomicEquiv F y :
            numberFieldComplexification F) :=
    IntermediateField.restrictRestrictAlgEquivMapHom_apply
      (numberFieldComplexificationCyclotomicLayer F)
      (numberFieldComplexificationBaseLayer F)
      (numberFieldComplexificationChangeBase F σ)
      (numberFieldComplexificationCyclotomicEquiv F y)
  calc
    (numberFieldComplexificationTransportCyclotomic F
        (numberFieldComplexificationRestriction F σ)
        (numberFieldComplexificationCyclotomicEquiv F y) :
      numberFieldComplexification F) =
        (numberFieldComplexificationCyclotomicEquiv F
          (numberFieldComplexificationRestriction F σ y) :
            numberFieldComplexification F) := by
      change
        (((numberFieldComplexificationCyclotomicEquiv F).symm.trans
          ((numberFieldComplexificationRestriction F σ).trans
            (numberFieldComplexificationCyclotomicEquiv F)))
            (numberFieldComplexificationCyclotomicEquiv F y) :
          numberFieldComplexification F) = _
      simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    _ = σ (numberFieldComplexificationCyclotomicEquiv F y :
        numberFieldComplexification F) := hraw
    _ = numberFieldComplexificationChangeBase F σ
        (numberFieldComplexificationCyclotomicEquiv F y :
          numberFieldComplexification F) := rfl
    _ = (numberFieldComplexificationLayerRestriction F
        (numberFieldComplexificationChangeBase F σ)
        (numberFieldComplexificationCyclotomicEquiv F y) :
          numberFieldComplexification F) := hrestrict.symm

open scoped Classical in
/-- The rational cyclotomic factor generates the complexification
together with `F`, hence restriction to that factor is injective. -/
theorem numberFieldComplexificationRestriction_injective :
    Function.Injective (numberFieldComplexificationRestriction F) := by
  intro σ τ hστ
  apply numberFieldComplexificationChangeBase_injective F
  apply numberFieldComplexificationLayerRestriction_injective F
  rw [← numberFieldComplexificationRestriction_commutes F σ,
    ← numberFieldComplexificationRestriction_commutes F τ, hστ]

open scoped Classical in
noncomputable instance numberFieldComplexification_isAbelianGalois :
    IsAbelianGalois F (numberFieldComplexification F) := by
  let : IsGalois ℚ (numberFieldComplexificationCyclotomicLayer F) :=
    numberFieldComplexificationCyclotomicLayer_isGalois F
  let : IsGalois (numberFieldComplexificationBaseLayer F)
      (numberFieldComplexification F) :=
    IsGalois.sup_right
      (numberFieldComplexificationCyclotomicLayer F)
      (numberFieldComplexificationBaseLayer F)
      (numberFieldComplexificationLayers_sup F)
  let : IsGalois F (numberFieldComplexification F) :=
    IsGalois.of_equiv_equiv
      (F := numberFieldComplexificationBaseLayer F)
      (E := numberFieldComplexification F)
      (M := F) (N := numberFieldComplexification F)
      (f :=
        (numberFieldComplexificationBaseEquiv F).symm.toRingEquiv)
      (g := RingEquiv.refl (numberFieldComplexification F))
      (by
        apply RingHom.ext
        intro y
        change
          algebraMap F (numberFieldComplexification F)
              ((numberFieldComplexificationBaseEquiv F).symm y) =
            algebraMap (numberFieldComplexificationBaseLayer F)
              (numberFieldComplexification F) y
        calc
          algebraMap F (numberFieldComplexification F)
              ((numberFieldComplexificationBaseEquiv F).symm y) =
              algebraMap (numberFieldComplexificationBaseLayer F)
                (numberFieldComplexification F)
                (numberFieldComplexificationBaseEquiv F
                  ((numberFieldComplexificationBaseEquiv F).symm y)) :=
            numberFieldComplexificationBaseEquiv_algebraMap F _
          _ = algebraMap (numberFieldComplexificationBaseLayer F)
              (numberFieldComplexification F) y := by
            rw [(numberFieldComplexificationBaseEquiv F).apply_symm_apply])
  exact
    { is_comm.comm := fun σ τ => by
        apply numberFieldComplexificationRestriction_injective F
        calc
          numberFieldComplexificationRestriction F (σ * τ) =
              numberFieldComplexificationRestriction F σ *
                numberFieldComplexificationRestriction F τ :=
            map_mul (numberFieldComplexificationRestriction F) σ τ
          _ =
              numberFieldComplexificationRestriction F τ *
                numberFieldComplexificationRestriction F σ :=
            IsMulCommutative.is_comm.comm _ _
          _ = numberFieldComplexificationRestriction F (τ * σ) :=
            (map_mul (numberFieldComplexificationRestriction F) τ σ).symm }

end Reciprocity
end GlobalClassFieldTheory
