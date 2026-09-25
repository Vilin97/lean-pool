/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerConjugation
/-!
# The maximal everywhere-unramified abelian subextension

The selected small Hilbert class field is characterized in actual field
order.  Its rational absolute class-formation norm subgroup is exactly
the intrinsic small-Hilbert subgroup of its fixed-field base.  The
order-reversing finite abelian classification then places every actual
finite abelian extension unramified at all finite and infinite places
inside the selected field.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation KummerTheory
open IdealClassFieldTheory LocalClassFieldTheory NumberField Reciprocity

/-- Fix the canonical quotient structure at the boundary between ordinary
idele classes and additive fixed subgroups. -/
@[instance_reducible]
private noncomputable def smallHilbertMaximalSubextensionIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] smallHilbertMaximalSubextensionIdeleClassCommGroup

private structure SmallHilbertTransportedAddSubgroupData
    {A B : Type} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (H : AddSubgroup A) where
  subgroup : AddSubgroup B
  map_symm : subgroup.map e.symm.toAddMonoidHom = H

private def smallHilbertTransportedAddSubgroupData
    {A B : Type} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (H : AddSubgroup A) :
    SmallHilbertTransportedAddSubgroupData e H where
  subgroup := H.map e.toAddMonoidHom
  map_symm :=
    (AddSubgroup.map_symm_eq_iff_map_eq
      (K := H) (H := H.map e.toAddMonoidHom) (e := e)).2 rfl

private theorem smallHilbertAddSubgroup_eq_of_map_symm_eq
    {A B : Type} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (H J : AddSubgroup B)
    (h : H.map e.symm.toAddMonoidHom =
      J.map e.symm.toAddMonoidHom) :
    H = J := by
  exact AddSubgroup.map_injective e.symm.injective h

/-- The fixed-field idèle-class equivalence at the selected small-Hilbert
base, named once so later subgroup comparisons do not reconstruct it. -/
private noncomputable def smallHilbertClassFieldMaximalIdeleClassEquiv
    (K : Type) [Field K] [NumberField K] :
    Additive (IdeleClassGroup (smallHilbertClassFieldBase K)) ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (smallHilbertClassFieldBaseSubgroup K) :=
  rationalAbstractFixedFieldIdeleClassEquivFixed
    (smallHilbertClassFieldBaseSubgroup K)

/-- The intrinsic ordinary norm subgroup at the selected base, with its
additive carrier fixed in the declaration type. -/
private noncomputable def smallHilbertClassFieldMaximalIntrinsicNormSubgroup
    (K : Type) [Field K] [NumberField K] :
    AddSubgroup (Additive (IdeleClassGroup (smallHilbertClassFieldBase K))) :=
  (smallHilbertClassFieldNormSubgroup
    (K := smallHilbertClassFieldBase K)).toAddSubgroup

private noncomputable def smallHilbertClassFieldMaximalTransportData
    (K : Type) [Field K] [NumberField K] :
    SmallHilbertTransportedAddSubgroupData
      (smallHilbertClassFieldMaximalIdeleClassEquiv K)
      (smallHilbertClassFieldMaximalIntrinsicNormSubgroup K) :=
  smallHilbertTransportedAddSubgroupData
    (smallHilbertClassFieldMaximalIdeleClassEquiv K)
    (smallHilbertClassFieldMaximalIntrinsicNormSubgroup K)

/-- A short typed name for the transported intrinsic subgroup used below.
Keeping this endpoint opaque prevents the fixed-field aliases from being
re-elaborated when the inverse transport is applied. -/
private noncomputable def smallHilbertClassFieldMaximalNormEndpoint
    (K : Type) [Field K] [NumberField K] :
    AddSubgroup
      (ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (smallHilbertClassFieldBaseSubgroup K)) :=
  (smallHilbertClassFieldMaximalTransportData K).subgroup

private theorem smallHilbertClassFieldMaximalNormEndpoint_map_symm
    (K : Type) [Field K] [NumberField K] :
    (smallHilbertClassFieldMaximalNormEndpoint K).map
        (smallHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom =
      smallHilbertClassFieldMaximalIntrinsicNormSubgroup K :=
  (smallHilbertClassFieldMaximalTransportData K).map_symm

private theorem smallHilbertClassFieldMaximalNormEndpoint_eq_public
    (K : Type) [Field K] [NumberField K] :
    smallHilbertClassFieldMaximalNormEndpoint K =
      smallHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (smallHilbertClassFieldNormAmbient K)) := by
  rfl

/-- Mapping the selected abstract norm subgroup back to the ordinary
idèle-class group gives the named intrinsic subgroup. -/
private theorem smallHilbertClassFieldMaximalNormSubgroup_map_symm
    (K : Type) [Field K] [NumberField K] :
    ((smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation).map
      (smallHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom =
        smallHilbertClassFieldMaximalIntrinsicNormSubgroup K := by
  let L :=
    smallHilbertClassFieldSubextension K
  let F :=
    smallHilbertClassFieldBase K
  let e :=
    rationalAbstractFixedFieldIdeleClassEquivFixed
      (smallHilbertClassFieldBaseSubgroup K)
  let hLfinite : Finite
      ((smallHilbertClassFieldBaseSubgroup K).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (smallHilbertClassFieldBaseSubgroup K)
          L.field L.below) :=
    L.finite
  calc
    (L.normSubgroup rationalIdeleClassRepresentation).map
        e.symm.toAddMonoidHom =
      (_root_.ideleClassNorm
        F (smallHilbertClassField K)).range.toAddSubgroup := by
      change
        (finiteNormSubgroup rationalIdeleClassRepresentation
            (smallHilbertClassFieldBaseSubgroup K)
            L.field L.below).map
            e.symm.toAddMonoidHom =
          (_root_.ideleClassNorm
            F (smallHilbertClassField K)).range.toAddSubgroup
      simpa only [L, F, e, smallHilbertClassField,
        smallHilbertClassFieldBase,
        smallHilbertClassFieldMaximalIdeleClassEquiv] using
        (map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
          (smallHilbertClassFieldBaseSubgroup K)
          (smallHilbertClassFieldSubextension K).field
          (smallHilbertClassFieldSubextension K).below
          (smallHilbertClassFieldSubextension K).normal)
    _ = smallHilbertClassFieldMaximalIntrinsicNormSubgroup K := by
      exact
        congrArg Subgroup.toAddSubgroup
          (smallHilbertClassField_ideleClassNorm_range_eq_intrinsic
            (K := K))

/-- Both subgroups have the same inverse image under the fixed-field
idèle-class equivalence. -/
private theorem smallHilbertClassFieldMaximalNormSubgroup_map_eq_endpoint_map
    (K : Type) [Field K] [NumberField K] :
    ((smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation).map
      (smallHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom =
      (smallHilbertClassFieldMaximalNormEndpoint K).map
        (smallHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom := by
  calc
    ((smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation).map
        (smallHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom =
      smallHilbertClassFieldMaximalIntrinsicNormSubgroup K :=
        smallHilbertClassFieldMaximalNormSubgroup_map_symm K
    _ = (smallHilbertClassFieldMaximalNormEndpoint K).map
        (smallHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom :=
      (smallHilbertClassFieldMaximalNormEndpoint_map_symm K).symm

private theorem smallHilbertClassFieldMaximalNormSubgroup_eq_endpoint
    (K : Type) [Field K] [NumberField K] :
    (smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation =
      smallHilbertClassFieldMaximalNormEndpoint K := by
  exact
    smallHilbertAddSubgroup_eq_of_map_symm_eq
      (A := Additive (IdeleClassGroup (smallHilbertClassFieldBase K)))
      (B := ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (smallHilbertClassFieldBaseSubgroup K))
      (e := smallHilbertClassFieldMaximalIdeleClassEquiv K)
      (H := (smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation)
      (J := smallHilbertClassFieldMaximalNormEndpoint K)
      (h := smallHilbertClassFieldMaximalNormSubgroup_map_eq_endpoint_map K)

/-- The selected small Hilbert class-field subextension realizes exactly
the intrinsic small-Hilbert norm subgroup in the rational absolute class
formation. -/
@[simp]
theorem smallHilbertClassFieldSubextension_normSubgroup
    (K : Type) [Field K] [NumberField K] :
    (smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation =
      smallHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (smallHilbertClassFieldNormAmbient K)) := by
  calc
    (smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation =
      smallHilbertClassFieldMaximalNormEndpoint K :=
        smallHilbertClassFieldMaximalNormSubgroup_eq_endpoint K
    _ = smallHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (smallHilbertClassFieldNormAmbient K)) :=
      smallHilbertClassFieldMaximalNormEndpoint_eq_public K

/-- The actual fixed-field extension represented by a finite abelian
subextension of the selected rational base is everywhere unramified.

Naming this predicate keeps the fixed-field instance tower out of the
signatures of every theorem which uses it. -/
def finiteAbelianSubextensionIsEverywhereUnramified
    (K : Type) [Field K] [NumberField K]
    (P : FiniteAbelianSubextension
      (smallHilbertClassFieldBaseSubgroup K)) : Prop :=
  let F :=
    smallHilbertClassFieldBase K
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  letI hPfinite : Finite
      ((smallHilbertClassFieldBaseSubgroup K).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (smallHilbertClassFieldBaseSubgroup K)
          P.field P.below) :=
    P.finite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ)
      (smallHilbertClassFieldBaseSubgroup K)
      P.field P.below inferInstance hPfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField E :=
    NumberField.of_module_finite ℚ E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ)
      (smallHilbertClassFieldBaseSubgroup K)
      P.field P.below P.normal
  IsEverywhereUnramified F E

/-- Every finite abelian subextension of the selected rational
fixed-field base which is unramified at every finite and infinite place
is contained in the selected small Hilbert class-field subextension. -/
theorem
    everywhereUnramifiedAbelianSubextension_le_smallHilbertClassFieldSubextension
    (K : Type) [Field K] [NumberField K]
    (P : FiniteAbelianSubextension
      (smallHilbertClassFieldBaseSubgroup K)) :
    finiteAbelianSubextensionIsEverywhereUnramified K P →
      P ≤ smallHilbertClassFieldSubextension K := by
  let F :=
    smallHilbertClassFieldBase K
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let hPfinite : Finite
      ((smallHilbertClassFieldBaseSubgroup K).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (smallHilbertClassFieldBaseSubgroup K)
          P.field P.below) :=
    P.finite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ)
      (smallHilbertClassFieldBaseSubgroup K)
      P.field P.below inferInstance hPfinite
  let : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ)
      (smallHilbertClassFieldBaseSubgroup K)
      P.field P.below P.normal
  intro hunramified
  change IsEverywhereUnramified F E at hunramified
  let KF :=
    numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K)
  exact
    everywhereUnramifiedFiniteAbelianSubextension_le_smallHilbertClassField
      KF (smallHilbertClassFieldSubextension K) P
      (smallHilbertClassFieldSubextension_normSubgroup K)
      hunramified

/-- The selected small Hilbert class field is genuinely everywhere
unramified, and its finite abelian subextension is maximal among all
actual everywhere-unramified abelian subextensions of the same rational
fixed-field base. -/
theorem
    smallHilbertClassFieldSubextension_isEverywhereUnramifiedAndMaximalAbelian
    (K : Type) [Field K] [NumberField K] :
    IsEverywhereUnramified K (smallHilbertClassField K) ∧
      ∀ P : FiniteAbelianSubextension
          (smallHilbertClassFieldBaseSubgroup K),
        finiteAbelianSubextensionIsEverywhereUnramified K P →
          P ≤ smallHilbertClassFieldSubextension K := by
  constructor
  · exact smallHilbertClassField_isEverywhereUnramified K
  · intro P
    exact
      everywhereUnramifiedAbelianSubextension_le_smallHilbertClassFieldSubextension
        K P

/-- Every finite abelian extension of `K` which is unramified at all
finite and infinite places has a genuine `K`-embedding into the selected
small Hilbert class field of `K`. -/
theorem
    finiteAbelianExtension_nonempty_algHom_to_smallHilbertClassField_of_everywhereUnramified
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L]
    [IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    Nonempty (L →ₐ[K] smallHilbertClassField K) := by
  apply
    finiteAbelianExtension_nonempty_algHom_of_normRange_le
      (K := K) L (smallHilbertClassField K)
  rw [smallHilbertClassField_ideleClassNorm_range_over_original]
  exact
    smallHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_everywhereUnramified
      (K := K) (L := L) hunramifiedFinite

end GlobalClassFields
end GlobalClassFieldTheory
