/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.EmbeddedAbelianSubextension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertNormCharacterization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
public import Mathlib.NumberTheory.NumberField.Basic
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup
/-!
# The maximal finite-unramified abelian subextension

The selected big Hilbert class field is characterized here in actual
field order.  Its abstract norm subgroup in the rational absolute
idele-class formation is identified exactly with the intrinsic
big-Hilbert subgroup of its fixed-field base.  Every finite abelian
subextension whose actual fixed-field extension is unramified at all
finite places has a larger norm subgroup, hence lies below the selected
big Hilbert class field by the order-reversing finite classification.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation KummerTheory
open LocalClassFieldTheory NumberField Reciprocity

private structure BigHilbertTransportedAddSubgroupData
    {A B : Type} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (H : AddSubgroup A) where
  subgroup : AddSubgroup B
  map_symm : subgroup.map e.symm.toAddMonoidHom = H
  mem_iff (x : B) : x ∈ subgroup ↔ e.symm x ∈ H

private def bigHilbertTransportedAddSubgroupData
    {A B : Type} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (H : AddSubgroup A) :
    BigHilbertTransportedAddSubgroupData e H where
  subgroup := H.map e.toAddMonoidHom
  map_symm :=
    (AddSubgroup.map_symm_eq_iff_map_eq
      (K := H) (H := H.map e.toAddMonoidHom) (e := e)).2 rfl
  mem_iff := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩

private theorem bigHilbertAddSubgroup_eq_of_map_symm_eq
    {A B : Type} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (H J : AddSubgroup B)
    (h : H.map e.symm.toAddMonoidHom =
      J.map e.symm.toAddMonoidHom) :
    H = J := by
  exact AddSubgroup.map_injective e.symm.injective h

/-- The intrinsic big-Hilbert norm subgroup of an actual rational fixed
field, transported into the rational absolute idele-class formation. -/
noncomputable def bigHilbertNormSubgroupInRationalClassFormation
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    AddSubgroup
      (ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field) :=
  (bigHilbertClassFieldNormSubgroup
    (K := abstractFixedField
      ℚ (SeparableClosure ℚ) K.field)).toAddSubgroup.map
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        K.field).toAddMonoidHom

private noncomputable def finiteAbstractBigHilbertIntrinsicNormSubgroup
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    AddSubgroup
      (Additive
        (IdeleClassGroup
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field))) :=
  (bigHilbertClassFieldNormSubgroup
    (K := abstractFixedField ℚ (SeparableClosure ℚ) K.field)).toAddSubgroup

private noncomputable def finiteAbstractBigHilbertTransportData
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    BigHilbertTransportedAddSubgroupData
      (rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
      (finiteAbstractBigHilbertIntrinsicNormSubgroup K) :=
  bigHilbertTransportedAddSubgroupData
    (rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
    (finiteAbstractBigHilbertIntrinsicNormSubgroup K)

private theorem bigHilbertNormSubgroupInRationalClassFormation_mem_iff
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (x : ambientFixedAddSubgroup rationalIdeleClassRepresentation K.field) :
    x ∈ bigHilbertNormSubgroupInRationalClassFormation K ↔
      (rationalAbstractFixedFieldIdeleClassEquivFixed K.field).symm x ∈
        finiteAbstractBigHilbertIntrinsicNormSubgroup K :=
  (finiteAbstractBigHilbertTransportData K).mem_iff x

/-- The fixed-field idele-class equivalence at the selected big-Hilbert
base, named once so later subgroup comparisons do not reconstruct it. -/
private noncomputable def bigHilbertClassFieldMaximalIdeleClassEquiv
    (K : Type) [Field K] [NumberField K] :
    Additive (IdeleClassGroup (bigHilbertClassFieldBase K)) ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (bigHilbertClassFieldBaseSubgroup K) :=
  rationalAbstractFixedFieldIdeleClassEquivFixed
    (bigHilbertClassFieldBaseSubgroup K)

/-- The intrinsic ordinary norm subgroup at the selected base, with its
additive carrier fixed in the declaration type. -/
private noncomputable def bigHilbertClassFieldMaximalIntrinsicNormSubgroup
    (K : Type) [Field K] [NumberField K] :
    AddSubgroup (Additive (IdeleClassGroup (bigHilbertClassFieldBase K))) :=
  (bigHilbertClassFieldNormSubgroup
    (K := bigHilbertClassFieldBase K)).toAddSubgroup

/-- The selected abstract norm subgroup, with its ambient additive carrier
fixed once in the declaration type. -/
private noncomputable def bigHilbertClassFieldMaximalActualNormEndpoint
    (K : Type) [Field K] [NumberField K] :
    AddSubgroup
      (ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (bigHilbertClassFieldBaseSubgroup K)) :=
  (bigHilbertClassFieldSubextension K).normSubgroup
    rationalIdeleClassRepresentation

private noncomputable def bigHilbertClassFieldMaximalTransportData
    (K : Type) [Field K] [NumberField K] :
    BigHilbertTransportedAddSubgroupData
      (bigHilbertClassFieldMaximalIdeleClassEquiv K)
      (bigHilbertClassFieldMaximalIntrinsicNormSubgroup K) :=
  bigHilbertTransportedAddSubgroupData
    (bigHilbertClassFieldMaximalIdeleClassEquiv K)
    (bigHilbertClassFieldMaximalIntrinsicNormSubgroup K)

/-- A short typed name for the transported intrinsic subgroup used below. -/
private noncomputable def bigHilbertClassFieldMaximalNormEndpoint
    (K : Type) [Field K] [NumberField K] :
    AddSubgroup
      (ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (bigHilbertClassFieldBaseSubgroup K)) :=
  (bigHilbertClassFieldMaximalTransportData K).subgroup

private theorem bigHilbertClassFieldMaximalNormEndpoint_map_symm
    (K : Type) [Field K] [NumberField K] :
    (bigHilbertClassFieldMaximalNormEndpoint K).map
        (bigHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom =
      bigHilbertClassFieldMaximalIntrinsicNormSubgroup K :=
  (bigHilbertClassFieldMaximalTransportData K).map_symm

private theorem bigHilbertClassFieldMaximalNormEndpoint_mem_iff
    (K : Type) [Field K] [NumberField K]
    (x : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (bigHilbertClassFieldBaseSubgroup K)) :
    x ∈ bigHilbertClassFieldMaximalNormEndpoint K ↔
      (bigHilbertClassFieldMaximalIdeleClassEquiv K).symm x ∈
        bigHilbertClassFieldMaximalIntrinsicNormSubgroup K :=
  (bigHilbertClassFieldMaximalTransportData K).mem_iff x

private theorem bigHilbertClassFieldMaximalNormEndpoint_eq_public
    (K : Type) [Field K] [NumberField K] :
    bigHilbertClassFieldMaximalNormEndpoint K =
      bigHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (bigHilbertClassFieldNormAmbient K)) := by
  rfl

/-- Mapping the selected abstract norm subgroup back to the ordinary
idele-class group gives the named intrinsic subgroup. -/
private theorem bigHilbertClassFieldMaximalNormSubgroup_map_symm
    (K : Type) [Field K] [NumberField K] :
    (bigHilbertClassFieldMaximalActualNormEndpoint K).map
      (bigHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom =
        bigHilbertClassFieldMaximalIntrinsicNormSubgroup K := by
  let L :=
    bigHilbertClassFieldSubextension K
  let F :=
    bigHilbertClassFieldBase K
  let e :=
    rationalAbstractFixedFieldIdeleClassEquivFixed
      (bigHilbertClassFieldBaseSubgroup K)
  let hLfinite : Finite
      ((bigHilbertClassFieldBaseSubgroup K).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (bigHilbertClassFieldBaseSubgroup K)
          L.field L.below) :=
    L.finite
  calc
    (L.normSubgroup rationalIdeleClassRepresentation).map
        e.symm.toAddMonoidHom =
      (_root_.ideleClassNorm
        F (bigHilbertClassField K)).range.toAddSubgroup := by
      change
        (finiteNormSubgroup rationalIdeleClassRepresentation
            (bigHilbertClassFieldBaseSubgroup K)
            L.field L.below).map
            e.symm.toAddMonoidHom =
          (_root_.ideleClassNorm
            F (bigHilbertClassField K)).range.toAddSubgroup
      simpa only [L, F, e, bigHilbertClassField,
        bigHilbertClassFieldBase,
        bigHilbertClassFieldMaximalIdeleClassEquiv] using
        (map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
          (bigHilbertClassFieldBaseSubgroup K)
          (bigHilbertClassFieldSubextension K).field
          (bigHilbertClassFieldSubextension K).below
          (bigHilbertClassFieldSubextension K).normal)
    _ = bigHilbertClassFieldMaximalIntrinsicNormSubgroup K := by
      exact
        congrArg Subgroup.toAddSubgroup
          (bigHilbertClassField_ideleClassNorm_range_eq_intrinsic
            (K := K))

/-- Membership in the selected abstract norm subgroup is detected after
applying the named inverse fixed-field equivalence. -/
private theorem bigHilbertClassFieldMaximalActualNormEndpoint_mem_iff
    (K : Type) [Field K] [NumberField K] :
    ∀ x : ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (bigHilbertClassFieldBaseSubgroup K),
      x ∈ bigHilbertClassFieldMaximalActualNormEndpoint K ↔
        (bigHilbertClassFieldMaximalIdeleClassEquiv K).symm x ∈
          bigHilbertClassFieldMaximalIntrinsicNormSubgroup K := by
  intro x
  have hmem :=
    congrArg
      (fun S =>
        (bigHilbertClassFieldMaximalIdeleClassEquiv K).symm x ∈ S)
      (bigHilbertClassFieldMaximalNormSubgroup_map_symm K)
  constructor
  · intro hx
    exact hmem.mp ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hmem.mpr hx
    have hxy : y = x :=
      (bigHilbertClassFieldMaximalIdeleClassEquiv K).symm.injective hyx
    subst y
    exact hy

private theorem bigHilbertClassFieldMaximalNormSubgroup_eq_endpoint
    (K : Type) [Field K] [NumberField K] :
    bigHilbertClassFieldMaximalActualNormEndpoint K =
      bigHilbertClassFieldMaximalNormEndpoint K := by
  apply AddSubgroup.ext
  intro x
  exact
    (bigHilbertClassFieldMaximalActualNormEndpoint_mem_iff K x).trans
      (bigHilbertClassFieldMaximalNormEndpoint_mem_iff K x).symm

/-- The selected big Hilbert class-field subextension realizes exactly
the intrinsic big-Hilbert norm subgroup in the rational absolute class
formation. -/
@[simp]
theorem bigHilbertClassFieldSubextension_normSubgroup
    (K : Type) [Field K] [NumberField K] :
    (bigHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation =
      bigHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (bigHilbertClassFieldNormAmbient K)) := by
  calc
    (bigHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation =
      bigHilbertClassFieldMaximalActualNormEndpoint K := by
        rfl
    _ =
      bigHilbertClassFieldMaximalNormEndpoint K :=
        bigHilbertClassFieldMaximalNormSubgroup_eq_endpoint K
    _ = bigHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (bigHilbertClassFieldNormAmbient K)) :=
      bigHilbertClassFieldMaximalNormEndpoint_eq_public K

section GeneralFixedFieldContainment

variable
    (K₀ : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P₀ : FiniteAbelianSubextension K₀.field)

local instance maximalSubextensionBaseQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K₀.field (le_baseField K₀.field)) :=
  K₀.finite

local instance maximalSubextensionRelativeQuotientFinite :
    Finite
      (K₀.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          K₀.field P₀.field P₀.below) :=
  P₀.finite

noncomputable local instance maximalSubextensionBaseFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K₀.field K₀.finite

noncomputable local instance maximalSubextensionRelativeFiniteDimensional :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P₀.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    K₀.field P₀.field P₀.below K₀.finite P₀.finite

local instance maximalSubextensionRelativeScalarTower :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P₀.below) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance maximalSubextensionTopFiniteDimensional :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P₀.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P₀.below)

noncomputable local instance maximalSubextensionBaseNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field)

noncomputable local instance maximalSubextensionTopNumberField :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P₀.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P₀.below)

noncomputable local instance maximalSubextensionRelativeIsGalois :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P₀.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    K₀.field P₀.field P₀.below P₀.normal

/-- The intrinsic big-Hilbert norm subgroup is contained in the norm
subgroup of the specified finite abelian subextension. -/
def bigHilbertNormSubgroupContainedInRationalClassFormation
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension K.field) : Prop :=
  bigHilbertNormSubgroupInRationalClassFormation K ≤
    P.normSubgroup rationalIdeleClassRepresentation

/-- The actual fixed-field extension represented by a finite abelian
subextension is unramified at every finite place. -/
def finiteAbelianSubextensionIsUnramifiedAtFinitePlaces
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension K.field) : Prop :=
  IsUnramifiedAtFinitePlaces
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below)

/-- Finite-prime unramifiedness of an actual finite abelian fixed-field
extension forces its abstract norm subgroup to contain the intrinsic
big-Hilbert subgroup. -/
theorem
    bigHilbertNormSubgroupInRationalClassFormation_le_normSubgroup_of_unramifiedAtFinitePlaces
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension K.field) :
    finiteAbelianSubextensionIsUnramifiedAtFinitePlaces K P →
      bigHilbertNormSubgroupContainedInRationalClassFormation K P := by
  classical
  intro hunramified
  unfold finiteAbelianSubextensionIsUnramifiedAtFinitePlaces at hunramified
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let e :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K.field
  have hnormMap :
      (P.normSubgroup rationalIdeleClassRepresentation).map
          e.symm.toAddMonoidHom =
        (_root_.ideleClassNorm F E).range.toAddSubgroup := by
    change
      (finiteNormSubgroup rationalIdeleClassRepresentation
          K.field P.field P.below).map
          e.symm.toAddMonoidHom =
        (_root_.ideleClassNorm F E).range.toAddSubgroup
    exact
      map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
        K.field P.field P.below P.normal
  have hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := F) (L := E) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    rw [_root_.mem_ramifiedBaseFinitePlaces_iff] at hv
    obtain ⟨Q, _hQ, hQramified⟩ := hv
    exact hQramified (hunramified Q)
  have hordinary :
      bigHilbertClassFieldNormSubgroup (K := F) ≤
        (_root_.ideleClassNorm F E).range :=
    bigHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_no_ramifiedFinitePlaces
      (K := F) (L := E) hunramifiedFinite
  unfold bigHilbertNormSubgroupContainedInRationalClassFormation
  intro x hx
  have hxIntrinsic :=
    (bigHilbertNormSubgroupInRationalClassFormation_mem_iff K x).mp hx
  have hmem :=
    congrArg (fun S => e.symm x ∈ S) hnormMap
  have hxMap := hmem.mpr (hordinary hxIntrinsic)
  obtain ⟨y, hy, hyx⟩ := hxMap
  have hxy : y = x := e.symm.injective hyx
  subst y
  exact hy

end GeneralFixedFieldContainment

/-- A finite abelian subextension of the selected rational fixed-field base
is unramified at every finite place. -/
def bigHilbertFiniteAbelianSubextensionIsUnramifiedAtFinitePlaces
    (K : Type) [Field K] [NumberField K]
    (P : FiniteAbelianSubextension
      (bigHilbertClassFieldBaseSubgroup K)) : Prop :=
  finiteAbelianSubextensionIsUnramifiedAtFinitePlaces
    (numberFieldTowerFiniteAbstractField K
      (bigHilbertClassFieldNormAmbient K)) P

section FixedFieldMaximalityInstances

variable
    (K : Type) [Field K] [NumberField K]
    (P : FiniteAbelianSubextension
      (bigHilbertClassFieldBaseSubgroup K))

local instance bigHilbertMaximalRelativeQuotientFinite :
    Finite
      ((bigHilbertClassFieldBaseSubgroup K).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (bigHilbertClassFieldBaseSubgroup K)
          P.field P.below) :=
  P.finite

noncomputable local instance bigHilbertMaximalRelativeFiniteDimensional :
    FiniteDimensional
      (bigHilbertClassFieldBase K)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (bigHilbertClassFieldBaseSubgroup K)
    P.field P.below inferInstance P.finite

local instance bigHilbertMaximalRelativeScalarTower :
    IsScalarTower ℚ
      (bigHilbertClassFieldBase K)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance bigHilbertMaximalTopFiniteDimensional :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  FiniteDimensional.trans ℚ
    (bigHilbertClassFieldBase K)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below)

noncomputable local instance bigHilbertMaximalTopNumberField :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below)

noncomputable local instance bigHilbertMaximalRelativeIsGalois :
    IsGalois
      (bigHilbertClassFieldBase K)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    (bigHilbertClassFieldBaseSubgroup K)
    P.field P.below P.normal

/-- Every finite abelian subextension of the same rational fixed-field
base which is unramified at all finite places is contained in the
selected big Hilbert class-field subextension. -/
theorem
    finiteUnramifiedAbelianSubextension_le_bigHilbertClassFieldSubextension
    (K : Type) [Field K] [NumberField K]
    (P : FiniteAbelianSubextension
      (bigHilbertClassFieldBaseSubgroup K)) :
    bigHilbertFiniteAbelianSubextensionIsUnramifiedAtFinitePlaces K P →
      P ≤ bigHilbertClassFieldSubextension K := by
  intro hunramified
  let KF :=
    numberFieldTowerFiniteAbstractField K
      (bigHilbertClassFieldNormAmbient K)
  apply
    (FiniteAbelianSubextension.le_iff_normSubgroup_le
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      KF P (bigHilbertClassFieldSubextension K)).2
  have hSelected :
      (bigHilbertClassFieldSubextension K).normSubgroup
          rationalIdeleClassRepresentation =
        bigHilbertNormSubgroupInRationalClassFormation KF :=
    bigHilbertClassFieldSubextension_normSubgroup K
  have hOther :
      bigHilbertNormSubgroupContainedInRationalClassFormation KF P :=
    bigHilbertNormSubgroupInRationalClassFormation_le_normSubgroup_of_unramifiedAtFinitePlaces
      KF P (by
        simpa only [KF,
          bigHilbertFiniteAbelianSubextensionIsUnramifiedAtFinitePlaces] using
          hunramified)
  unfold bigHilbertNormSubgroupContainedInRationalClassFormation at hOther
  calc
    (bigHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation =
      bigHilbertNormSubgroupInRationalClassFormation KF := hSelected
    _ ≤ P.normSubgroup rationalIdeleClassRepresentation := hOther

end FixedFieldMaximalityInstances

/-- The selected big Hilbert class field is genuinely finite-unramified,
and its finite abelian subextension is maximal among all actual
finite-unramified abelian subextensions of the same rational fixed-field
base. -/
theorem
    bigHilbertClassFieldSubextension_isFiniteUnramifiedAndMaximalAbelian
    (K : Type) [Field K] [NumberField K] :
    IsUnramifiedAtFinitePlaces K (bigHilbertClassField K) ∧
      ∀ P : FiniteAbelianSubextension
          (bigHilbertClassFieldBaseSubgroup K),
        bigHilbertFiniteAbelianSubextensionIsUnramifiedAtFinitePlaces K P →
          P ≤ bigHilbertClassFieldSubextension K := by
  constructor
  · exact bigHilbertClassField_isUnramifiedAtFinitePlaces K
  · intro P
    exact
      finiteUnramifiedAbelianSubextension_le_bigHilbertClassFieldSubextension
        K P

/-!
## Maximality over the original number field

The preceding order statement lives over the fixed-field copy of the
base used by the rational absolute class formation.  We now embed an
arbitrary actual finite abelian extension `E / K` compatibly with that
copy, apply the fixed-field maximality theorem there, and restrict its
ambient embedding to the selected big Hilbert class field.
-/

/-- The distinguished embedding of the original number field into the
rational separable closure underlying the selected big Hilbert class
field. -/
noncomputable def bigHilbertClassFieldBaseEmbedding
    (K : Type) [Field K] [NumberField K] :
    K →ₐ[ℚ] SeparableClosure ℚ :=
  numberFieldTowerLowerEmbedding K
    (bigHilbertClassFieldNormAmbient K)

/-- The canonical fixed-field equivalence has the distinguished base
embedding as its underlying map into the rational separable closure. -/
theorem bigHilbertClassFieldBaseEquiv_coe
    (K : Type) [Field K] [NumberField K]
    (x : K) :
    ((bigHilbertClassFieldBaseEquiv (K := K) x :
        bigHilbertClassFieldBase K) :
      SeparableClosure ℚ) =
      bigHilbertClassFieldBaseEmbedding K x := by
  rfl

/-- An actual finite extension of `K`, embedded into the rational
separable closure so that its restriction to `K` is exactly the base
embedding used by the selected big Hilbert class field. -/
noncomputable def bigHilbertClassFieldCompatibleEmbedding
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] :
    E →ₐ[ℚ] SeparableClosure ℚ :=
  Classical.choose
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ) (L := K) (E := E)
      (M := SeparableClosure ℚ)
      (bigHilbertClassFieldBaseEmbedding K))

/-- Compatibility of the chosen ambient embedding with the selected
copy of the original base field. -/
@[simp]
theorem bigHilbertClassFieldCompatibleEmbedding_restrictDomain
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] :
    (bigHilbertClassFieldCompatibleEmbedding K E).domRestrict K =
      bigHilbertClassFieldBaseEmbedding K :=
  Classical.choose_spec
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ) (L := K) (E := E)
      (M := SeparableClosure ℚ)
      (bigHilbertClassFieldBaseEmbedding K))

/-- Evaluation on the original scalar map agrees with the distinguished
base embedding. -/
@[simp]
theorem bigHilbertClassFieldCompatibleEmbedding_algebraMap
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    (x : K) :
    bigHilbertClassFieldCompatibleEmbedding K E
        (algebraMap K E x) =
      bigHilbertClassFieldBaseEmbedding K x := by
  have h :=
    DFunLike.congr_fun
      (bigHilbertClassFieldCompatibleEmbedding_restrictDomain K E) x
  exact h

/-- The fixing subgroup of the compatible embedded copy of `K` is the
base subgroup of the selected big Hilbert class field. -/
@[simp]
theorem bigHilbertClassFieldCompatibleEmbedding_baseSubgroup
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] :
    numberFieldEmbeddedBaseSubgroup K E
        (bigHilbertClassFieldCompatibleEmbedding K E) =
      bigHilbertClassFieldBaseSubgroup K := by
  change
    RamificationTheory.closedFixingSubgroup ℚ (SeparableClosure ℚ)
        ((bigHilbertClassFieldCompatibleEmbedding K E).domRestrict K).fieldRange =
      RamificationTheory.closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (bigHilbertClassFieldBaseEmbedding K).fieldRange
  exact
    congrArg
      (fun i : K →ₐ[ℚ] SeparableClosure ℚ =>
        RamificationTheory.closedFixingSubgroup ℚ
          (SeparableClosure ℚ) i.fieldRange)
      (bigHilbertClassFieldCompatibleEmbedding_restrictDomain K E)

/-- The actual finite abelian extension `E / K`, represented inside the
same rational absolute Galois group as the selected big Hilbert class
field. -/
noncomputable def bigHilbertClassFieldEmbeddedAbelianSubextension
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E] :
    FiniteAbelianSubextension
      (bigHilbertClassFieldBaseSubgroup K) :=
  numberFieldEmbeddedAbelianSubextension K E
    (bigHilbertClassFieldCompatibleEmbedding K E)
    (bigHilbertClassFieldBaseSubgroup K)
    (bigHilbertClassFieldCompatibleEmbedding_baseSubgroup K E)

/-- The top subgroup of the embedded abelian subextension is exactly
the fixing subgroup of the compatible embedded copy of `E`. -/
@[simp]
theorem bigHilbertClassFieldEmbeddedAbelianSubextension_field
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E] :
    (bigHilbertClassFieldEmbeddedAbelianSubextension K E).field =
      numberFieldEmbeddedTopSubgroup K E
        (bigHilbertClassFieldCompatibleEmbedding K E) := by
  exact
    numberFieldEmbeddedAbelianSubextension_field K E
      (bigHilbertClassFieldCompatibleEmbedding K E)
      (bigHilbertClassFieldBaseSubgroup K)
      (bigHilbertClassFieldCompatibleEmbedding_baseSubgroup K E)

/-- Finite-prime unramifiedness is preserved when the top number field
is replaced by an equivalent `K`-algebra. -/
theorem finitePlaceUnramifiedness_congrTop
    {K L M : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M)
    (h : IsUnramifiedAtFinitePlaces K L) :
    IsUnramifiedAtFinitePlaces K M := by
  let hAlgebra : Algebra L M :=
    e.toRingHom.toAlgebra
  let hScalarTower : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (e.commutes x).symm)
  let eLM : L ≃ₐ[L] M :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun _ => rfl)
  let eOLM : (𝓞 L) ≃ₐ[𝓞 L] (𝓞 M) :=
    NumberField.RingOfIntegers.mapAlgEquiv eLM
  let hFormallyUnramified :
      Algebra.FormallyUnramified (𝓞 L) (𝓞 M) :=
    Algebra.FormallyUnramified.of_equiv eOLM
  have hLM :
      IsUnramifiedAtFinitePlaces L M := by
    intro P
    infer_instance
  exact
    IsUnramifiedAtFinitePlaces.trans h hLM

/-- Any actual finite unramified abelian extension of `K` embeds over
`K` into the selected big Hilbert class field. -/
noncomputable def
    finiteUnramifiedAbelianExtensionEmbeddingIntoBigHilbertClassField
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E]
    (hunramified : IsUnramifiedAtFinitePlaces K E) :
    E →ₐ[K] bigHilbertClassField K := by
  let j :=
    bigHilbertClassFieldCompatibleEmbedding K E
  let P :=
    bigHilbertClassFieldEmbeddedAbelianSubextension K E
  let F :=
    bigHilbertClassFieldBase K
  let A :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  letI hBaseAlgebra : Algebra K A :=
    ((algebraMap F A).comp
      (algebraMap K F)).toAlgebra
  letI hBaseScalarTower : IsScalarTower K F A :=
    IsScalarTower.of_algebraMap_eq' rfl
  let eQ :=
    numberFieldEmbeddedAbstractTopFieldEquiv K E j
  have hPField :
      P.field = numberFieldEmbeddedTopSubgroup K E j := by
    simpa only [P, j] using
      (bigHilbertClassFieldEmbeddedAbelianSubextension_field K E)
  let RawField :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K E j)
  let eRestrict : (RawField.restrictScalars ℚ) ≃+* A :=
    { toFun := fun x =>
        ⟨x.1, by
          change x.1 ∈
            abstractFixedField ℚ (SeparableClosure ℚ) P.field
          rw [hPField]
          exact x.2⟩
      invFun := fun x =>
        ⟨x.1, by
          change x.1 ∈
            abstractFixedField ℚ (SeparableClosure ℚ)
              (numberFieldEmbeddedTopSubgroup K E j)
          rw [← hPField]
          exact x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl }
  let eTopRing : E ≃+* A := by
    exact eQ.toRingEquiv.trans eRestrict
  let eTop : E ≃ₐ[K] A :=
    AlgEquiv.ofRingEquiv (f := eTopRing) (fun x => by
      apply Subtype.ext
      change
        j (algebraMap K E x) =
          ((bigHilbertClassFieldBaseEquiv (K := K) x :
              F) :
            SeparableClosure ℚ)
      rw [bigHilbertClassFieldCompatibleEmbedding_algebraMap,
        bigHilbertClassFieldBaseEquiv_coe])
  letI hAFiniteDimensional : FiniteDimensional K A :=
    FiniteDimensional.of_surjective eTop.toLinearMap eTop.surjective
  letI hANumberField : NumberField A :=
    NumberField.of_module_finite K A
  have hKA :
      IsUnramifiedAtFinitePlaces K A :=
    finitePlaceUnramifiedness_congrTop eTop hunramified
  have hFA :
      IsUnramifiedAtFinitePlaces F A :=
    IsUnramifiedAtFinitePlaces.top
      (k := K) (K := F) (F := A) hKA
  have hcontain :
      P ≤ bigHilbertClassFieldSubextension K :=
    finiteUnramifiedAbelianSubextension_le_bigHilbertClassFieldSubextension
      K P (by
        simpa only [bigHilbertFiniteAbelianSubextensionIsUnramifiedAtFinitePlaces,
          finiteAbelianSubextensionIsUnramifiedAtFinitePlaces, F, A] using hFA)
  let jH : E →+* bigHilbertClassField K :=
    j.toRingHom.codRestrict
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (bigHilbertClassFieldSubextension K).below).toSubring
      (fun x => by
        change
          j x ∈
            abstractFixedField ℚ (SeparableClosure ℚ)
              (bigHilbertClassFieldSubextension K).field
        have hxP :
            j x ∈
              abstractFixedField ℚ (SeparableClosure ℚ)
                P.field := by
          rw [bigHilbertClassFieldEmbeddedAbelianSubextension_field]
          change
            j x ∈
              IntermediateField.fixedField j.fieldRange.fixingSubgroup
          rw [InfiniteGalois.fixedField_fixingSubgroup]
          exact ⟨x, rfl⟩
        have hsubgroup :
            (bigHilbertClassFieldSubextension K).field.toSubgroup ≤
              P.field.toSubgroup :=
          hcontain
        exact
          (abstractFixedField_le
            ℚ (SeparableClosure ℚ) hsubgroup) hxP)
  exact
    { jH with
      commutes' := fun x => by
        apply Subtype.ext
        change
          j (algebraMap K E x) =
            ((bigHilbertClassFieldBaseEquiv (K := K) x :
                F) :
              SeparableClosure ℚ)
        rw [bigHilbertClassFieldCompatibleEmbedding_algebraMap,
          bigHilbertClassFieldBaseEquiv_coe] }

/-- Containment form of maximality: every finite unramified abelian
extension of `K` has a `K`-embedding into the selected big Hilbert
class field. -/
theorem
    finiteUnramifiedAbelianExtension_nonempty_algHom_bigHilbertClassField
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E]
    (hunramified : IsUnramifiedAtFinitePlaces K E) :
    Nonempty (E →ₐ[K] bigHilbertClassField K) :=
  ⟨finiteUnramifiedAbelianExtensionEmbeddingIntoBigHilbertClassField
    K E hunramified⟩

/-- The selected big Hilbert class field is the actual maximal finite
unramified abelian extension of the original number field: it is finite,
abelian Galois and unramified at every finite prime, and it contains
every other finite unramified abelian extension over the same base. -/
theorem bigHilbertClassField_isMaximalUnramifiedAbelianExtension
    (K : Type) [Field K] [NumberField K] :
    FiniteDimensional K (bigHilbertClassField K) ∧
      IsAbelianGalois K (bigHilbertClassField K) ∧
      IsUnramifiedAtFinitePlaces K (bigHilbertClassField K) ∧
      ∀ (E : Type) [Field E] [NumberField E]
        [Algebra K E] [FiniteDimensional K E]
        [IsAbelianGalois K E],
        IsUnramifiedAtFinitePlaces K E →
          Nonempty (E →ₐ[K] bigHilbertClassField K) := by
  refine ⟨inferInstance, inferInstance,
    bigHilbertClassField_isUnramifiedAtFinitePlaces K, ?_⟩
  intro E _ _ _ _ _
  exact
    finiteUnramifiedAbelianExtension_nonempty_algHom_bigHilbertClassField
      K E

end GlobalClassFields
end GlobalClassFieldTheory
