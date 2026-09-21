/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassNormTopology
/-!
# Class fields from ordinary idele-class norm neighbourhoods

An actual finite Galois norm subgroup contained in an ordinary
idele-class subgroup makes the transported subgroup norm-open in the
rational absolute class formation.  Finite abelian classification then
constructs its class field.  The final theorem below transports the
result back to the ordinary idele class group of the actual fixed field,
so its conclusion is an equality of genuine determinant-norm ranges.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open Reciprocity

/-- Fix the canonical quotient group before converting fixed-field
equivalences to additive homomorphisms. -/
@[instance_reducible]
private noncomputable def ordinaryNormClassFieldIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] ordinaryNormClassFieldIdeleClassCommGroup

private theorem addSubgroup_map_map_eq_of_comp_eq
    {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    (S : AddSubgroup A) (f : A →+ B) (g : B →+ C) (h : A →+ C)
    (hcomp : g.comp f = h) :
    (S.map f).map g = S.map h := by
  rw [AddSubgroup.map_map, hcomp]

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/- The fixed-field typeclass data used by the topology comparison are kept
behind named constants.  This prevents every consumer from rebuilding the
same finite-dimensional and number-field proof terms while reducing the
dependent fixed-field type. -/
omit [FiniteDimensional K L] [IsGalois K L] in
private theorem numberFieldTowerFixedBaseFiniteDimensionalPackage :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem numberFieldTowerFixedBaseNumberFieldPackage :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) := by
  let hFiniteDimensional : FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) :=
    numberFieldTowerFixedBaseFiniteDimensionalPackage K L
  exact
    NumberField.of_module_finite ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L))

omit [FiniteDimensional K L] [IsGalois K L] in
noncomputable local instance
    numberFieldTowerFixedBaseFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) :=
  numberFieldTowerFixedBaseFiniteDimensionalPackage K L

omit [FiniteDimensional K L] [IsGalois K L] in
noncomputable local instance numberFieldTowerFixedBaseNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) :=
  numberFieldTowerFixedBaseNumberFieldPackage K L

/- The norm-open subgroup and its openness proof form one opaque value.  Both
the classification theorem and the topology comparison consume projections
of this same package. -/
private noncomputable def ordinaryNormOpenSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    ClassFormation.FiniteAbelianSubextension.NormOpenAddSubgroup
      rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L) := by
  let f : Additive (IdeleClassGroup K) →+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation (numberFieldTowerBaseSubgroup K L) :=
    (numberFieldTowerIdeleClassEquivAmbientFixed K L).toAddMonoidHom
  refine ⟨H.toAddSubgroup.map f, ?_⟩
  exact numberFieldTowerTransport_isNormOpen_of_normRange_le K L H hLH

private theorem ordinaryNormOpenSubgroup_val
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    (ordinaryNormOpenSubgroup K L H hLH).1 =
      H.toAddSubgroup.map
        (numberFieldTowerIdeleClassEquivAmbientFixed K L).toAddMonoidHom :=
  rfl

section FixedBaseTransport

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem numberFieldTowerIdeleClassEquivAmbientFixed_symm_apply
    (c : Additive (IdeleClassGroup K)) :
    (rationalAbstractFixedFieldIdeleClassEquivFixed
        (numberFieldTowerBaseSubgroup K L)).symm
      (numberFieldTowerIdeleClassEquivAmbientFixed K L c) =
        MulEquiv.toAdditive
          (ideleClassCongr
            (numberFieldTowerAbstractBaseFieldEquiv K L)) c := by
  let eFixed :=
    rationalAbstractFixedFieldIdeleClassEquivFixed
      (numberFieldTowerBaseSubgroup K L)
  let eBase :=
    MulEquiv.toAdditive
      (ideleClassCongr
        (numberFieldTowerAbstractBaseFieldEquiv K L))
  simpa only [numberFieldTowerIdeleClassEquivAmbientFixed,
    AddEquiv.trans_apply] using
      eFixed.symm_apply_apply (eBase c)

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem numberFieldTowerIdeleClassEquivAmbientFixed_comp :
    (rationalAbstractFixedFieldIdeleClassEquivFixed
        (numberFieldTowerBaseSubgroup K L)).symm.toAddMonoidHom.comp
      (numberFieldTowerIdeleClassEquivAmbientFixed K L).toAddMonoidHom =
        (MulEquiv.toAdditive
          (ideleClassCongr
            (numberFieldTowerAbstractBaseFieldEquiv K L))) := by
  apply AddMonoidHom.ext
  intro c
  exact
    numberFieldTowerIdeleClassEquivAmbientFixed_symm_apply
      K L (c : Additive (IdeleClassGroup K))

private theorem numberFieldTowerBaseTransport_isOpen_of_normRange_le_core
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsOpen
      (((H.toAddSubgroup).map
        (MulEquiv.toAdditive
          (ideleClassCongr
            (numberFieldTowerAbstractBaseFieldEquiv
              K L))).toAddMonoidHom :
        AddSubgroup
          (Additive
            (IdeleClassGroup
              (abstractFixedField ℚ (SeparableClosure ℚ)
                (numberFieldTowerBaseSubgroup K L))))) :
        Set
          (Additive
            (IdeleClassGroup
              (abstractFixedField ℚ (SeparableClosure ℚ)
                (numberFieldTowerBaseSubgroup K L))))) := by
  let B := numberFieldTowerBaseSubgroup K L
  let F := abstractFixedField ℚ (SeparableClosure ℚ) B
  let eFixed :
      Additive (IdeleClassGroup F) ≃+
        KummerTheory.ambientFixedAddSubgroup rationalIdeleClassRepresentation B :=
    rationalAbstractFixedFieldIdeleClassEquivFixed B
  let eBase : Additive (IdeleClassGroup K) ≃+ Additive (IdeleClassGroup F) :=
    MulEquiv.toAdditive
      (ideleClassCongr
        (numberFieldTowerAbstractBaseFieldEquiv K L))
  let eTower :
      Additive (IdeleClassGroup K) ≃+
        KummerTheory.ambientFixedAddSubgroup rationalIdeleClassRepresentation B :=
    numberFieldTowerIdeleClassEquivAmbientFixed K L
  let N : AddSubgroup
      (KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation B) :=
    (ordinaryNormOpenSubgroup K L H hLH).1
  have hN :
      IsNormOpen rationalIdeleClassRepresentation B N :=
    (ordinaryNormOpenSubgroup K L H hLH).2
  have hopen :=
    rationalNormOpenSubgroup_isOpen B N hN
  have hcomp :
      eFixed.symm.toAddMonoidHom.comp
          eTower.toAddMonoidHom =
        eBase.toAddMonoidHom :=
    numberFieldTowerIdeleClassEquivAmbientFixed_comp K L
  have hmap :
      rationalTransportedNormSubgroup B N =
        H.toAddSubgroup.map eBase.toAddMonoidHom := by
    simpa only [rationalTransportedNormSubgroup, N,
      ordinaryNormOpenSubgroup_val, AddSubgroup.map_map] using
      congrArg
        (fun f : Additive (IdeleClassGroup K) →+
            Additive (IdeleClassGroup F) =>
          AddSubgroup.map (N := Additive (IdeleClassGroup F)) f H.toAddSubgroup)
        hcomp
  exact
    (congrArg
      (fun S : AddSubgroup (Additive (IdeleClassGroup F)) =>
        IsOpen (S : Set (Additive (IdeleClassGroup F))))
      hmap).mp hopen

end FixedBaseTransport

/-- A finite Galois norm neighbourhood inside an ordinary idele-class
subgroup produces a finite abelian subextension whose abstract norm
subgroup is exactly the transported ordinary subgroup. -/
theorem exists_finiteAbelianSubextension_normSubgroup_eq_of_normRange_le
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    ∃ M : FiniteAbelianSubextension
        (numberFieldTowerBaseSubgroup K L),
      M.normSubgroup rationalIdeleClassRepresentation =
        (H.toAddSubgroup).map
          (numberFieldTowerIdeleClassEquivAmbientFixed
            K L).toAddMonoidHom := by
  let :=
    numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L
  let B : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    { field := numberFieldTowerBaseSubgroup K L
      finite := numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L }
  let N := ordinaryNormOpenSubgroup K L H hLH
  obtain ⟨M, hM⟩ :
      ∃ M : FiniteAbelianSubextension
          (numberFieldTowerBaseSubgroup K L),
        FiniteAbelianSubextension.normSubgroupMap
            rationalIdeleClassRepresentation M = N :=
    FiniteAbelianSubextension.normSubgroupMap_surjective
      Reciprocity.rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom B N
  refine ⟨M, ?_⟩
  rw [← FiniteAbelianSubextension.normSubgroupMap_val]
  rw [congrArg Subtype.val hM]
  exact ordinaryNormOpenSubgroup_val K L H hLH

/-- The ordinary subgroup transported from `K` to its compatible
embedded fixed-field copy is open whenever it contains an actual finite
Galois norm subgroup.  This is the concrete comparison between the norm
topology and the usual idele-class topology at the chosen realization. -/
theorem numberFieldTowerBaseTransport_isOpen_of_normRange_le
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    let B := numberFieldTowerBaseSubgroup K L
    let F := abstractFixedField ℚ (SeparableClosure ℚ) B
    IsOpen
      (((H.toAddSubgroup).map
        (MulEquiv.toAdditive
          (ideleClassCongr
            (numberFieldTowerAbstractBaseFieldEquiv
              K L))).toAddMonoidHom :
        AddSubgroup (Additive (IdeleClassGroup F))) :
        Set (Additive (IdeleClassGroup F))) := by
  exact
    numberFieldTowerBaseTransport_isOpen_of_normRange_le_core
      K L H hLH

/-- The finite abelian subextension selected from an ordinary norm
neighbourhood.  This is the unique choice point for the realization API
below. -/
noncomputable def ordinaryNormClassFieldSubextension
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    FiniteAbelianSubextension (numberFieldTowerBaseSubgroup K L) :=
  Classical.choose
    (exists_finiteAbelianSubextension_normSubgroup_eq_of_normRange_le
      K L H hLH)

/-- The selected subextension has the prescribed abstract norm subgroup. -/
theorem ordinaryNormClassFieldSubextension_normSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    (ordinaryNormClassFieldSubextension K L H hLH).normSubgroup
        rationalIdeleClassRepresentation =
      H.toAddSubgroup.map
        (numberFieldTowerIdeleClassEquivAmbientFixed
          K L).toAddMonoidHom :=
  Classical.choose_spec
    (exists_finiteAbelianSubextension_normSubgroup_eq_of_normRange_le
      K L H hLH)

/-- The canonical fixed-field copy of the base used by every ordinary
norm-neighbourhood realization in the ambient extension `L / K`. -/
noncomputable abbrev ordinaryNormClassFieldBase : Type :=
  abstractFixedField ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)

omit [FiniteDimensional K L] [IsGalois K L] in
noncomputable instance ordinaryNormClassFieldBaseFiniteDimensional :
    FiniteDimensional ℚ (ordinaryNormClassFieldBase K L) :=
  numberFieldTowerFixedBaseFiniteDimensionalPackage K L

omit [FiniteDimensional K L] [IsGalois K L] in
noncomputable instance ordinaryNormClassFieldBaseNumberField :
    NumberField (ordinaryNormClassFieldBase K L) :=
  numberFieldTowerFixedBaseNumberFieldPackage K L

/-- The actual relative fixed field of the selected ordinary class-field
subextension. -/
noncomputable abbrev ordinaryNormClassFieldExtension
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) : Type :=
  abstractRelativeFixedField ℚ (SeparableClosure ℚ)
    (ordinaryNormClassFieldSubextension K L H hLH).below

noncomputable instance ordinaryNormClassFieldExtensionFiniteDimensional
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    FiniteDimensional (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (ordinaryNormClassFieldSubextension K L H hLH).field
    (ordinaryNormClassFieldSubextension K L H hLH).below
    (numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)
    (ordinaryNormClassFieldSubextension K L H hLH).finite

noncomputable instance ordinaryNormClassFieldScalarTower
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsScalarTower ℚ (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable instance ordinaryNormClassFieldAbsoluteFiniteDimensional
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    FiniteDimensional ℚ
      (ordinaryNormClassFieldExtension K L H hLH) :=
  FiniteDimensional.trans ℚ (ordinaryNormClassFieldBase K L)
    (ordinaryNormClassFieldExtension K L H hLH)

noncomputable instance ordinaryNormClassFieldExtensionNumberField
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    NumberField (ordinaryNormClassFieldExtension K L H hLH) :=
  NumberField.of_module_finite ℚ
    (ordinaryNormClassFieldExtension K L H hLH)

noncomputable instance ordinaryNormClassFieldExtensionIsGalois
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsGalois (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (ordinaryNormClassFieldSubextension K L H hLH).field
    (ordinaryNormClassFieldSubextension K L H hLH).below
    (ordinaryNormClassFieldSubextension K L H hLH).normal

noncomputable instance ordinaryNormClassFieldExtensionIsAbelianGalois
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsAbelianGalois (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois
    (ordinaryNormClassFieldSubextension K L H hLH)

/-- The canonical equivalence from the original base to the selected
fixed-field base. -/
noncomputable abbrev ordinaryNormClassFieldBaseEquiv :
    K ≃ₐ[ℚ] ordinaryNormClassFieldBase K L :=
  numberFieldTowerAbstractBaseFieldEquiv K L

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem ordinaryNormClassFieldBaseIdeleClassTransport_comp :
    let B := numberFieldTowerBaseSubgroup K L
    let eFixed := rationalAbstractFixedFieldIdeleClassEquivFixed B
    let eBase :=
      MulEquiv.toAdditive
        (ideleClassCongr (ordinaryNormClassFieldBaseEquiv K L))
    let eTower := numberFieldTowerIdeleClassEquivAmbientFixed K L
    eFixed.symm.toAddMonoidHom.comp eTower.toAddMonoidHom =
      eBase.toAddMonoidHom := by
  exact numberFieldTowerIdeleClassEquivAmbientFixed_comp K L

/-- The determinant-norm range of the selected ordinary class field is
the original subgroup transported to the canonical fixed-field base. -/
theorem ordinaryNormClassField_ideleClassNorm_range
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    (_root_.ideleClassNorm
      (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH)).range.toAddSubgroup =
        H.toAddSubgroup.map
          (MulEquiv.toAdditive
            (ideleClassCongr
              (ordinaryNormClassFieldBaseEquiv K L))).toAddMonoidHom := by
  let M := ordinaryNormClassFieldSubextension K L H hLH
  let B := numberFieldTowerBaseSubgroup K L
  let hRelativeQuotientFinite : Finite
      (B.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup B M.field M.below) :=
    M.finite
  let eFixed := rationalAbstractFixedFieldIdeleClassEquivFixed B
  let eTower := numberFieldTowerIdeleClassEquivAmbientFixed K L
  let f : Additive (IdeleClassGroup K) →+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation B :=
    eTower.toAddMonoidHom
  let g : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation B →+
        Additive (IdeleClassGroup (ordinaryNormClassFieldBase K L)) :=
    eFixed.symm.toAddMonoidHom
  let h : Additive (IdeleClassGroup K) →+
      Additive (IdeleClassGroup (ordinaryNormClassFieldBase K L)) :=
    (MulEquiv.toAdditive
      (ideleClassCongr
        (ordinaryNormClassFieldBaseEquiv K L))).toAddMonoidHom
  have hnorm :
      (M.normSubgroup rationalIdeleClassRepresentation).map
          g =
        (_root_.ideleClassNorm
          (ordinaryNormClassFieldBase K L)
          (ordinaryNormClassFieldExtension K L H hLH)).range.toAddSubgroup := by
    simpa only [FiniteAbelianSubextension.normSubgroup,
      M, B, ordinaryNormClassFieldBase,
      ordinaryNormClassFieldExtension] using
      (map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
        B M.field M.below M.normal)
  have hcomp :
      g.comp f = h := by
    simpa only [f, g, h, eFixed, eTower] using
      (ordinaryNormClassFieldBaseIdeleClassTransport_comp K L)
  calc
    (_root_.ideleClassNorm
          (ordinaryNormClassFieldBase K L)
          (ordinaryNormClassFieldExtension K L H hLH)).range.toAddSubgroup =
        (M.normSubgroup rationalIdeleClassRepresentation).map
          g := hnorm.symm
    _ =
        (H.toAddSubgroup.map f).map g := by
      exact
        congrArg
          (fun S : AddSubgroup
              (KummerTheory.ambientFixedAddSubgroup
                rationalIdeleClassRepresentation B) =>
            AddSubgroup.map
              (N := Additive (IdeleClassGroup (ordinaryNormClassFieldBase K L))) g S)
          (ordinaryNormClassFieldSubextension_normSubgroup
            K L H hLH)
    _ = H.toAddSubgroup.map h := by
      exact
        addSubgroup_map_map_eq_of_comp_eq
          (A := Additive (IdeleClassGroup K))
          (B := KummerTheory.ambientFixedAddSubgroup
            rationalIdeleClassRepresentation B)
          (C := Additive
            (IdeleClassGroup (ordinaryNormClassFieldBase K L)))
          (S := H.toAddSubgroup)
          (f := f) (g := g) (h := h)
          (hcomp := hcomp)

end GlobalClassFields
end GlobalClassFieldTheory
