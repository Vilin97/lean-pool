/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicTorsionFixedField
import LeanPool.ClassFieldTheory.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.InfiniteBaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.GroupTheory.Index
/-!
# Base change of the rational cyclotomic `ZHat`-extension

The rational cyclotomic `ZHat`-extension lives inside the fixed separable
closure of `ℚ`.  To form its compositum with an arbitrary number field, we first
embed that number field into the same separable closure.  The
intersection degree below is the normalization integer

`f_K = [K ∩ ℚ_tilde : ℚ]`.

All fields in this file are the actual mathlib intermediate fields in
`SeparableClosure ℚ`; no abstract copy of the compositum or of its
Galois group is introduced.
-/

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  continuousMulEquivOfCompactToT2 →
    continuousMulEquivOfCompactToT2


noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped Topology
open AlgebraicNumberTheory
open ClassFormation
open KummerTheory

/-- The fixed rational separable closure, with the intermediate-field algebra
structure used by Mathlib's `IsSepClosure` construction. -/
noncomputable instance rationalSeparableClosure_isGalois :
    IsGalois ℚ (SeparableClosure ℚ) := by
  exact @IsSepClosure.isGalois
    ℚ _ (SeparableClosure ℚ) _
    ((separableClosure ℚ (AlgebraicClosure ℚ)).algebra)
    (separableClosure.isSepClosure ℚ (AlgebraicClosure ℚ))

/-- The chosen rational separable closure is normal over `ℚ`. -/
noncomputable instance rationalSeparableClosure_isNormal :
    Normal ℚ (SeparableClosure ℚ) :=
  rationalSeparableClosure_isGalois.to_normal

/-- The cyclotomic `ZHat`-extension of `ℚ`, regarded as an actual
intermediate field of `SeparableClosure ℚ`. -/
def rationalCyclotomicZHatField :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  IntermediateField.lift rationalCyclotomicTorsionFixedField

noncomputable instance rationalCyclotomicZHatField_isAbelianGalois :
    IsAbelianGalois ℚ rationalCyclotomicZHatField := by
  exact @IsAbelianGalois.of_algHom
    ℚ rationalCyclotomicZHatField rationalCyclotomicTorsionFixedField
    _ _ _ _ _
    (IntermediateField.liftAlgEquiv
      rationalCyclotomicTorsionFixedField).symm.toAlgHom
    KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois

/-- The lifted cyclotomic `ZHat`-field is normal with its canonical
`IntermediateField` algebra structure.  This is the normality used by
restriction maps out of the fixed rational separable closure. -/
theorem rationalCyclotomicZHatField_normal :
    @Normal ℚ rationalCyclotomicZHatField _ _
      rationalCyclotomicZHatField.algebra' := by
  exact @IsGalois.to_normal
    ℚ _ rationalCyclotomicZHatField _
      rationalCyclotomicZHatField.algebra'
    (@IsAbelianGalois.of_algHom
      ℚ rationalCyclotomicZHatField rationalCyclotomicTorsionFixedField
      _ _ rationalCyclotomicZHatField.algebra' _ _
      (IntermediateField.liftAlgEquiv
        rationalCyclotomicTorsionFixedField).symm.toAlgHom
      KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois).toIsGalois

/-- The lifted cyclotomic `ZHat`-field is normal for the ambient algebra
structure selected by ordinary Galois-theory APIs. -/
noncomputable instance rationalCyclotomicZHatField_isNormal :
    Normal ℚ rationalCyclotomicZHatField :=
  rationalCyclotomicZHatField_isAbelianGalois.toIsGalois.to_normal

/-- The cyclotomic Galois-group equivalence, transported from the nested
presentation to the copy of `ℚ_tilde` in `SeparableClosure ℚ`. -/
noncomputable def rationalCyclotomicZHatFieldGalEquivZHat :
    (rationalCyclotomicZHatField ≃ₐ[ℚ]
      rationalCyclotomicZHatField) ≃ₜ*
        Multiplicative ZHat := by
  let _ : T2Space
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
    krullTopology_t2
  let e :=
    IntermediateField.liftAlgEquiv
      rationalCyclotomicTorsionFixedField
  let c :
      (rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
          rationalCyclotomicTorsionFixedField) ≃ₜ*
        (rationalCyclotomicZHatField ≃ₐ[ℚ]
          rationalCyclotomicZHatField) :=
    continuousMulEquivOfCompactToT2
        (AlgEquiv.autCongr e)
        (continuous_algEquiv_autCongr e)
  exact c.symm.trans
    rationalCyclotomicTorsionFixedFieldGalEquivZHat

/-- Restriction from the full rational cyclotomic field to its actual
`ZHat` torsion-fixed subfield, transported to the copy inside
`SeparableClosure ℚ`. -/
noncomputable def rationalCyclotomicFullRestrictionToZHat :
    (KummerTheory.rationalCyclotomicField ≃ₐ[ℚ]
        KummerTheory.rationalCyclotomicField) →*
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
  (AlgEquiv.autCongr
      (IntermediateField.liftAlgEquiv
        KummerTheory.rationalCyclotomicTorsionFixedField)).toMonoidHom.comp
    (@AlgEquiv.restrictNormalHom
      ℚ _ KummerTheory.rationalCyclotomicField _ _
      KummerTheory.rationalCyclotomicTorsionFixedField _ _ _ _
      KummerTheory.rationalCyclotomicTorsionFixedField_normal)

/-- The actual restriction to the lifted `ZHat`-field has coordinate
equal to the torsion-free component of the full cyclotomic character. -/
@[simp]
theorem rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction
    (σ :
      KummerTheory.rationalCyclotomicField ≃ₐ[ℚ]
        KummerTheory.rationalCyclotomicField) :
    rationalCyclotomicZHatFieldGalEquivZHat
        (rationalCyclotomicFullRestrictionToZHat σ) =
      (KummerTheory.zHatUnitsDecomposition
        (KummerTheory.rationalCyclotomicCharacterContinuousMulEquiv
          σ)).1 := by
  let _ : T2Space
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
    krullTopology_t2
  let e :=
    IntermediateField.liftAlgEquiv
      KummerTheory.rationalCyclotomicTorsionFixedField
  let c :
      (KummerTheory.rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
          KummerTheory.rationalCyclotomicTorsionFixedField) ≃ₜ*
        (rationalCyclotomicZHatField ≃ₐ[ℚ]
          rationalCyclotomicZHatField) :=
    continuousMulEquivOfCompactToT2
      (AlgEquiv.autCongr e)
      (continuous_algEquiv_autCongr e)
  change
    rationalCyclotomicTorsionFixedFieldGalEquivZHat
        (c.symm
          (c
            (@AlgEquiv.restrictNormalHom
              ℚ _ KummerTheory.rationalCyclotomicField _ _
              KummerTheory.rationalCyclotomicTorsionFixedField _ _ _ _
              KummerTheory.rationalCyclotomicTorsionFixedField_normal σ))) =
      (KummerTheory.zHatUnitsDecomposition
        (KummerTheory.rationalCyclotomicCharacterContinuousMulEquiv
          σ)).1
  rw [c.symm_apply_apply,
    rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal]

/-- Restriction from the actual absolute Galois group of `ℚ` to the
cyclotomic `ZHat`-extension. -/
noncomputable def
    rationalAbsoluteGaloisRestrictionToCyclotomicZHat :
    (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) →ₜ*
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) where
  toMonoidHom :=
    @AlgEquiv.restrictNormalHom
      ℚ _ (SeparableClosure ℚ) _ _
      rationalCyclotomicZHatField _
      rationalCyclotomicZHatField.algebra' _ _
      rationalCyclotomicZHatField_normal
  continuous_toFun := by
    let : @Normal ℚ rationalCyclotomicZHatField _ _
        rationalCyclotomicZHatField.algebra' :=
      rationalCyclotomicZHatField_normal
    exact
      InfiniteGalois.restrictNormalHom_continuous
        rationalCyclotomicZHatField

/-- The actual global degree datum
`d : Gal(ℚ_bar/ℚ) → Multiplicative ZHat`, obtained by restriction to the
cyclotomic `ZHat`-extension. -/
noncomputable def rationalCyclotomicDegreeData :
    DegreeData
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  degree :=
    (ContinuousMonoidHom.toContinuousMonoidHom
      rationalCyclotomicZHatFieldGalEquivZHat).comp
        rationalAbsoluteGaloisRestrictionToCyclotomicZHat
  degree_surjective :=
    by
      let : @Normal ℚ rationalCyclotomicZHatField _ _
          rationalCyclotomicZHatField.algebra' :=
        rationalCyclotomicZHatField_normal
      exact
        rationalCyclotomicZHatFieldGalEquivZHat.surjective.comp
          (AlgEquiv.restrictNormalHom_surjective
            (F := ℚ)
            (K₁ := rationalCyclotomicZHatField)
            (E := SeparableClosure ℚ))

/-- The inertia subgroup of the actual cyclotomic degree datum is
literally the subgroup fixing the cyclotomic `ZHat`-extension. -/
theorem rationalCyclotomicDegreeData_inertia :
    rationalCyclotomicDegreeData.inertia =
      RamificationTheory.closedFixingSubgroup ℚ (SeparableClosure ℚ)
        rationalCyclotomicZHatField := by
  let : @Normal ℚ rationalCyclotomicZHatField _ _
      rationalCyclotomicZHatField.algebra' :=
    rationalCyclotomicZHatField_normal
  let r := rationalAbsoluteGaloisRestrictionToCyclotomicZHat
  have hrker : r.toMonoidHom.ker =
      rationalCyclotomicZHatField.fixingSubgroup := by
    change
      (@AlgEquiv.restrictNormalHom
        ℚ _ (SeparableClosure ℚ) _ _
        rationalCyclotomicZHatField _
        rationalCyclotomicZHatField.algebra' _ _
        rationalCyclotomicZHatField_normal).ker =
          rationalCyclotomicZHatField.fixingSubgroup
    exact
      @IntermediateField.restrictNormalHom_ker
        ℚ (SeparableClosure ℚ) _ _ _
        rationalCyclotomicZHatField
        rationalCyclotomicZHatField_normal
  ext σ
  change
    σ ∈ rationalCyclotomicDegreeData.inertia ↔
      σ ∈ RamificationTheory.closedFixingSubgroup ℚ (SeparableClosure ℚ)
        rationalCyclotomicZHatField
  rw [rationalCyclotomicDegreeData.mem_inertia_iff]
  change
    rationalCyclotomicZHatFieldGalEquivZHat
        (r σ) =
        1 ↔
      σ ∈ rationalCyclotomicZHatField.fixingSubgroup
  constructor
  · intro hσ
    have hrestrict :
        r σ =
          1 := by
      apply rationalCyclotomicZHatFieldGalEquivZHat.injective
      simpa using hσ
    have hker :
        σ ∈ r.toMonoidHom.ker :=
      hrestrict
    exact hrker ▸ hker
  · intro hσ
    have hker :
        σ ∈ r.toMonoidHom.ker := by
      rw [hrker]
      exact hσ
    change
      rationalCyclotomicZHatFieldGalEquivZHat
          (r σ) =
        1
    have hzero : r σ = 1 :=
      MonoidHom.mem_ker.mp hker
    rw [hzero, map_one]

/-- The field fixed by cyclotomic inertia is the actual cyclotomic
`ZHat`-extension inside the chosen rational separable closure. -/
theorem rationalCyclotomicDegreeData_fixedField_inertia :
    LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        rationalCyclotomicDegreeData.inertia =
      rationalCyclotomicZHatField := by
  rw [rationalCyclotomicDegreeData_inertia]
  exact
    InfiniteGalois.fixedField_fixingSubgroup
      rationalCyclotomicZHatField

/-- For every abstract rational fixed field `F`, the field fixed by
its cyclotomic inertia is the genuine compositum `Fℚ_tilde` in
`SeparableClosure ℚ`. -/
theorem
    rationalCyclotomicDegreeData_fixedField_fieldInertia
    (H : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicDegreeData.fieldInertia H) =
      LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H ⊔
        rationalCyclotomicZHatField := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H
  have hsubgroup :
      (rationalCyclotomicDegreeData.fieldInertia H).toSubgroup =
        (F ⊔ rationalCyclotomicZHatField).fixingSubgroup := by
    calc
      (rationalCyclotomicDegreeData.fieldInertia H).toSubgroup =
          H.toSubgroup ⊓
            rationalCyclotomicDegreeData.inertia.toSubgroup :=
        rfl
      _ =
          H.toSubgroup ⊓
            rationalCyclotomicZHatField.fixingSubgroup := by
        rw [rationalCyclotomicDegreeData_inertia]
        rfl
      _ =
          F.fixingSubgroup ⊓
            rationalCyclotomicZHatField.fixingSubgroup := by
        rw [InfiniteGalois.fixingSubgroup_fixedField H]
      _ =
          (F ⊔ rationalCyclotomicZHatField).fixingSubgroup :=
        IntermediateField.fixingSubgroup_sup.symm
  change
    IntermediateField.fixedField
        (rationalCyclotomicDegreeData.fieldInertia H).toSubgroup =
      F ⊔ rationalCyclotomicZHatField
  rw [hsubgroup]
  exact
    InfiniteGalois.fixedField_fixingSubgroup
      (F ⊔ rationalCyclotomicZHatField)

/-- Restricting a closed subgroup of the rational absolute Galois group
to the cyclotomic `ZHat`-extension gives exactly the subgroup fixing the
intersection with its concrete fixed field. -/
theorem
    rationalAbsoluteGaloisRestriction_image_eq_intersection_fixingSubgroup
    (H : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    H.toSubgroup.map
        rationalAbsoluteGaloisRestrictionToCyclotomicZHat.toMonoidHom =
      (((LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H) ⊓
        rationalCyclotomicZHatField).restrict
        (show
          LocalClassFieldTheory.abstractFixedField
                ℚ (SeparableClosure ℚ) H ⊓
              rationalCyclotomicZHatField ≤
            rationalCyclotomicZHatField from
          inf_le_right)).fixingSubgroup := by
  let _ : T2Space
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
    krullTopology_t2
  let r := rationalAbsoluteGaloisRestrictionToCyclotomicZHat
  let R : ClosedSubgroup
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
    { toSubgroup := H.toSubgroup.map r
      isClosed' := by
        change IsClosed (r '' H.carrier)
        exact
          (H.isClosed'.isCompact.image
            r.continuous).isClosed }
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H
  let J : IntermediateField ℚ (SeparableClosure ℚ) :=
    F ⊓ rationalCyclotomicZHatField
  let hJT : J ≤ rationalCyclotomicZHatField :=
    inf_le_right
  let E : IntermediateField ℚ rationalCyclotomicZHatField :=
    J.restrict hJT
  have hE :
      E = IntermediateField.fixedField R.toSubgroup := by
    apply
      (IntermediateField.lift_injective
        rationalCyclotomicZHatField)
    calc
      IntermediateField.lift E = J :=
        IntermediateField.lift_restrict hJT
      _ =
          IntermediateField.lift
            (IntermediateField.fixedField R.toSubgroup) := by
        dsimp only [F, J, R, r]
        change
          IntermediateField.fixedField H.toSubgroup ⊓
              rationalCyclotomicZHatField =
            IntermediateField.lift
              (IntermediateField.fixedField
                (Subgroup.map
                  (@AlgEquiv.restrictNormalHom
                    ℚ _ (SeparableClosure ℚ) _ _
                    rationalCyclotomicZHatField _
                    rationalCyclotomicZHatField.algebra' _ _
                    rationalCyclotomicZHatField_normal)
                  H.toSubgroup))
        exact
          @InfiniteGalois.restrict_fixedField
            ℚ (SeparableClosure ℚ) _ _ _ H.toSubgroup
            rationalCyclotomicZHatField
            rationalCyclotomicZHatField_normal
  have hfix :
      E.fixingSubgroup = R.toSubgroup := by
    rw [hE]
    exact InfiniteGalois.fixingSubgroup_fixedField R
  exact hfix.symm

/-- The degree image of a closed subgroup of the rational absolute
Galois group is the subgroup of `ZHat` fixing the intersection of its
concrete fixed field with the actual cyclotomic `ZHat`-extension. -/
theorem
    rationalCyclotomicDegreeData_fieldImage_eq_intersection_fixingSubgroup :
    ∀ H : ClosedSubgroup
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ),
      rationalCyclotomicDegreeData.fieldImage H =
        (((LocalClassFieldTheory.abstractFixedField
              ℚ (SeparableClosure ℚ) H) ⊓
            rationalCyclotomicZHatField).restrict
          (show
            LocalClassFieldTheory.abstractFixedField
                  ℚ (SeparableClosure ℚ) H ⊓
                rationalCyclotomicZHatField ≤
              rationalCyclotomicZHatField from
            inf_le_right)).fixingSubgroup.map
              rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom := by
  intro H
  rw [rationalCyclotomicDegreeData.fieldImage_eq_map]
  change
    H.toSubgroup.map
        (rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom.comp
          rationalAbsoluteGaloisRestrictionToCyclotomicZHat.toMonoidHom) =
      (((LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H) ⊓
          rationalCyclotomicZHatField).restrict
        (show
          LocalClassFieldTheory.abstractFixedField
                ℚ (SeparableClosure ℚ) H ⊓
              rationalCyclotomicZHatField ≤
            rationalCyclotomicZHatField from
          inf_le_right)).fixingSubgroup.map
        rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom
  rw [← Subgroup.map_map,
    rationalAbsoluteGaloisRestriction_image_eq_intersection_fixingSubgroup]

/-- For a finite abstract rational field, the residue degree supplied
by the actual cyclotomic degree datum is the degree of the concrete
intersection with the cyclotomic `ZHat`-extension. -/
theorem
    rationalCyclotomicDegreeData_residueDegree_eq_intersection_finrank
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    (H.residueDegree rationalCyclotomicDegreeData : ℕ) =
      Module.finrank ℚ
        ((LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field ⊓
          rationalCyclotomicZHatField :
            IntermediateField ℚ (SeparableClosure ℚ))) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let J : IntermediateField ℚ (SeparableClosure ℚ) :=
    F ⊓ rationalCyclotomicZHatField
  let hJT : J ≤ rationalCyclotomicZHatField :=
    inf_le_right
  let E : IntermediateField ℚ rationalCyclotomicZHatField :=
    J.restrict hJT
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : FiniteDimensional ℚ J :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion
        (show J ≤ F from inf_le_left)).toLinearMap
      (IntermediateField.inclusion
        (show J ≤ F from inf_le_left)).injective
  let : FiniteDimensional ℚ E :=
    ((IntermediateField.restrictAlgEquiv hJT).toLinearEquiv).finiteDimensional
  let HR :=
    H.toFiniteResidueAbstractField
      rationalCyclotomicDegreeData
  let : Finite
      (rationalCyclotomicDegreeData.residueQuotient
        H.field) :=
    HR.finiteResidueQuotient
  have hindex :
      (rationalCyclotomicDegreeData.fieldImage
        H.field).index =
          Module.finrank ℚ J := by
    rw [
      rationalCyclotomicDegreeData_fieldImage_eq_intersection_fixingSubgroup
        H.field]
    change
      (E.fixingSubgroup.map
        rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom).index =
          Module.finrank ℚ J
    calc
      (E.fixingSubgroup.map
          rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom).index =
          E.fixingSubgroup.index :=
        Subgroup.index_map_equiv E.fixingSubgroup
          rationalCyclotomicZHatFieldGalEquivZHat.toMulEquiv
      _ = Module.finrank ℚ E :=
        (IntermediateField.finrank_eq_fixingSubgroup_index rationalCyclotomicZHatField E).symm
      _ = Module.finrank ℚ J := by
        change Module.finrank ℚ (J.restrict hJT) = Module.finrank ℚ J
        exact
          ((IntermediateField.restrictAlgEquiv hJT).toLinearEquiv).finrank_eq.symm
  let :
      (rationalCyclotomicDegreeData.fieldImage
        HR.field).IsFiniteRelIndex
          (⊤ : Subgroup ZHatMul) :=
    ⟨by
      change
        (rationalCyclotomicDegreeData.fieldImage H.field).relIndex
            (⊤ : Subgroup ZHatMul) ≠ 0
      rw [Subgroup.relIndex_top_right, hindex]
      exact Module.finrank_pos.ne'⟩
  apply Nat.cast_injective (R := Cardinal)
  change
    ((H.residueDegree
      rationalCyclotomicDegreeData : ℕ) : Cardinal) =
        (Module.finrank ℚ J : Cardinal)
  rw [show
      H.residueDegree rationalCyclotomicDegreeData =
        HR.residueDegree from rfl,
    ← HR.residueDegreeCardinal_eq_coe,
    DegreeData.residueDegreeCardinal,
    relativeIndexCardinal_eq_index_of_finite
      (show rationalCyclotomicDegreeData.fieldImage HR.field ≤
        (⊤ : Subgroup ZHatMul) from le_top)]
  norm_cast
  simpa only [HR, FiniteAbstractField.toFiniteResidueAbstractField,
    Subgroup.relIndex_top_right] using hindex

/-- The degree of the intersection with the rational cyclotomic
`ZHat`-extension does not depend on the chosen embedding of an
abstract fixed field into `SeparableClosure ℚ`.

The proof extends the embedding to an automorphism of the separable
closure.  That automorphism preserves the cyclotomic `ZHat`-field
because the latter is normal over `ℚ`, and hence carries the canonical
intersection onto the intersection formed with the chosen image. -/
theorem
    abstractFixedFieldCyclotomicZHatIntersection_finrank_eq_of_embedding
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (ι :
      LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field →ₐ[ℚ]
        SeparableClosure ℚ) :
    Module.finrank ℚ
        ((ι.fieldRange ⊓ rationalCyclotomicZHatField :
          IntermediateField ℚ (SeparableClosure ℚ))) =
      Module.finrank ℚ
        ((LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field ⊓
          rationalCyclotomicZHatField :
            IntermediateField ℚ (SeparableClosure ℚ))) := by
  let K :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let T := rationalCyclotomicZHatField
  let J : IntermediateField ℚ (SeparableClosure ℚ) :=
    K ⊓ T
  let Jι : IntermediateField ℚ (SeparableClosure ℚ) :=
    ι.fieldRange ⊓ T
  let : FiniteDimensional ℚ K :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : FiniteDimensional ℚ J :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion
        (show J ≤ K from inf_le_left)).toLinearMap
      (IntermediateField.inclusion
        (show J ≤ K from inf_le_left)).injective
  let : FiniteDimensional ℚ ι.fieldRange :=
    (ι.equivFieldRange.toLinearEquiv).finiteDimensional
  let : FiniteDimensional ℚ Jι :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion
        (show Jι ≤ ι.fieldRange from inf_le_left)).toLinearMap
      (IntermediateField.inclusion
        (show Jι ≤ ι.fieldRange from inf_le_left)).injective
  let σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ :=
    AlgEquiv.ofBijective
      (ι.liftNormal (SeparableClosure ℚ))
      (AlgHom.normal_bijective
        ℚ (SeparableClosure ℚ) (SeparableClosure ℚ) _)
  have hσK (x : K) :
      σ (x : SeparableClosure ℚ) = ι x := by
    dsimp only [σ]
    rw [AlgEquiv.ofBijective_apply]
    simpa only [IntermediateField.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using
      ι.liftNormal_commutes (SeparableClosure ℚ) x
  have hmapK :
      K.map σ.toAlgHom = ι.fieldRange := by
    ext y
    constructor
    · rw [IntermediateField.mem_map]
      rintro ⟨x, hx, hxy⟩
      rw [AlgHom.mem_fieldRange]
      exact
        ⟨⟨x, hx⟩,
          (hσK ⟨x, hx⟩).symm.trans hxy⟩
    · rw [AlgHom.mem_fieldRange]
      rintro ⟨x, hxy⟩
      rw [IntermediateField.mem_map]
      exact
        ⟨(x : SeparableClosure ℚ), x.property,
          (hσK x).trans hxy⟩
  have hmapT :
      T.map σ.toAlgHom = T :=
    (IntermediateField.normal_iff_forall_map_eq'.1
      (by
        simpa only [T] using rationalCyclotomicZHatField_normal)) σ
  have hmapJ :
      J.map σ.toAlgHom = Jι := by
    dsimp only [J, Jι]
    rw [IntermediateField.map_inf, hmapK, hmapT]
  let e : J ≃ₐ[ℚ] Jι :=
    (IntermediateField.equivMap J σ.toAlgHom).trans
      (IntermediateField.equivOfEq hmapJ)
  exact e.toLinearEquiv.finrank_eq.symm

/-- The Galois group of the actual `ZHat`-extension of `ℚ` is
torsion-free.  This is the property that removes every archimedean
order-two Artin factor in the normalized reciprocity construction. -/
noncomputable instance rationalCyclotomicZHatFieldGal_isMulTorsionFree :
    IsMulTorsionFree
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
  Function.Injective.isMulTorsionFree
    rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom
    rationalCyclotomicZHatFieldGalEquivZHat.injective

variable (K : Type*) [Field K] [NumberField K]

/-- The finite intersection `K ∩ ℚ_tilde` inside the common separable
closure. -/
def numberFieldCyclotomicZHatIntersection :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  numberFieldInRationalSeparableClosure K ⊓
    rationalCyclotomicZHatField

/-- The intersection `K ∩ ℚ_tilde`, embedded back into the original number
field through the chosen copy of `K` in `SeparableClosure ℚ`. -/
noncomputable def numberFieldCyclotomicZHatIntersectionEmbedding :
    numberFieldCyclotomicZHatIntersection K →ₐ[ℚ] K :=
  (numberFieldSeparableClosureEmbedding K).equivFieldRange.symm.toAlgHom.comp
    (IntermediateField.inclusion inf_le_left)

/-- The embedding of the cyclotomic intersection into `K` commutes with
the chosen embedding of `K` into the rational separable closure. -/
@[simp]
theorem numberFieldCyclotomicZHatIntersectionEmbedding_commutes
    (x : numberFieldCyclotomicZHatIntersection K) :
    numberFieldSeparableClosureEmbedding K
        (numberFieldCyclotomicZHatIntersectionEmbedding K x) =
      (x : SeparableClosure ℚ) := by
  change
    (((numberFieldSeparableClosureEmbedding K).equivFieldRange
      ((numberFieldSeparableClosureEmbedding K).equivFieldRange.symm
        ((IntermediateField.inclusion inf_le_left) x)) :
        numberFieldInRationalSeparableClosure K) :
      SeparableClosure ℚ) =
        (x : SeparableClosure ℚ)
  rw [AlgEquiv.apply_symm_apply]
  rfl

noncomputable instance
    numberFieldCyclotomicZHatIntersection_finiteDimensional :
    FiniteDimensional ℚ
      (numberFieldCyclotomicZHatIntersection K) := by
  let f :
      numberFieldCyclotomicZHatIntersection K →ₐ[ℚ]
        numberFieldInRationalSeparableClosure K :=
    (IntermediateField.inclusion
      (show
        numberFieldCyclotomicZHatIntersection K ≤
          numberFieldInRationalSeparableClosure K from
        inf_le_left))
  exact FiniteDimensional.of_injective f.toLinearMap f.injective

noncomputable instance
    numberFieldCyclotomicZHatIntersection_numberField :
    NumberField (numberFieldCyclotomicZHatIntersection K) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

noncomputable instance
    numberFieldCyclotomicZHatIntersection_isAbelianGalois :
    IsAbelianGalois ℚ
      (numberFieldCyclotomicZHatIntersection K) := by
  exact @IsAbelianGalois.of_algHom
    ℚ (numberFieldCyclotomicZHatIntersection K)
      rationalCyclotomicZHatField
    _ _ _ _ _
    (IntermediateField.inclusion
      (show
        numberFieldCyclotomicZHatIntersection K ≤
          rationalCyclotomicZHatField from
        inf_le_right))
    rationalCyclotomicZHatField_isAbelianGalois

/-- The cyclotomic intersection degree
`f_K = [K ∩ ℚ_tilde : ℚ]`. -/
noncomputable def cyclotomicZHatIntersectionDegree : ℕ :=
  Module.finrank ℚ (numberFieldCyclotomicZHatIntersection K)

/-- For an abstract fixed field, the intersection degree computed
using `numberFieldSeparableClosureEmbedding` is the degree of the
canonical intersection already present in the rational absolute
Galois correspondence. -/
theorem
    cyclotomicZHatIntersectionDegree_abstractFixedField_eq_intersection_finrank
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    cyclotomicZHatIntersectionDegree F =
      Module.finrank ℚ
        ((F ⊓ rationalCyclotomicZHatField :
          IntermediateField ℚ (SeparableClosure ℚ))) := by
  dsimp only
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  change
    Module.finrank ℚ
        (numberFieldCyclotomicZHatIntersection F) =
      Module.finrank ℚ
        ((F ⊓ rationalCyclotomicZHatField :
          IntermediateField ℚ (SeparableClosure ℚ)))
  change
    Module.finrank ℚ
        (((numberFieldSeparableClosureEmbedding F).fieldRange ⊓
          rationalCyclotomicZHatField :
          IntermediateField ℚ (SeparableClosure ℚ))) =
      Module.finrank ℚ
        ((LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field ⊓ rationalCyclotomicZHatField :
          IntermediateField ℚ (SeparableClosure ℚ)))
  exact
    abstractFixedFieldCyclotomicZHatIntersection_finrank_eq_of_embedding
      H (numberFieldSeparableClosureEmbedding F)

/-- The concrete intersection degree of an abstract fixed field,
formed using the arbitrary chosen number-field embedding, is exactly
the residue degree supplied by `rationalCyclotomicDegreeData`. -/
theorem
    cyclotomicZHatIntersectionDegree_abstractFixedField_eq_residueDegree
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    cyclotomicZHatIntersectionDegree F =
      (H.residueDegree rationalCyclotomicDegreeData : ℕ) := by
  exact
    (cyclotomicZHatIntersectionDegree_abstractFixedField_eq_intersection_finrank
      H).trans
      (rationalCyclotomicDegreeData_residueDegree_eq_intersection_finrank
        H).symm

/-- The cyclotomic intersection degree is positive. -/
theorem cyclotomicZHatIntersectionDegree_pos :
    0 < cyclotomicZHatIntersectionDegree K :=
  Module.finrank_pos

/-- The intersection degree divides the absolute degree of the number
field. -/
theorem cyclotomicZHatIntersectionDegree_dvd_finrank :
    cyclotomicZHatIntersectionDegree K ∣
      Module.finrank ℚ K := by
  have h :
      Module.finrank ℚ
          (numberFieldCyclotomicZHatIntersection K) ∣
        Module.finrank ℚ
          (numberFieldInRationalSeparableClosure K) :=
    IntermediateField.finrank_dvd_of_le_right
      (show
        numberFieldCyclotomicZHatIntersection K ≤
          numberFieldInRationalSeparableClosure K from
        inf_le_left)
  rw [numberFieldInRationalSeparableClosure] at h
  rw [←
    ((numberFieldSeparableClosureEmbedding K).equivFieldRange.toLinearEquiv).finrank_eq] at h
  simpa only [cyclotomicZHatIntersectionDegree] using h

/-- Under the actual Galois identification with `ZHat`, the
subgroup fixing `K ∩ ℚ_tilde` is precisely
`f_K ZHat`, where `f_K = [K ∩ ℚ_tilde : ℚ]`. -/
theorem
    rationalCyclotomicZHatFieldGal_fixingSubgroup_image_eq_mulNat_range :
    (((numberFieldCyclotomicZHatIntersection K).restrict
          (show
            numberFieldCyclotomicZHatIntersection K ≤
              rationalCyclotomicZHatField from
            inf_le_right)).fixingSubgroup.map
        rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom).toAddSubgroup' =
      (zHatMulNat
        (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range := by
  let hle :
      numberFieldCyclotomicZHatIntersection K ≤
        rationalCyclotomicZHatField :=
    inf_le_right
  let E : IntermediateField ℚ rationalCyclotomicZHatField :=
    (numberFieldCyclotomicZHatIntersection K).restrict hle
  let e :=
    rationalCyclotomicZHatFieldGalEquivZHat
  change
    (E.fixingSubgroup.map
      e.toMonoidHom).toAddSubgroup' =
        (zHatMulNat
          (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range
  refine
    zHatAddSubgroup_eq_mulNat_range_of_index_eq
      (E.fixingSubgroup.map
        e.toMonoidHom).toAddSubgroup'
      (cyclotomicZHatIntersectionDegree_pos K) ?_
  change
    (E.fixingSubgroup.map e.toMonoidHom).index =
      cyclotomicZHatIntersectionDegree K
  calc
    (E.fixingSubgroup.map e.toMonoidHom).index = E.fixingSubgroup.index :=
      Subgroup.index_map_equiv E.fixingSubgroup e.toMulEquiv
    _ = Module.finrank ℚ E :=
      (IntermediateField.finrank_eq_fixingSubgroup_index rationalCyclotomicZHatField E).symm
    _ = cyclotomicZHatIntersectionDegree K := by
      change
        Module.finrank ℚ
            ((numberFieldCyclotomicZHatIntersection K).restrict hle) =
          Module.finrank ℚ (numberFieldCyclotomicZHatIntersection K)
      exact
        ((IntermediateField.restrictAlgEquiv hle).toLinearEquiv).finrank_eq.symm

/-- The actual compositum of the chosen copy of `K` with a finite
Galois layer of the rational cyclotomic `ZHat`-extension. -/
def numberFieldCyclotomicZHatFiniteCompositum
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  numberFieldInRationalSeparableClosure K ⊔
    IntermediateField.lift E.toIntermediateField

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositum_finiteDimensional
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional ℚ
      (numberFieldCyclotomicZHatFiniteCompositum K E) := by
  let : FiniteDimensional ℚ (IntermediateField.lift E.toIntermediateField) :=
    ((IntermediateField.liftAlgEquiv E.toIntermediateField).toLinearEquiv).finiteDimensional
  exact
    IntermediateField.finiteDimensional_sup
      (numberFieldInRationalSeparableClosure K)
      (IntermediateField.lift E.toIntermediateField)

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositum_numberField
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  NumberField.of_module_finite ℚ
    (numberFieldCyclotomicZHatFiniteCompositum K E)

/-- The chosen embedding of `K` into each finite cyclotomic
compositum. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteCompositumEmbedding
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    K →ₐ[ℚ] numberFieldCyclotomicZHatFiniteCompositum K E :=
  (numberFieldSeparableClosureEmbedding K).codRestrict
    (numberFieldCyclotomicZHatFiniteCompositum K E).toSubalgebra
    (fun x =>
      (show numberFieldInRationalSeparableClosure K ≤
          numberFieldCyclotomicZHatFiniteCompositum K E from
        le_sup_left)
        (show numberFieldSeparableClosureEmbedding K x ∈
            numberFieldInRationalSeparableClosure K from
          (AlgHom.mem_fieldRange).mpr ⟨x, rfl⟩))

/-- A finite cyclotomic layer embedded into its compositum with `K`. -/
noncomputable def
    rationalCyclotomicZHatFiniteLayerCompositumEmbedding
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    E →ₐ[ℚ] numberFieldCyclotomicZHatFiniteCompositum K E :=
  (IntermediateField.inclusion le_sup_right).comp
    (IntermediateField.liftAlgEquiv E.toIntermediateField).toAlgHom

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositumAlgebra
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra K
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  (numberFieldCyclotomicZHatFiniteCompositumEmbedding K E).toRingHom.toAlgebra

noncomputable instance
    rationalCyclotomicZHatFiniteLayerCompositumAlgebra
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra E
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  (rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E).toRingHom.toAlgebra

/-- The scalar action on the finite compositum induced by its actual
finite-layer embedding.  Declaring it directly avoids asking instance search
to rediscover the action through an unrelated intermediate-field algebra. -/
noncomputable instance
    rationalCyclotomicZHatFiniteLayerCompositumSmul
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul E
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  (rationalCyclotomicZHatFiniteLayerCompositumAlgebra K E).toSMul

/-- The actual intersection `K ∩ E` inside the finite compositum,
transported back to the finite cyclotomic layer `E`. -/
def numberFieldCyclotomicZHatFiniteIntersection
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IntermediateField ℚ E :=
  IntermediateField.comap
    (rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E)
    (numberFieldCyclotomicZHatFiniteCompositumEmbedding K E).fieldRange

/-- An element of the finite-layer intersection is, in the common
separable closure, an element of the full intersection `K ∩ ℚ_tilde`. -/
theorem
    numberFieldCyclotomicZHatFiniteIntersection_coe_mem_intersection
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (x : E)
    (hx :
      x ∈ numberFieldCyclotomicZHatFiniteIntersection K E) :
    ((((x : E) : rationalCyclotomicZHatField) :
        SeparableClosure ℚ)) ∈
      numberFieldCyclotomicZHatIntersection K := by
  let C :=
    numberFieldCyclotomicZHatFiniteCompositum K E
  let eK : K →ₐ[ℚ] C :=
    numberFieldCyclotomicZHatFiniteCompositumEmbedding K E
  let eE : E →ₐ[ℚ] C :=
    rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E
  change eE x ∈ eK.fieldRange at hx
  rw [AlgHom.mem_fieldRange] at hx
  obtain ⟨k, hk⟩ := hx
  have hkΩ :
      numberFieldSeparableClosureEmbedding K k =
        ((((x : E) : rationalCyclotomicZHatField) :
          SeparableClosure ℚ)) := by
    have h := congrArg (fun y : C => y.1) hk
    change numberFieldSeparableClosureEmbedding K k =
      ((((x : E) : rationalCyclotomicZHatField) :
        SeparableClosure ℚ)) at h
    exact h
  constructor
  · exact ⟨k, hkΩ⟩
  · exact ((x : E) : rationalCyclotomicZHatField).property

private theorem sup_restrict_sup_eq_top
    {R Ω : Type*} [Field R] [Field Ω] [Algebra R Ω]
    (A B : IntermediateField R Ω) :
    B.restrict (show B ≤ A ⊔ B from le_sup_right) ⊔
      A.restrict (show A ≤ A ⊔ B from le_sup_left) = ⊤ := by
  apply IntermediateField.lift_injective (A ⊔ B)
  rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
    IntermediateField.lift_restrict, IntermediateField.lift_top]
  exact sup_comm _ _

instance
    numberFieldCyclotomicZHatFiniteCompositum_scalarTower
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ K
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  IsScalarTower.of_algebraMap_eq'
    ((numberFieldCyclotomicZHatFiniteCompositumEmbedding K E).comp_algebraMap.symm)

instance
    rationalCyclotomicZHatFiniteLayerCompositum_scalarTower
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ E
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  IsScalarTower.of_algebraMap_eq'
    ((rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E).comp_algebraMap.symm)

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositum_finiteDimensional_over_K
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional K
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  FiniteDimensional.right ℚ K
    (numberFieldCyclotomicZHatFiniteCompositum K E)

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositum_finiteDimensional_over_layer
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional E
      (numberFieldCyclotomicZHatFiniteCompositum K E) := by
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : Algebra E
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
    ((rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E).toRingHom).toAlgebra
  let : Module E
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
    Algebra.toModule
  let : IsScalarTower ℚ E
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
    rationalCyclotomicZHatFiniteLayerCompositum_scalarTower K E
  exact
    FiniteDimensional.right ℚ E
      (numberFieldCyclotomicZHatFiniteCompositum K E)

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositum_isGalois
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsGalois K
      (numberFieldCyclotomicZHatFiniteCompositum K E) := by
  let C :=
    numberFieldCyclotomicZHatFiniteCompositum K E
  let : Algebra ℚ C := C.algebra'
  let A : IntermediateField ℚ C :=
    (numberFieldInRationalSeparableClosure K).restrict
      (show
        numberFieldInRationalSeparableClosure K ≤ C from
        le_sup_left)
  let B : IntermediateField ℚ C :=
    (IntermediateField.lift E.toIntermediateField).restrict
      (show IntermediateField.lift E.toIntermediateField ≤ C from le_sup_right)
  let : Algebra ℚ B := B.algebra'
  let eK : K ≃ₐ[ℚ] A :=
    (numberFieldSeparableClosureEmbedding K).equivFieldRange.trans
      (IntermediateField.restrictAlgEquiv le_sup_left)
  let eE : E ≃ₐ[ℚ] B :=
    (IntermediateField.liftAlgEquiv E.toIntermediateField).trans
      (IntermediateField.restrictAlgEquiv le_sup_right)
  let hE : IsGalois ℚ E := E.isGalois
  let : IsGalois ℚ E := hE
  let hfiniteB : FiniteDimensional ℚ B :=
    eE.toLinearEquiv.finiteDimensional
  let hB : IsGalois ℚ B :=
    @IsGalois.of_algEquiv ℚ E _ _ B _ _ _ hE eE
  let : FiniteDimensional ℚ B := hfiniteB
  let : IsGalois ℚ B := hB
  have hsup : B ⊔ A = ⊤ := sup_restrict_sup_eq_top _ _
  let : IsGalois A C :=
    @IsGalois.sup_right ℚ _ C _ _ B A hB hfiniteB hsup
  refine
    @IsGalois.of_equiv_equiv A C _ _ _ K C _ _ _ (by infer_instance)
      eK.symm.toRingEquiv (RingEquiv.refl C) ?_
  ext x
  have heK (y : K) :
      algebraMap K C y = algebraMap A C (eK y) := by
    apply Subtype.ext
    rfl
  simpa using
    congrArg (fun z : C => (z : SeparableClosure ℚ)) (heK (eK.symm x))

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositum_isAbelianGalois
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois K
      (numberFieldCyclotomicZHatFiniteCompositum K E) := by
  let C :=
    numberFieldCyclotomicZHatFiniteCompositum K E
  let : Algebra ℚ C := C.algebra'
  let A : IntermediateField ℚ C :=
    (numberFieldInRationalSeparableClosure K).restrict
      (show
        numberFieldInRationalSeparableClosure K ≤ C from
        le_sup_left)
  let B : IntermediateField ℚ C :=
    (IntermediateField.lift E.toIntermediateField).restrict
      (show IntermediateField.lift E.toIntermediateField ≤ C from le_sup_right)
  let : Algebra ℚ B := B.algebra'
  let eK : K ≃ₐ[ℚ] A :=
    (numberFieldSeparableClosureEmbedding K).equivFieldRange.trans
      (IntermediateField.restrictAlgEquiv le_sup_left)
  let eE : E ≃ₐ[ℚ] B :=
    (IntermediateField.liftAlgEquiv E.toIntermediateField).trans
      (IntermediateField.restrictAlgEquiv le_sup_right)
  let hE : IsGalois ℚ E := E.isGalois
  let : IsGalois ℚ E := hE
  let hfiniteB : FiniteDimensional ℚ B :=
    eE.toLinearEquiv.finiteDimensional
  let : IsAbelianGalois ℚ E :=
    IsAbelianGalois.tower_bot ℚ E rationalCyclotomicZHatField
  let hB : IsAbelianGalois ℚ B :=
    @IsAbelianGalois.of_algHom ℚ B E _ _ _ _ _ eE.symm.toAlgHom
      (IsAbelianGalois.tower_bot ℚ E rationalCyclotomicZHatField)
  let : FiniteDimensional ℚ B := hfiniteB
  let : IsAbelianGalois ℚ B := hB
  have hsup : B ⊔ A = ⊤ := sup_restrict_sup_eq_top _ _
  let : IsGalois A C :=
    @IsGalois.sup_right ℚ _ C _ _ B A hB.toIsGalois hfiniteB hsup
  let r :
      (C ≃ₐ[A] C) →* (B ≃ₐ[ℚ] B) :=
    IntermediateField.restrictRestrictAlgEquivMapHom
      ℚ B A C
  have hr : Function.Injective r :=
    IntermediateField.restrictRestrictAlgEquivMapHom_injective B A hsup
  let : IsAbelianGalois A C :=
    { is_comm.comm := fun σ τ => by
        apply hr
        calc
          r (σ * τ) = r σ * r τ := r.map_mul σ τ
          _ = r τ * r σ := IsMulCommutative.is_comm.comm _ _
          _ = r (τ * σ) := (r.map_mul τ σ).symm }
  have heK (x : K) :
      algebraMap K C x =
        algebraMap A C (eK x) := by
    apply Subtype.ext
    rfl
  let changeBase :
      (C ≃ₐ[K] C) →* (C ≃ₐ[A] C) :=
    { toFun := fun σ =>
        { σ.toRingEquiv with
          commutes' := by
            intro y
            have hy :
                algebraMap K C (eK.symm y) =
                  algebraMap A C y := by
              simpa using heK (eK.symm y)
            rw [← hy]
            change σ (algebraMap K C (eK.symm y)) =
              algebraMap K C (eK.symm y)
            exact σ.commutes _ }
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hchangeBase :
      Function.Injective changeBase := by
    intro σ τ hστ
    apply AlgEquiv.ext
    intro x
    exact
      congrArg
        (fun f : C ≃ₐ[A] C => f x)
        hστ
  exact
    { is_comm.comm := fun σ τ => by
        apply hchangeBase
        calc
          changeBase (σ * τ) = changeBase σ * changeBase τ :=
            changeBase.map_mul σ τ
          _ = changeBase τ * changeBase σ := IsMulCommutative.is_comm.comm _ _
          _ = changeBase (τ * σ) := (changeBase.map_mul τ σ).symm }

/-- Restriction from the actual finite compositum over `K` has image
exactly the subgroup of `Gal(E/ℚ)` fixing the actual intersection
`K ∩ E`. -/
theorem
    numberFieldCyclotomicZHatFiniteCompositum_restriction_range
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    letI : Normal ℚ E := E.isGalois.to_normal
    let C :=
      numberFieldCyclotomicZHatFiniteCompositum K E
    (IntermediateField.restrictRestrictAlgEquivMapHom
        ℚ E K C).range =
      (numberFieldCyclotomicZHatFiniteIntersection K E).fixingSubgroup := by
  let : Normal ℚ E := E.isGalois.to_normal
  let C :=
    numberFieldCyclotomicZHatFiniteCompositum K E
  let : Algebra ℚ C := C.algebra'
  let : Algebra K C :=
    numberFieldCyclotomicZHatFiniteCompositumAlgebra K E
  let : IsScalarTower ℚ K C :=
    numberFieldCyclotomicZHatFiniteCompositum_scalarTower K E
  let : Algebra E C :=
    rationalCyclotomicZHatFiniteLayerCompositumAlgebra K E
  let : IsScalarTower ℚ E C :=
    rationalCyclotomicZHatFiniteLayerCompositum_scalarTower K E
  let eK : K →ₐ[ℚ] C :=
    numberFieldCyclotomicZHatFiniteCompositumEmbedding K E
  let eE : E →ₐ[ℚ] C :=
    rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E
  let r :
      (C ≃ₐ[K] C) →* (E ≃ₐ[ℚ] E) :=
    IntermediateField.restrictRestrictAlgEquivMapHom
      ℚ E K C
  let J : IntermediateField ℚ E :=
    numberFieldCyclotomicZHatFiniteIntersection K E
  have restriction_commutes
      (τ : C ≃ₐ[K] C) (x : E) :
      eE (r τ x) = τ (eE x) := by
    change algebraMap E C (r τ x) = τ (algebraMap E C x)
    change
      algebraMap E C
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ C τ) E) x) =
        (MulSemiringAction.toAlgEquiv ℚ C τ) (algebraMap E C x)
    exact AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv ℚ C τ) E x
  have hfixedField :
      IntermediateField.fixedField r.range = J := by
    ext x
    rw [IntermediateField.mem_fixedField_iff]
    change
      (∀ σ, σ ∈ r.range → σ x = x) ↔
        eE x ∈ eK.fieldRange
    constructor
    · intro hx
      have hfixed :
          ∀ τ : C ≃ₐ[K] C, τ (eE x) = eE x := by
        intro τ
        have hxτ :
            r τ x = x :=
          hx (r τ) ⟨τ, rfl⟩
        have hrestrict :
            eE (r τ x) = τ (eE x) := by
          exact restriction_commutes τ x
        exact hrestrict.symm.trans (congrArg eE hxτ)
      have hmem :
          eE x ∈ Set.range (algebraMap K C) :=
        (IsGalois.mem_range_algebraMap_iff_fixed
          (eE x)).2 hfixed
      rw [AlgHom.mem_fieldRange]
      obtain ⟨k, hk⟩ := hmem
      refine ⟨k, ?_⟩
      change algebraMap K C k = eE x
      exact hk
    · intro hx σ hσ
      obtain ⟨τ, rfl⟩ := hσ
      rw [AlgHom.mem_fieldRange] at hx
      obtain ⟨k, hk⟩ := hx
      apply eE.injective
      change eE (r τ x) = eE x
      have hrestrict :
          eE (r τ x) = τ (eE x) := by
        exact restriction_commutes τ x
      rw [hrestrict, ← hk]
      change τ (algebraMap K C k) = algebraMap K C k
      exact τ.commutes k
  calc
    r.range =
        (IntermediateField.fixedField r.range).fixingSubgroup :=
      (IntermediateField.fixingSubgroup_fixedField
        r.range).symm
    _ = J.fixingSubgroup := by rw [hfixedField]

/-- The actual compositum `Kℚ_tilde` inside `SeparableClosure ℚ`. -/
def numberFieldCyclotomicZHatCompositum :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  numberFieldInRationalSeparableClosure K ⊔
    rationalCyclotomicZHatField

/-- The chosen copy of `K` embedded into its actual cyclotomic
`ZHat`-compositum. -/
noncomputable def numberFieldCyclotomicZHatCompositumEmbedding :
    K →ₐ[ℚ] numberFieldCyclotomicZHatCompositum K :=
  (numberFieldSeparableClosureEmbedding K).codRestrict
    (numberFieldCyclotomicZHatCompositum K).toSubalgebra
    (fun x =>
      (show numberFieldInRationalSeparableClosure K ≤
          numberFieldCyclotomicZHatCompositum K from
        le_sup_left)
        (show numberFieldSeparableClosureEmbedding K x ∈
            numberFieldInRationalSeparableClosure K from
          (AlgHom.mem_fieldRange).mpr ⟨x, rfl⟩))

/-- The compositum embedding preserves the chosen separable-closure representative. -/
theorem numberFieldCyclotomicZHatCompositumEmbedding_coe (x : K) :
    (numberFieldCyclotomicZHatCompositumEmbedding K x : SeparableClosure ℚ) =
      numberFieldSeparableClosureEmbedding K x := rfl

/-- The rational cyclotomic `ZHat`-field embedded into its compositum
with `K`. -/
noncomputable def rationalCyclotomicZHatCompositumEmbedding :
    rationalCyclotomicZHatField →ₐ[ℚ]
      numberFieldCyclotomicZHatCompositum K :=
  IntermediateField.inclusion le_sup_right

noncomputable instance numberFieldCyclotomicZHatCompositumAlgebra :
    Algebra K (numberFieldCyclotomicZHatCompositum K) :=
  ((numberFieldCyclotomicZHatCompositumEmbedding K).toRingHom).toAlgebra

noncomputable instance rationalCyclotomicZHatCompositumAlgebra :
    Algebra rationalCyclotomicZHatField
      (numberFieldCyclotomicZHatCompositum K) :=
  ((rationalCyclotomicZHatCompositumEmbedding K).toRingHom).toAlgebra

instance numberFieldCyclotomicZHatCompositum_scalarTower :
    IsScalarTower ℚ K
      (numberFieldCyclotomicZHatCompositum K) :=
  IsScalarTower.of_algebraMap_eq'
    ((numberFieldCyclotomicZHatCompositumEmbedding K).comp_algebraMap.symm)

instance rationalCyclotomicZHatCompositum_scalarTower :
    IsScalarTower ℚ rationalCyclotomicZHatField
      (numberFieldCyclotomicZHatCompositum K) :=
  IsScalarTower.of_algebraMap_eq'
    ((rationalCyclotomicZHatCompositumEmbedding K).comp_algebraMap.symm)

noncomputable instance
    numberFieldCyclotomicZHatCompositum_isGalois :
    IsGalois K (numberFieldCyclotomicZHatCompositum K) := by
  let A : IntermediateField ℚ (SeparableClosure ℚ) :=
    numberFieldInRationalSeparableClosure K
  let : Algebra A (SeparableClosure ℚ) := A.val.toAlgebra
  let rationalCyclotomicZHatFieldIsGalois :
      IsGalois ℚ rationalCyclotomicZHatField :=
    rationalCyclotomicZHatField_isAbelianGalois.toIsGalois
  let C := numberFieldCyclotomicZHatCompositum K
  let eK : K ≃ₐ[ℚ] A :=
    (numberFieldSeparableClosureEmbedding K).equivFieldRange
  have hG :
      ∀ E : FiniteGaloisIntermediateField ℚ rationalCyclotomicZHatField,
        IsGalois A
          (IntermediateField.extendScalars (F := A)
            (E := A ⊔ IntermediateField.lift E.toIntermediateField)
            le_sup_left) := by
    intro E
    let D := numberFieldCyclotomicZHatFiniteCompositum K E
    let hAD : A ≤ D := by
      dsimp only [A, D, numberFieldCyclotomicZHatFiniteCompositum]
      exact le_sup_left
    let : Algebra A D := (IntermediateField.inclusion hAD).toAlgebra
    change IsGalois A (IntermediateField.extendScalars hAD)
    have hcompat (x : K) :
        algebraMap K D x = IntermediateField.inclusion hAD (eK x) := by
      apply Subtype.ext
      rfl
    refine
      IsGalois.of_equiv_equiv
        (F := K) (E := D) (M := A) (N := D)
        (h := by infer_instance)
        (f := eK.toRingEquiv) (g := RingEquiv.refl D) ?_
    apply RingHom.ext
    intro x
    have hADmap (y : A) :
        algebraMap A D y = IntermediateField.inclusion hAD y := by
      rfl
    change algebraMap A D (eK x) = algebraMap K D x
    exact (hADmap (eK x)).trans (hcompat x).symm
  let hAC : A ≤ C := by
    dsimp only [A, C, numberFieldCyclotomicZHatCompositum]
    exact le_sup_left
  let full : IntermediateField A (SeparableClosure ℚ) :=
    IntermediateField.extendScalars hAC
  have hfull0 : IsGalois A
      (IntermediateField.extendScalars (F := A)
        (E := A ⊔ rationalCyclotomicZHatField) le_sup_left) :=
    @IntermediateField.isGalois_extendScalars_sup_of_forall_finiteGalois
      ℚ (SeparableClosure ℚ) _ _ _ A rationalCyclotomicZHatField
      rationalCyclotomicZHatFieldIsGalois hG
  have hfull : IsGalois A full := by
    change IsGalois A
      (IntermediateField.extendScalars (F := A)
        (E := A ⊔ rationalCyclotomicZHatField) le_sup_left)
    exact hfull0
  let : Algebra A C := (IntermediateField.inclusion hAC).toAlgebra
  have hfull' := hfull
  change IsGalois A C at hfull'
  let : IsGalois A C := hfull'
  have hcompat (x : K) :
      algebraMap K C x =
        IntermediateField.inclusion hAC (eK x) := by
    apply Subtype.ext
    rfl
  refine
    IsGalois.of_equiv_equiv
      (F := A) (E := C) (M := K) (N := C)
      (h := hfull')
      (f := eK.symm.toRingEquiv) (g := RingEquiv.refl C) ?_
  apply RingHom.ext
  intro x
  have hACmap (y : A) :
      algebraMap A C y = IntermediateField.inclusion hAC y := by
    rfl
  have hEq : algebraMap K C (eK.symm x) = algebraMap A C x := by
    refine (hcompat (eK.symm x)).trans ?_
    rw [eK.apply_symm_apply]
    exact (hACmap x).symm
  exact hEq

noncomputable instance
    numberFieldCyclotomicZHatCompositum_isAbelianGalois :
    IsAbelianGalois K
      (numberFieldCyclotomicZHatCompositum K) := by
  let C := numberFieldCyclotomicZHatCompositum K
  let : Algebra ℚ C := C.algebra'
  let A : IntermediateField ℚ C :=
    (numberFieldInRationalSeparableClosure K).restrict
      (show
        numberFieldInRationalSeparableClosure K ≤ C from
        le_sup_left)
  let B : IntermediateField ℚ C :=
    rationalCyclotomicZHatField.restrict
      (show rationalCyclotomicZHatField ≤ C from le_sup_right)
  let : Algebra ℚ B := B.algebra'
  let eK : K ≃ₐ[ℚ] A :=
    (numberFieldSeparableClosureEmbedding K).equivFieldRange.trans
      (IntermediateField.restrictAlgEquiv le_sup_left)
  let eT : rationalCyclotomicZHatField ≃ₐ[ℚ] B :=
    IntermediateField.restrictAlgEquiv le_sup_right
  let hB : IsAbelianGalois ℚ B :=
    @IsAbelianGalois.of_algHom ℚ B rationalCyclotomicZHatField
      _ _ _ _ _ eT.symm.toAlgHom
      rationalCyclotomicZHatField_isAbelianGalois
  let : IsAbelianGalois ℚ B := hB
  have hsup : B ⊔ A = ⊤ := sup_restrict_sup_eq_top _ _
  have heK (x : K) :
      algebraMap K C x =
        algebraMap A C (eK x) := by
    apply Subtype.ext
    rfl
  let hAC : IsGalois A C := by
    refine
      @IsGalois.of_equiv_equiv K C _ _ _ A C _ _ _ (by infer_instance)
        eK.toRingEquiv (RingEquiv.refl C) ?_
    ext x
    simpa using
      congrArg (fun z : C => (z : SeparableClosure ℚ)) (heK x).symm
  let : IsGalois A C := hAC
  let r :
      (C ≃ₐ[A] C) →* (B ≃ₐ[ℚ] B) :=
    IntermediateField.restrictRestrictAlgEquivMapHom
      ℚ B A C
  have hr : Function.Injective r :=
    IntermediateField.restrictRestrictAlgEquivMapHom_injective
      B A hsup
  let : IsAbelianGalois A C :=
    { is_comm.comm := fun σ τ => by
        apply hr
        calc
          r (σ * τ) = r σ * r τ := r.map_mul σ τ
          _ = r τ * r σ := IsMulCommutative.is_comm.comm _ _
          _ = r (τ * σ) := (r.map_mul τ σ).symm }
  let changeBase :
      (C ≃ₐ[K] C) →* (C ≃ₐ[A] C) :=
    { toFun := fun σ =>
        { σ.toRingEquiv with
          commutes' := by
            intro y
            have hy :
                algebraMap K C (eK.symm y) =
                  algebraMap A C y := by
              simpa using heK (eK.symm y)
            rw [← hy]
            change σ (algebraMap K C (eK.symm y)) =
              algebraMap K C (eK.symm y)
            exact σ.commutes _ }
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hchangeBase :
      Function.Injective changeBase := by
    intro σ τ hστ
    apply AlgEquiv.ext
    intro x
    exact
      congrArg
        (fun f : C ≃ₐ[A] C => f x)
        hστ
  exact
    { is_comm.comm := fun σ τ => by
        apply hchangeBase
        calc
          changeBase (σ * τ) = changeBase σ * changeBase τ :=
            changeBase.map_mul σ τ
          _ = changeBase τ * changeBase σ := IsMulCommutative.is_comm.comm _ _
          _ = changeBase (τ * σ) :=
            (changeBase.map_mul τ σ).symm }

/-- Inclusion of a finite cyclotomic compositum into the full
cyclotomic `ZHat`-compositum. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteCompositumInclusion
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    numberFieldCyclotomicZHatFiniteCompositum K E →ₐ[ℚ]
      numberFieldCyclotomicZHatCompositum K :=
  IntermediateField.inclusion
    (sup_le_sup le_rfl
      (IntermediateField.lift_le E.toIntermediateField))

/-- Inclusion of a finite compositum preserves its separable-closure representative. -/
theorem numberFieldCyclotomicZHatFiniteCompositumInclusion_coe
    (E : FiniteGaloisIntermediateField ℚ rationalCyclotomicZHatField)
    (x : numberFieldCyclotomicZHatFiniteCompositum K E) :
    (numberFieldCyclotomicZHatFiniteCompositumInclusion K E x : SeparableClosure ℚ) =
      (x : SeparableClosure ℚ) :=
  IntermediateField.coe_inclusion
    (sup_le_sup le_rfl (IntermediateField.lift_le E.toIntermediateField)) x

/-- The same finite-layer inclusion, over the chosen copy of `K`. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteCompositumInclusionOverBase
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    numberFieldCyclotomicZHatFiniteCompositum K E →ₐ[K]
      numberFieldCyclotomicZHatCompositum K := by
  let f :=
    numberFieldCyclotomicZHatFiniteCompositumInclusion K E
  exact
    { f.toRingHom with
      commutes' := by
        intro x
        rfl }

/-- The finite cyclotomic compositum, as an intermediate field of the
full compositum over `K`. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteLayerInCompositum
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IntermediateField K
      (numberFieldCyclotomicZHatCompositum K) :=
  (numberFieldCyclotomicZHatFiniteCompositumInclusionOverBase K E).fieldRange

noncomputable instance
    numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional K
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
  (AlgEquiv.toLinearEquiv
    (AlgHom.equivFieldRange
      (numberFieldCyclotomicZHatFiniteCompositumInclusionOverBase K E))).finiteDimensional

noncomputable instance
    numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois K
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
  IsAbelianGalois.of_algHom
    (AlgEquiv.toAlgHom
      (AlgEquiv.symm
        (AlgHom.equivFieldRange
          (numberFieldCyclotomicZHatFiniteCompositumInclusionOverBase K E))))

noncomputable instance
    numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
  NumberField.of_module_finite K
    (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)

instance
    numberFieldCyclotomicZHatFiniteLayerInCompositum_scalarTower
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ K
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  change algebraMap ℚ (numberFieldCyclotomicZHatCompositum K) x =
    algebraMap K (numberFieldCyclotomicZHatCompositum K)
      (algebraMap ℚ K x)
  exact
    IsScalarTower.algebraMap_apply
      ℚ K (numberFieldCyclotomicZHatCompositum K) x

/-- A finite rational cyclotomic layer embedded into the corresponding
finite intermediate field of the full compositum. -/
noncomputable def
    rationalCyclotomicZHatFiniteLayerInCompositumEmbedding
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    E →ₐ[ℚ]
      numberFieldCyclotomicZHatFiniteLayerInCompositum K E := by
  exact
    (AlgEquiv.toAlgHom
      (AlgEquiv.restrictScalars ℚ
        (AlgHom.equivFieldRange
          (numberFieldCyclotomicZHatFiniteCompositumInclusionOverBase K E)))).comp
      (rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E)

noncomputable instance
    rationalCyclotomicZHatFiniteLayerInCompositumAlgebra
  (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra E
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
  RingHom.toAlgebra
    (AlgHom.toRingHom
      (rationalCyclotomicZHatFiniteLayerInCompositumEmbedding K E))

/-- The finite-layer scalar action on its actual image in the full
compositum. -/
noncomputable instance
    rationalCyclotomicZHatFiniteLayerInCompositumSmul
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul E
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
  Algebra.toSMul
    (self := rationalCyclotomicZHatFiniteLayerInCompositumAlgebra K E)

instance
    rationalCyclotomicZHatFiniteLayerInCompositum_scalarTower
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ E
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
  IsScalarTower.of_algebraMap_eq'
    (AlgHom.comp_algebraMap
      (rationalCyclotomicZHatFiniteLayerInCompositumEmbedding K E)).symm

/-- The corresponding finite layer as an object of the inverse system
of finite Galois subextensions of the full compositum. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteGaloisLayerInCompositum
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteGaloisIntermediateField K
      (numberFieldCyclotomicZHatCompositum K) where
  toIntermediateField :=
    numberFieldCyclotomicZHatFiniteLayerInCompositum K E
  finiteDimensional := inferInstance
  isGalois := inferInstance

/-- Restriction from the cyclotomic compositum over `K` to the rational
cyclotomic `ZHat`-field. -/
noncomputable def numberFieldCyclotomicZHatCompositumRestriction :
    Gal((numberFieldCyclotomicZHatCompositum K)/K) →*
      Gal(rationalCyclotomicZHatField/ℚ) :=
  IntermediateField.restrictRestrictAlgEquivMapHom
    ℚ rationalCyclotomicZHatField K
      (numberFieldCyclotomicZHatCompositum K)

/-- Restriction to the rational cyclotomic factor is injective. -/
theorem numberFieldCyclotomicZHatCompositumRestriction_injective :
    Function.Injective
      (numberFieldCyclotomicZHatCompositumRestriction K) := by
  let C := numberFieldCyclotomicZHatCompositum K
  let : Algebra ℚ C := C.algebra'
  let : Algebra K C := numberFieldCyclotomicZHatCompositumAlgebra K
  let : IsScalarTower ℚ K C :=
    numberFieldCyclotomicZHatCompositum_scalarTower K
  let : Algebra rationalCyclotomicZHatField C :=
    rationalCyclotomicZHatCompositumAlgebra K
  let : IsScalarTower ℚ rationalCyclotomicZHatField C :=
    rationalCyclotomicZHatCompositum_scalarTower K
  let A : IntermediateField ℚ C :=
    (numberFieldInRationalSeparableClosure K).restrict
      (show
        numberFieldInRationalSeparableClosure K ≤ C from
        le_sup_left)
  let B : IntermediateField ℚ C :=
    rationalCyclotomicZHatField.restrict
      (show rationalCyclotomicZHatField ≤ C from le_sup_right)
  let : Algebra ℚ B := B.algebra'
  let eK : K ≃ₐ[ℚ] A :=
    (numberFieldSeparableClosureEmbedding K).equivFieldRange.trans
      (IntermediateField.restrictAlgEquiv le_sup_left)
  let eT : rationalCyclotomicZHatField ≃ₐ[ℚ] B :=
    IntermediateField.restrictAlgEquiv le_sup_right
  let hB : IsAbelianGalois ℚ B :=
    @IsAbelianGalois.of_algHom ℚ B rationalCyclotomicZHatField
      _ _ _ _ _ eT.symm.toAlgHom
      rationalCyclotomicZHatField_isAbelianGalois
  let : IsAbelianGalois ℚ B := hB
  have hsup : B ⊔ A = ⊤ := sup_restrict_sup_eq_top _ _
  let rB :
      (C ≃ₐ[A] C) →* (B ≃ₐ[ℚ] B) :=
    IntermediateField.restrictRestrictAlgEquivMapHom ℚ B A C
  have hrB : Function.Injective rB :=
    IntermediateField.restrictRestrictAlgEquivMapHom_injective B A hsup
  have heK (x : K) :
      algebraMap K C x = algebraMap A C (eK x) := by
    apply Subtype.ext
    rfl
  let changeBase :
      (C ≃ₐ[K] C) →* (C ≃ₐ[A] C) :=
    { toFun := fun σ =>
        { σ.toRingEquiv with
          commutes' := by
            intro y
            have hy :
                algebraMap K C (eK.symm y) =
                  algebraMap A C y := by
              simpa using heK (eK.symm y)
            rw [← hy]
            change σ (algebraMap K C (eK.symm y)) =
              algebraMap K C (eK.symm y)
            exact σ.commutes _ }
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hchangeBase : Function.Injective changeBase := by
    intro σ τ hστ
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun f : C ≃ₐ[A] C => f x) hστ
  let transportT :
      Gal(rationalCyclotomicZHatField/ℚ) →*
        (B ≃ₐ[ℚ] B) :=
    (AlgEquiv.autCongr eT).toMonoidHom
  have raw_restriction_commutes
      (σ : C ≃ₐ[K] C) (x : rationalCyclotomicZHatField) :
      (eT ((numberFieldCyclotomicZHatCompositumRestriction K σ) x) : C) =
        σ (eT x : C) := by
    change
      algebraMap rationalCyclotomicZHatField C
          (numberFieldCyclotomicZHatCompositumRestriction K σ x) =
        σ (algebraMap rationalCyclotomicZHatField C x)
    change
      algebraMap rationalCyclotomicZHatField C
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ C σ)
            rationalCyclotomicZHatField) x) =
        (MulSemiringAction.toAlgEquiv ℚ C σ)
          (algebraMap rationalCyclotomicZHatField C x)
    exact AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv ℚ C σ)
      rationalCyclotomicZHatField x
  have hcomm (σ : C ≃ₐ[K] C) :
      transportT (numberFieldCyclotomicZHatCompositumRestriction K σ) =
        rB (changeBase σ) := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := eT.surjective x
    apply Subtype.ext
    have hBrestrict :
        (rB (changeBase σ) (eT y) : C) =
          changeBase σ (eT y : C) := by
      exact IntermediateField.restrictRestrictAlgEquivMapHom_apply
        B A (changeBase σ) (eT y)
    calc
      (transportT (numberFieldCyclotomicZHatCompositumRestriction K σ)
          (eT y) : C) =
          (eT (numberFieldCyclotomicZHatCompositumRestriction K σ y) : C) := by
            change
              ((eT.symm.trans
                ((numberFieldCyclotomicZHatCompositumRestriction K σ).trans eT))
                  (eT y) : C) =
                (eT ((numberFieldCyclotomicZHatCompositumRestriction K σ) y) : C)
            simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
      _ = σ (eT y : C) := raw_restriction_commutes σ y
      _ = changeBase σ (eT y : C) := rfl
      _ = (rB (changeBase σ) (eT y) : C) := hBrestrict.symm
  intro σ τ hστ
  apply hchangeBase
  apply hrB
  rw [← hcomm σ, ← hcomm τ, hστ]

/-- Restriction to a finite rational cyclotomic layer commutes with
first restricting an automorphism of the full compositum to the
corresponding finite compositum over `K`. -/
theorem
    restrictNormalHom_numberFieldCyclotomicZHatCompositumRestriction
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (σ :
      Gal((numberFieldCyclotomicZHatCompositum K)/K)) :
    letI : Algebra ℚ (numberFieldCyclotomicZHatCompositum K) :=
      (numberFieldCyclotomicZHatCompositum K).algebra'
    letI : Algebra K (numberFieldCyclotomicZHatCompositum K) :=
      numberFieldCyclotomicZHatCompositumAlgebra K
    letI : IsScalarTower ℚ K (numberFieldCyclotomicZHatCompositum K) :=
      numberFieldCyclotomicZHatCompositum_scalarTower K
    letI : Normal ℚ E := E.isGalois.to_normal
    letI : Normal K
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) := by
      let : IsAbelianGalois K
          (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
        numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois K E
      exact IsGalois.to_normal
    letI : IsScalarTower K
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
        (numberFieldCyclotomicZHatCompositum K) := by
      exact IntermediateField.isScalarTower_mid
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
    AlgEquiv.restrictNormalHom E
        (numberFieldCyclotomicZHatCompositumRestriction K σ) =
      IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E K
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
        (AlgEquiv.restrictNormalHom
          (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
          σ) := by
  let : Normal ℚ E := E.isGalois.to_normal
  let : Algebra ℚ (numberFieldCyclotomicZHatCompositum K) :=
    (numberFieldCyclotomicZHatCompositum K).algebra'
  let : Algebra K (numberFieldCyclotomicZHatCompositum K) :=
    numberFieldCyclotomicZHatCompositumAlgebra K
  let : IsScalarTower ℚ K (numberFieldCyclotomicZHatCompositum K) :=
    numberFieldCyclotomicZHatCompositum_scalarTower K
  let : Normal K
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) := by
    let : IsAbelianGalois K
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
      numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois K E
    exact IsGalois.to_normal
  let : IsScalarTower K
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
      (numberFieldCyclotomicZHatCompositum K) := by
    exact IntermediateField.isScalarTower_mid
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
  let C := numberFieldCyclotomicZHatCompositum K
  let T := rationalCyclotomicZHatField
  let P : IntermediateField K C :=
    numberFieldCyclotomicZHatFiniteLayerInCompositum K E
  let : Algebra T C := rationalCyclotomicZHatCompositumAlgebra K
  let : IsScalarTower ℚ T C :=
    rationalCyclotomicZHatCompositum_scalarTower K
  let : Algebra E P :=
    rationalCyclotomicZHatFiniteLayerInCompositumAlgebra K E
  let : IsScalarTower ℚ E P :=
    rationalCyclotomicZHatFiniteLayerInCompositum_scalarTower K E
  let : IsAbelianGalois K P := by
    change IsAbelianGalois K
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
    exact numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois K E
  let : Normal K P := IsGalois.to_normal
  let eEP : E →ₐ[ℚ] P :=
    rationalCyclotomicZHatFiniteLayerInCompositumEmbedding K E
  let iP : P →ₐ[K] C := IntermediateField.val P
  let iT : T →ₐ[ℚ] C := rationalCyclotomicZHatCompositumEmbedding K
  have hEmbedding (z : E) :
      iP (eEP z) = iT (z : T) := by
    apply Subtype.ext
    rfl
  have hL (z : E) :
      ((AlgEquiv.restrictNormalHom E
        (numberFieldCyclotomicZHatCompositumRestriction K σ)) z : T) =
        (numberFieldCyclotomicZHatCompositumRestriction K σ) (z : T) := by
    change
      algebraMap E T
          ((AlgEquiv.restrictNormalHom E
            (numberFieldCyclotomicZHatCompositumRestriction K σ)) z) =
        (numberFieldCyclotomicZHatCompositumRestriction K σ)
          (algebraMap E T z)
    change
      algebraMap E T
          ((AlgEquiv.restrictNormal
            (numberFieldCyclotomicZHatCompositumRestriction K σ) E) z) =
        (numberFieldCyclotomicZHatCompositumRestriction K σ)
          (algebraMap E T z)
    exact AlgEquiv.restrictNormal_commutes
      (numberFieldCyclotomicZHatCompositumRestriction K σ) E z
  have hRaw (z : T) :
      iT (numberFieldCyclotomicZHatCompositumRestriction K σ z) =
        σ (iT z) := by
    change
      algebraMap T C
          (numberFieldCyclotomicZHatCompositumRestriction K σ z) =
        σ (algebraMap T C z)
    change
      algebraMap T C
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ C σ) T) z) =
        (MulSemiringAction.toAlgEquiv ℚ C σ) (algebraMap T C z)
    exact AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv ℚ C σ) T z
  have hP (z : P) :
      iP (AlgEquiv.restrictNormalHom P σ z) = σ (iP z) := by
    change
      algebraMap P C (AlgEquiv.restrictNormalHom P σ z) =
        σ (algebraMap P C z)
    change
      algebraMap P C
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv K C σ) P) z) =
        (MulSemiringAction.toAlgEquiv K C σ) (algebraMap P C z)
    exact AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv K C σ) P z
  have hQ (z : E) :
      eEP
          (IntermediateField.restrictRestrictAlgEquivMapHom
            ℚ E K P (AlgEquiv.restrictNormalHom P σ) z) =
        (AlgEquiv.restrictNormalHom P σ) (eEP z) := by
    change
      algebraMap E P
          (IntermediateField.restrictRestrictAlgEquivMapHom
            ℚ E K P (AlgEquiv.restrictNormalHom P σ) z) =
        (AlgEquiv.restrictNormalHom P σ) (algebraMap E P z)
    change
      algebraMap E P
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ P
              (AlgEquiv.restrictNormalHom P σ)) E) z) =
        (MulSemiringAction.toAlgEquiv ℚ P
          (AlgEquiv.restrictNormalHom P σ)) (algebraMap E P z)
    exact AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv ℚ P
        (AlgEquiv.restrictNormalHom P σ)) E z
  apply AlgEquiv.ext
  intro x
  apply eEP.injective
  apply iP.injective
  calc
    iP (eEP
        (AlgEquiv.restrictNormalHom E
          (numberFieldCyclotomicZHatCompositumRestriction K σ) x)) =
        iT (((AlgEquiv.restrictNormalHom E
          (numberFieldCyclotomicZHatCompositumRestriction K σ) x) : T)) :=
      hEmbedding _
    _ = iT
        (numberFieldCyclotomicZHatCompositumRestriction K σ (x : T)) :=
      congrArg iT (hL x)
    _ = σ (iT (x : T)) := hRaw (x : T)
    _ = σ (iP (eEP x)) := congrArg σ (hEmbedding x).symm
    _ = iP (AlgEquiv.restrictNormalHom P σ (eEP x)) := (hP (eEP x)).symm
    _ = iP (eEP
        (IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E K P (AlgEquiv.restrictNormalHom P σ) x)) :=
      congrArg iP (hQ x).symm

/-- Restriction from the full cyclotomic compositum to its rational
cyclotomic factor is continuous for the actual Krull topologies. -/
theorem numberFieldCyclotomicZHatCompositumRestriction_continuous :
    Continuous
      (numberFieldCyclotomicZHatCompositumRestriction K) := by
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def, map_one]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨M, hMfinite, hMU⟩ := hU
  let : FiniteDimensional ℚ M := hMfinite
  let E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField :=
    { toIntermediateField :=
        IntermediateField.normalClosure
          ℚ M rationalCyclotomicZHatField
      finiteDimensional :=
        normalClosure.is_finiteDimensional
          ℚ M rationalCyclotomicZHatField
      isGalois :=
        IsGalois.normalClosure
          ℚ M rationalCyclotomicZHatField }
  let : Normal ℚ E := E.isGalois.to_normal
  let P :=
    numberFieldCyclotomicZHatFiniteLayerInCompositum K E
  let : IsAbelianGalois K P :=
    numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois K E
  let : Normal K P := IsGalois.to_normal
  let : IsScalarTower K P
      (numberFieldCyclotomicZHatCompositum K) :=
    IntermediateField.isScalarTower_mid P
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨P, inferInstance, ?_⟩
  intro σ hσ
  have hfixP :
      AlgEquiv.restrictNormalHom
          P
          σ =
        1 := by
    have hker : σ ∈ (AlgEquiv.restrictNormalHom P).ker := by
      rw [IntermediateField.restrictNormalHom_ker]
      exact hσ
    exact hker
  have hkerE :
      AlgEquiv.restrictNormalHom E
          (numberFieldCyclotomicZHatCompositumRestriction K σ) = 1 := by
    rw [
      restrictNormalHom_numberFieldCyclotomicZHatCompositumRestriction,
      hfixP,
      map_one]
  have hfixE :
      (numberFieldCyclotomicZHatCompositumRestriction K σ) ∈
        (E : IntermediateField ℚ rationalCyclotomicZHatField).fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    exact hkerE
  apply hMU
  exact IntermediateField.fixingSubgroup_antitone
    (IntermediateField.le_normalClosure M) hfixE

end Reciprocity
end GlobalClassFieldTheory
