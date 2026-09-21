/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitExtensionAction
/-!
# Norms on rational fixed-field idele classes

Compatibility of fixed-field inclusion and relative norm with the actual
idele-class extension attached to the abstract subgroup tower.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

private theorem fourStepAddEquiv_apply_eq
    {V A B C D : Type*}
    [Add V] [Add A] [Add B] [Add C] [Add D]
    (eV : V ≃+ D) (eB : B ≃+ D)
    (eA : A ≃+ B) (eC : A ≃+ C)
    {y : V} {z : A} {w : C}
    (h : eV y = eB (eA z))
    (ht : eC z = w) :
    (((eV.trans eB.symm).trans eA.symm).trans eC) y = w := by
  change eC (eA.symm (eB.symm (eV y))) = w
  rw [h, eB.symm_apply_apply, eA.symm_apply_apply]
  exact ht

private theorem repOfMulDistribMulAction_rho_toMul
    {G A : Type*} [Group G] [CommGroup A]
    [MulDistribMulAction G A]
    (g : G) (a : Additive A) :
    Additive.toMul
        ((Rep.ofMulDistribMulAction G A).ρ g a) =
      g • Additive.toMul a :=
  rfl

private theorem fintype_prod_comp_equiv
    {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [CommMonoid A]
    (e : ι ≃ κ) (f : κ → A) :
    (∏ i, f (e i)) = ∏ k, f k :=
  Fintype.prod_equiv e
    (fun i => f (e i)) f (fun _ => rfl)

private theorem eq_of_common_ofMul_image
    {A B : Type*}
    (f : A → B) (hf : Function.Injective f)
    {u : Additive B} {a b : A}
    (ha : u = Additive.ofMul (f a))
    (hb : u = Additive.ofMul (f b)) :
    a = b := by
  have h := congrArg Additive.toMul (ha.symm.trans hb)
  change f a = f b at h
  exact hf h

private noncomputable def relativeIdeleClassNormAdditiveValue
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (c : Additive (RelativeIdeleGroup.ClassGroup F E)) :
    Additive (IdeleClassGroup F) :=
  Additive.ofMul
    (RelativeIdeleGroup.Cohomology.ideleClassNorm F E
      (Additive.toMul c))

private noncomputable def includedRelativeIdeleClassNormAdditiveValue
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (c : Additive (RelativeIdeleGroup.ClassGroup F E)) :
    Additive (RelativeIdeleGroup.ClassGroup F E) :=
  Additive.ofMul
    (RelativeIdeleGroup.classInclusion F E
      (RelativeIdeleGroup.Cohomology.ideleClassNorm F E
        (Additive.toMul c)))

private noncomputable def rationalFixedFieldInclusionComparison
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : RelativeIdeleGroup.ClassGroup ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K)) :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  (rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
      ((extensionFixedRepresentationEquiv
        rationalIdeleClassRepresentation K L hLK hnormal).symm
        (fixedFieldInclusion rationalIdeleClassRepresentation
          K L hLK
          (rationalAbstractFixedFieldIdeleClassEquivFixed K
            (Additive.ofMul
              (_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := F) c))))),
    Additive.ofMul
      (RelativeIdeleGroup.classInclusion F E
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c)))

private noncomputable def rationalExtensionNormComparison
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (x : (extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal).V) :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K inferInstance
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK inferInstance inferInstance
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let e :=
    rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
  (e (M.norm.hom x),
    includedRelativeIdeleClassNormAdditiveValue F E (e x))

private noncomputable def rationalRelativeNormComparison
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let eK := rationalAbstractFixedFieldIdeleClassEquivFixed K
  let e :=
    rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
  (eK.symm
      (relativeNorm rationalIdeleClassRepresentation
        K L hLK a),
    relativeIdeleClassNormAdditiveValue F E
      (e (eAmbient.symm a)))

private noncomputable def rationalFixedFieldIdeleClassAdditiveType
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))] : Type :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : NumberField F := NumberField.of_module_finite ℚ F
  Additive (IdeleClassGroup F)

private noncomputable def rationalFixedFieldIdeleClassType
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))] : Type :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : NumberField F := NumberField.of_module_finite ℚ F
  IdeleClassGroup F

private noncomputable def rationalRelativeNormSource
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    rationalFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) K :=
  (rationalRelativeNormComparison
    (hKfinite := hKfinite) (hfinite := hfinite)
    K L hLK hnormal a).1

private noncomputable def rationalRelativeNormTarget
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    rationalFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) K :=
  (rationalRelativeNormComparison
    (hKfinite := hKfinite) (hfinite := hfinite)
    K L hLK hnormal a).2

private noncomputable def rationalRelativeNormClassNormSource
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    rationalFixedFieldIdeleClassType
      (hKfinite := hKfinite) K :=
  Additive.toMul
    (rationalRelativeNormTarget
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK hnormal a)

private noncomputable def rationalRelativeNormClassNormTarget
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    rationalFixedFieldIdeleClassType
      (hKfinite := hKfinite) K :=
  Additive.toMul
    (rationalRelativeNormSource
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK hnormal a)

/-- The fixed-part inclusion from the lower abstract field to the upper
one becomes the existing relative idele-class inclusion under the
fixed-field realization. -/
theorem
    rationalAbstractExtensionIdeleClassEquiv_fixedFieldInclusion
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : RelativeIdeleGroup.ClassGroup ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K)) :
    let comparison :=
      rationalFixedFieldInclusionComparison K L hLK hnormal c
    comparison.1 = comparison.2 := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ := hnormal
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let _ : NumberField E := NumberField.of_module_finite ℚ E
  let _ : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  let hFE : F ≤ E.restrictScalars ℚ :=
    abstractFixedField_le ℚ (SeparableClosure ℚ) hLK
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let eFixed :
      Additive (IdeleClassGroup E) ≃+
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation L :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK
  let eRelative :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (IdeleClassGroup E) :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))
  let eTower :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (RelativeIdeleGroup.ClassGroup F E) :=
    MulEquiv.toAdditive
      ((TowerRelativeIdeleGroup.classGroupEquiv
        ℚ F E).symm.trans
        (towerRelativeIdeleClassBaseChangeMulEquiv
          ℚ F E))
  let aK :
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K
      (Additive.ofMul
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c))
  let cE : RelativeIdeleGroup.ClassGroup ℚ E :=
    RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
      (IntermediateField.inclusion hFE) c
  let z : Additive (RelativeIdeleGroup.ClassGroup ℚ E) :=
    Additive.ofMul cE
  let y :
      (extensionFixedRepresentation rationalIdeleClassRepresentation
        K L hLK hnormal).V :=
    eAmbient.symm
      (fixedFieldInclusion rationalIdeleClassRepresentation
        K L hLK aK)
  have hFixed :
      eFixed (eRelative z) =
        fixedFieldInclusion rationalIdeleClassRepresentation
          K L hLK aK := by
    apply Subtype.ext
    calc
      (eFixed (eRelative z)).1 =
          (rationalIdeleClassEquivFixed
            (E.restrictScalars ℚ)
            (Additive.ofMul
              (_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := E) cE))).1 := by
        rfl
      _ =
          (rationalIdeleClassEquivFixed F
            (Additive.ofMul
              (_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := F) c))).1 := by
        change
          Additive.ofMul
              (rationalIntermediateIdeleClassToDirectLimit
                (E.restrictScalars ℚ)
                (_root_.relativeIdeleClassBaseChangeMulEquiv
                  (K := ℚ) (L := E.restrictScalars ℚ)
                  (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
                    (IntermediateField.inclusion hFE) c))) =
            Additive.ofMul
              (rationalIntermediateIdeleClassToDirectLimit F
                (_root_.relativeIdeleClassBaseChangeMulEquiv
                  (K := ℚ) (L := F) c))
        exact congrArg Additive.ofMul
          (rationalIntermediateIdeleClassToDirectLimit_extension hFE c)
      _ = aK.1 := by
        simpa only [aK, F] using
          (rationalAbstractFixedFieldIdeleClassEquivFixed_coe K
            (Additive.ofMul
              (_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := F) c))).symm
      _ =
          (fixedFieldInclusion rationalIdeleClassRepresentation
            K L hLK aK).1 := by
        exact
          (fixedFieldInclusion_coe rationalIdeleClassRepresentation
            K L hLK aK).symm
  have hAmbient :
      eAmbient y = eFixed (eRelative z) := by
    calc
      eAmbient y =
          fixedFieldInclusion rationalIdeleClassRepresentation
            K L hLK aK :=
        eAmbient.apply_symm_apply _
      _ = eFixed (eRelative z) := hFixed.symm
  have hTower :
      eTower z =
        Additive.ofMul
          (RelativeIdeleGroup.classInclusion F E
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := F) c)) := by
    apply Additive.toMul.injective
    change
      towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
          ((TowerRelativeIdeleGroup.classGroupEquiv
            ℚ F E).symm cE) =
        RelativeIdeleGroup.classInclusion F E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) c)
    exact
      rationalRelativeIdeleClassEmbedding_towerBaseChange hFE c
  change
    (((eAmbient.trans eFixed.symm).trans eRelative.symm).trans eTower) y =
      Additive.ofMul
        (RelativeIdeleGroup.classInclusion F E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) c))
  exact fourStepAddEquiv_apply_eq
    eAmbient eFixed eRelative eTower hAmbient hTower

/-- Under the fixed-field realization, the representation norm is the
existing relative idele-class norm, viewed in the upper class group by
the existing class inclusion. -/
theorem rationalAbstractExtensionIdeleClassEquiv_norm
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (x : (extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal).V) :
    let comparison :=
      rationalExtensionNormComparison K L hLK hnormal x
    comparison.1 = comparison.2 := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ := hnormal
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K inferInstance
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK inferInstance inferInstance
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let _ : NumberField E := NumberField.of_module_finite ℚ E
  let _ : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let _ : MulDistribMulAction (E ≃ₐ[F] E)
      (RelativeIdeleGroup.ClassGroup F E) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  let _ : Fintype Q := Fintype.ofFinite Q
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let e :=
    rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
  let eQ :=
    abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let c : RelativeIdeleGroup.ClassGroup F E :=
    Additive.toMul (e x)
  change e (M.norm.hom x) =
    includedRelativeIdeleClassNormAdditiveValue F E (e x)
  apply Additive.toMul.injective
  simp only [Rep.norm, Representation.norm]
  change
    Additive.toMul (e ((∑ q : Q, M.ρ q) x)) =
      RelativeIdeleGroup.classInclusion F E
        (RelativeIdeleGroup.Cohomology.ideleClassNorm F E c)
  rw [LinearMap.sum_apply, map_sum, toMul_sum]
  have hActionProd :
      (∏ q : Q, Additive.toMul (e (M.ρ q x))) =
        ∏ q : Q, eQ q • c := by
    apply Finset.prod_congr rfl
    intro q _
    rw [rationalAbstractExtensionIdeleClassEquiv_action
      K L hLK hnormal q x]
    exact repOfMulDistribMulAction_rho_toMul (eQ q) (e x)
  have hReindex :
      (∏ q : Q, eQ q • c) =
        ∏ τ : E ≃ₐ[F] E, τ • c := by
    exact fintype_prod_comp_equiv eQ.toEquiv
      (fun τ : E ≃ₐ[F] E => τ • c)
  have hNormProd :
      (∏ τ : E ≃ₐ[F] E, τ • c) =
        RelativeIdeleGroup.classInclusion F E
          (RelativeIdeleGroup.Cohomology.ideleClassNorm F E c) :=
    (RelativeIdeleGroup.classInclusion_ideleClassNorm_eq_prod_conjugates
      c).symm
  exact Eq.trans hActionProd (Eq.trans hReindex hNormProd)

private theorem rationalRelativeNorm_representation_norm
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    let M :=
      extensionFixedRepresentation rationalIdeleClassRepresentation
        K L hLK hnormal
    let eAmbient :=
      extensionFixedRepresentationEquiv
        rationalIdeleClassRepresentation K L hLK hnormal
    M.norm.hom (eAmbient.symm a) =
      eAmbient.symm
        (fixedFieldInclusion rationalIdeleClassRepresentation
          K L hLK
          (relativeNorm rationalIdeleClassRepresentation
            K L hLK a)) := by
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let x := eAmbient.symm a
  let n :=
    relativeNorm rationalIdeleClassRepresentation K L hLK a
  change
    M.norm.hom x =
      eAmbient.symm
        (fixedFieldInclusion rationalIdeleClassRepresentation
          K L hLK n)
  apply Subtype.ext
  change (M.norm.hom x).1 = n.1
  have hNormCoe :=
    extensionFixedRepresentation_norm_coe
      rationalIdeleClassRepresentation
      K L hLK hnormal x
  change
    (M.norm.hom x).1 =
      (relativeNorm rationalIdeleClassRepresentation
        K L hLK (eAmbient x)).1 at hNormCoe
  have hxa : eAmbient x = a :=
    eAmbient.apply_symm_apply a
  rw [hxa] at hNormCoe
  exact hNormCoe

private theorem rationalRelativeNormClassNorm_eq
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    rationalRelativeNormClassNormSource
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a =
      rationalRelativeNormClassNormTarget
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ := hnormal
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let _ : NumberField E := NumberField.of_module_finite ℚ E
  let _ : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  let _ : Fintype Q := Fintype.ofFinite Q
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let eK :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K
  let e :=
    rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
  let x := eAmbient.symm a
  let n :=
    relativeNorm rationalIdeleClassRepresentation K L hLK a
  let q :=
    RelativeIdeleGroup.Cohomology.ideleClassNorm F E
      (Additive.toMul (e x))
  let cK : RelativeIdeleGroup.ClassGroup ℚ F :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := F)).symm
      (Additive.toMul (eK.symm n))
  have hcK :
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) cK =
        Additive.toMul (eK.symm n) := by
    exact
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := F)).apply_symm_apply
        (Additive.toMul (eK.symm n))
  have hn :
      eK
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := F) cK)) =
        n := by
    rw [hcK]
    change eK (eK.symm n) = n
    exact eK.apply_symm_apply n
  have hMnorm :
      M.norm.hom x =
        eAmbient.symm
          (fixedFieldInclusion rationalIdeleClassRepresentation
            K L hLK n) := by
    exact rationalRelativeNorm_representation_norm
      (hfinite := hfinite) K L hLK hnormal a
  have hNorm :=
    rationalAbstractExtensionIdeleClassEquiv_norm
      K L hLK hnormal x
  have hInclusion :=
    rationalAbstractExtensionIdeleClassEquiv_fixedFieldInclusion
      K L hLK hnormal cK
  change
    e (M.norm.hom x) =
      Additive.ofMul
        (RelativeIdeleGroup.classInclusion F E q) at hNorm
  change
    e
        (eAmbient.symm
          (fixedFieldInclusion rationalIdeleClassRepresentation
            K L hLK
            (eK
              (Additive.ofMul
                (_root_.relativeIdeleClassBaseChangeMulEquiv
                  (K := ℚ) (L := F) cK))))) =
      Additive.ofMul
        (RelativeIdeleGroup.classInclusion F E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) cK)) at hInclusion
  have hNorm' :=
    (congrArg (fun t => e t) hMnorm).symm.trans hNorm
  have hInclusionLeft := congrArg
    (fun b =>
      e
        (eAmbient.symm
          (fixedFieldInclusion rationalIdeleClassRepresentation
            K L hLK b)))
    hn
  have hInclusionRight := congrArg
    (fun d : IdeleClassGroup F =>
      Additive.ofMul
        (RelativeIdeleGroup.classInclusion F E d))
    hcK
  have hInclusion' :=
    hInclusionLeft.symm.trans (hInclusion.trans hInclusionRight)
  have hq :
      q = Additive.toMul (eK.symm n) := by
    exact eq_of_common_ofMul_image
      (fun d : IdeleClassGroup F =>
        RelativeIdeleGroup.classInclusion F E d)
      (RelativeIdeleGroup.classInclusion_injective F E)
      hNorm' hInclusion'
  change q = Additive.toMul (eK.symm n)
  exact hq

/-- The relative norm in the rational absolute idele-class
representation is the existing relative idele-class norm on the two
actual fixed fields. -/
theorem
    rationalAbstractFixedFieldIdeleClassEquivFixed_relativeNorm
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    rationalRelativeNormSource
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a =
      rationalRelativeNormTarget
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a := by
  have h := congrArg Additive.ofMul
    (rationalRelativeNormClassNorm_eq
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK hnormal a).symm
  change
    rationalRelativeNormSource
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a =
      rationalRelativeNormTarget
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a at h
  exact h

end Reciprocity
end GlobalClassFieldTheory
