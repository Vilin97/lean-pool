/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicPrincipalProduct
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleValueTopology
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicZHatBaseChange
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitExtension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.IdeleClassNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation
/-!
# The cyclotomic valuation on idele classes

The cyclotomic idele value is trivial on principal ideles, so it descends
to the ordinary idele class group.  Its restriction to the compact
norm-one idele class group still has dense image in `ZHat`; compactness
therefore upgrades density to surjectivity.

For a number field `K`, the defining normalization gives the exact
identity

`f_K v_K(c) = v_ℚ(N_{K/ℚ} c)`.

Surjectivity of `v_K` then identifies the image of the actual
idele-class norm with `f_K ZHat`.  For the actual fixed field attached
to a finite abstract field, the already constructed cyclotomic
base-change theorem identifies `f_K` with the residue degree.  This
supplies the norm-range field of the concrete henselian valuation data.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

/-- Fix the canonical source-group dictionary before constructing the value maps
and their additive ranges. -/
@[instance_reducible]
private noncomputable def cyclotomicValuationIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] cyclotomicValuationIdeleClassCommGroup

/-- Lift a continuous multiplicative map through a quotient group once its
defining normal subgroup is contained in the kernel.  Keeping the quotient-map
argument here avoids repeating the same large continuity elaboration for the
rational and number-field cyclotomic values. -/
private noncomputable def ideleClassContinuousQuotientLift
    {A B : Type*} [Group A] [TopologicalSpace A]
    [Group B] [TopologicalSpace B]
    (N : Subgroup A) [N.Normal] (f : A →ₜ* B)
    (hN : N ≤ f.toMonoidHom.ker) : (A ⧸ N) →ₜ* B := by
  let φ : (A ⧸ N) →* B := QuotientGroup.lift N f.toMonoidHom hN
  have hcomp :
      Continuous (fun a : A => φ (QuotientGroup.mk' N a)) := by
    refine f.continuous_toFun.congr (fun a => ?_)
    change f.toMonoidHom a = φ (QuotientGroup.mk' N a)
    exact (QuotientGroup.lift_mk N hN a).symm
  exact
    { toMonoidHom := φ
      continuous_toFun :=
        (QuotientGroup.isQuotientMap_mk
          (G := A) (N := N)).continuous_iff.2 hcomp }

private theorem ideleClassContinuousQuotientLift_mk
    {A B : Type*} [Group A] [TopologicalSpace A]
    [Group B] [TopologicalSpace B]
    (N : Subgroup A) [N.Normal] (f : A →ₜ* B)
    (hN : N ≤ f.toMonoidHom.ker) (a : A) :
    ideleClassContinuousQuotientLift N f hN
        (QuotientGroup.mk' N a) =
      f a := by
  change QuotientGroup.lift N f.toMonoidHom hN
      (QuotientGroup.mk' N a) = f a
  exact QuotientGroup.lift_mk N hN a

/-- Principal rational ideles lie in the kernel of the cyclotomic value. -/
private theorem rationalCyclotomicZHatIdeleValue_principalSubgroup_le_ker :
    IdeleGroup.principalSubgroup ℚ ≤
      rationalCyclotomicZHatIdeleValue.toMonoidHom.ker := by
  rintro _ ⟨x, rfl⟩
  exact rationalCyclotomicZHatIdeleValue_principalIdele_eq_one x

/-- The rational cyclotomic value descended continuously through
`C_ℚ = I_ℚ / ℚˣ`. -/
noncomputable def rationalCyclotomicZHatIdeleClassValueContinuousMul :
    IdeleClassGroup ℚ →ₜ* Multiplicative ZHat :=
  ideleClassContinuousQuotientLift
    (IdeleGroup.principalSubgroup ℚ)
    rationalCyclotomicZHatIdeleValue
    rationalCyclotomicZHatIdeleValue_principalSubgroup_le_ker

/-- Evaluation of the descended rational value on an idele class
represented by an idele. -/
theorem rationalCyclotomicZHatIdeleClassValueContinuousMul_mk
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleClassValueContinuousMul
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup ℚ) a) =
      rationalCyclotomicZHatIdeleValue a :=
  ideleClassContinuousQuotientLift_mk
    (IdeleGroup.principalSubgroup ℚ)
    rationalCyclotomicZHatIdeleValue
    rationalCyclotomicZHatIdeleValue_principalSubgroup_le_ker a

/-- The rational cyclotomic value on idele classes, in continuous
additive notation. -/
noncomputable def rationalCyclotomicZHatIdeleClassValueContinuous :
    Additive (IdeleClassGroup ℚ) →ₜ+ ZHat where
  __ := MonoidHom.toAdditiveLeft
    rationalCyclotomicZHatIdeleClassValueContinuousMul.toMonoidHom
  continuous_toFun := continuous_toAdd.comp
    (rationalCyclotomicZHatIdeleClassValueContinuousMul.continuous_toFun.comp
      continuous_toMul)

/-- Evaluation of the additive rational class value on a representative. -/
theorem rationalCyclotomicZHatIdeleClassValueContinuous_mk
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleClassValueContinuous
        (Additive.ofMul
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup ℚ) a)) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue a) := by
  change
    Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleClassValueContinuousMul
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup ℚ) a)) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue a)
  rw [rationalCyclotomicZHatIdeleClassValueContinuousMul_mk]

variable (K : Type) [Field K] [NumberField K]

/-- Principal ideles lie in the kernel of the normalized cyclotomic value. -/
private theorem
    normalizedCyclotomicZHatIdeleValue_principalSubgroup_le_ker :
    IdeleGroup.principalSubgroup K ≤
      (normalizedCyclotomicZHatIdeleValueContinuousMul K).toMonoidHom.ker := by
  rintro _ ⟨x, rfl⟩
  change
    normalizedCyclotomicZHatIdeleValue K
        (Additive.ofMul (IdeleGroup.principalIdele K x)) =
      0
  exact normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero K x

/-- The normalized cyclotomic value descended continuously through
`C_K = I_K / Kˣ`. -/
noncomputable def normalizedCyclotomicZHatIdeleClassValueContinuousMul :
    IdeleClassGroup K →ₜ* Multiplicative ZHat :=
  ideleClassContinuousQuotientLift
    (IdeleGroup.principalSubgroup K)
    (normalizedCyclotomicZHatIdeleValueContinuousMul K)
    (normalizedCyclotomicZHatIdeleValue_principalSubgroup_le_ker K)

/-- Evaluation of the normalized class value on an idele representative. -/
theorem normalizedCyclotomicZHatIdeleClassValueContinuousMul_mk
    (a : IdeleGroup K) :
    normalizedCyclotomicZHatIdeleClassValueContinuousMul K
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      Multiplicative.ofAdd
        (normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a)) := by
  exact
    ideleClassContinuousQuotientLift_mk
      (IdeleGroup.principalSubgroup K)
      (normalizedCyclotomicZHatIdeleValueContinuousMul K)
      (normalizedCyclotomicZHatIdeleValue_principalSubgroup_le_ker K) a

/-- The normalized cyclotomic value on idele classes, in continuous
additive notation. -/
noncomputable def normalizedCyclotomicZHatIdeleClassValueContinuous :
    Additive (IdeleClassGroup K) →ₜ+ ZHat where
  __ := MonoidHom.toAdditiveLeft
    (normalizedCyclotomicZHatIdeleClassValueContinuousMul K).toMonoidHom
  continuous_toFun := continuous_toAdd.comp
    ((normalizedCyclotomicZHatIdeleClassValueContinuousMul K).continuous_toFun.comp
      continuous_toMul)

/-- Evaluation of the normalized additive class value on a representative. -/
theorem normalizedCyclotomicZHatIdeleClassValueContinuous_mk
    (a : IdeleGroup K) :
    normalizedCyclotomicZHatIdeleClassValueContinuous K
        (Additive.ofMul
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      normalizedCyclotomicZHatIdeleValue K
        (Additive.ofMul a) := by
  change
    Multiplicative.toAdd
        (normalizedCyclotomicZHatIdeleClassValueContinuousMul K
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a)) =
      normalizedCyclotomicZHatIdeleValue K
        (Additive.ofMul a)
  rw [normalizedCyclotomicZHatIdeleClassValueContinuousMul_mk]
  rfl

/-- The chosen local-factor product on the actual cyclotomic
`ZHat`-compositum kills every principal idele.  This is the
number-field form of the cyclotomic principal-idele formula: after restricting
to the rational
cyclotomic factor, norm--restriction turns the assertion into the
rational principal-idele product formula, and that restriction is
injective. -/
theorem
    infiniteGlobalArtinMonoidHom_numberFieldCyclotomicZHatCompositum_principalIdele
    (x : Kˣ) :
    infiniteGlobalArtinMonoidHom K
        (numberFieldCyclotomicZHatCompositum K)
        (IdeleGroup.principalIdele K x) =
      1 := by
  apply numberFieldCyclotomicZHatCompositumRestriction_injective K
  rw [
    numberFieldCyclotomicZHatCompositumRestriction_infiniteGlobalArtinMonoidHom,
    IdeleGroup.norm_principalIdele]
  apply rationalCyclotomicZHatFieldGalEquivZHat.injective
  simpa only [
    rationalCyclotomicZHatIdeleValue_apply,
    map_one] using
    (rationalCyclotomicZHatIdeleValue_principalIdele_eq_one
      (Units.map (Algebra.norm ℚ) x))

/-- The genuine infinite Artin map of the cyclotomic
`ZHat`-compositum, descended to the idele class group. -/
noncomputable def
    numberFieldCyclotomicZHatCompositumIdeleClassArtinMonoidHom :
    IdeleClassGroup K →*
      Gal(numberFieldCyclotomicZHatCompositum K/K) :=
  QuotientGroup.lift
    (IdeleGroup.principalSubgroup K)
    (infiniteGlobalArtinMonoidHom K
      (numberFieldCyclotomicZHatCompositum K)).toMonoidHom
    (by
      rintro _ ⟨x, rfl⟩
      exact
        infiniteGlobalArtinMonoidHom_numberFieldCyclotomicZHatCompositum_principalIdele
          K x)

/-- Evaluation of the descended compositum Artin map on an idele
representative. -/
theorem
    numberFieldCyclotomicZHatCompositumIdeleClassArtinMonoidHom_mk
    (a : IdeleGroup K) :
    numberFieldCyclotomicZHatCompositumIdeleClassArtinMonoidHom K
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      infiniteGlobalArtinMonoidHom K
        (numberFieldCyclotomicZHatCompositum K) a := by
  rw [numberFieldCyclotomicZHatCompositumIdeleClassArtinMonoidHom]
  exact QuotientGroup.lift_mk _ _ _

/-- In the rational cyclotomic Galois coordinate, the genuine
idele-class Artin symbol over `K` is exactly `f_K` times the normalized
cyclotomic valuation. -/
theorem
    numberFieldCyclotomicZHatCompositumIdeleClassArtin_coordinate
    (c : IdeleClassGroup K) :
    Multiplicative.toAdd
        (rationalCyclotomicZHatFieldGalEquivZHat
          (numberFieldCyclotomicZHatCompositumRestriction K
            (numberFieldCyclotomicZHatCompositumIdeleClassArtinMonoidHom
              K c))) =
      cyclotomicZHatIntersectionDegree K •
        normalizedCyclotomicZHatIdeleClassValueContinuous K
          (Additive.ofMul c) := by
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (IdeleGroup.principalSubgroup K) c
  rw [
    numberFieldCyclotomicZHatCompositumIdeleClassArtinMonoidHom_mk,
    numberFieldCyclotomicZHatCompositumRestriction_infiniteGlobalArtinMonoidHom,
    normalizedCyclotomicZHatIdeleClassValueContinuous_mk]
  change
    cyclotomicZHatNormComposite K (Additive.ofMul a) =
      cyclotomicZHatIntersectionDegree K •
        normalizedCyclotomicZHatIdeleValue K (Additive.ofMul a)
  exact
    (cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleValue
      K (Additive.ofMul a)).symm

/-- The kernel of the genuine Artin map to the cyclotomic
`ZHat`-compositum is the zero fibre of the normalized cyclotomic
idele-class valuation. -/
@[simp]
theorem
    numberFieldCyclotomicZHatCompositumIdeleClassArtin_eq_one_iff
    (c : IdeleClassGroup K) :
    numberFieldCyclotomicZHatCompositumIdeleClassArtinMonoidHom K c =
        1 ↔
      normalizedCyclotomicZHatIdeleClassValueContinuous K
          (Additive.ofMul c) =
        0 := by
  constructor
  · intro hc
    have hcoordinate :=
      numberFieldCyclotomicZHatCompositumIdeleClassArtin_coordinate K c
    rw [hc] at hcoordinate
    have hcoordinate' :
        0 =
        cyclotomicZHatIntersectionDegree K •
          normalizedCyclotomicZHatIdeleClassValueContinuous K
            (Additive.ofMul c) := by
      simpa only [map_one, toAdd_one] using hcoordinate
    apply
      zHatMulNat_injective
        (cyclotomicZHatIntersectionDegree_pos K)
    change
      cyclotomicZHatIntersectionDegree K •
          normalizedCyclotomicZHatIdeleClassValueContinuous K
            (Additive.ofMul c) =
        cyclotomicZHatIntersectionDegree K • (0 : ZHat)
    simpa only [smul_zero] using hcoordinate'.symm
  · intro hc
    apply numberFieldCyclotomicZHatCompositumRestriction_injective K
    apply rationalCyclotomicZHatFieldGalEquivZHat.injective
    apply Multiplicative.ext
    have hcoordinate :=
      numberFieldCyclotomicZHatCompositumIdeleClassArtin_coordinate K c
    rw [hc, smul_zero] at hcoordinate
    simpa only [map_one, toAdd_one] using hcoordinate

/-- Use the rational algebra structure expected by the imported finite-layer
API throughout this block.  Fixing it before the first finite-layer binder
keeps the parameter and every restriction target definitionally aligned. -/
noncomputable local instance
    cyclotomicIdeleClassValuationRationalCyclotomicZHatFieldAlgebra :
    Algebra ℚ rationalCyclotomicZHatField :=
  DivisionRing.toRatAlgebra

/-- The canonical number-field structure used by every finite-layer
idele-class declaration below.  Keeping this witness opaque prevents the
module-finiteness construction from being rebuilt along distinct paths. -/
private theorem
    numberFieldCyclotomicZHatFiniteLayerNumberField
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
  NumberField.of_module_finite K
    (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)

attribute [local instance]
  numberFieldCyclotomicZHatFiniteLayerNumberField

private structure NumberFieldCyclotomicZHatFiniteLayerArtinData
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Type where
  toMonoidHom :
    IdeleGroup K →*
      Gal(numberFieldCyclotomicZHatFiniteLayerInCompositum K E/K)
  principal (x : Kˣ) :
    toMonoidHom (IdeleGroup.principalIdele K x) = 1
  restriction (a : IdeleGroup K) :
    AlgEquiv.restrictNormalHom
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
        (infiniteGlobalArtinMonoidHom K
          (numberFieldCyclotomicZHatCompositum K) a) =
      toMonoidHom a

private theorem
    rawGlobalArtinMonoidHom_numberFieldCyclotomicZHatFiniteLayer_principalIdele
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (x : Kˣ) :
    globalArtinMonoidHom
        (K := K)
        (L :=
          numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
        (IdeleGroup.principalIdele K x) =
      1 := by
  have hprojection :
      AlgEquiv.restrictNormalHom
          (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
          (infiniteGlobalArtinMonoidHom K
            (numberFieldCyclotomicZHatCompositum K)
            (IdeleGroup.principalIdele K x)) =
        globalArtinMonoidHom
          (K := K)
          (L :=
            numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
          (IdeleGroup.principalIdele K x) :=
    restrictNormalHom_infiniteGlobalArtinMonoidHom
      K (numberFieldCyclotomicZHatCompositum K)
      (IdeleGroup.principalIdele K x)
      (numberFieldCyclotomicZHatFiniteGaloisLayerInCompositum K E)
  calc
    globalArtinMonoidHom
          (K := K)
          (L :=
            numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
          (IdeleGroup.principalIdele K x) =
        AlgEquiv.restrictNormalHom
          (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
          (infiniteGlobalArtinMonoidHom K
            (numberFieldCyclotomicZHatCompositum K)
            (IdeleGroup.principalIdele K x)) :=
      hprojection.symm
    _ = AlgEquiv.restrictNormalHom
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) 1 := by
      rw [
        infiniteGlobalArtinMonoidHom_numberFieldCyclotomicZHatCompositum_principalIdele]
    _ = 1 := map_one
      (AlgEquiv.restrictNormalHom
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E))

private theorem
    rawGlobalArtinMonoidHom_numberFieldCyclotomicZHatFiniteLayer_restriction
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (a : IdeleGroup K) :
    AlgEquiv.restrictNormalHom
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
        (infiniteGlobalArtinMonoidHom K
          (numberFieldCyclotomicZHatCompositum K) a) =
      globalArtinMonoidHom
        (K := K)
        (L :=
          numberFieldCyclotomicZHatFiniteLayerInCompositum K E) a :=
  restrictNormalHom_infiniteGlobalArtinMonoidHom
    K (numberFieldCyclotomicZHatCompositum K) a
    (numberFieldCyclotomicZHatFiniteGaloisLayerInCompositum K E)

private noncomputable def
    numberFieldCyclotomicZHatFiniteLayerArtinData
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberFieldCyclotomicZHatFiniteLayerArtinData K E where
  toMonoidHom :=
    globalArtinMonoidHom
      (K := K)
      (L := numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
  principal :=
    rawGlobalArtinMonoidHom_numberFieldCyclotomicZHatFiniteLayer_principalIdele
      K E
  restriction :=
    rawGlobalArtinMonoidHom_numberFieldCyclotomicZHatFiniteLayer_restriction
      K E

/-- The chosen finite-layer global Artin map, kept opaque so every descended
idele-class declaration shares the same dependent instance data. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteLayerGlobalArtinMonoidHom
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IdeleGroup K →*
      Gal(numberFieldCyclotomicZHatFiniteLayerInCompositum K E/K) :=
  (numberFieldCyclotomicZHatFiniteLayerArtinData K E).toMonoidHom

/-- Every finite cyclotomic layer over a number field inherits the
principal-idele product formula from the full cyclotomic
`ZHat`-compositum. -/
@[simp]
theorem
    globalArtinMonoidHom_numberFieldCyclotomicZHatFiniteLayer_principalIdele
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (x : Kˣ) :
    numberFieldCyclotomicZHatFiniteLayerGlobalArtinMonoidHom K E
        (IdeleGroup.principalIdele K x) =
      1 := by
  exact
    (numberFieldCyclotomicZHatFiniteLayerArtinData K E).principal x

private theorem
    numberFieldCyclotomicZHatFiniteLayer_principalSubgroup_le_ker
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IdeleGroup.principalSubgroup K ≤
      (numberFieldCyclotomicZHatFiniteLayerGlobalArtinMonoidHom K E).ker := by
  rintro _ ⟨x, rfl⟩
  exact
    globalArtinMonoidHom_numberFieldCyclotomicZHatFiniteLayer_principalIdele
      K E x

/-- The actual chosen-local-factor Artin map of a finite cyclotomic
layer, descended through `C_K = I_K / Kˣ`. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteLayerIdeleClassArtinMonoidHom
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IdeleClassGroup K →*
      Gal(numberFieldCyclotomicZHatFiniteLayerInCompositum K E/K) := by
  exact
    QuotientGroup.lift
      (IdeleGroup.principalSubgroup K)
      (numberFieldCyclotomicZHatFiniteLayerGlobalArtinMonoidHom K E)
      (numberFieldCyclotomicZHatFiniteLayer_principalSubgroup_le_ker K E)

/-- Evaluation of the descended finite-layer Artin map on an idele
representative. -/
theorem
    numberFieldCyclotomicZHatFiniteLayerIdeleClassArtinMonoidHom_mk
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (a : IdeleGroup K) :
    numberFieldCyclotomicZHatFiniteLayerIdeleClassArtinMonoidHom K E
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) =
      numberFieldCyclotomicZHatFiniteLayerGlobalArtinMonoidHom K E a := by
  rw [numberFieldCyclotomicZHatFiniteLayerIdeleClassArtinMonoidHom]
  exact
    QuotientGroup.lift_mk
      (IdeleGroup.principalSubgroup K)
      (numberFieldCyclotomicZHatFiniteLayer_principalSubgroup_le_ker K E)
      a

/-- Restriction of the descended Artin map of the full cyclotomic
compositum to a finite cyclotomic layer is the descended finite-layer
chosen-local-factor Artin map. -/
theorem
    numberFieldCyclotomicZHatCompositumIdeleClassArtinMonoidHom_restrict
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    (AlgEquiv.restrictNormalHom
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)).comp
        (numberFieldCyclotomicZHatCompositumIdeleClassArtinMonoidHom K) =
      numberFieldCyclotomicZHatFiniteLayerIdeleClassArtinMonoidHom K E := by
  apply MonoidHom.ext
  intro c
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (IdeleGroup.principalSubgroup K) c
  rw [
    MonoidHom.comp_apply,
    numberFieldCyclotomicZHatCompositumIdeleClassArtinMonoidHom_mk,
    numberFieldCyclotomicZHatFiniteLayerIdeleClassArtinMonoidHom_mk]
  exact
    (numberFieldCyclotomicZHatFiniteLayerArtinData K E).restriction a

/-- The descended rational class value has dense image already on the
compact norm-one idele class group. -/
theorem
    rationalCyclotomicZHatIdeleClassValue_normOne_denseRange :
    DenseRange
      (fun c : IdeleClassGroup.normOneSubgroup (K := ℚ) =>
        rationalCyclotomicZHatIdeleClassValueContinuous
          (Additive.ofMul (c : IdeleClassGroup ℚ))) := by
  have hToAdd :
      Function.Surjective
        (Multiplicative.toAdd :
          Multiplicative ZHat → ZHat) :=
    fun z => ⟨Multiplicative.ofAdd z, rfl⟩
  have hidele :
      DenseRange
        (fun b : IdeleGroup.normOneSubgroup (K := ℚ) =>
          Multiplicative.toAdd
            (rationalCyclotomicZHatIdeleValue
              (b : IdeleGroup ℚ))) :=
    hToAdd.denseRange.comp
      rationalCyclotomicZHatIdeleValue_normOne_denseRange
      continuous_toAdd
  apply hidele.mono
  rintro z ⟨b, rfl⟩
  let c : IdeleClassGroup.normOneSubgroup (K := ℚ) :=
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup ℚ)
        (b : IdeleGroup ℚ),
      (IdeleClassGroup.mk_mem_normOneSubgroup_iff
        (b : IdeleGroup ℚ)).2 b.2⟩
  refine ⟨c, ?_⟩
  simp only [c,
    rationalCyclotomicZHatIdeleClassValueContinuous_mk]

/-- Compactness upgrades the dense rational norm-one image to
surjectivity. -/
theorem
    rationalCyclotomicZHatIdeleClassValue_normOne_surjective :
    Function.Surjective
      (fun c : IdeleClassGroup.normOneSubgroup (K := ℚ) =>
        rationalCyclotomicZHatIdeleClassValueContinuous
          (Additive.ofMul (c : IdeleClassGroup ℚ))) := by
  let f :=
    fun c : IdeleClassGroup.normOneSubgroup (K := ℚ) =>
      rationalCyclotomicZHatIdeleClassValueContinuous
        (Additive.ofMul (c : IdeleClassGroup ℚ))
  have hf : Continuous f := by
    exact
      (rationalCyclotomicZHatIdeleClassValueContinuous.continuous_toFun).comp
        (continuous_ofMul.comp continuous_subtype_val)
  have hclosed : IsClosed (Set.range f) :=
    (isCompact_range hf).isClosed
  have hdense : DenseRange f := by
    simpa only [f] using
      rationalCyclotomicZHatIdeleClassValue_normOne_denseRange
  intro z
  have hz : z ∈ closure (Set.range f) := by
    rw [hdense.closure_range]
    trivial
  rwa [hclosed.closure_eq] at hz

/-- The rational cyclotomic idele-class value is surjective. -/
theorem rationalCyclotomicZHatIdeleClassValue_surjective :
    Function.Surjective
      rationalCyclotomicZHatIdeleClassValueContinuous := by
  intro z
  obtain ⟨c, hc⟩ :=
    rationalCyclotomicZHatIdeleClassValue_normOne_surjective z
  exact ⟨Additive.ofMul (c : IdeleClassGroup ℚ), hc⟩

/-- The normalized class value has dense image already on the compact
norm-one idele class group. -/
theorem normalizedCyclotomicZHatIdeleClassValue_normOne_denseRange :
    DenseRange
      (fun c : IdeleClassGroup.normOneSubgroup (K := K) =>
        normalizedCyclotomicZHatIdeleClassValueContinuous K
          (Additive.ofMul (c : IdeleClassGroup K))) := by
  apply
    (normalizedCyclotomicZHatIdeleValue_normOne_denseRange K).mono
  rintro z ⟨b, rfl⟩
  let c : IdeleClassGroup.normOneSubgroup (K := K) :=
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (b : IdeleGroup K),
      (IdeleClassGroup.mk_mem_normOneSubgroup_iff
        (b : IdeleGroup K)).2 b.2⟩
  refine ⟨c, ?_⟩
  simp only [c,
    normalizedCyclotomicZHatIdeleClassValueContinuous_mk]

/-- Compactness upgrades the dense normalized norm-one image to
surjectivity. -/
theorem normalizedCyclotomicZHatIdeleClassValue_normOne_surjective :
    Function.Surjective
      (fun c : IdeleClassGroup.normOneSubgroup (K := K) =>
        normalizedCyclotomicZHatIdeleClassValueContinuous K
          (Additive.ofMul (c : IdeleClassGroup K))) := by
  let f :=
    fun c : IdeleClassGroup.normOneSubgroup (K := K) =>
      normalizedCyclotomicZHatIdeleClassValueContinuous K
        (Additive.ofMul (c : IdeleClassGroup K))
  have hf : Continuous f := by
    exact
      (normalizedCyclotomicZHatIdeleClassValueContinuous K).continuous_toFun.comp
        (continuous_ofMul.comp continuous_subtype_val)
  have hclosed : IsClosed (Set.range f) :=
    (isCompact_range hf).isClosed
  have hdense : Dense (Set.range f) := by
    change DenseRange f
    simpa only [f] using
      (normalizedCyclotomicZHatIdeleClassValue_normOne_denseRange K)
  intro z
  have hz : z ∈ closure (Set.range f) := by
    rw [hdense.closure_eq]
    trivial
  rwa [hclosed.closure_eq] at hz

/-- The normalized cyclotomic idele-class value is surjective. -/
theorem normalizedCyclotomicZHatIdeleClassValue_surjective :
    Function.Surjective
      (normalizedCyclotomicZHatIdeleClassValueContinuous K) := by
  intro z
  obtain ⟨c, hc⟩ :=
    normalizedCyclotomicZHatIdeleClassValue_normOne_surjective K z
  exact ⟨Additive.ofMul (c : IdeleClassGroup K), hc⟩

/-- The normalized cyclotomic class value has full value group. -/
theorem normalizedCyclotomicZHatIdeleClassValue_range :
    (normalizedCyclotomicZHatIdeleClassValueContinuous K).toAddMonoidHom.range =
      (⊤ : AddSubgroup ZHat) :=
  AddMonoidHom.range_eq_top_of_surjective
    (normalizedCyclotomicZHatIdeleClassValueContinuous K).toAddMonoidHom
    (normalizedCyclotomicZHatIdeleClassValue_surjective K)

/-- The rational cyclotomic class value has full value group. -/
theorem rationalCyclotomicZHatIdeleClassValue_range :
    rationalCyclotomicZHatIdeleClassValueContinuous.toAddMonoidHom.range =
      (⊤ : AddSubgroup ZHat) :=
  AddMonoidHom.range_eq_top_of_surjective
    rationalCyclotomicZHatIdeleClassValueContinuous.toAddMonoidHom
    rationalCyclotomicZHatIdeleClassValue_surjective

/-- The defining normalized-value identity after descent to idele
classes:

`f_K v_K(c) = v_ℚ(N_{K/ℚ} c)`. -/
theorem
    cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleClassValue
    (c : Additive (IdeleClassGroup K)) :
    cyclotomicZHatIntersectionDegree K •
        normalizedCyclotomicZHatIdeleClassValueContinuous K c =
      rationalCyclotomicZHatIdeleClassValueContinuous
        (Additive.ofMul
          (_root_.ideleClassNorm ℚ K
            (Additive.toMul c))) := by
  obtain ⟨a, ha⟩ :=
    QuotientGroup.mk'_surjective
      (IdeleGroup.principalSubgroup K) (Additive.toMul c)
  have hc :
      c =
        Additive.ofMul
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a) := by
    apply Additive.ext
    exact ha.symm
  rw [hc, normalizedCyclotomicZHatIdeleClassValueContinuous_mk,
    toMul_ofMul,
    _root_.ideleClassNorm_mk,
    rationalCyclotomicZHatIdeleClassValueContinuous_mk]
  simpa only [cyclotomicZHatNormComposite_apply] using
    (cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleValue
      K (Additive.ofMul a))

/-- The rational cyclotomic value after the actual class norm
`N_{K/ℚ} : C_K → C_ℚ`. -/
noncomputable def rationalCyclotomicZHatIdeleClassNormComposite :
    Additive (IdeleClassGroup K) →+ ZHat :=
  (rationalCyclotomicZHatIdeleClassValueContinuous.toAddMonoidHom).comp
      (MonoidHom.toAdditive (_root_.ideleClassNorm ℚ K))

/-- Evaluation of the rational class-norm composite. -/
@[simp]
theorem rationalCyclotomicZHatIdeleClassNormComposite_apply
    (c : Additive (IdeleClassGroup K)) :
    rationalCyclotomicZHatIdeleClassNormComposite K c =
      rationalCyclotomicZHatIdeleClassValueContinuous
        (Additive.ofMul
          (_root_.ideleClassNorm ℚ K
            (Additive.toMul c))) :=
  rfl

/-- Exact image of the actual idele-class norm under the rational
cyclotomic value. -/
theorem rationalCyclotomicZHatIdeleClassNormComposite_range :
    (rationalCyclotomicZHatIdeleClassNormComposite K).range =
      nsmulImage (⊤ : AddSubgroup ZHat)
        (cyclotomicZHatIntersectionDegree K) := by
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    rw [mem_nsmulImage_iff]
    refine
      ⟨normalizedCyclotomicZHatIdeleClassValueContinuous K c,
        AddSubgroup.mem_top _, ?_⟩
    simpa only [
      rationalCyclotomicZHatIdeleClassNormComposite_apply] using
      (cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleClassValue
        K c)
  · rw [mem_nsmulImage_iff]
    rintro ⟨x, _hx, hx⟩
    obtain ⟨c, hc⟩ :=
      normalizedCyclotomicZHatIdeleClassValue_surjective K x
    refine ⟨c, ?_⟩
    calc
      rationalCyclotomicZHatIdeleClassNormComposite K c =
          cyclotomicZHatIntersectionDegree K •
            normalizedCyclotomicZHatIdeleClassValueContinuous K c := by
        simpa only [
          rationalCyclotomicZHatIdeleClassNormComposite_apply] using
          (cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleClassValue
            K c).symm
      _ =
          cyclotomicZHatIntersectionDegree K • x := by
        rw [hc]
      _ = z := hx

/-- Restriction of the normalized class value to the compact norm-one
idele class group. -/
noncomputable def normalizedCyclotomicZHatNormOneIdeleClassValue :
    Additive (IdeleClassGroup.normOneSubgroup (K := K)) →+ ZHat :=
  ((normalizedCyclotomicZHatIdeleClassValueContinuous K).toAddMonoidHom).comp
      (MonoidHom.toAdditive
        (IdeleClassGroup.normOneSubgroup (K := K)).subtype)

/-- The normalized norm-one class value remains surjective. -/
theorem normalizedCyclotomicZHatNormOneIdeleClassValue_surjective :
    Function.Surjective
      (normalizedCyclotomicZHatNormOneIdeleClassValue K) := by
  intro z
  obtain ⟨c, hc⟩ :=
    normalizedCyclotomicZHatIdeleClassValue_normOne_surjective K z
  refine ⟨Additive.ofMul c, ?_⟩
  change
    normalizedCyclotomicZHatIdeleClassValueContinuous K
        (Additive.ofMul (c : IdeleClassGroup K)) =
      z
  exact hc

/-- The rational class value composed with the actual class norm,
restricted to norm-one idele classes.  The codomain restriction in
`normOneNorm` is supplied by preservation of the absolute idele norm. -/
noncomputable def rationalCyclotomicZHatNormOneIdeleClassNormComposite :
    Additive (IdeleClassGroup.normOneSubgroup (K := K)) →+ ZHat :=
  (rationalCyclotomicZHatIdeleClassValueContinuous.toAddMonoidHom).comp
      (MonoidHom.toAdditive
        ((IdeleClassGroup.normOneSubgroup (K := ℚ)).subtype.comp
          (IdeleClassGroup.normOneNorm ℚ K)))

/-- The normalized identity restricted to the actual norm-one class
norm. -/
theorem
    cyclotomicZHatIntersectionDegree_nsmul_normalizedNormOneIdeleClassValue
    (c : Additive
      (IdeleClassGroup.normOneSubgroup (K := K))) :
    cyclotomicZHatIntersectionDegree K •
        normalizedCyclotomicZHatNormOneIdeleClassValue K c =
      rationalCyclotomicZHatNormOneIdeleClassNormComposite K c := by
  change
    cyclotomicZHatIntersectionDegree K •
        normalizedCyclotomicZHatIdeleClassValueContinuous K
          (Additive.ofMul
            ((Additive.toMul c :
                IdeleClassGroup.normOneSubgroup (K := K)) :
              IdeleClassGroup K)) =
      rationalCyclotomicZHatIdeleClassValueContinuous
        (Additive.ofMul
          ((IdeleClassGroup.normOneNorm ℚ K
              (Additive.toMul c) :
            IdeleClassGroup.normOneSubgroup (K := ℚ)) :
            IdeleClassGroup ℚ))
  rw [IdeleClassGroup.normOneNorm_apply]
  exact
    cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleClassValue
      K
      (Additive.ofMul
        ((Additive.toMul c :
            IdeleClassGroup.normOneSubgroup (K := K)) :
          IdeleClassGroup K))

/-- The exact cyclotomic image of the actual class norm is already
attained on norm-one idele classes. -/
theorem
    rationalCyclotomicZHatNormOneIdeleClassNormComposite_range :
    (rationalCyclotomicZHatNormOneIdeleClassNormComposite K).range =
      nsmulImage (⊤ : AddSubgroup ZHat)
        (cyclotomicZHatIntersectionDegree K) := by
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    rw [mem_nsmulImage_iff]
    refine
      ⟨normalizedCyclotomicZHatNormOneIdeleClassValue K c,
        AddSubgroup.mem_top _, ?_⟩
    exact
      cyclotomicZHatIntersectionDegree_nsmul_normalizedNormOneIdeleClassValue
        K c
  · rw [mem_nsmulImage_iff]
    rintro ⟨x, _hx, hx⟩
    obtain ⟨c, hc⟩ :=
      normalizedCyclotomicZHatNormOneIdeleClassValue_surjective K x
    refine ⟨c, ?_⟩
    calc
      rationalCyclotomicZHatNormOneIdeleClassNormComposite K c =
          cyclotomicZHatIntersectionDegree K •
            normalizedCyclotomicZHatNormOneIdeleClassValue K c :=
        (cyclotomicZHatIntersectionDegree_nsmul_normalizedNormOneIdeleClassValue
          K c).symm
      _ =
          cyclotomicZHatIntersectionDegree K • x := by
        rw [hc]
      _ = z := hx

/-- The rational cyclotomic class valuation transported to the
distinguished base fixed part of the absolute idele-class
representation. -/
noncomputable def rationalCyclotomicZHatValuation :
    KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (ClassFormation.baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) →+
      ZHat :=
  (rationalCyclotomicZHatIdeleClassValueContinuous.toAddMonoidHom).comp
      rationalIdeleClassEquivBaseFixed.symm.toAddMonoidHom

/-- The transported rational cyclotomic valuation is surjective. -/
theorem rationalCyclotomicZHatValuation_surjective :
    Function.Surjective rationalCyclotomicZHatValuation := by
  intro z
  obtain ⟨c, hc⟩ :=
    rationalCyclotomicZHatIdeleClassValue_surjective z
  refine ⟨rationalIdeleClassEquivBaseFixed c, ?_⟩
  change
    rationalCyclotomicZHatIdeleClassValueContinuous
        (rationalIdeleClassEquivBaseFixed.symm
          (rationalIdeleClassEquivBaseFixed c)) =
      z
  rw [rationalIdeleClassEquivBaseFixed.symm_apply_apply]
  exact hc

/-- The value group of the transported rational valuation is all of
`ZHat`. -/
@[simp]
theorem rationalCyclotomicZHatValuation_range :
    rationalCyclotomicZHatValuation.range =
      (⊤ : AddSubgroup ZHat) :=
  AddMonoidHom.range_eq_top_of_surjective
    rationalCyclotomicZHatValuation
    rationalCyclotomicZHatValuation_surjective

/-- Every integral profinite value belongs to the transported rational
cyclotomic valuation range. -/
theorem rationalCyclotomicZHatValuation_integer_mem_range
    (m : ℤ) :
    (Int.castRingHom ZHat) m ∈
      rationalCyclotomicZHatValuation.range := by
  rw [rationalCyclotomicZHatValuation_range]
  exact AddSubgroup.mem_top _

/-- The canonical quotient map for the transported rational cyclotomic
valuation is bijective at every positive level. -/
theorem
    rationalCyclotomicZHatValuation_canonicalValueQuotientMap_bijective
    (n : ℕ) (hn : 0 < n) :
    Function.Bijective
      (canonicalValueQuotientMap
        rationalCyclotomicZHatValuation.range n hn) := by
  rw [rationalCyclotomicZHatValuation_range]
  exact canonicalValueQuotientMap_top_bijective n hn

section AbstractFixedFieldNormRange

variable
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))

local instance rationalCyclotomicFiniteAbstractFieldQuotientFinite :
    Finite
      ((ClassFormation.baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (ClassFormation.baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H.field (ClassFormation.le_baseField H.field)) :=
  H.finite

private theorem rationalAbstractFixedFieldFiniteDimensional :
    FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) :=
  LocalClassFieldTheory.abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) H.field H.finite

private theorem rationalAbstractFixedFieldNumberField :
    NumberField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) := by
  let : FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) :=
    rationalAbstractFixedFieldFiniteDimensional H
  exact NumberField.of_module_finite ℚ
    (LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field)

/-- For the actual number field fixed by a finite abstract field, the
actual idele-class norm has cyclotomic image equal to the
residue-degree multiples of `ZHat`. -/
theorem
    rationalCyclotomicZHatIdeleClassNormComposite_abstractFixedField_range :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    let : FiniteDimensional ℚ F :=
      rationalAbstractFixedFieldFiniteDimensional H
    let : NumberField F :=
      rationalAbstractFixedFieldNumberField H
    (rationalCyclotomicZHatIdeleClassNormComposite F).range =
      nsmulImage (⊤ : AddSubgroup ZHat)
        (H.residueDegree rationalCyclotomicDegreeData : ℕ) := by
  intro F hfinite hnumberField
  clear hfinite
  have hdegree :=
    cyclotomicZHatIntersectionDegree_abstractFixedField_eq_residueDegree H
  rw [rationalCyclotomicZHatIdeleClassNormComposite_range]
  exact
    congrArg
      (fun n : ℕ => nsmulImage (⊤ : AddSubgroup ZHat) n)
      hdegree

/-- Exact norm-range identity after transport from the actual
fixed-field idele class group to the abstract fixed part. -/
theorem rationalCyclotomicZHatValuation_normToBase_range :
    (rationalCyclotomicZHatValuation.comp
      (normToBase rationalIdeleClassRepresentation H.field)).range =
      nsmulImage rationalCyclotomicZHatValuation.range
        (H.residueDegree rationalCyclotomicDegreeData : ℕ) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : NumberField F :=
    rationalAbstractFixedFieldNumberField H
  let eF :=
    rationalAbstractFixedFieldIdeleClassEquivFixed H.field
  have heval
      (c : Additive (IdeleClassGroup F)) :
      (rationalCyclotomicZHatValuation.comp
          (normToBase rationalIdeleClassRepresentation H.field))
          (eF c) =
        rationalCyclotomicZHatIdeleClassNormComposite F c := by
    change
      rationalCyclotomicZHatIdeleClassValueContinuous
          (rationalIdeleClassEquivBaseFixed.symm
            (normToBase rationalIdeleClassRepresentation H.field
              (eF c))) =
        rationalCyclotomicZHatIdeleClassValueContinuous
          (Additive.ofMul
            (_root_.ideleClassNorm ℚ F
              (Additive.toMul c)))
    exact congrArg
      rationalCyclotomicZHatIdeleClassValueContinuous
      (rationalAbstractFixedFieldNormToBase_eq_ordinaryIdeleClassNorm
        H c)
  have htransport :
      (rationalCyclotomicZHatValuation.comp
        (normToBase rationalIdeleClassRepresentation H.field)).range =
        (rationalCyclotomicZHatIdeleClassNormComposite F).range := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨c, rfl⟩ := eF.surjective a
      exact ⟨c, (heval c).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨eF c, heval c⟩
  calc
    (rationalCyclotomicZHatValuation.comp
        (normToBase rationalIdeleClassRepresentation H.field)).range =
        (rationalCyclotomicZHatIdeleClassNormComposite F).range :=
      htransport
    _ =
        nsmulImage (⊤ : AddSubgroup ZHat)
          (H.residueDegree rationalCyclotomicDegreeData : ℕ) := by
      simpa only [F] using
        (rationalCyclotomicZHatIdeleClassNormComposite_abstractFixedField_range
          H)
    _ =
        nsmulImage rationalCyclotomicZHatValuation.range
          (H.residueDegree rationalCyclotomicDegreeData : ℕ) := by
      rw [rationalCyclotomicZHatValuation_range]

end AbstractFixedFieldNormRange

/-- The concrete henselian valuation data on the absolute rational
idele-class representation, with cyclotomic degree data. -/
noncomputable def rationalCyclotomicIdeleClassValuationData :
    ValuationData
      rationalCyclotomicDegreeData
      rationalIdeleClassRepresentation where
  toAddMonoidHom :=
    rationalCyclotomicZHatValuation
  integers_mem :=
    rationalCyclotomicZHatValuation_integer_mem_range
  canonical_value_quotient_bijective :=
    rationalCyclotomicZHatValuation_canonicalValueQuotientMap_bijective
  norm_range := by
    intro H
    exact rationalCyclotomicZHatValuation_normToBase_range H

/-- Transporting an actual fixed-field idele class into the rational
absolute representation and then taking the base norm gives its
ordinary idele-class norm cyclotomic value. -/
theorem rationalCyclotomicZHatValuation_normToBase_fixed_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (c : Additive
      (IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))) :
    rationalCyclotomicZHatValuation
        (normToBase rationalIdeleClassRepresentation H.field
          (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c)) =
      rationalCyclotomicZHatIdeleClassNormComposite
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) c := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : NumberField F :=
    rationalAbstractFixedFieldNumberField H
  change
    rationalCyclotomicZHatIdeleClassValueContinuous
        (rationalIdeleClassEquivBaseFixed.symm
          (normToBase rationalIdeleClassRepresentation H.field
            (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c))) =
      rationalCyclotomicZHatIdeleClassValueContinuous
        (Additive.ofMul
          (_root_.ideleClassNorm ℚ F
            (Additive.toMul c)))
  exact congrArg
    rationalCyclotomicZHatIdeleClassValueContinuous
    (rationalAbstractFixedFieldNormToBase_eq_ordinaryIdeleClassNorm
      H c)

/-- Under the genuine fixed-field idele-class comparison, the
valuation used by abstract reciprocity is exactly the normalized
cyclotomic idele-class value of that fixed field. -/
theorem
    rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (c : Additive
      (IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))) :
    ((rationalCyclotomicIdeleClassValuationData.valuationAt H
        (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c) :
          rationalCyclotomicIdeleClassValuationData.valueGroup) :
        ZHat) =
      normalizedCyclotomicZHatIdeleClassValueContinuous
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) c := by
  have hdegree :=
    cyclotomicZHatIntersectionDegree_abstractFixedField_eq_residueDegree
      H
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : NumberField F :=
    rationalAbstractFixedFieldNumberField H
  apply
    zHatMulNat_injective
      (H.residueDegree rationalCyclotomicDegreeData).pos
  calc
    (H.residueDegree rationalCyclotomicDegreeData : ℕ) •
          ((rationalCyclotomicIdeleClassValuationData.valuationAt H
              (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c) :
                rationalCyclotomicIdeleClassValuationData.valueGroup) :
            ZHat) =
        rationalCyclotomicIdeleClassValuationData.normCompositeAt H
          (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c) := by
      exact
        rationalCyclotomicIdeleClassValuationData.residueDegree_nsmul_dividedAt
          H
          (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c)
    _ =
        rationalCyclotomicZHatIdeleClassNormComposite F c :=
      rationalCyclotomicZHatValuation_normToBase_fixed_apply H c
    _ =
        cyclotomicZHatIntersectionDegree F •
          normalizedCyclotomicZHatIdeleClassValueContinuous F c := by
      simpa only [
        rationalCyclotomicZHatIdeleClassNormComposite_apply] using
        (cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleClassValue
          F c).symm
    _ =
        (H.residueDegree rationalCyclotomicDegreeData : ℕ) •
          normalizedCyclotomicZHatIdeleClassValueContinuous F c := by
      exact
        congrArg
          (fun n : ℕ =>
            n • normalizedCyclotomicZHatIdeleClassValueContinuous F c)
          hdegree

end Reciprocity
end GlobalClassFieldTheory
