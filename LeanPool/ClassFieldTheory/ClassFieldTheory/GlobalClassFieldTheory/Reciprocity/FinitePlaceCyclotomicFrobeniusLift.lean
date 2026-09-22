/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Galois.CyclicPrimeSubextension
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.OnePlaceBaseNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift
import LeanPool.ClassFieldTheory.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerPrimeProduct
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicPrincipalIdele
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicZHatBaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicPrincipalPrimeFactor
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.ClosedAddSubgroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Topology.Algebra.ContinuousMonoidHom
/-!
# Decomposition-compatible cyclotomic Frobenius lifts

The finite-place reduction in the local--global compatibility theorem
uses automorphisms in a specified decomposition group, not arbitrary
lifts in the ambient absolute Galois group.

This file begins with the source map needed for that construction.
For a normal intermediate field, restriction maps the decomposition
group upstairs onto the decomposition group of the restricted
valuation.  The proof uses the actual valuation-conjugacy correction
in `absoluteValueDecompositionGroup_map_restrictNormalHom`.
-/

open AlgebraicNumberTheory.Valuations
open AlgebraicNumberTheory
open HilbertRamification
open ClassFormation
open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

local instance rationalCyclotomicFrobeniusLiftPrimePowerNumberField
    (p : Nat.Primes) (k : ℕ) :
    NumberField (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

local instance rationalCyclotomicFrobeniusLiftPrimePowerFiniteDimensional
    (p : Nat.Primes) (k : ℕ) :
    FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

local instance rationalCyclotomicFrobeniusLiftPrimePowerIsAbelianGalois
    (p : Nat.Primes) (k : ℕ) :
    IsAbelianGalois ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevelIsAbelianGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

noncomputable local instance
    rationalCyclotomicFrobeniusLiftLevelFiniteDimensional
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional m

noncomputable local instance
    rationalCyclotomicFrobeniusLiftLevelIsAbelianGalois
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicLevelIsAbelianGalois m

variable
    {K L Ω : Type}
    [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower K L Ω] [Normal K L]

/-- Restriction along a normal intermediate field, as a homomorphism
between the decomposition groups of a valuation and its restriction.

Unlike an unrestricted Galois restriction, the codomain records the
valuation-stabilizer condition, which is the condition needed to
transport local Artin symbols through a global field tower. -/
noncomputable def absoluteValueDecompositionGroupRestrictionHom
    (wΩ : AbsoluteValue Ω ℝ) :
    absoluteValueDecompositionGroup K wΩ →*
      absoluteValueDecompositionGroup K
        (wΩ.comp (f := algebraMap L Ω)
          (algebraMap L Ω).injective) where
  toFun τ :=
    ⟨AlgEquiv.restrictNormalHom
        (F := K) (K₁ := Ω) L τ.1,
      by
        intro x
        change
          wΩ
              (algebraMap L Ω
                ((AlgEquiv.restrictNormalHom
                  (F := K) (K₁ := Ω) L τ.1) x)) < 1 ↔
            wΩ (algebraMap L Ω x) < 1
        change
          wΩ
              (algebraMap L Ω
                ((AlgEquiv.restrictNormal τ.1 L) x)) < 1 ↔
            wΩ (algebraMap L Ω x) < 1
        rw [AlgEquiv.restrictNormal_commutes]
        exact τ.2 (algebraMap L Ω x)⟩
  map_one' := by
    apply Subtype.ext
    exact
      map_one
        (AlgEquiv.restrictNormalHom
          (F := K) (K₁ := Ω) L)
  map_mul' τ η := by
    apply Subtype.ext
    exact
      map_mul
        (AlgEquiv.restrictNormalHom
          (F := K) (K₁ := Ω) L) τ.1 η.1

/-- Restriction from a Galois overfield is surjective on the actual
decomposition groups of a nontrivial valuation.

The preimage is obtained by first extending the requested
automorphism and then correcting it by an automorphism fixing the
normal intermediate field.  Thus the resulting lift genuinely
stabilizes the specified valuation upstairs. -/
theorem absoluteValueDecompositionGroupRestrictionHom_surjective
    [IsGalois K Ω]
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (wΩ : AbsoluteValueExtension vK Ω) :
    Function.Surjective
      (absoluteValueDecompositionGroupRestrictionHom
        (K := K) (L := L) (Ω := Ω) wΩ.1) := by
  intro σ
  have hσ :
      σ.1 ∈
        (absoluteValueDecompositionGroup K wΩ.1).map
          (AlgEquiv.restrictNormalHom
            (F := K) (K₁ := Ω) L) := by
    rw [
      absoluteValueDecompositionGroup_map_restrictNormalHom
        (F := K) (E := Ω) (M := L) vK hvK wΩ]
    exact σ.2
  obtain ⟨τ, hτ, hτσ⟩ := hσ
  refine ⟨⟨τ, hτ⟩, ?_⟩
  apply Subtype.ext
  exact hτσ

/-- The infinite global Artin symbol of a finite one-place idèle
stabilizes every chosen extension of that finite place to an abelian
Galois overfield.

The proof is genuinely inverse-limit in nature.  For each element of
the overfield, we pass to the finite Galois closure it generates.  The
restriction of the infinite Artin symbol is then the finite chosen local
Artin symbol, whose image is the finite decomposition group.  Independence
of the exact extension in the abelian finite layer returns the valuation
stabilizer statement upstairs. -/
theorem
    infiniteGlobalArtinMonoidHom_finitePlaceIdele_mem_absoluteValueDecompositionGroup
    {F A : Type}
    [Field F] [NumberField F]
    [Field A] [Algebra F A] [IsAbelianGalois F A]
    (v : HeightOneSpectrum (𝓞 F))
    (wA : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) A)
    (x : (v.adicCompletion F)ˣ) :
    infiniteGlobalArtinMonoidHom F A
        (IdeleGroup.finitePlaceIdele v x) ∈
      absoluteValueDecompositionGroup F wA.1 := by
  rw [mem_absoluteValueDecompositionGroup_iff]
  intro y
  let M : IntermediateField F A :=
    IntermediateField.adjoin F {y}
  let : FiniteDimensional F M :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral y)
  let E :
      FiniteGaloisIntermediateField F A :=
    { toIntermediateField :=
        IntermediateField.normalClosure F M A
      finiteDimensional :=
        normalClosure.is_finiteDimensional F M A
      isGalois :=
        IsGalois.normalClosure F M A }
  let : NumberField E :=
    NumberField.of_module_finite F E
  let : IsAbelianGalois F E :=
    IsAbelianGalois.of_algHom
      (E : IntermediateField F A).val
  let vF :=
    NumberField.HeightOneSpectrum.adicAbv F v
  let wE : AbsoluteValueExtension vF E :=
    restrictAbsoluteValueExtensionToIntermediate
      vF wA E
  have hyM : y ∈ M :=
    IntermediateField.subset_adjoin
      (F := F) (S := {y}) (by rfl)
  have hyE : y ∈ E.toIntermediateField :=
    IntermediateField.le_normalClosure M hyM
  have hrestriction :
      AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom F A
            (IdeleGroup.finitePlaceIdele v x)) =
        chosenFinitePlaceArtinMonoidHom
          (K := F) (L := E) v x := by
    rw [
      restrictNormalHom_infiniteGlobalArtinMonoidHom,
      globalArtinMonoidHom_finitePlaceIdele]
  have hchosen :
      AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom F A
            (IdeleGroup.finitePlaceIdele v x)) ∈
        finitePlaceDecompositionGroup
          (K := F) (L := E) v := by
    rw [←
      chosenFinitePlaceArtinMonoidHom_range
        (K := F) (L := E) v]
    exact ⟨x, hrestriction.symm⟩
  have hrestricted :
      AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom F A
            (IdeleGroup.finitePlaceIdele v x)) ∈
        absoluteValueDecompositionGroup F wE.1 := by
    rw [←
      absoluteValueDecompositionGroup_eq_of_exactExtensions_of_isMulCommutative
        vF
        (RayClass.adicAbv_isNontrivial v)
        (chosenFinitePlaceExtension (L := E) v)
        wE]
    exact hchosen
  have hvalue :=
    (mem_absoluteValueDecompositionGroup_iff F wE.1 _).1
      hrestricted ⟨y, hyE⟩
  have hcommutes :
      (((AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom F A
            (IdeleGroup.finitePlaceIdele v x))) ⟨y, hyE⟩ : E) : A) =
        infiniteGlobalArtinMonoidHom F A
          (IdeleGroup.finitePlaceIdele v x) y :=
    AlgEquiv.restrictNormal_commutes
      (infiniteGlobalArtinMonoidHom F A
        (IdeleGroup.finitePlaceIdele v x)) E ⟨y, hyE⟩
  simpa only [wE, restrictAbsoluteValueExtensionToIntermediate_apply,
    hcommutes] using hvalue

section FiniteCyclotomicBaseChange

variable
    {F : Type*} [Field F] [NumberField F]

/-- Restriction from a finite cyclotomic compositum over a number
field to its rational cyclotomic layer. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteCompositumRestriction
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(numberFieldCyclotomicZHatFiniteCompositum F E / F) →*
      Gal(E / ℚ) := by
  letI : Normal ℚ E := E.isGalois.to_normal
  exact
    IntermediateField.restrictRestrictAlgEquivMapHom
      ℚ E F
        (numberFieldCyclotomicZHatFiniteCompositum F E)

/-- Restriction to the rational factor is injective on the actual
finite compositum: an automorphism fixing both generating fields fixes
their supremum. -/
theorem
    numberFieldCyclotomicZHatFiniteCompositumRestriction_injective
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Function.Injective
      (numberFieldCyclotomicZHatFiniteCompositumRestriction
        (F := F) E) := by
  let : Normal ℚ E := E.isGalois.to_normal
  let C :=
    numberFieldCyclotomicZHatFiniteCompositum F E
  let : Algebra ℚ C := C.algebra'
  let : Algebra F C :=
    numberFieldCyclotomicZHatFiniteCompositumAlgebra F E
  let : IsScalarTower ℚ F C :=
    numberFieldCyclotomicZHatFiniteCompositum_scalarTower F E
  let : Algebra E C :=
    rationalCyclotomicZHatFiniteLayerCompositumAlgebra F E
  let : IsScalarTower ℚ E C :=
    rationalCyclotomicZHatFiniteLayerCompositum_scalarTower F E
  let A : IntermediateField ℚ C :=
    (numberFieldInRationalSeparableClosure F).restrict
      (show
        numberFieldInRationalSeparableClosure F ≤ C from
        le_sup_left)
  let B : IntermediateField ℚ C :=
    (IntermediateField.lift E.toIntermediateField).restrict
      (show
        IntermediateField.lift E.toIntermediateField ≤ C from
        le_sup_right)
  let : Algebra ℚ B := B.algebra'
  let eF : F ≃ₐ[ℚ] A :=
    (numberFieldSeparableClosureEmbedding F).equivFieldRange.trans
      (IntermediateField.restrictAlgEquiv le_sup_left)
  let eE : E ≃ₐ[ℚ] B :=
    (IntermediateField.liftAlgEquiv E.toIntermediateField).trans
      (IntermediateField.restrictAlgEquiv le_sup_right)
  let : Normal ℚ B := Normal.of_algEquiv eE
  have hsup : B ⊔ A = ⊤ := by
    apply IntermediateField.lift_injective C
    rw [IntermediateField.lift_sup,
      IntermediateField.lift_restrict,
      IntermediateField.lift_restrict,
      IntermediateField.lift_top]
    exact sup_comm _ _
  let rB :
      (C ≃ₐ[A] C) →* (B ≃ₐ[ℚ] B) :=
    IntermediateField.restrictRestrictAlgEquivMapHom ℚ B A C
  have hrB : Function.Injective rB :=
    IntermediateField.restrictRestrictAlgEquivMapHom_injective
      B A hsup
  have heF (x : F) :
      algebraMap F C x = algebraMap A C (eF x) := by
    apply Subtype.ext
    rfl
  let changeBase :
      (C ≃ₐ[F] C) →* (C ≃ₐ[A] C) :=
    { toFun := fun σ =>
        { σ.toRingEquiv with
          commutes' := by
            intro y
            have hy :
                algebraMap F C (eF.symm y) =
                  algebraMap A C y := by
              simpa using heF (eF.symm y)
            rw [← hy]
            change σ (algebraMap F C (eF.symm y)) =
              algebraMap F C (eF.symm y)
            exact σ.commutes _ }
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hchangeBase : Function.Injective changeBase := by
    intro σ τ hστ
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun f : C ≃ₐ[A] C => f x) hστ
  let transportE : Gal(E / ℚ) →* (B ≃ₐ[ℚ] B) :=
    (AlgEquiv.autCongr eE).toMonoidHom
  have raw_restriction_commutes
      (σ : C ≃ₐ[F] C) (x : E) :
      (eE
          (numberFieldCyclotomicZHatFiniteCompositumRestriction
            (F := F) E σ x) : C) =
        σ (eE x : C) := by
    change
      algebraMap E C
          (numberFieldCyclotomicZHatFiniteCompositumRestriction
            (F := F) E σ x) =
        σ (algebraMap E C x)
    change
      algebraMap E C
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ C σ) E) x) =
        (MulSemiringAction.toAlgEquiv ℚ C σ)
          (algebraMap E C x)
    exact
      AlgEquiv.restrictNormal_commutes
        (MulSemiringAction.toAlgEquiv ℚ C σ) E x
  have hcomm (σ : C ≃ₐ[F] C) :
      transportE
          (numberFieldCyclotomicZHatFiniteCompositumRestriction
            (F := F) E σ) =
        rB (changeBase σ) := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := eE.surjective x
    apply Subtype.ext
    have hBrestrict :
        (rB (changeBase σ) (eE y) : C) =
          changeBase σ (eE y : C) := by
      exact
        IntermediateField.restrictRestrictAlgEquivMapHom_apply
          B A (changeBase σ) (eE y)
    calc
      (transportE
            (numberFieldCyclotomicZHatFiniteCompositumRestriction
              (F := F) E σ) (eE y) : C) =
          (eE
            (numberFieldCyclotomicZHatFiniteCompositumRestriction
              (F := F) E σ y) : C) := by
        change
          ((eE.symm.trans
            ((numberFieldCyclotomicZHatFiniteCompositumRestriction
              (F := F) E σ).trans eE)) (eE y) : C) =
            (eE
              (numberFieldCyclotomicZHatFiniteCompositumRestriction
                (F := F) E σ y) : C)
        simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
      _ = σ (eE y : C) := raw_restriction_commutes σ y
      _ = changeBase σ (eE y : C) := rfl
      _ = (rB (changeBase σ) (eE y) : C) := hBrestrict.symm
  intro σ τ hστ
  apply hchangeBase
  apply hrB
  rw [← hcomm σ, ← hcomm τ, hστ]

/-- The Galois group of the finite compositum is canonically the
subgroup of the rational finite-layer Galois group fixing the actual
intersection with the number field. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteCompositumGalEquivFixingSubgroup
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Gal(numberFieldCyclotomicZHatFiniteCompositum F E / F) ≃*
      (numberFieldCyclotomicZHatFiniteIntersection F E).fixingSubgroup := by
  letI : Normal ℚ E := E.isGalois.to_normal
  let r :=
    numberFieldCyclotomicZHatFiniteCompositumRestriction
      (F := F) E
  let eRange :
      Gal(numberFieldCyclotomicZHatFiniteCompositum F E / F) ≃*
        r.range :=
    MulEquiv.ofBijective r.rangeRestrict
      ⟨fun σ τ h =>
          numberFieldCyclotomicZHatFiniteCompositumRestriction_injective
            (F := F) E (congrArg Subtype.val h),
        MonoidHom.rangeRestrict_surjective _⟩
  have hrange :
      r.range =
        (numberFieldCyclotomicZHatFiniteIntersection F E).fixingSubgroup := by
    simpa only [r,
      numberFieldCyclotomicZHatFiniteCompositumRestriction] using
      (numberFieldCyclotomicZHatFiniteCompositum_restriction_range
        (K := F) E)
  exact
    eRange.trans
      (MulEquiv.subgroupCongr hrange)

/-- The finite compositum Galois group and the intersection-fixing
subgroup have the same cardinality. -/
theorem
    numberFieldCyclotomicZHatFiniteCompositum_galois_card
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Nat.card
        (Gal(numberFieldCyclotomicZHatFiniteCompositum F E / F)) =
      Nat.card
        (numberFieldCyclotomicZHatFiniteIntersection F E).fixingSubgroup :=
  Nat.card_congr
    (numberFieldCyclotomicZHatFiniteCompositumGalEquivFixingSubgroup
      (F := F) E).toEquiv

end FiniteCyclotomicBaseChange

/-- Restriction from the full actual cyclotomic `ZHat`-compositum over
a number field has image exactly the subgroup fixing the genuine
intersection with the rational cyclotomic `ZHat`-field. -/
theorem numberFieldCyclotomicZHatCompositumRestriction_range
    (F : Type*) [Field F] [NumberField F] :
    (numberFieldCyclotomicZHatCompositumRestriction F).range =
      ((numberFieldCyclotomicZHatIntersection F).restrict
        (show
          numberFieldCyclotomicZHatIntersection F ≤
            rationalCyclotomicZHatField from
          by
            dsimp only [numberFieldCyclotomicZHatIntersection]
            exact inf_le_right)).fixingSubgroup := by
  let C := numberFieldCyclotomicZHatCompositum F
  let : Algebra ℚ C := C.algebra'
  let : Algebra F C :=
    numberFieldCyclotomicZHatCompositumAlgebra F
  let : IsScalarTower ℚ F C :=
    numberFieldCyclotomicZHatCompositum_scalarTower F
  let : Algebra rationalCyclotomicZHatField C :=
    rationalCyclotomicZHatCompositumAlgebra F
  let : IsScalarTower ℚ rationalCyclotomicZHatField C :=
    rationalCyclotomicZHatCompositum_scalarTower F
  let : Normal ℚ rationalCyclotomicZHatField :=
    rationalCyclotomicZHatField_normal
  let eF : F →ₐ[ℚ] C :=
    numberFieldCyclotomicZHatCompositumEmbedding F
  let eT : rationalCyclotomicZHatField →ₐ[ℚ] C :=
    rationalCyclotomicZHatCompositumEmbedding F
  let r := numberFieldCyclotomicZHatCompositumRestriction F
  have hIntersection_le :
      numberFieldCyclotomicZHatIntersection F ≤
        rationalCyclotomicZHatField := by
    change
      numberFieldInRationalSeparableClosure F ⊓
          rationalCyclotomicZHatField ≤
        rationalCyclotomicZHatField
    exact inf_le_right
  let J : IntermediateField ℚ rationalCyclotomicZHatField :=
    (numberFieldCyclotomicZHatIntersection F).restrict
      hIntersection_le
  have eF_eq_algebraMap (y : F) :
      eF y = algebraMap F C y := by
    rfl
  have restriction_commutes
      (τ : C ≃ₐ[F] C) (z : rationalCyclotomicZHatField) :
      eT (r τ z) = τ (eT z) := by
    change
      algebraMap rationalCyclotomicZHatField C (r τ z) =
        τ (algebraMap rationalCyclotomicZHatField C z)
    change
      algebraMap rationalCyclotomicZHatField C
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ C τ)
            rationalCyclotomicZHatField) z) =
        (MulSemiringAction.toAlgEquiv ℚ C τ)
          (algebraMap rationalCyclotomicZHatField C z)
    exact
      AlgEquiv.restrictNormal_commutes
        (MulSemiringAction.toAlgEquiv ℚ C τ)
        rationalCyclotomicZHatField z
  have hJ (x : rationalCyclotomicZHatField) :
      x ∈ J ↔ eT x ∈ eF.fieldRange := by
    change
      x ∈ (numberFieldCyclotomicZHatIntersection F).restrict
          hIntersection_le ↔
        eT x ∈ eF.fieldRange
    rw [IntermediateField.mem_restrict]
    change
      x.1 ∈
          numberFieldInRationalSeparableClosure F ⊓
            rationalCyclotomicZHatField ↔
        eT x ∈ eF.fieldRange
    rw [IntermediateField.mem_inf]
    simp only [x.2, and_true]
    change
      x.1 ∈ (numberFieldSeparableClosureEmbedding F).fieldRange ↔
        eT x ∈ eF.fieldRange
    rw [AlgHom.mem_fieldRange, AlgHom.mem_fieldRange]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      apply Subtype.ext
      change numberFieldSeparableClosureEmbedding F y = x.1
      exact hy
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change numberFieldSeparableClosureEmbedding F y = x.1
      exact congrArg Subtype.val hy
  have hfixedField :
      IntermediateField.fixedField r.range = J := by
    ext x
    rw [IntermediateField.mem_fixedField_iff]
    rw [hJ]
    constructor
    · intro hx
      have hfixed :
          ∀ τ : C ≃ₐ[F] C, τ (eT x) = eT x := by
        intro τ
        have hxτ : r τ x = x :=
          hx (r τ) ⟨τ, rfl⟩
        have hrestrict :
            eT (r τ x) = τ (eT x) := by
          exact restriction_commutes τ x
        exact hrestrict.symm.trans (congrArg eT hxτ)
      have hmem :
          eT x ∈ Set.range (algebraMap F C) :=
        (InfiniteGalois.mem_range_algebraMap_iff_fixed
          (eT x)).2 hfixed
      rw [AlgHom.mem_fieldRange]
      obtain ⟨y, hy⟩ := hmem
      exact ⟨y, (eF_eq_algebraMap y).trans hy⟩
    · intro hx σ hσ
      obtain ⟨τ, rfl⟩ := hσ
      rw [AlgHom.mem_fieldRange] at hx
      obtain ⟨y, hy⟩ := hx
      apply eT.injective
      have hrestrict :
          eT (r τ x) = τ (eT x) := by
        exact restriction_commutes τ x
      calc
        eT (r τ x) = τ (eT x) := hrestrict
        _ = τ (eF y) := congrArg τ hy.symm
        _ = eF y := by
          rw [eF_eq_algebraMap]
          exact τ.commutes y
        _ = eT x := hy
  let H : ClosedSubgroup
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
    { toSubgroup := r.range
      isClosed' := by
        change IsClosed (Set.range r)
        have hrClosed :
            IsClosed
              (Set.range
                (numberFieldCyclotomicZHatCompositumRestriction F)) :=
          (isCompact_range
            (numberFieldCyclotomicZHatCompositumRestriction_continuous F)).isClosed
        simpa only [r] using hrClosed }
  change r.range = J.fixingSubgroup
  calc
    r.range =
        (IntermediateField.fixedField r.range).fixingSubgroup :=
      (by
        have hH := InfiniteGalois.fixingSubgroup_fixedField H
        change
          (IntermediateField.fixedField r.range).fixingSubgroup =
            r.range at hH
        exact hH.symm)
    _ = J.fixingSubgroup :=
      congrArg
        (fun E : IntermediateField ℚ rationalCyclotomicZHatField =>
          E.fixingSubgroup)
        hfixedField

/-- The genuine cyclotomic `ZHat` coordinate on the full compositum
over a number field. -/
noncomputable def numberFieldCyclotomicZHatCompositumCoordinate
    (F : Type*) [Field F] [NumberField F] :
    Gal(numberFieldCyclotomicZHatCompositum F / F) →*
      Multiplicative ZHat :=
  rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom.comp
    (numberFieldCyclotomicZHatCompositumRestriction F)

/-- The genuine cyclotomic coordinate on the full compositum is
injective. -/
theorem numberFieldCyclotomicZHatCompositumCoordinate_injective
    (F : Type*) [Field F] [NumberField F] :
    Function.Injective
      (numberFieldCyclotomicZHatCompositumCoordinate F) :=
  rationalCyclotomicZHatFieldGalEquivZHat.injective.comp
    (numberFieldCyclotomicZHatCompositumRestriction_injective F)

/-- The actual cyclotomic `ZHat`-compositum over every number field
has torsion-free Galois group. -/
noncomputable instance
    numberFieldCyclotomicZHatCompositumGal_isMulTorsionFree
    (F : Type*) [Field F] [NumberField F] :
    IsMulTorsionFree
      (Gal(numberFieldCyclotomicZHatCompositum F / F)) :=
  Function.Injective.isMulTorsionFree
    (numberFieldCyclotomicZHatCompositumCoordinate F)
    (numberFieldCyclotomicZHatCompositumCoordinate_injective F)

/-- The image of the actual cyclotomic compositum over `F` is precisely
`f_F ZHat`, where `f_F` is the degree of the genuine intersection
`F ∩ ℚ_tilde`. -/
theorem
    numberFieldCyclotomicZHatCompositumCoordinate_range_toAddSubgroup
    (F : Type*) [Field F] [NumberField F] :
    (numberFieldCyclotomicZHatCompositumCoordinate F).range.toAddSubgroup' =
      (zHatMulNat
        (cyclotomicZHatIntersectionDegree F)).toAddMonoidHom.range := by
  rw [numberFieldCyclotomicZHatCompositumCoordinate,
    MonoidHom.range_comp,
    numberFieldCyclotomicZHatCompositumRestriction_range]
  exact
    rationalCyclotomicZHatFieldGal_fixingSubgroup_image_eq_mulNat_range
      F

/-- A surjective restriction map admits positive cyclotomic-degree
lifts as soon as the degrees contributed by its kernel have finite
index in `ZHat`.

This is the group-theoretic core of the decomposition-compatible
Frobenius lift: the initial preimage is corrected inside the genuine
restriction kernel, so its prescribed image is unchanged. -/
theorem exists_positiveZHatDegree_lift_of_surjective
    {D A : Type*} [Group D] [Group A]
    (restriction : D →* A)
    (hrestriction : Function.Surjective restriction)
    (degree : D →* Multiplicative ZHat)
    (hdegree :
      ((restriction.ker.map degree).toAddSubgroup').index ≠ 0)
    (σ : A) :
    ∃ τ : D,
      restriction τ = σ ∧
        ∃ n : ℕ, 0 < n ∧
          degree τ =
            (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
  obtain ⟨s, hs⟩ := hrestriction σ
  let H : AddSubgroup ZHat :=
    (restriction.ker.map degree).toAddSubgroup'
  obtain ⟨n, hn, hmem⟩ :=
    exists_positive_nsmul_one_sub_mem_of_index_ne_zero
      H hdegree (Multiplicative.toAdd (degree s))
  have hcorrection :
      n • (1 : ZHat) -
          Multiplicative.toAdd (degree s) ∈ H := by
    simpa only [neg_sub] using H.neg_mem hmem
  rw [Subgroup.mem_toAddSubgroup'] at hcorrection
  obtain ⟨k, hk, hdk⟩ := hcorrection
  refine ⟨s * k, ?_, ⟨n, hn, ?_⟩⟩
  · rw [map_mul, hs]
    change restriction k = 1 at hk
    rw [hk, mul_one]
  · apply Multiplicative.ext
    rw [map_mul]
    rw [toAdd_mul, toAdd_pow, toAdd_ofAdd]
    have hdk' := congrArg Multiplicative.toAdd hdk
    rw [toAdd_ofAdd] at hdk'
    rw [hdk']
    abel

/-- Two homomorphisms out of a finite commutative group agree once
they agree on every primary component.

This is the precise prime-power reduction used in the finite-place
argument.  It is proved from the actual direct-product decomposition
by the Sylow subgroups; no cyclicity hypothesis on the whole group is
introduced. -/
theorem MonoidHom.ext_of_eq_on_finitePrimaryComponents
    {G A : Type*}
    [CommGroup G] [Finite G]
    [CommGroup A]
    (f g : G →* A)
    (hprimary :
      ∀ (p : ℕ) (_hp : Fact p.Prime)
        (x : CommGroup.primaryComponent G p),
        f x = g x) :
    f = g := by
  classical
  let sylowFintype (p : ℕ) : Fintype (Sylow p G) :=
    Fintype.ofFinite _
  let e :
      (∀ p : (Nat.card G).primeFactors,
        ∀ P : Sylow p.1 G, P) ≃* G :=
    Sylow.directProductOfNormal
      (G := G)
      (fun P =>
        Subgroup.normal_of_isMulCommutative
          (P : Subgroup G))
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy :
      y =
        ∏ p : (Nat.card G).primeFactors,
          ∏ P : Sylow p.1 G,
            Pi.mulSingle p
              (Pi.mulSingle P (y p P)) := by
    calc
      y =
          ∏ p : (Nat.card G).primeFactors,
            Pi.mulSingle p (y p) :=
        (Finset.univ_prod_mulSingle y).symm
      _ =
          ∏ p : (Nat.card G).primeFactors,
            Pi.mulSingle p
              (∏ P : Sylow p.1 G,
                Pi.mulSingle P (y p P)) := by
        apply Finset.prod_congr rfl
        intro p _
        rw [Finset.univ_prod_mulSingle]
      _ =
          ∏ p : (Nat.card G).primeFactors,
            ∏ P : Sylow p.1 G,
              Pi.mulSingle p
                (Pi.mulSingle P (y p P)) := by
        apply Finset.prod_congr rfl
        intro p _
        exact
          map_prod
            (MonoidHom.mulSingle
              (fun q : (Nat.card G).primeFactors =>
                ∀ Q : Sylow q.1 G, Q) p)
            (fun P : Sylow p.1 G =>
              Pi.mulSingle P (y p P)) Finset.univ
  have hfactor
      (p : (Nat.card G).primeFactors)
      (P : Sylow p.1 G) :
      f (e (Pi.mulSingle p
          (Pi.mulSingle P (y p P)))) =
        g (e (Pi.mulSingle p
          (Pi.mulSingle P (y p P)))) := by
    let hpFact : Fact (Nat.Prime p.1) :=
      ⟨Nat.prime_of_mem_primeFactors p.2⟩
    let u :
        ∀ q : (Nat.card G).primeFactors,
          ∀ Q : Sylow q.1 G, Q :=
      Pi.mulSingle p
        (Pi.mulSingle P (y p P))
    let z : G := e u
    have hz :
        z ∈ CommGroup.primaryComponent G p.1 := by
      obtain ⟨n, hn⟩ :=
        P.isPGroup' (y p P)
      refine ⟨n, ?_⟩
      have hu : u ^ p.1 ^ n = 1 := by
        dsimp only [u]
        rw [← Pi.mulSingle_pow,
          ← Pi.mulSingle_pow,
          hn,
          Pi.mulSingle_one,
          Pi.mulSingle_one]
      calc
        z ^ p.1 ^ n = e (u ^ p.1 ^ n) := by
          exact (map_pow e u (p.1 ^ n)).symm
        _ = e 1 := by rw [hu]
        _ = 1 := map_one e
    exact
      hprimary p.1 hpFact
        ⟨z, hz⟩
  rw [hy]
  simp only [map_prod, hfactor]

/-- Every individual `p`-adic coordinate of the profinite integers is
surjective.  This is extracted from the genuine Chinese-remainder
equivalence `ZHat ≃ ∏ p, ℤ_p`. -/
theorem zHatToPadicInt_surjective
    (p : Nat.Primes) :
    Function.Surjective (zHatToPadicInt p) := by
  classical
  intro x
  let y : ProfiniteIntegerPrimeProduct :=
    Pi.single p x
  obtain ⟨z, hz⟩ :=
    zHatToProfiniteIntegerPrimeProduct_surjective y
  refine ⟨z, ?_⟩
  have hp := congrFun hz p
  simpa only [zHatToProfiniteIntegerPrimeProduct_apply,
    y, Pi.single_eq_same] using hp

/-- The genuine `p`-adic cyclotomic coordinate on the actual Galois
group of the rational cyclotomic `ZHat`-extension. -/
noncomputable def rationalCyclotomicPadicCoordinate
    (p : Nat.Primes) :
    (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) →ₜ*
      Multiplicative ℤ_[p.1] := by
  let pCoordinate :
      Multiplicative ZHat →ₜ*
        Multiplicative ℤ_[p.1] :=
    ⟨AddMonoidHom.toMultiplicative
        (zHatToPadicInt p).toAddMonoidHom,
      continuous_ofAdd.comp
        ((continuous_zHatToPadicInt p).comp
          continuous_toAdd)⟩
  exact
    pCoordinate.comp
      (ContinuousMonoidHom.toContinuousMonoidHom
        rationalCyclotomicZHatFieldGalEquivZHat)

/-- The rational cyclotomic `p`-adic coordinate is obtained by applying the
canonical `ZHat`-to-`ℤ_p` coordinate to the cyclotomic character. -/
@[simp]
theorem rationalCyclotomicPadicCoordinate_apply
    (p : Nat.Primes)
    (σ :
      rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :
    Multiplicative.toAdd
        (rationalCyclotomicPadicCoordinate p σ) =
      zHatToPadicInt p
        (Multiplicative.toAdd
          (rationalCyclotomicZHatFieldGalEquivZHat σ)) :=
  rfl

/-- The `p`-adic cyclotomic coordinate on the actual decomposition
group of an arbitrary absolute value of the number-field cyclotomic
`ZHat`-compositum.

This is the restriction of the genuine compositum Galois group to the
rational cyclotomic factor, followed by its actual `ℤ_p` coordinate.
The source is the valuation stabilizer itself, rather than an abstract
copy of a local Galois group. -/
noncomputable def
    numberFieldCyclotomicPadicDecompositionCoordinate
    (F : Type) [Field F] [NumberField F]
    (wC : AbsoluteValue
      (numberFieldCyclotomicZHatCompositum F) ℝ)
    (p : Nat.Primes) :
    absoluteValueDecompositionGroup F wC →ₜ*
      Multiplicative ℤ_[p.1] where
  toMonoidHom :=
    (rationalCyclotomicPadicCoordinate p).toMonoidHom.comp
      ((numberFieldCyclotomicZHatCompositumRestriction F).comp
        (absoluteValueDecompositionGroup F wC).subtype)
  continuous_toFun :=
    (rationalCyclotomicPadicCoordinate p).continuous_toFun.comp
      ((numberFieldCyclotomicZHatCompositumRestriction_continuous
        (K := F)).comp continuous_subtype_val)

/-- The decomposition-group coordinate is the rational cyclotomic coordinate
of the restricted global automorphism. -/
@[simp]
theorem numberFieldCyclotomicPadicDecompositionCoordinate_apply
    (F : Type) [Field F] [NumberField F]
    (wC : AbsoluteValue
      (numberFieldCyclotomicZHatCompositum F) ℝ)
    (p : Nat.Primes)
    (σ : absoluteValueDecompositionGroup F wC) :
    numberFieldCyclotomicPadicDecompositionCoordinate
        F wC p σ =
      rationalCyclotomicPadicCoordinate p
        (numberFieldCyclotomicZHatCompositumRestriction F σ.1) :=
  rfl

/-- On an actual global Artin symbol lying in a decomposition group,
the decomposition coordinate is the `p`-adic coordinate of the
rational cyclotomic idèle value of the ordinary field norm. -/
theorem
    numberFieldCyclotomicPadicDecompositionCoordinate_infiniteGlobalArtin
    (F : Type) [Field F] [NumberField F]
    (wC : AbsoluteValue
      (numberFieldCyclotomicZHatCompositum F) ℝ)
    (p : Nat.Primes) (a : IdeleGroup F)
    (ha :
      infiniteGlobalArtinMonoidHom F
          (numberFieldCyclotomicZHatCompositum F) a ∈
        absoluteValueDecompositionGroup F wC) :
    numberFieldCyclotomicPadicDecompositionCoordinate
        F wC p
        ⟨infiniteGlobalArtinMonoidHom F
          (numberFieldCyclotomicZHatCompositum F) a, ha⟩ =
      Multiplicative.ofAdd
        (zHatToPadicInt p
          (Multiplicative.toAdd
            (rationalCyclotomicZHatIdeleValue
              (IdeleGroup.norm ℚ F a)))) := by
  apply Multiplicative.ext
  rw [
    numberFieldCyclotomicPadicDecompositionCoordinate_apply,
    numberFieldCyclotomicZHatCompositumRestriction_infiniteGlobalArtinMonoidHom,
    rationalCyclotomicPadicCoordinate_apply,
    rationalCyclotomicZHatIdeleValue_apply]
  rfl

/-- The image of a cyclotomic `p`-adic decomposition coordinate is
closed.  This is the compact image of the actual closed decomposition
group in the Krull topology. -/
theorem
    numberFieldCyclotomicPadicDecompositionCoordinate_range_isClosed
    (F : Type) [Field F] [NumberField F]
    (wC : AbsoluteValue
      (numberFieldCyclotomicZHatCompositum F) ℝ)
    (p : Nat.Primes) :
    IsClosed
      ((numberFieldCyclotomicPadicDecompositionCoordinate
        F wC p).range :
        Set (Multiplicative ℤ_[p.1])) := by
  let :
      CompactSpace
        (absoluteValueDecompositionGroup F wC) :=
    isCompact_iff_compactSpace.mp
      (absoluteValueDecompositionGroup_isClosed F wC).isCompact
  rw [MonoidHom.coe_range]
  exact
    (isCompact_range
      (numberFieldCyclotomicPadicDecompositionCoordinate
        F wC p).continuous_toFun).isClosed

/-- Reduction of the full cyclotomic character of a rational one-place
idèle whose component is a power of a principal local component.  The
result is the same power of the genuine chosen local Artin character. -/
theorem
    rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_principalComponent_toZModPow
    (p q : Nat.Primes) (k d : ℕ) (x : ℚˣ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (KummerTheory.rationalCyclotomicCharacterPrimeProduct
          (infiniteGlobalArtinMonoidHom
            ℚ KummerTheory.rationalCyclotomicField
            (IdeleGroup.finitePlaceIdele
              (RayClass.rationalPrime q)
              ((IdeleGroup.finiteComponent
                (RayClass.rationalPrime q)
                (IdeleGroup.principalIdele ℚ x)) ^ d))) p) =
      (rationalCyclotomicPrincipalFinitePlaceCharacter
        p k x q) ^ d := by
  have hprime :
      RayClass.rationalPrime q =
        ((Rat.HeightOneSpectrum.primesEquiv
          (R := NumberField.RingOfIntegers ℚ)).symm q) := by
    rfl
  rw [
    rationalCyclotomicGlobalArtin_character_toZModPow,
    globalArtinMonoidHom_finitePlaceIdele,
    hprime,
    map_pow,
    map_pow]
  exact
    congrArg (fun u => u ^ d)
      (rationalCyclotomicPrincipalFinitePlaceCharacter_chosenArtin_spec
        p k x q).symm

/-- At the place `p`, the full `p`-adic cyclotomic character of the
one-place idèle obtained from the rational unit `p + 1` is the direct
unit `p + 1`, with the prescribed local-degree power. -/
theorem
    rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_primeSucc
    (p : Nat.Primes) (d : ℕ) :
    KummerTheory.rationalCyclotomicCharacterPrimeProduct
        (infiniteGlobalArtinMonoidHom
          ℚ KummerTheory.rationalCyclotomicField
          (IdeleGroup.finitePlaceIdele
            (RayClass.rationalPrime p)
            ((IdeleGroup.finiteComponent
              (RayClass.rationalPrime p)
              (IdeleGroup.principalIdele ℚ
                (Units.mk0
                  ((p.1 + 1 : ℕ) : ℚ)
                  (by positivity)))) ^ d))) p =
      (padicNatUnit p (p.1 + 1)
        (Nat.coprime_self_add_right.mpr
          (Nat.coprime_one_right p.1))) ^ d := by
  let x : ℚˣ :=
    Units.mk0
      ((p.1 + 1 : ℕ) : ℚ)
      (by positivity)
  have hx :
      (x : ℚ) =
        ((p.1 + 1 : ℕ) : ℚ) :=
    rfl
  have hprimeUnit :
      (rationalPrimeUnit x p : ℚ) =
        ((p.1 + 1 : ℕ) : ℚ) := by
    rw [rationalPrimeUnit_val,
      hx,
      padicValRat_rationalPrime_succ,
      neg_zero,
      zpow_zero,
      one_mul]
  have hunit :
      padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p) =
        padicNatUnit p (p.1 + 1)
          (Nat.coprime_self_add_right.mpr
            (Nat.coprime_one_right p.1)) := by
    apply Units.ext
    apply Subtype.ext
    rw [padicIntUnitOfRat_coe,
      padicNatUnit_val,
      hprimeUnit]
    exact PadicInt.coe_natCast (p.1 + 1)
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  let hpFact : Fact (Nat.Prime p.1) := ⟨p.2⟩
  have hred :=
    rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_principalComponent_toZModPow
      p p k d x
  rw [
    rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime p k x,
    hunit] at hred
  have hredVal := congrArg Units.val hred
  simp only [Units.coe_map, Units.val_pow_eq_pow_val] at hredVal
  have htoZModPow (z : ℤ_[p.1]) :
      (PadicInt.toZModPow
          (p := p.1) (k : ℕ)).toMonoidHom z =
        PadicInt.toZModPow (p := p.1) (k : ℕ) z :=
    rfl
  simp only [htoZModPow] at hredVal
  simpa only [x, Units.val_pow_eq_pow_val, map_pow] using hredVal

/-- Away from `p`, the full `p`-adic cyclotomic character of the
rational-prime one-place idèle is inverse arithmetic Frobenius, again
with the prescribed local-degree power. -/
theorem
    rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_primeAway
    (p q : Nat.Primes) (hqp : q ≠ p) (d : ℕ) :
    KummerTheory.rationalCyclotomicCharacterPrimeProduct
        (infiniteGlobalArtinMonoidHom
          ℚ KummerTheory.rationalCyclotomicField
          (IdeleGroup.finitePlaceIdele
            (RayClass.rationalPrime q)
            ((IdeleGroup.finiteComponent
              (RayClass.rationalPrime q)
              (IdeleGroup.principalIdele ℚ
                (Units.mk0 (q.1 : ℚ)
                  (by exact_mod_cast q.2.ne_zero)))) ^ d))) p =
      ((padicNatUnit p q.1
        ((Nat.coprime_primes p.2 q.2).2
          (fun hpq =>
            hqp (Subtype.ext hpq.symm))))⁻¹) ^ d := by
  let x : ℚˣ :=
    Units.mk0 (q.1 : ℚ)
      (by exact_mod_cast q.2.ne_zero)
  let hcoprime : p.1.Coprime q.1 :=
    (Nat.coprime_primes p.2 q.2).2
      (fun hpq =>
        hqp (Subtype.ext hpq.symm))
  have hx : (x : ℚ) = q.1 := rfl
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  let hpFact : Fact (Nat.Prime p.1) := ⟨p.2⟩
  have hlocal :
      rationalCyclotomicPrincipalFinitePlaceCharacter
          p k x q =
        (ZMod.unitOfCoprime q.1
          (q.2.coprime_iff_not_dvd.mpr
            (rationalPrime_not_dvd_pow_of_ne
              q p hqp k)))⁻¹ := by
    rw [
      rationalCyclotomicPrincipalFinitePlaceCharacter_of_ne
        p q hqp k x,
      hx,
      padicValRat.self q.2.one_lt,
      zpow_neg,
      zpow_one]
  have hred :=
    rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_principalComponent_toZModPow
      p q k d x
  rw [hlocal] at hred
  have htarget :
      Units.map
          (PadicInt.toZModPow
            (p := p.1) (k : ℕ)).toMonoidHom
          (((padicNatUnit p q.1 hcoprime)⁻¹) ^ d) =
        ((ZMod.unitOfCoprime q.1
          (hcoprime.symm.pow_right k))⁻¹) ^ d := by
    rw [map_pow, map_inv,
      padicNatUnit_toZModPow]
  have hredVal :=
    congrArg Units.val (hred.trans htarget.symm)
  simp only [Units.coe_map, Units.val_pow_eq_pow_val] at hredVal
  have htoZModPow (z : ℤ_[p.1]) :
      (PadicInt.toZModPow
          (p := p.1) (k : ℕ)).toMonoidHom z =
        PadicInt.toZModPow (p := p.1) (k : ℕ) z :=
    rfl
  simp only [htoZModPow] at hredVal
  simpa only [x, hcoprime, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val] using hredVal

/-- The image of the actual decomposition group has a nonzero
`p`-adic cyclotomic coordinate.

The witness is a genuine one-place idèle over `F`.  Its component is
obtained by extending a rational completion unit to the chosen place:
at residue characteristic `p` we use `p + 1`, and away from `p` we use
the rational residue prime.  The ordinary idèle norm is the corresponding
positive local-degree power.  The direct-unit and inverse-Frobenius
local formulas show that its full `p`-adic cyclotomic character is
non-torsion, so its torsion-free coordinate cannot vanish. -/
theorem
    numberFieldCyclotomicPadicDecompositionCoordinate_range_toAddSubgroup_ne_bot
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (wC : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v)
      (numberFieldCyclotomicZHatCompositum F))
    (p : Nat.Primes) :
    (numberFieldCyclotomicPadicDecompositionCoordinate
        F wC.1 p).range.toAddSubgroup' ≠
      (⊥ : AddSubgroup ℤ_[p.1]) := by
  let q₀ : HeightOneSpectrum (𝓞 ℚ) :=
    _root_.finitePlaceBelow (K := ℚ) v
  let q : Nat.Primes :=
    Rat.HeightOneSpectrum.primesEquiv
      (R := 𝓞 ℚ) q₀
  have hq :
      RayClass.rationalPrime q = q₀ := by
    simpa only [q] using
      (Rat.HeightOneSpectrum.primesEquiv
        (R := 𝓞 ℚ)).symm_apply_apply q₀
  let x : ℚˣ :=
    if q = p then
      Units.mk0
        ((p.1 + 1 : ℕ) : ℚ)
        (by positivity)
    else
      Units.mk0 (q.1 : ℚ)
        (by exact_mod_cast q.2.ne_zero)
  let b : (q₀.adicCompletion ℚ)ˣ :=
    IdeleGroup.finiteComponent q₀
      (IdeleGroup.principalIdele ℚ x)
  let d : ℕ :=
    IdeleGroup.finitePlaceCompletionDegree
      (K := ℚ) (L := F) v
  have hd : 0 < d :=
    IdeleGroup.finitePlaceCompletionDegree_pos
      (K := ℚ) (L := F) v
  let a : IdeleGroup F :=
    IdeleGroup.finitePlaceIdele v
      (IdeleGroup.finitePlaceBaseUnitExtension
        (K := ℚ) (L := F) v b)
  have hnorm :
      IdeleGroup.norm ℚ F a =
        IdeleGroup.finitePlaceIdele q₀ (b ^ d) := by
    exact
      IdeleGroup.norm_finitePlaceIdele_finitePlaceBaseUnitExtension
        (K := ℚ) (L := F) v b
  have hArtin :
      infiniteGlobalArtinMonoidHom F
          (numberFieldCyclotomicZHatCompositum F) a ∈
        absoluteValueDecompositionGroup F wC.1 := by
    exact
      infiniteGlobalArtinMonoidHom_finitePlaceIdele_mem_absoluteValueDecompositionGroup
        v wC
        (IdeleGroup.finitePlaceBaseUnitExtension
          (K := ℚ) (L := F) v b)
  let τ :
      absoluteValueDecompositionGroup F wC.1 :=
    ⟨infiniteGlobalArtinMonoidHom F
        (numberFieldCyclotomicZHatCompositum F) a,
      hArtin⟩
  have hτne :
      numberFieldCyclotomicPadicDecompositionCoordinate
          F wC.1 p τ ≠ 1 := by
    intro hτone
    have hcoordinate :=
      numberFieldCyclotomicPadicDecompositionCoordinate_infiniteGlobalArtin
        F wC.1 p a hArtin
    have hfreeNorm :
        zHatToPadicInt p
            (Multiplicative.toAdd
              (rationalCyclotomicZHatIdeleValue
                (IdeleGroup.norm ℚ F a))) =
          0 := by
      have hone :
          Multiplicative.ofAdd
              (zHatToPadicInt p
                (Multiplicative.toAdd
                  (rationalCyclotomicZHatIdeleValue
                    (IdeleGroup.norm ℚ F a)))) =
            1 :=
        hcoordinate.symm.trans hτone
      exact congrArg Multiplicative.toAdd hone
    rw [hnorm,
      rationalCyclotomicZHatIdeleValue_eq_fullCharacterFreePart]
        at hfreeNorm
    let σQ :=
      infiniteGlobalArtinMonoidHom
        ℚ KummerTheory.rationalCyclotomicField
        (IdeleGroup.finitePlaceIdele q₀ (b ^ d))
    let u : ZHatˣ :=
      KummerTheory.rationalCyclotomicCharacterContinuousMulEquiv σQ
    have hfree :
        zHatToPadicInt p
            (Multiplicative.toAdd
              (KummerTheory.zHatUnitsDecomposition u).1) =
          0 := by
      simpa only [u, σQ] using hfreeNorm
    have hfinite :
        IsOfFinOrder
          (KummerTheory.rationalCyclotomicCharacterPrimeProduct
            σQ p) := by
      have htorsion :=
        KummerTheory.zHatUnit_padicCoordinate_isOfFinOrder_of_freeCoordinate_eq_zero
          u p hfree
      simpa only [
        u,
        KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter]
        using htorsion
    by_cases hqp : q = p
    · have hcharacter :
          KummerTheory.rationalCyclotomicCharacterPrimeProduct
              σQ p =
            (padicNatUnit p (p.1 + 1)
              (Nat.coprime_self_add_right.mpr
                (Nat.coprime_one_right p.1))) ^ d := by
        dsimp only [σQ, b, x]
        rw [ite_eq_left hqp, ← hq, hqp]
        exact
          rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_primeSucc
            p d
      have hpowerFinite :
          IsOfFinOrder
            ((padicNatUnit p (p.1 + 1)
              (Nat.coprime_self_add_right.mpr
                (Nat.coprime_one_right p.1))) ^ d) := by
        rw [← hcharacter]
        exact hfinite
      have hbaseFinite := hpowerFinite.of_pow hd.ne'
      exact
        (padicNatUnit_not_isOfFinOrder_of_one_lt
          p (p.1 + 1)
          (Nat.coprime_self_add_right.mpr
            (Nat.coprime_one_right p.1))
          (Nat.lt_trans p.2.one_lt
            (Nat.lt_succ_self p.1))) hbaseFinite
    · let hcoprime : p.1.Coprime q.1 :=
        (Nat.coprime_primes p.2 q.2).2
          (fun hpq =>
            hqp (Subtype.ext hpq.symm))
      have hcharacter :
          KummerTheory.rationalCyclotomicCharacterPrimeProduct
              σQ p =
            ((padicNatUnit p q.1 hcoprime)⁻¹) ^ d := by
        dsimp only [σQ, b, x]
        rw [ite_eq_right hqp, ← hq]
        simpa only [hcoprime] using
          rationalCyclotomicCharacterPrimeProduct_finitePlaceIdele_primeAway
            p q hqp d
      have hinversePowerFinite :
          IsOfFinOrder
            (((padicNatUnit p q.1 hcoprime)⁻¹) ^ d) := by
        rw [← hcharacter]
        exact hfinite
      have hinverseFinite := hinversePowerFinite.of_pow hd.ne'
      have hbaseFinite := hinverseFinite.of_inv
      exact
        (padicNatUnit_not_isOfFinOrder_of_one_lt
          p q.1 hcoprime q.2.one_lt) hbaseFinite
  intro hbot
  have hmem :
      Multiplicative.toAdd
          (numberFieldCyclotomicPadicDecompositionCoordinate
            F wC.1 p τ) ∈
        (numberFieldCyclotomicPadicDecompositionCoordinate
          F wC.1 p).range.toAddSubgroup' := by
    rw [Subgroup.mem_toAddSubgroup', ofAdd_toAdd]
    exact ⟨τ, rfl⟩
  rw [hbot] at hmem
  exact
    hτne
      (congrArg Multiplicative.ofAdd
        (AddSubgroup.mem_bot.mp hmem))

/-- The actual `p`-adic coordinate of a finite-place decomposition
group has finite index in `ℤ_[p]`.  This is the precise nonvanishing
input used to correct a Frobenius lift inside the restriction kernel. -/
theorem
    numberFieldCyclotomicPadicDecompositionCoordinate_range_index_ne_zero
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (wC : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v)
      (numberFieldCyclotomicZHatCompositum F))
    (p : Nat.Primes) :
    ((numberFieldCyclotomicPadicDecompositionCoordinate
        F wC.1 p).range.toAddSubgroup').index ≠ 0 := by
  let H : AddSubgroup ℤ_[p.1] :=
    (numberFieldCyclotomicPadicDecompositionCoordinate
      F wC.1 p).range.toAddSubgroup'
  have hclosed :
      IsClosed (H : Set ℤ_[p.1]) := by
    change
      IsClosed
        ((numberFieldCyclotomicPadicDecompositionCoordinate
          F wC.1 p).range :
          Set (Multiplicative ℤ_[p.1]))
    exact
      numberFieldCyclotomicPadicDecompositionCoordinate_range_isClosed
        F wC.1 p
  have hne : H ≠ ⊥ :=
    numberFieldCyclotomicPadicDecompositionCoordinate_range_toAddSubgroup_ne_bot
      F v wC p
  have hopen : IsOpen (H : Set ℤ_[p.1]) :=
    PadicInt.addSubgroup_isOpen_of_isClosed_of_ne_bot
      p.1 H hclosed hne
  let : Finite (ℤ_[p.1] ⧸ H) :=
    AddSubgroup.quotient_finite_of_isOpen H hopen
  exact H.index_ne_zero_of_finite

/-- The finite-index conclusion depends only on the valuation
class of the chosen absolute value on the cyclotomic compositum. -/
theorem
    numberFieldCyclotomicPadicDecompositionCoordinate_range_index_ne_zero_of_isEquiv
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (wC : AbsoluteValue
      (numberFieldCyclotomicZHatCompositum F) ℝ)
    (wC' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v)
      (numberFieldCyclotomicZHatCompositum F))
    (hww' : wC.IsEquiv wC'.1)
    (p : Nat.Primes) :
    ((numberFieldCyclotomicPadicDecompositionCoordinate
        F wC p).range.toAddSubgroup').index ≠ 0 := by
  have hD :
      absoluteValueDecompositionGroup F wC =
        absoluteValueDecompositionGroup F wC'.1 :=
    absoluteValueDecompositionGroup_eq_of_absoluteValue_isEquiv
      wC wC'.1 hww'
  have hrange :
      (numberFieldCyclotomicPadicDecompositionCoordinate
          F wC p).range =
        (numberFieldCyclotomicPadicDecompositionCoordinate
          F wC'.1 p).range := by
    ext y
    constructor
    · rintro ⟨σ, rfl⟩
      let σ' :
          absoluteValueDecompositionGroup F wC'.1 :=
        ⟨σ.1, by
          rw [← hD]
          exact σ.2⟩
      exact ⟨σ', rfl⟩
    · rintro ⟨σ, rfl⟩
      let σ' :
          absoluteValueDecompositionGroup F wC :=
        ⟨σ.1, by
          rw [hD]
          exact σ.2⟩
      exact ⟨σ', rfl⟩
  rw [hrange]
  exact
    numberFieldCyclotomicPadicDecompositionCoordinate_range_index_ne_zero
      F v wC' p

/-- The finite-index conclusion for an arbitrary representative of the
valuation class above `v`.

The hypothesis only compares the restriction of the chosen absolute value
with the normalized `v`-adic absolute value.  We raise the chosen
nonarchimedean absolute value to the unique positive normalizing exponent,
obtaining an exact extension without changing its decomposition group. -/
theorem
    numberFieldCyclotomicPadicDecompositionCoordinate_range_index_ne_zero_of_base_isEquiv
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (wC : AbsoluteValue
      (numberFieldCyclotomicZHatCompositum F) ℝ)
    (hbase :
      (wC.comp
          (f := algebraMap F
            (numberFieldCyclotomicZHatCompositum F))
          (algebraMap F
            (numberFieldCyclotomicZHatCompositum F)).injective).IsEquiv
        (NumberField.HeightOneSpectrum.adicAbv F v))
    (p : Nat.Primes) :
    ((numberFieldCyclotomicPadicDecompositionCoordinate
        F wC p).range.toAddSubgroup').index ≠ 0 := by
  let vF : AbsoluteValue F ℝ :=
    NumberField.HeightOneSpectrum.adicAbv F v
  let wF : AbsoluteValue F ℝ :=
    wC.comp
      (f := algebraMap F
        (numberFieldCyclotomicZHatCompositum F))
      (algebraMap F
        (numberFieldCyclotomicZHatCompositum F)).injective
  have hvFna : IsNonarchimedean (vF : F → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
  have hwFna : IsNonarchimedean (wF : F → ℝ) := by
    rw [AbsoluteValue.isNonarchimedean_iff_bounded_nat]
    refine ⟨1, ?_⟩
    intro n
    exact
      (hbase.le_one_iff).2
        (hvFna.apply_natCast_le_one
          (map_zero_le vF 1) (map_one vF))
  have hwCna :
      IsNonarchimedean
        (wC :
          numberFieldCyclotomicZHatCompositum F → ℝ) := by
    rw [AbsoluteValue.isNonarchimedean_iff_bounded_nat]
    refine ⟨1, ?_⟩
    intro n
    have hn :
        (n : numberFieldCyclotomicZHatCompositum F) =
          algebraMap F
            (numberFieldCyclotomicZHatCompositum F)
            (n : F) := by
      exact
        (map_natCast
          (algebraMap F
            (numberFieldCyclotomicZHatCompositum F)) n).symm
    rw [hn]
    exact
      hwFna.apply_natCast_le_one
        (map_zero_le wF 1) (map_one wF)
  obtain ⟨c, hc, hpow⟩ :=
    (AbsoluteValue.isEquiv_iff_exists_rpow_eq).1 hbase
  let wC' :
      AbsoluteValueExtension vF
        (numberFieldCyclotomicZHatCompositum F) :=
    ⟨AbsoluteValue.nonarchimedeanRpow
        wC hwCna c hc,
      by
        intro x
        change
          wC
                (algebraMap F
                  (numberFieldCyclotomicZHatCompositum F) x) ^
              c =
            vF x
        exact congrFun hpow x⟩
  have hwwC' : wC.IsEquiv wC'.1 :=
    AbsoluteValue.isEquiv_nonarchimedeanRpow
      wC hwCna c hc
  exact
    numberFieldCyclotomicPadicDecompositionCoordinate_range_index_ne_zero_of_isEquiv
      F v wC wC' hwwC' p

/-- The actual cyclotomic `p`-adic coordinate is onto. -/
theorem rationalCyclotomicPadicCoordinate_surjective
    (p : Nat.Primes) :
    Function.Surjective
      (rationalCyclotomicPadicCoordinate p) := by
  intro y
  obtain ⟨z, hz⟩ :=
    zHatToPadicInt_surjective p
      (Multiplicative.toAdd y)
  obtain ⟨σ, hσ⟩ :=
    rationalCyclotomicZHatFieldGalEquivZHat.surjective
      (Multiplicative.ofAdd z)
  refine ⟨σ, ?_⟩
  apply Multiplicative.ext
  rw [rationalCyclotomicPadicCoordinate_apply, hσ]
  exact hz

/-- The closed subgroup fixing the `p`-primary cyclotomic direction. -/
noncomputable def rationalCyclotomicPadicKernel
    (p : Nat.Primes) :
    ClosedSubgroup
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) where
  toSubgroup :=
    (rationalCyclotomicPadicCoordinate p).toMonoidHom.ker
  isClosed' := by
    change
      IsClosed
        ((rationalCyclotomicPadicCoordinate p) ⁻¹'
          ({1} : Set (Multiplicative ℤ_[p.1])))
    exact
      isClosed_singleton.preimage
        (rationalCyclotomicPadicCoordinate p).continuous_toFun

/-- The closed `p`-adic coordinate kernel is normal because it is the
kernel of a group homomorphism. -/
instance rationalCyclotomicPadicKernel_normal
    (p : Nat.Primes) :
    (rationalCyclotomicPadicKernel p).toSubgroup.Normal := by
  change
    (rationalCyclotomicPadicCoordinate p).toMonoidHom.ker.Normal
  exact MonoidHom.normal_ker _

/-- The `p`-primary cyclotomic field inside the rational cyclotomic
`ZHat`-extension.  Its defining subgroup is the kernel of the actual
coordinate to `ℤ_p`. -/
abbrev rationalCyclotomicPadicFieldWithinZHat
    (p : Nat.Primes) :
    IntermediateField ℚ rationalCyclotomicZHatField :=
  IntermediateField.fixedField
    (rationalCyclotomicPadicKernel p).toSubgroup

/-- The internal `p`-primary fixed field is Galois over `ℚ`. -/
noncomputable instance
    rationalCyclotomicPadicFieldWithinZHat_isGalois
    (p : Nat.Primes) :
    IsGalois ℚ (rationalCyclotomicPadicFieldWithinZHat p) := by
  change
    IsGalois ℚ
      (IntermediateField.fixedField
        (rationalCyclotomicPadicKernel p).toSubgroup)
  exact
    IsGalois.of_fixedField_normal_subgroup
      (rationalCyclotomicPadicKernel p).toSubgroup

/-- The canonical algebra maps through the internal `p`-primary fixed
field form a scalar tower. -/
instance rationalCyclotomicPadicFieldWithinZHat_scalarTower
    (p : Nat.Primes) :
    IsScalarTower ℚ (rationalCyclotomicPadicFieldWithinZHat p)
      rationalCyclotomicZHatField := by
  apply IsScalarTower.of_algebraMap_eq'
  rfl

/-- The actual `p`-primary cyclotomic field in the fixed rational
separable closure. -/
def rationalCyclotomicPadicField
    (p : Nat.Primes) :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  IntermediateField.lift
    (rationalCyclotomicPadicFieldWithinZHat p)

/-- The actual `p`-primary field is contained in the cyclotomic
`ZHat`-extension. -/
theorem rationalCyclotomicPadicField_le_cyclotomicZHatField
    (p : Nat.Primes) :
    rationalCyclotomicPadicField p ≤
      rationalCyclotomicZHatField :=
  IntermediateField.lift_le
    (rationalCyclotomicPadicFieldWithinZHat p)

/-- The fixing subgroup of the internal `p`-primary field is exactly
the kernel of the `p`-adic cyclotomic coordinate. -/
theorem rationalCyclotomicPadicFieldWithinZHat_fixingSubgroup
    (p : Nat.Primes) :
    (rationalCyclotomicPadicFieldWithinZHat p).fixingSubgroup =
      (rationalCyclotomicPadicKernel p).toSubgroup := by
  exact
    InfiniteGalois.fixingSubgroup_fixedField
      (rationalCyclotomicPadicKernel p)

/-- The Galois group of the internal `p`-primary cyclotomic field is
the actual additive group of `p`-adic integers, written
multiplicatively. -/
noncomputable def
    rationalCyclotomicPadicFieldWithinZHatGalEquivPadicInt
    (p : Nat.Primes) :
    (rationalCyclotomicPadicFieldWithinZHat p ≃ₐ[ℚ]
        rationalCyclotomicPadicFieldWithinZHat p) ≃*
      Multiplicative ℤ_[p.1] :=
  (InfiniteGalois.normalAutEquivQuotient
      (rationalCyclotomicPadicKernel p)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (rationalCyclotomicPadicCoordinate p).toMonoidHom
      (rationalCyclotomicPadicCoordinate_surjective p))

/-- Under the `ℤ_p` coordinate, restriction to the internal
`p`-primary field is exactly the original cyclotomic coordinate. -/
theorem
    rationalCyclotomicPadicFieldWithinZHatGalEquivPadicInt_restrict
    (p : Nat.Primes)
    (σ :
      rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :
    rationalCyclotomicPadicFieldWithinZHatGalEquivPadicInt p
        (AlgEquiv.restrictNormalHom
          (rationalCyclotomicPadicFieldWithinZHat p) σ) =
      rationalCyclotomicPadicCoordinate p σ := by
  let e :=
    InfiniteGalois.normalAutEquivQuotient
      (rationalCyclotomicPadicKernel p)
  let q :=
    QuotientGroup.quotientKerEquivOfSurjective
      (rationalCyclotomicPadicCoordinate p).toMonoidHom
      (rationalCyclotomicPadicCoordinate_surjective p)
  change
    q
        (e.symm (e σ)) =
      rationalCyclotomicPadicCoordinate p σ
  rw [e.symm_apply_apply]
  rfl

/-- The actual `p`-primary cyclotomic field is an abelian Galois
extension of `ℚ`. -/
noncomputable instance
    rationalCyclotomicPadicField_isAbelianGalois
    (p : Nat.Primes) :
    IsAbelianGalois ℚ (rationalCyclotomicPadicField p) := by
  exact
    @IsAbelianGalois.of_algHom
      ℚ (rationalCyclotomicPadicField p)
      rationalCyclotomicZHatField
      _ _ _ _ _
      (IntermediateField.inclusion
        (rationalCyclotomicPadicField_le_cyclotomicZHatField p))
      rationalCyclotomicZHatField_isAbelianGalois

/-- Reduction from `p`-adic integers to a finite `p`-power quotient is
surjective. -/
theorem padicIntToZModPow_surjective
    (p : Nat.Primes) (n : ℕ) :
    Function.Surjective
      (PadicInt.toZModPow
        (p := p.1) n) := by
  intro x
  refine ⟨(x.val : ℤ_[p.1]), ?_⟩
  calc
    PadicInt.toZModPow n (x.val : ℤ_[p.1]) =
        (x.val : ZMod (p.1 ^ n)) := by
      exact map_natCast
        (PadicInt.toZModPow
          (p := p.1) n) x.val
    _ = x := ZMod.natCast_zmod_val x

/-- The finite `p^n` cyclotomic coordinate on the genuine
cyclotomic `ZHat` Galois group. -/
noncomputable def rationalCyclotomicPadicReduction
    (p : Nat.Primes) (n : ℕ) :
    (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) →*
      Multiplicative (ZMod (p.1 ^ n)) :=
  (AddMonoidHom.toMultiplicative
      (PadicInt.toZModPow
        (p := p.1) n).toAddMonoidHom).comp
    (rationalCyclotomicPadicCoordinate p).toMonoidHom

/-- Finite cyclotomic reduction is obtained by reducing the `p`-adic
cyclotomic coordinate modulo `p^n`. -/
@[simp]
theorem rationalCyclotomicPadicReduction_apply
    (p : Nat.Primes) (n : ℕ)
    (σ :
      rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :
    Multiplicative.toAdd
        (rationalCyclotomicPadicReduction p n σ) =
      PadicInt.toZModPow n
        (Multiplicative.toAdd
          (rationalCyclotomicPadicCoordinate p σ)) :=
  rfl

/-- Every finite `p^n` cyclotomic coordinate is onto. -/
theorem rationalCyclotomicPadicReduction_surjective
    (p : Nat.Primes) (n : ℕ) :
    Function.Surjective
      (rationalCyclotomicPadicReduction p n) := by
  intro y
  obtain ⟨a, ha⟩ :=
    padicIntToZModPow_surjective p n
      (Multiplicative.toAdd y)
  obtain ⟨σ, hσ⟩ :=
    rationalCyclotomicPadicCoordinate_surjective p
      (Multiplicative.ofAdd a)
  refine ⟨σ, ?_⟩
  apply Multiplicative.ext
  rw [rationalCyclotomicPadicReduction_apply, hσ]
  exact ha

/-- The closed subgroup cutting out the finite `p^n` cyclotomic
layer. -/
noncomputable def rationalCyclotomicPadicLevelKernel
    (p : Nat.Primes) (n : ℕ) :
    ClosedSubgroup
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) where
  toSubgroup :=
    (rationalCyclotomicPadicReduction p n).ker
  isClosed' := by
    let c :=
      fun σ :
          rationalCyclotomicZHatField ≃ₐ[ℚ]
            rationalCyclotomicZHatField =>
        Multiplicative.toAdd
          (rationalCyclotomicPadicCoordinate p σ)
    have hc : Continuous c :=
      continuous_toAdd.comp
        (rationalCyclotomicPadicCoordinate p).continuous_toFun
    have hspan :
        IsClosed
          ((Ideal.span
            ({(p.1 : ℤ_[p.1]) ^ n} :
              Set ℤ_[p.1]) :
            Ideal ℤ_[p.1]) :
            Set ℤ_[p.1]) := by
      have hset :
          ((Ideal.span
              ({(p.1 : ℤ_[p.1]) ^ n} :
                Set ℤ_[p.1]) :
              Ideal ℤ_[p.1]) :
              Set ℤ_[p.1]) =
            Metric.closedBall 0
              ((p.1 : ℝ) ^ (-n : ℤ)) := by
        ext x
        change
          x ∈
              (Ideal.span
                ({(p.1 : ℤ_[p.1]) ^ n} : Set ℤ_[p.1]) :
                Ideal ℤ_[p.1]) ↔
            dist x 0 ≤ (p.1 : ℝ) ^ (-n : ℤ)
        rw [dist_zero_right,
          PadicInt.norm_le_pow_iff_mem_span_pow]
      rw [hset]
      exact Metric.isClosed_closedBall
    change
      IsClosed
        {σ |
          rationalCyclotomicPadicReduction p n σ = 1}
    rw [show
      {σ |
        rationalCyclotomicPadicReduction p n σ = 1} =
          c ⁻¹'
            ((Ideal.span
              ({(p.1 : ℤ_[p.1]) ^ n} :
                Set ℤ_[p.1]) :
              Ideal ℤ_[p.1]) :
              Set ℤ_[p.1]) by
      ext σ
      change
        PadicInt.toZModPow n (c σ) = 0 ↔
          c σ ∈
            (Ideal.span
              ({(p.1 : ℤ_[p.1]) ^ n} :
                Set ℤ_[p.1]) :
              Ideal ℤ_[p.1])
      rw [← PadicInt.ker_toZModPow n,
        RingHom.mem_ker]]
    exact hspan.preimage hc

/-- The finite-coordinate kernel is normal because it is the kernel of
a group homomorphism. -/
instance rationalCyclotomicPadicLevelKernel_normal
    (p : Nat.Primes) (n : ℕ) :
    (rationalCyclotomicPadicLevelKernel p n).toSubgroup.Normal := by
  change (rationalCyclotomicPadicReduction p n).ker.Normal
  exact MonoidHom.normal_ker _

/-- The finite-coordinate kernel is open in the cyclotomic Galois
group. -/
theorem rationalCyclotomicPadicLevelKernel_isOpen
    (p : Nat.Primes) (n : ℕ) :
    IsOpen
      ((rationalCyclotomicPadicLevelKernel p n :
          Subgroup
            (rationalCyclotomicZHatField ≃ₐ[ℚ]
              rationalCyclotomicZHatField)) :
        Set
          (rationalCyclotomicZHatField ≃ₐ[ℚ]
            rationalCyclotomicZHatField)) := by
  let q :=
    rationalCyclotomicPadicReduction p n
  let :
      Finite
        ((rationalCyclotomicZHatField ≃ₐ[ℚ]
            rationalCyclotomicZHatField) ⧸ q.ker) :=
    Finite.of_injective
      (QuotientGroup.quotientKerEquivOfSurjective
        q
        (rationalCyclotomicPadicReduction_surjective p n))
      (QuotientGroup.quotientKerEquivOfSurjective
        q
        (rationalCyclotomicPadicReduction_surjective p n)).injective
  let : q.ker.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  change
    IsOpen
      (q.ker :
        Set
          (rationalCyclotomicZHatField ≃ₐ[ℚ]
            rationalCyclotomicZHatField))
  exact
    q.ker.isOpen_of_isClosed_of_finiteIndex
      (rationalCyclotomicPadicLevelKernel p n).isClosed'

/-- The genuine finite cyclotomic `p^n` layer inside the actual
cyclotomic `ZHat`-extension. -/
noncomputable abbrev rationalCyclotomicPadicFiniteLevel
    (p : Nat.Primes) (n : ℕ) :
    FiniteGaloisIntermediateField
      ℚ rationalCyclotomicZHatField where
  toIntermediateField :=
    IntermediateField.fixedField
      (rationalCyclotomicPadicLevelKernel p n).toSubgroup
  finiteDimensional := by
    apply
      (InfiniteGalois.isOpen_iff_finite
        (IntermediateField.fixedField
          (rationalCyclotomicPadicLevelKernel p n).toSubgroup)).mp
    rw [
      InfiniteGalois.fixingSubgroup_fixedField
        (rationalCyclotomicPadicLevelKernel p n)]
    exact
      rationalCyclotomicPadicLevelKernel_isOpen p n
  isGalois := by infer_instance

/-- The bundled finite `p^n` layer exposes its constructed Galois
instance across the opaque field definition. -/
noncomputable instance rationalCyclotomicPadicFiniteLevel_isGalois
    (p : Nat.Primes) (n : ℕ) :
    IsGalois ℚ (rationalCyclotomicPadicFiniteLevel p n) :=
  (rationalCyclotomicPadicFiniteLevel p n).isGalois

/-- The canonical algebra maps through the finite `p^n` layer form a
scalar tower. -/
instance rationalCyclotomicPadicFiniteLevel_scalarTower
    (p : Nat.Primes) (n : ℕ) :
    IsScalarTower ℚ (rationalCyclotomicPadicFiniteLevel p n)
      rationalCyclotomicZHatField := by
  apply IsScalarTower.of_algebraMap_eq'
  rfl

/-- The Galois group of the finite `p^n` cyclotomic level is the
actual cyclic group `ZMod (p^n)`. -/
noncomputable def
    rationalCyclotomicPadicFiniteLevelGalEquivZMod
    (p : Nat.Primes) (n : ℕ) :
    (rationalCyclotomicPadicFiniteLevel p n ≃ₐ[ℚ]
        rationalCyclotomicPadicFiniteLevel p n) ≃*
      Multiplicative (ZMod (p.1 ^ n)) :=
  (InfiniteGalois.normalAutEquivQuotient
      (rationalCyclotomicPadicLevelKernel p n)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (rationalCyclotomicPadicReduction p n)
      (rationalCyclotomicPadicReduction_surjective p n))

/-- Restriction to a finite `p^n` level is exactly reduction of the
genuine `p`-adic cyclotomic coordinate modulo `p^n`. -/
theorem
    rationalCyclotomicPadicFiniteLevelGalEquivZMod_restrict
    (p : Nat.Primes) (n : ℕ)
    (σ :
      rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :
    rationalCyclotomicPadicFiniteLevelGalEquivZMod p n
        (AlgEquiv.restrictNormalHom
          (rationalCyclotomicPadicFiniteLevel p n) σ) =
      rationalCyclotomicPadicReduction p n σ := by
  let e :=
    InfiniteGalois.normalAutEquivQuotient
      (rationalCyclotomicPadicLevelKernel p n)
  let q :=
    QuotientGroup.quotientKerEquivOfSurjective
      (rationalCyclotomicPadicReduction p n)
      (rationalCyclotomicPadicReduction_surjective p n)
  change
    q
        (e.symm (e σ)) =
      rationalCyclotomicPadicReduction p n σ
  rw [e.symm_apply_apply]
  rfl

/-- The Galois group of the base-changed finite `p`-primary
cyclotomic layer, embedded in its genuine `ZMod (p^n)` coordinate. -/
noncomputable def
    numberFieldCyclotomicPadicFiniteCompositumCoordinate
    (F : Type*) [Field F] [NumberField F]
    (p : Nat.Primes) (n : ℕ) :
    Gal(numberFieldCyclotomicZHatFiniteCompositum F
          (rationalCyclotomicPadicFiniteLevel p n) / F) →*
      Multiplicative (ZMod (p.1 ^ n)) :=
  (rationalCyclotomicPadicFiniteLevelGalEquivZMod
      p n).toMonoidHom.comp
    (numberFieldCyclotomicZHatFiniteCompositumRestriction
      (F := F)
      (rationalCyclotomicPadicFiniteLevel p n))

/-- The finite base-changed cyclotomic coordinate is injective.  Thus
the actual compositum Galois group is realized as a subgroup of the
cyclic `p`-power coordinate, with no abstract replacement field. -/
theorem
    numberFieldCyclotomicPadicFiniteCompositumCoordinate_injective
    (F : Type*) [Field F] [NumberField F]
    (p : Nat.Primes) (n : ℕ) :
    Function.Injective
      (numberFieldCyclotomicPadicFiniteCompositumCoordinate
        F p n) :=
  (rationalCyclotomicPadicFiniteLevelGalEquivZMod p n).injective.comp
    (numberFieldCyclotomicZHatFiniteCompositumRestriction_injective
      (F := F)
      (rationalCyclotomicPadicFiniteLevel p n))

/-- Every actual finite base-changed `p`-primary cyclotomic layer has
cyclic Galois group.  The statement is about the genuine compositum
over `F`: cyclicity follows by embedding its Galois group into the
standard cyclic `ZMod (p^n)` coordinate. -/
theorem
    numberFieldCyclotomicPadicFiniteCompositum_isCyclic
    (F : Type*) [Field F] [NumberField F]
    (p : Nat.Primes) (n : ℕ) :
    IsCyclic
      (Gal(numberFieldCyclotomicZHatFiniteCompositum F
        (rationalCyclotomicPadicFiniteLevel p n) / F)) :=
  isCyclic_of_injective
    (numberFieldCyclotomicPadicFiniteCompositumCoordinate
      F p n)
    (numberFieldCyclotomicPadicFiniteCompositumCoordinate_injective
      F p n)

/-- The degree of the genuine finite `p^n` cyclotomic level is
exactly `p^n`. -/
theorem rationalCyclotomicPadicFiniteLevel_finrank
    (p : Nat.Primes) (n : ℕ) :
    Module.finrank ℚ
        (rationalCyclotomicPadicFiniteLevel p n) =
      p.1 ^ n := by
  let :
      FiniteDimensional ℚ
        (rationalCyclotomicPadicFiniteLevel p n).toIntermediateField :=
    (rationalCyclotomicPadicFiniteLevel p n).finiteDimensional
  calc
    Module.finrank ℚ
        (rationalCyclotomicPadicFiniteLevel p n) =
        Nat.card
          (rationalCyclotomicPadicFiniteLevel p n ≃ₐ[ℚ]
            rationalCyclotomicPadicFiniteLevel p n) :=
      (IsGalois.card_aut_eq_finrank
        ℚ (rationalCyclotomicPadicFiniteLevel p n)).symm
    _ =
        Nat.card
          (Multiplicative (ZMod (p.1 ^ n))) :=
      Nat.card_congr
        (rationalCyclotomicPadicFiniteLevelGalEquivZMod
          p n).toEquiv
    _ = Nat.card (ZMod (p.1 ^ n)) :=
      Nat.card_congr Multiplicative.toAdd
    _ = p.1 ^ n := Nat.card_zmod (p.1 ^ n)

end Reciprocity
end GlobalClassFieldTheory
