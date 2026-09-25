/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedLevel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedPrimitiveAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedPolynomialEvaluation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizerNormalization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusBaseEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusContinuity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldAlgebra
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldCoefficientDescent
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldDegree
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldGeneration
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPowerBasis
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPrimitive
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusLift
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveIrreducible
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectBracketAtCompletedLevel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracket
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracketRecursion
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectTargetLevelEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaAtCompletedLevel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFirstIdentity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFrobeniusFixed
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaIteration
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaSeries
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaAtCompletedLevel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaLocalInverse
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.AmbientBracketAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.DivisionModuleEndomorphisms
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateEndomorphism
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CompletedUnramifiedField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.ContractingEquation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.LaurentSeriesFrobenius
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldMembership
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFrobeniusFixed
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitsNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.LevelAlgebra
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.StandardSubgroupNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitQuotientCard
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitTransport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaCoefficients
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaEvaluation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaFirstIdentity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaSeries
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaUniqueness
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.RealIndexSteps
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.DivisionPolynomial
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveIrreducible
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveTorsion
/-!
# Equal-characteristic Lubin--Tate unit quotients and Galois groups

This file constructs the finite-level Galois action of a power-series unit
with the local-Artin orientation: `a` sends the chosen primitive generator
to `[a⁻¹]`.  Its kernel is the `(n + 1)`-st higher-unit subgroup, so the
action descends to a multiplicative equivalence from the finite unit
quotient to the Galois group.
-/

@[expose] public section

noncomputable
section

open scoped LaurentSeries PowerSeries Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LubinTate.EqualCharacteristic

variable {K : Type u} [Field K]

/-- The finite-level root obtained from the Artin-oriented bracket `[a⁻¹]`. -/
noncomputable def equalCharacteristicLubinTateArtinUnitLevelRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateLevelField F n :=
  equalCharacteristicLubinTateLevelBracket F n (n + 1)
    ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
    (equalCharacteristicLubinTateLevelPowerBasis F n).gen

/-- The Artin-oriented unit root annihilates the generator's minimal
polynomial. -/
theorem equalCharacteristicLubinTateArtinUnitLevelRoot_aeval_minpoly
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    Polynomial.aeval
        (equalCharacteristicLubinTateArtinUnitLevelRoot F n a)
        (minpoly F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen) = 0 := by
  rw [equalCharacteristicLubinTateLevelPowerBasis_minpoly]
  let ι : equalCharacteristicLubinTateLevelField F n →ₐ[
      F.residueField⸨X⸩] SeparableClosure F.residueField⸨X⸩ :=
    (equalCharacteristicLubinTateLevelField F n).val
  apply ι.injective
  change ι (Polynomial.aeval
      (equalCharacteristicLubinTateArtinUnitLevelRoot F n a)
      (equalCharacteristicLubinTatePrimitivePolynomial F n)) = ι 0
  rw [← Polynomial.aeval_algHom_apply (f := ι), map_zero]
  rw [Polynomial.aeval_def,
    ← equalCharacteristicSeparableBaseHom_eq_algebraMap]
  change Polynomial.eval₂
      (equalCharacteristicSeparableBaseHom F)
      (equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n))
      (equalCharacteristicLubinTatePrimitivePolynomial F n) = 0
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using
    (equalCharacteristicLubinTatePrimitivePolynomial_isRoot_bracket
      F n a⁻¹)

/-- The finite-level algebra endomorphism with Artin orientation. -/
noncomputable def equalCharacteristicLubinTateArtinUnitAlgHom
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateLevelField F n →ₐ[F.residueField⸨X⸩]
      equalCharacteristicLubinTateLevelField F n :=
  (equalCharacteristicLubinTateLevelPowerBasis F n).lift
    (equalCharacteristicLubinTateArtinUnitLevelRoot F n a)
    (equalCharacteristicLubinTateArtinUnitLevelRoot_aeval_minpoly F n a)

@[simp]
theorem equalCharacteristicLubinTateArtinUnitAlgHom_apply_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitAlgHom F n a
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      equalCharacteristicLubinTateArtinUnitLevelRoot F n a :=
  (equalCharacteristicLubinTateLevelPowerBasis F n).lift_gen _ _

/-- The finite-level Galois automorphism whose generator action is
`[a⁻¹]`. -/
noncomputable def equalCharacteristicLubinTateArtinUnitAlgEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateLevelField F n ≃ₐ[F.residueField⸨X⸩]
      equalCharacteristicLubinTateLevelField F n := by
  letI : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  exact AlgEquiv.ofBijective
    (equalCharacteristicLubinTateArtinUnitAlgHom F n a)
    (AlgHom.bijective (equalCharacteristicLubinTateArtinUnitAlgHom F n a))

@[simp]
theorem equalCharacteristicLubinTateArtinUnitAlgEquiv_apply_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitAlgEquiv F n a
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      equalCharacteristicLubinTateArtinUnitLevelRoot F n a := by
  rw [equalCharacteristicLubinTateArtinUnitAlgEquiv,
    AlgEquiv.ofBijective_apply,
    equalCharacteristicLubinTateArtinUnitAlgHom_apply_gen]

theorem equalCharacteristicLubinTateArtinUnitAlgEquiv_one
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateArtinUnitAlgEquiv F n 1 = 1 := by
  apply MulSemiringAction.toAlgHom_injective F.residueField⸨X⸩
    (equalCharacteristicLubinTateLevelField F n)
  apply (equalCharacteristicLubinTateLevelPowerBasis F n).algHom_ext
  simp only [MulSemiringAction.toAlgHom_apply, one_smul,
    AlgEquiv.smul_def]
  rw [equalCharacteristicLubinTateArtinUnitAlgEquiv_apply_gen]
  apply Subtype.ext
  change
    equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (((1 : F.residueField⟦X⟧ˣ)⁻¹ :
          F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
      chosenEqualCharacteristicLubinTatePrimitiveRoot F n
  simpa using
    (equalCharacteristicLubinTateAmbientBracket_one_apply_of_torsion F
      (equalCharacteristicSeparableCoefficientHom F)
      (equalCharacteristicSeparableUniformizer F) (n + 1)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n))

theorem equalCharacteristicLubinTateArtinUnitAlgEquiv_mul
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a b : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitAlgEquiv F n (a * b) =
      equalCharacteristicLubinTateArtinUnitAlgEquiv F n a *
        equalCharacteristicLubinTateArtinUnitAlgEquiv F n b := by
  apply MulSemiringAction.toAlgHom_injective F.residueField⸨X⸩
    (equalCharacteristicLubinTateLevelField F n)
  apply (equalCharacteristicLubinTateLevelPowerBasis F n).algHom_ext
  simp only [MulSemiringAction.toAlgHom_apply, mul_smul,
    AlgEquiv.smul_def]
  rw [equalCharacteristicLubinTateArtinUnitAlgEquiv_apply_gen,
    equalCharacteristicLubinTateArtinUnitAlgEquiv_apply_gen]
  unfold equalCharacteristicLubinTateArtinUnitLevelRoot
  have hmap :
      equalCharacteristicLubinTateArtinUnitAlgEquiv F n a
          (equalCharacteristicLubinTateLevelBracket F n (n + 1)
            ((b⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
            (equalCharacteristicLubinTateLevelPowerBasis F n).gen) =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          ((b⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
          (equalCharacteristicLubinTateArtinUnitAlgEquiv F n a
            (equalCharacteristicLubinTateLevelPowerBasis F n).gen) := by
    simpa only [AlgEquiv.toAlgHom_apply] using
      (equalCharacteristicLubinTateLevelBracket_map F n (n + 1)
        ((b⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
        (equalCharacteristicLubinTateArtinUnitAlgEquiv F n a).toAlgHom
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen)
  rw [hmap, equalCharacteristicLubinTateArtinUnitAlgEquiv_apply_gen]
  apply Subtype.ext
  change
    equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        ((((a * b)⁻¹ : F.residueField⟦X⟧ˣ)) :
          F.residueField⟦X⟧)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        ((b⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
        (equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1)
          ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n))
  rw [← equalCharacteristicLubinTateAmbientBracket_mul_apply_of_torsion
    F (equalCharacteristicSeparableCoefficientHom F)
    (equalCharacteristicSeparableUniformizer F) (n + 1)
    ((b⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
    ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
    (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
    (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n)]
  congr 2

/-- Power-series units acting on the finite Lubin--Tate level with Artin
orientation. -/
noncomputable def equalCharacteristicLubinTateArtinUnitToGal
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    F.residueField⟦X⟧ˣ →*
      Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩) where
  toFun := equalCharacteristicLubinTateArtinUnitAlgEquiv F n
  map_one' := equalCharacteristicLubinTateArtinUnitAlgEquiv_one F n
  map_mul' := equalCharacteristicLubinTateArtinUnitAlgEquiv_mul F n

@[simp]
theorem equalCharacteristicLubinTateArtinUnitToGal_apply_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitToGal F n a
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      equalCharacteristicLubinTateArtinUnitLevelRoot F n a :=
  equalCharacteristicLubinTateArtinUnitAlgEquiv_apply_gen F n a

/-- The kernel of the Artin-oriented explicit unit action is the level
higher-unit subgroup. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_ker
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    MonoidHom.ker (equalCharacteristicLubinTateArtinUnitToGal F n) =
      equalCharacteristicLubinTateHigherUnitSubgroup F n := by
  ext a
  rw [MonoidHom.mem_ker]
  constructor
  · intro ha
    have hgen := congrArg
      (fun σ : Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩) =>
        σ (equalCharacteristicLubinTateLevelPowerBasis F n).gen) ha
    rw [equalCharacteristicLubinTateArtinUnitToGal_apply_gen] at hgen
    simp only [AlgEquiv.one_apply] at hgen
    have hgen' := congrArg Subtype.val hgen
    change
      equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1)
          ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
        chosenEqualCharacteristicLubinTatePrimitiveRoot F n at hgen'
    exact
      (equalCharacteristicLubinTateAmbientBracket_inv_primitiveRoot_eq_iff_mem_higherUnitSubgroup
        F n a).1 hgen'
  · intro ha
    apply MulSemiringAction.toAlgHom_injective F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n)
    apply (equalCharacteristicLubinTateLevelPowerBasis F n).algHom_ext
    simp only [MulSemiringAction.toAlgHom_apply, one_smul,
      AlgEquiv.smul_def]
    rw [equalCharacteristicLubinTateArtinUnitToGal_apply_gen]
    apply Subtype.ext
    exact
      (equalCharacteristicLubinTateAmbientBracket_inv_primitiveRoot_eq_iff_mem_higherUnitSubgroup
        F n a).2 ha

/-- A visible finite parameter is obtained from the Artin-oriented unit
action by inverting its represented power-series unit. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_parameterUnit_inv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (p : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateArtinUnitToGal F n
        (equalCharacteristicLubinTateUnitParameterUnit F n p)⁻¹ =
      equalCharacteristicLubinTateUnitParameterAlgEquiv F n p := by
  apply MulSemiringAction.toAlgHom_injective F.residueField⸨X⸩
    (equalCharacteristicLubinTateLevelField F n)
  apply (equalCharacteristicLubinTateLevelPowerBasis F n).algHom_ext
  simp only [MulSemiringAction.toAlgHom_apply, AlgEquiv.smul_def]
  rw [equalCharacteristicLubinTateArtinUnitToGal_apply_gen,
    equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_gen]
  apply Subtype.ext
  simp only [equalCharacteristicLubinTateArtinUnitLevelRoot,
    equalCharacteristicLubinTateLevelBracket_coe,
    equalCharacteristicLubinTateUnitParameterLevelRoot_coe,
    equalCharacteristicLubinTateUnitParameterRoot, inv_inv,
    equalCharacteristicLubinTateUnitParameterUnit_val,
    equalCharacteristicLubinTateLevelPowerBasis_gen_coe]

/-- Every finite-level Galois automorphism is induced by an Artin-oriented
power-series unit. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_surjective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Function.Surjective
      (equalCharacteristicLubinTateArtinUnitToGal F n) := by
  intro σ
  obtain ⟨p, hp⟩ :=
    equalCharacteristicLubinTateLevelField_exists_unitParameter F n σ
  refine ⟨(equalCharacteristicLubinTateUnitParameterUnit F n p)⁻¹, ?_⟩
  exact (equalCharacteristicLubinTateArtinUnitToGal_parameterUnit_inv
    F n p).trans hp.symm

/-- The Artin-oriented explicit finite-level reciprocity equivalence from
the unit quotient. -/
noncomputable def equalCharacteristicLubinTateArtinUnitQuotientEquivGal
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    F.residueField⟦X⟧ˣ ⧸
        equalCharacteristicLubinTateHigherUnitSubgroup F n ≃*
      Gal((equalCharacteristicLubinTateLevelField F n)/F.residueField⸨X⸩) :=
  (QuotientGroup.quotientMulEquivOfEq
      (equalCharacteristicLubinTateArtinUnitToGal_ker F n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (equalCharacteristicLubinTateArtinUnitToGal F n)
      (equalCharacteristicLubinTateArtinUnitToGal_surjective F n))

@[simp]
theorem equalCharacteristicLubinTateArtinUnitQuotientEquivGal_mk
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitQuotientEquivGal F n
        (QuotientGroup.mk a) =
      equalCharacteristicLubinTateArtinUnitToGal F n a := by
  simp only [equalCharacteristicLubinTateArtinUnitQuotientEquivGal,
    MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- On a representative, the quotient-to-Galois equivalence is the inverse
orientation of the existing quotient action on the primitive torsion
point. -/
theorem
    equalCharacteristicLubinTateArtinUnitQuotientEquivGal_mk_apply_gen_coe
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    ((equalCharacteristicLubinTateArtinUnitQuotientEquivGal F n
          (QuotientGroup.mk a))
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen :
      SeparableClosure F.residueField⸨X⸩) =
      (equalCharacteristicLubinTateUnitQuotientAutomorphismEquiv F n
        (QuotientGroup.mk a⁻¹)
        (⟨chosenEqualCharacteristicLubinTatePrimitiveRoot F n,
          chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n⟩ :
          equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
            (equalCharacteristicSeparableUniformizer F) (n + 1))).1 := by
  rw [equalCharacteristicLubinTateArtinUnitQuotientEquivGal_mk,
    equalCharacteristicLubinTateArtinUnitToGal_apply_gen]
  rw [equalCharacteristicLubinTateUnitQuotientAutomorphismEquiv_mk_apply]
  rfl

/-- Kernel membership in pointwise form. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_eq_one_iff
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitToGal F n a = 1 ↔
      a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n := by
  rw [← MonoidHom.mem_ker,
    equalCharacteristicLubinTateArtinUnitToGal_ker]

/-- The explicit congruence criterion for trivial finite-level action. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_eq_one_iff_sub_one_mem
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitToGal F n a = 1 ↔
      (a : F.residueField⟦X⟧) - 1 ∈
        Ideal.span
          ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧) :=
  (equalCharacteristicLubinTateArtinUnitToGal_eq_one_iff F n a).trans
    (mem_equalCharacteristicLubinTateHigherUnitSubgroup F n a)

end LubinTate
