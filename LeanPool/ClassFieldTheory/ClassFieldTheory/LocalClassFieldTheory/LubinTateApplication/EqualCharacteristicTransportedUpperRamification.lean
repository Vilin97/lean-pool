/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LaurentPrincipalUnitTransport
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.BaseChange
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedLevel
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedPrimitiveAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedPolynomialEvaluation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizer
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizerNormalization
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusBaseEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusContinuity
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldAlgebra
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldCoefficientDescent
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldDegree
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldGeneration
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPowerBasis
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPrimitive
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusLift
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveIrreducible
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectBracketAtCompletedLevel
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracket
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracketRecursion
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectTargetLevelEmbedding
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaAtCompletedLevel
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFirstIdentity
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFrobeniusFixed
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaIteration
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaSeries
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaAtCompletedLevel
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaLocalInverse
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.DivisionPolynomial
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveIrreducible
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveTorsion
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.UnitQuotientGalois
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.AmbientBracketAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.DivisionModuleEndomorphisms
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateEndomorphism
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CompletedUnramifiedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.ContractingEquation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.LaurentSeriesFrobenius
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEmbedding
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldMembership
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFrobeniusFixed
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitsNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.LevelAlgebra
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.StandardSubgroupNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitQuotientCard
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitTransport
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaCoefficients
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaEvaluation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaFirstIdentity
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaSeries
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaUniqueness
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.RealIndexSteps
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.Core
/-!
# Upper ramification groups on transported equal-characteristic levels

The explicit Lubin--Tate level field is unchanged when its Laurent-series
base algebra is transported to an arbitrary equal-characteristic local
field.  The normalized Laurent equivalence preserves the valuation rings,
so the general base-field transport theorem identifies the two upper
ramification filtrations.
-/

noncomputable section

open scoped LaurentSeries ValuativeRel

namespace LubinTate

open LocalFieldTheory
open RamificationTheory.LocalField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate.EqualCharacteristic

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The two algebra maps from the Laurent model and the target local field
to a transported Lubin--Tate level have the same image. -/
theorem equalCharacteristicTransportedLubinTate_algebraMap_compat
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ)
    (x :
      let F := equalCharacteristicTargetLocalField K
      F.residueField⸨X⸩) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    algebraMap K E
        (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ x) =
      algebraMap B E x := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F n
  let : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  have hcomp :=
    DFunLike.congr_fun
      (equalCharacteristicTransportedLubinTateLevelAlgebra_comp
        K p ϖ hϖ n) x
  simpa using hcomp

/-- Identification of the Galois group over the Laurent base with the
Galois group for the transported target-field algebra.  It leaves every
underlying automorphism of the level field unchanged. -/
noncomputable def equalCharacteristicTransportedLubinTateGaloisEquiv
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    Gal(E/B) ≃* Gal(E/K) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  letI : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F n
  letI : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F n
  letI : CharP K p := hKp
  letI : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  exact
    galoisGroupEquivOfBaseRingEquiv B K E
      (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ)
      (equalCharacteristicTransportedLubinTate_algebraMap_compat
        K p ϖ hϖ n)

@[simp]
theorem equalCharacteristicTransportedLubinTateGaloisEquiv_apply
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ)
    (σ :
      let F := equalCharacteristicTargetLocalField K
      let B := F.residueField⸨X⸩
      letI : CharP K F.residueCharacteristic :=
        equalCharacteristicTargetResidueCharacteristicCharP K p
      let E := equalCharacteristicLubinTateLevelField F n
      letI : Algebra B E :=
        equalCharacteristicLubinTateLevelAlgebra F n
      Gal(E/B))
    (x :
      let F := equalCharacteristicTargetLocalField K
      letI : CharP K F.residueCharacteristic :=
        equalCharacteristicTargetResidueCharacteristicCharP K p
      equalCharacteristicLubinTateLevelField F n) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    equalCharacteristicTransportedLubinTateGaloisEquiv
        K p ϖ hϖ n σ x =
      σ x := by
  rfl

private theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq_baseChange
    [Fact
      (equalCharacteristicTargetLocalField K).residueCharacteristic.Prime]
    [CharP K
      (equalCharacteristicTargetLocalField K).residueCharacteristic]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ) :
    let F := equalCharacteristicTargetLocalField K
    let q := F.residueCharacteristic
    let B := F.residueField⸨X⸩
    let E := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI algBE : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI finBE : FiniteDimensional B E :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    letI galBE : IsGalois B E :=
      equalCharacteristicLubinTateLevelField_isGalois F n
    let upperB :=
      @localUpperRamificationGroup B E
        inferInstance inferInstance
        algBE finBE galBE
        inferInstance inferInstance inferInstance
    letI algKE : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K q ϖ hϖ n
    letI finKE : FiniteDimensional K E :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K q ϖ hϖ n
    letI galKE : IsGalois K E :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K q ϖ hϖ n
    let upperK :=
      @localUpperRamificationGroup K E
        inferInstance inferInstance
        algKE finKE galKE
        inferInstance inferInstance inferInstance
    Subgroup.map
        (@galoisGroupEquivOfBaseRingEquiv
          B K E
          inferInstance inferInstance inferInstance
          algBE algKE
          (equalCharacteristicTargetLaurentRingEquiv K q ϖ hϖ)
          (equalCharacteristicTransportedLubinTate_algebraMap_compat
            K q ϖ hϖ n)).toMonoidHom
        (upperB t) =
      upperK t := by
  let F := equalCharacteristicTargetLocalField K
  let q := F.residueCharacteristic
  let B := F.residueField⸨X⸩
  let E := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B :=
    equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let algBE : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let finBE : FiniteDimensional B E :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let galBE : IsGalois B E :=
    equalCharacteristicLubinTateLevelField_isGalois F n
  let algKE : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K q ϖ hϖ n
  let finKE : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K q ϖ hϖ n
  let galKE : IsGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isGalois
      K q ϖ hϖ n
  dsimp only
  convert
    @localUpperRamificationGroup_map_baseRingEquiv
      B K E
      inferInstance inferInstance inferInstance
      algBE algKE finBE finKE galBE galKE
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      (equalCharacteristicTargetLaurentRingEquiv K q ϖ hϖ)
      (equalCharacteristicTransportedLubinTate_algebraMap_compat
        K q ϖ hϖ n)
      (equalCharacteristicTargetLaurentRingEquiv_val_le_one_iff
        K q ϖ hϖ) t using 1

private theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq_residueCharacteristic
    [Fact
      (equalCharacteristicTargetLocalField K).residueCharacteristic.Prime]
    [CharP K
      (equalCharacteristicTargetLocalField K).residueCharacteristic]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ) :
    let F := equalCharacteristicTargetLocalField K
    let q := F.residueCharacteristic
    let B := F.residueField⸨X⸩
    let E := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI algBE : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI finBE : FiniteDimensional B E :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    letI galBE : IsGalois B E :=
      equalCharacteristicLubinTateLevelField_isGalois F n
    let upperB :=
      @localUpperRamificationGroup B E
        (by infer_instance) (by infer_instance)
        algBE finBE galBE
        (by infer_instance) (by infer_instance) (by infer_instance)
    letI algKE : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K q ϖ hϖ n
    letI finKE : FiniteDimensional K E :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K q ϖ hϖ n
    letI galKE : IsGalois K E :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K q ϖ hϖ n
    let upperK :=
      @localUpperRamificationGroup K E
        (by infer_instance) (by infer_instance)
        algKE finKE galKE
        (by infer_instance) (by infer_instance) (by infer_instance)
    Subgroup.map
        (equalCharacteristicTransportedLubinTateGaloisEquiv
          K q ϖ hϖ n).toMonoidHom
        (upperB t) =
      upperK t := by
  simpa only [equalCharacteristicTransportedLubinTateGaloisEquiv] using
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq_baseChange
      K ϖ hϖ n t

/-- The normalized base-field equivalence transports the canonical local
upper ramification group on every explicit Lubin--Tate level. -/
theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B E :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    let upperB := localUpperRamificationGroup B E
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p (hKp := hKp) ϖ hϖ n
    letI : Module K E := Algebra.toModule
    letI : IsGalois K E :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K p (hKp := hKp) ϖ hϖ n
    letI : FiniteDimensional K E :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K p (hKp := hKp) ϖ hϖ n
    let upperK := localUpperRamificationGroup K E
    Subgroup.map
        (equalCharacteristicTransportedLubinTateGaloisEquiv
          K p (hKp := hKp) ϖ hϖ n).toMonoidHom
        (upperB t) =
      upperK t := by
  let F := equalCharacteristicTargetLocalField K
  have hp : F.residueCharacteristic = p :=
    F.residueCharacteristic_eq_of_charP p
      ((Fact.out : Nat.Prime p).ne_zero)
  subst p
  convert
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq_residueCharacteristic
      K ϖ hϖ n t using 1

end LubinTate
