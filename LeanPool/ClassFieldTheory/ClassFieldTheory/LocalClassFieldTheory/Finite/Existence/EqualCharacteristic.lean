/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Series
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.LinearTerm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Intertwiner
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Reduction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.StandardSeries
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerCoefficient
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.CompletedSeries
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.DefectCorrection
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.IntertwinerConstruction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.ScalarCompatibility
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.ScalarEndomorphisms
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardCompositum
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFixedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFrobenius
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardResidue
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardUnramified
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerFixedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerPrimitive
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerThetaFixed
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusEvaluation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusLift
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedLevel
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveIrreducible
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveUniformizer
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedResidueFrobenius
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedStandardLevelTransport
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedFrobeniusFixed
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.Core
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeIntertwiner
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeSeries
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.GaloisParameterFiltration
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.HerbrandFormula
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.HigherUnitLevelEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelFieldTower
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LocalUpperRamification
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveTorsion
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.CompletedEvaluation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.NormUniformizer
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.CompletedIterates
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveAction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelAutomorphisms
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ChangedPrimitiveEvaluation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelAbelian
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelValuation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ChangedLevelCompositum
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LowerRamification
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.UpperRamification
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LowerRamificationFormula
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
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.NormIndex
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.NormSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LubinTateTransport
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LaurentPrincipalUnitTransport
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicTransportedUpperRamification
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicTransportedLevelTower
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardNormIndex
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardSubgroupIndex
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardNormSubgroupExact
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.TransportedNormSubgroupExact
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.PadicMultiplicativeArtinComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicUpperFiltration
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardSubgroupIntersection
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormContainment
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupSurjectivity
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm
/-!
# Equal-characteristic existence for local class field theory

The explicit Lubin--Tate level over the Laurent-series model is transported
to an arbitrary equal-characteristic local field.  Together with an
unramified extension, it supplies a finite Galois extension whose norm
subgroup lies in any prescribed open finite-index subgroup of `Kˣ`.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open LubinTate.EqualCharacteristic

variable (K : Type) [Field K]

section LocalField

variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A transported equal-characteristic Lubin--Tate level whose norm subgroup
is contained in the prescribed uniformizer/principal-unit subgroup. -/
theorem exists_equalCharacteristicLubinTateFiniteGaloisExtension_normSubgroup_map_le
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (n : ℕ) (hn : 0 < n) :
    ∃ T : FiniteGaloisSubextension (intrinsicAbstractBase K),
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup := by
  let F := equalCharacteristicTargetLocalField K
  let hKres : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F (n - 1)
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ (n - 1)
  let : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ (n - 1)
  let : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ (n - 1)
  have hLT :
      localNormSubgroup K E ≤
        LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n := by
    simpa [equalCharacteristicTransportedLubinTateNormSubgroup, F, E] using
      (equalCharacteristicTransportedLubinTateNormSubgroup_le_of_pos
        K p ϖ hϖ n hn)
  exact
    exists_finiteGaloisExtension_normSubgroup_map_le_of_normSubgroup_le
      K E (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n) hLT

/-- The transported Lubin--Tate level retained as a named finite abelian
subextension of the fixed separable closure. -/
noncomputable def
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    FiniteAbelianSubextension (intrinsicAbstractBase K) := by
  let F := equalCharacteristicTargetLocalField K
  letI : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  letI : CharP K p := hKp
  letI : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  letI : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ m
  letI : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ m
  exact
    finiteAbelianAbstractExtensionOfEmbedding K E
      (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K E)

/-- The explicit transported Lubin--Tate level is base-linearly equivalent
to the concrete fixed field represented by its named finite abelian
subextension. -/
noncomputable def equalCharacteristicTransportedLubinTateFixedFieldEquiv
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F m
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
    E ≃ₐ[K]
      abstractFixedField K (SeparableClosure K)
        (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
          K p ϖ hϖ m).field := by
  let F := equalCharacteristicTargetLocalField K
  letI : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  letI : CharP K p := hKp
  letI : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  letI : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ m
  letI : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ m
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K E
  let T :=
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
      K p ϖ hϖ m
  have hfixed :
      abstractFixedField K (SeparableClosure K) T.field =
        finiteGaloisFieldRangeOfEmbedding K E i := by
    change
      IntermediateField.fixedField
          (finiteGaloisFieldRangeOfEmbedding K E i).fixingSubgroup =
        finiteGaloisFieldRangeOfEmbedding K E i
    exact
      InfiniteGalois.fixedField_fixingSubgroup
        (finiteGaloisFieldRangeOfEmbedding K E i)
  rw [hfixed]
  exact finiteGaloisFieldRangeEquivOfEmbedding K E i

/-- The named transported Lubin--Tate subextension retains the concrete norm
containment at level `m + 1`. -/
theorem
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension_normSubgroup_map_le
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let T :=
      equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
        K p ϖ hϖ m
    (T.normSubgroup (intrinsicAbsoluteUnits K)).map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
      (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1)).toAddSubgroup := by
  let F := equalCharacteristicTargetLocalField K
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  let : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ m
  let : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ m
  have hLT :
      localNormSubgroup K E ≤
        LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1) := by
    simpa [equalCharacteristicTransportedLubinTateNormSubgroup, F, E] using
      (equalCharacteristicTransportedLubinTateNormSubgroup_le_uniformizerPrincipalSubgroup
        K p ϖ hϖ m)
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K E
  let T :=
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
      K p ϖ hϖ m
  have hmap :
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
        additiveNormSubgroup K E := by
    simpa [T,
      equalCharacteristicTransportedLubinTateFiniteAbelianSubextension,
      i, F, E] using
      map_finiteAbelianAbstractExtension_normSubgroup_eq K E i
  change
    (T.normSubgroup (intrinsicAbsoluteUnits K)).map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
      (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1)).toAddSubgroup
  rw [hmap]
  intro x hx
  change Additive.toMul x ∈ LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1)
  apply hLT
  exact hx

/-- The transported equal-characteristic Lubin--Tate level, packaged as a
finite abelian subextension of the fixed separable closure. -/
theorem exists_equalCharacteristicLubinTateFiniteAbelianExtension_normSubgroup_map_le
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (n : ℕ) (hn : 0 < n) :
    ∃ T : FiniteAbelianSubextension (intrinsicAbstractBase K),
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup := by
  refine
    ⟨equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
        K p ϖ hϖ (n - 1), ?_⟩
  simpa [Nat.sub_add_cancel hn] using
    (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension_normSubgroup_map_le
      K p ϖ hϖ (n - 1))

/-- The named finite abelian standard compositum: its first factor is the
canonical degree-`d` unramified extension and its second factor is the
transported Lubin--Tate level indexed by `n - 1`, whose norm subgroup uses
the principal-unit level `n`. -/
noncomputable def equalCharacteristicStandardFiniteAbelianCompositum
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (d n : ℕ) (hd : 0 < d) :
    FiniteAbelianSubextension (intrinsicAbstractBase K) :=
  (localFiniteUnramifiedAbelianSubextension K d hd).compositum
    (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
      K p ϖ hϖ (n - 1))

/-- The concrete fixed field of the named standard compositum is the
compositum of its unramified and transported Lubin--Tate fixed fields. -/
theorem equalCharacteristicStandardFiniteAbelianCompositum_fixedField_eq_sup
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (d n : ℕ) (hd : 0 < d) :
    abstractFixedField K (SeparableClosure K)
        (equalCharacteristicStandardFiniteAbelianCompositum
          K p ϖ hϖ d n hd).field =
      abstractFixedField K (SeparableClosure K)
          (localFiniteUnramifiedAbelianSubextension K d hd).field ⊔
        abstractFixedField K (SeparableClosure K)
          (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
            K p ϖ hϖ (n - 1)).field := by
  simpa [equalCharacteristicStandardFiniteAbelianCompositum] using
    (finiteAbelianSubextension_compositum_fixedField K
      (localFiniteUnramifiedAbelianSubextension K d hd)
      (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
        K p ϖ hϖ (n - 1)))

/-- The ordinary norm subgroup of the named standard compositum is contained
in every overgroup of `⟨ϖ^d⟩ U^n`. -/
theorem
    equalCharacteristicStandardFiniteAbelianCompositum_nativeNormSubgroup_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (hd : 0 < d) (hn : 0 < n)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H) :
    finiteAbelianNormSubgroup K
        (equalCharacteristicStandardFiniteAbelianCompositum
          K p ϖ hϖ d n hd) ≤
      H := by
  let U := localFiniteUnramifiedAbelianSubextension K d hd
  let T :=
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
      K p ϖ hϖ (n - 1)
  have hUle :
      (U.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (unramifiedNormSubgroup K d).toAddSubgroup := by
    simpa [U] using
      localFiniteUnramifiedAbelianSubextension_normSubgroup_map_le
        K d hd
  have hTle :
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup := by
    simpa [T, Nat.sub_add_cancel hn] using
      (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension_normSubgroup_map_le
        K p ϖ hϖ (n - 1))
  have hP :
      (U.compositum T).normSubgroup (intrinsicAbsoluteUnits K) ≤
        H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom :=
    finiteAbelianCompositum_normSubgroup_le_of_standard
      K H ϖ d n hϖ hstandard U T hUle hTle
  simpa [equalCharacteristicStandardFiniteAbelianCompositum, U, T] using
    (finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map
      K (U.compositum T) H hP)

/-- The two finite abelian factors of the positive-characteristic standard
construction can be retained explicitly, together with their norm controls
and the native norm containment for their compositum. -/
theorem
    exists_equalCharacteristicStandardFiniteAbelianCompositum_nativeNormSubgroup_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (hd : 0 < d) (hn : 0 < n)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H) :
    ∃ U T : FiniteAbelianSubextension (intrinsicAbstractBase K),
      (U.normSubgroup (intrinsicAbsoluteUnits K)).map
            (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
          (unramifiedNormSubgroup K d).toAddSubgroup ∧
        (T.normSubgroup (intrinsicAbsoluteUnits K)).map
            (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
          (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup ∧
        finiteAbelianNormSubgroup K (U.compositum T) ≤ H := by
  obtain ⟨U, hUle⟩ :=
    exists_unramifiedFiniteAbelianExtension_normSubgroup_map_le K d hd
  obtain ⟨T, hTle⟩ :=
    exists_equalCharacteristicLubinTateFiniteAbelianExtension_normSubgroup_map_le
      K p ϖ hϖ n hn
  have hP :
      (U.compositum T).normSubgroup (intrinsicAbsoluteUnits K) ≤
        H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom :=
    finiteAbelianCompositum_normSubgroup_le_of_standard
      K H ϖ d n hϖ hstandard U T hUle hTle
  refine ⟨U, T, hUle, hTle, ?_⟩
  exact
    finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map
      K (U.compositum T) H hP

/-- A standard subgroup in positive characteristic is dominated by the norm
subgroup of an explicitly assembled finite abelian compositum: an unramified
factor controls the uniformizer exponent and a transported Lubin--Tate factor
controls the principal units. -/
theorem exists_equalCharacteristicStandardFiniteAbelianExtension_normSubgroup_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (hd : 0 < d) (hn : 0 < n)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H) :
    ∃ P : FiniteAbelianSubextension (intrinsicAbstractBase K),
      P.normSubgroup (intrinsicAbsoluteUnits K) ≤
        H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom := by
  obtain ⟨U, hUle⟩ :=
    exists_unramifiedFiniteAbelianExtension_normSubgroup_map_le K d hd
  obtain ⟨T, hTle⟩ :=
    exists_equalCharacteristicLubinTateFiniteAbelianExtension_normSubgroup_map_le
      K p ϖ hϖ n hn
  refine ⟨U.compositum T, ?_⟩
  exact
    finiteAbelianCompositum_normSubgroup_le_of_standard
      K H ϖ d n hϖ hstandard U T hUle hTle

/-- Native field-facing form of the preceding construction: the represented
finite abelian fixed field has ordinary norm subgroup contained in the
prescribed standard overgroup. -/
theorem exists_equalCharacteristicStandardFiniteAbelianNativeNormSubgroup_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (hd : 0 < d) (hn : 0 < n)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H) :
    ∃ P : FiniteAbelianSubextension (intrinsicAbstractBase K),
      finiteAbelianNormSubgroup K P ≤ H := by
  obtain ⟨P, hP⟩ :=
    exists_equalCharacteristicStandardFiniteAbelianExtension_normSubgroup_le
      K p H ϖ d n hϖ hd hn hstandard
  exact
    ⟨P,
      finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map
        K P H hP⟩

/-- In positive characteristic, every ordinary open finite-index subgroup of
`Kˣ` is open for the norm topology. -/
theorem openFiniteIndexSubgroup_isNormOpen_of_charP
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (H : Subgroup Kˣ) [H.FiniteIndex]
    (hH : IsOpen (H : Set Kˣ)) :
    let A := intrinsicAbsoluteUnits K
    let B := intrinsicAbstractBase K
    let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
    ClassFormation.IsNormOpen A B
      ((H.toAddSubgroup.map e.toAddMonoidHom :
        AddSubgroup (ambientFixedAddSubgroup A B)) :
        Set (ambientFixedAddSubgroup A B)) := by
  let A := intrinsicAbsoluteUnits K
  let B := intrinsicAbstractBase K
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  obtain ⟨ϖ, d, n, hϖ, hd, hn, hstandard⟩ :=
    LocalFieldTheory.exists_uniformizerPrincipalSubgroup_le_of_isOpen_finiteIndex
      K H hH
  obtain ⟨U, hUle⟩ :=
    exists_unramifiedFiniteGaloisExtension_normSubgroup_map_le K d hd
  obtain ⟨T, hTle⟩ :=
    exists_equalCharacteristicLubinTateFiniteGaloisExtension_normSubgroup_map_le
      K p ϖ hϖ n hn
  let P := U.compositum T
  have hP :
      P.normSubgroup A ≤ H.toAddSubgroup.map e.toAddMonoidHom := by
    simpa [A, B, e, P] using
      (finiteGaloisCompositum_normSubgroup_le_of_standard
        K H ϖ d n hϖ hstandard U T hUle hTle)
  exact (ClassFormation.normTopology_addSubgroup_isOpen_iff A B
    (H.toAddSubgroup.map e.toAddMonoidHom)).2 ⟨P, hP⟩

/-- In positive characteristic, every ordinary open finite-index subgroup is
the ordinary norm subgroup of a finite abelian subextension. -/
theorem finiteAbelianNormSubgroupMap_surjective_of_charP
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Function.Surjective (finiteAbelianNormSubgroupMap K) := by
  intro H
  let : H.subgroup.FiniteIndex := H.finiteIndex
  apply exists_finiteAbelianNormSubgroup_eq_of_normOpen K H
  exact openFiniteIndexSubgroup_isNormOpen_of_charP
    K p H.subgroup H.isOpen

/-- Positive-characteristic local existence as an order isomorphism: finite
abelian subextensions correspond to ordinary open finite-index subgroups of
Kˣ with the opposite inclusion order. -/
noncomputable def finiteAbelianNormSubgroupOrderIsoOfCharP
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    FiniteAbelianSubextension (intrinsicAbstractBase K) ≃o
      (OpenFiniteIndexSubgroup K)ᵒᵈ where
  toEquiv := Equiv.ofBijective (finiteAbelianNormSubgroupMap K)
    ⟨finiteAbelianNormSubgroupMap_injective K,
      finiteAbelianNormSubgroupMap_surjective_of_charP K p⟩
  map_rel_iff' := by
    intro L₁ L₂
    change finiteAbelianNormSubgroup K L₂ ≤
        finiteAbelianNormSubgroup K L₁ ↔ L₁ ≤ L₂
    exact (finiteAbelianSubextension_le_iff_normSubgroup_le K L₁ L₂).symm

/-- Underlying equivalence of positive-characteristic local existence. -/
noncomputable def finiteAbelianNormSubgroupEquivOfCharP
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    FiniteAbelianSubextension (intrinsicAbstractBase K) ≃
      OpenFiniteIndexSubgroup K :=
  (finiteAbelianNormSubgroupOrderIsoOfCharP K p).toEquiv

/-- States the theorem `finiteAbelianNormSubgroupOrderIso_of_charP_apply`. -/
@[simp]
theorem finiteAbelianNormSubgroupOrderIso_of_charP_apply
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianNormSubgroupOrderIsoOfCharP K p L =
      finiteAbelianNormSubgroupMap K L := by
  rfl

end LocalField

end LocalClassFieldTheory
