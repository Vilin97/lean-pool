/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.Instances
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.H0
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.HMinusOne
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.HerbrandEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.H0
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.HMinusOne
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Trivial
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Quotient
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.Product
/-!
# The local class-field axiom for finite families of local blocks

This file combines the local class-field calculation with the finite-product
description of local idele blocks.  It supplies the finite-place-family part
of the finite family of localized class-formation blocks:

* degree-zero cohomology is the product of the genuine local norm quotients;
* degree-minus-one cohomology has cardinality one;
* the Herbrand quotient is the product of the local degrees.
-/

open scoped BigOperators

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology
open LocalClassFieldTheory
open LocalFieldTheory

universe uι

variable {K L : Type}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
variable {ι : Type uι} [Fintype ι]

/-- Degree-zero local-block cohomology, with the local terms identified with their
actual norm quotients. -/
noncomputable def localBlockFamilyHerbrandH0EquivNormQuotients
    (d : ι → LocalPlaceDatum K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI _extensionAlgebra : ∀ i,
        Algebra K (d i).extension.1.Completion :=
      fun i ↦ AbsoluteValue.extensionCompletionAlgebra
        (K := K) (d i).extension.1
    letI _extensionSmul : ∀ i,
        SMul K (d i).extension.1.Completion :=
      fun i ↦ (inferInstance :
        Algebra K (d i).extension.1.Completion).toSMul
    letI _completionAlgebra : ∀ i,
        Algebra (d i).base.Completion
          (d i).extension.1.Completion :=
      fun i ↦ AbsoluteValue.completionAlgebra
        (d i).base (d i).extension.1
        (d i).extension.2
    letI _globalAlgebra : ∀ i,
        Algebra K
          (LocalizedCompletion
            (d i).base (d i).extension) :=
      fun i ↦ localizedCompletionGlobalAlgebra
        (d i).base (d i).extension
    letI _scalarTower : ∀ i,
        IsScalarTower K (d i).base.Completion
          (LocalizedCompletion
            (d i).base (d i).extension) :=
      fun i ↦ localizedCompletionIsScalarTower
        (d i).base (d i).extension
    letI _localizedFinite : ∀ i,
        FiniteDimensional (d i).base.Completion
          (LocalizedCompletion
            (d i).base (d i).extension) :=
      fun i ↦ localizedCompletionModuleFinite
        (d i).base (d i).base_isNontrivial
        (d i).extension
    letI _localizedGalois : ∀ i,
        IsGalois (d i).base.Completion
          (LocalizedCompletion
            (d i).base (d i).extension) :=
      fun i ↦ HilbertRamification.algebraicLocalization_isGalois
        (d i).base (d i).extension
    letI _localAction : ∀ i,
        MulDistribMulAction
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ :=
      fun i ↦ decompositionGroupLocalUnitsAction
        (d i).base (d i).base_isNontrivial
        (d i).extension
    letI _blockAction : ∀ i,
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension) :=
      fun i ↦ inducedMulDistribMulAction
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
    letI _familyAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalBlockFamily d) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i ↦ LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension)
    letI _decompositionFintype : ∀ i,
        Fintype
          (absoluteValueDecompositionGroup K
            (d i).extension.1) :=
      fun _ ↦ Fintype.ofFinite _
    HerbrandH0 (L ≃ₐ[K] L)
        (LocalBlockFamily d) ≃*
      ∀ i, NormQuotient
        (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) := by
  letI extensionAlgebra : ∀ i,
      Algebra K (d i).extension.1.Completion :=
    fun i ↦ AbsoluteValue.extensionCompletionAlgebra
      (K := K) (d i).extension.1
  letI extensionSmul : ∀ i,
      SMul K (d i).extension.1.Completion :=
    fun i ↦ (extensionAlgebra i).toSMul
  letI completionAlgebra : ∀ i,
      Algebra (d i).base.Completion
        (d i).extension.1.Completion :=
    fun i ↦ AbsoluteValue.completionAlgebra
      (d i).base (d i).extension.1
      (d i).extension.2
  letI globalAlgebra : ∀ i,
      Algebra K
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionGlobalAlgebra
      (d i).base (d i).extension
  letI scalarTower : ∀ i,
      IsScalarTower K (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionIsScalarTower
      (d i).base (d i).extension
  letI localizedFinite : ∀ i,
      FiniteDimensional (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionModuleFinite
      (d i).base (d i).base_isNontrivial
      (d i).extension
  letI localizedGalois : ∀ i,
      IsGalois (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ HilbertRamification.algebraicLocalization_isGalois
      (d i).base (d i).extension
  letI localAction : ∀ i,
      MulDistribMulAction
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
    fun i ↦ decompositionGroupLocalUnitsAction
      (d i).base (d i).base_isNontrivial
      (d i).extension
  letI blockAction : ∀ i,
      MulDistribMulAction (L ≃ₐ[K] L)
        (LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension) :=
    fun i ↦ inducedMulDistribMulAction
      (absoluteValueDecompositionGroup K
        (d i).extension.1)
  letI familyAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (LocalBlockFamily d) :=
    piMulDistribMulAction (L ≃ₐ[K] L)
      (fun i ↦ LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension)
  letI decompositionFintype : ∀ i,
      Fintype
        (absoluteValueDecompositionGroup K
          (d i).extension.1) :=
    fun _ ↦ Fintype.ofFinite _
  exact
    (localBlockFamilyHerbrandH0Equiv
      d σ hgen).trans
      (MulEquiv.piCongrRight fun i ↦
        localHerbrandH0EquivNormQuotient
          (d i).base (d i).base_isNontrivial
          (d i).extension)

/-- The degree-zero cohomology of a finite family of local blocks is finite. -/
theorem localBlockFamilyHerbrandH0Finite
    (d : ι → LocalPlaceDatum K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    [∀ i, ValuativeRel (d i).base.Completion]
    [∀ i,
      IsNonarchimedeanLocalField
        (d i).base.Completion] :
    letI _localAction : ∀ i,
        MulDistribMulAction
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ :=
      fun i ↦ decompositionGroupLocalUnitsAction
        (d i).base (d i).base_isNontrivial
        (d i).extension
    letI _blockAction : ∀ i,
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension) :=
      fun i ↦ inducedMulDistribMulAction
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
    letI _familyAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalBlockFamily d) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i ↦ LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension)
    letI _decompositionFintype : ∀ i,
        Fintype
          (absoluteValueDecompositionGroup K
            (d i).extension.1) :=
      fun _ ↦ Fintype.ofFinite _
    Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (LocalBlockFamily d)) := by
  let extensionAlgebra : ∀ i,
      Algebra K (d i).extension.1.Completion :=
    fun i ↦ AbsoluteValue.extensionCompletionAlgebra
      (K := K) (d i).extension.1
  let extensionSmul : ∀ i,
      SMul K (d i).extension.1.Completion :=
    fun i ↦ (extensionAlgebra i).toSMul
  let completionAlgebra : ∀ i,
      Algebra (d i).base.Completion
        (d i).extension.1.Completion :=
    fun i ↦ AbsoluteValue.completionAlgebra
      (d i).base (d i).extension.1
      (d i).extension.2
  let globalAlgebra : ∀ i,
      Algebra K
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionGlobalAlgebra
      (d i).base (d i).extension
  let scalarTower : ∀ i,
      IsScalarTower K (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionIsScalarTower
      (d i).base (d i).extension
  let localizedFinite : ∀ i,
      FiniteDimensional (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionModuleFinite
      (d i).base (d i).base_isNontrivial
      (d i).extension
  let localizedGalois : ∀ i,
      IsGalois (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ HilbertRamification.algebraicLocalization_isGalois
      (d i).base (d i).extension
  let localAction : ∀ i,
      MulDistribMulAction
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
    fun i ↦ decompositionGroupLocalUnitsAction
      (d i).base (d i).base_isNontrivial
      (d i).extension
  let blockAction : ∀ i,
      MulDistribMulAction (L ≃ₐ[K] L)
        (LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension) :=
    fun i ↦ inducedMulDistribMulAction
      (absoluteValueDecompositionGroup K
        (d i).extension.1)
  let familyAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (LocalBlockFamily d) :=
    piMulDistribMulAction (L ≃ₐ[K] L)
      (fun i ↦ LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension)
  let decompositionFintype : ∀ i,
      Fintype
        (absoluteValueDecompositionGroup K
          (d i).extension.1) :=
    fun _ ↦ Fintype.ofFinite _
  let localFinite : ∀ i,
      Finite
        (HerbrandH0
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ) :=
    fun i ↦ localHerbrandH0Finite
      (d i).base (d i).base_isNontrivial
      (d i).extension σ hgen
  exact Finite.of_equiv
    (∀ i,
      HerbrandH0
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ)
    (localBlockFamilyHerbrandH0Equiv
      d σ hgen).symm.toEquiv

/-- The degree-minus-one cohomology of a finite family of local blocks is
finite. -/
theorem localBlockFamilyHerbrandHMinusOneFinite
    (d : ι → LocalPlaceDatum K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    [∀ i, ValuativeRel (d i).base.Completion]
    [∀ i,
      IsNonarchimedeanLocalField
        (d i).base.Completion] :
    letI _localAction : ∀ i,
        MulDistribMulAction
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ :=
      fun i ↦ decompositionGroupLocalUnitsAction
        (d i).base (d i).base_isNontrivial
        (d i).extension
    letI _blockAction : ∀ i,
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension) :=
      fun i ↦ inducedMulDistribMulAction
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
    letI _familyAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalBlockFamily d) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i ↦ LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension)
    letI _decompositionFintype : ∀ i,
        Fintype
          (absoluteValueDecompositionGroup K
            (d i).extension.1) :=
      fun _ ↦ Fintype.ofFinite _
    Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalBlockFamily d) σ) := by
  let extensionAlgebra : ∀ i,
      Algebra K (d i).extension.1.Completion :=
    fun i ↦ AbsoluteValue.extensionCompletionAlgebra
      (K := K) (d i).extension.1
  let extensionSmul : ∀ i,
      SMul K (d i).extension.1.Completion :=
    fun i ↦ (extensionAlgebra i).toSMul
  let completionAlgebra : ∀ i,
      Algebra (d i).base.Completion
        (d i).extension.1.Completion :=
    fun i ↦ AbsoluteValue.completionAlgebra
      (d i).base (d i).extension.1
      (d i).extension.2
  let globalAlgebra : ∀ i,
      Algebra K
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionGlobalAlgebra
      (d i).base (d i).extension
  let scalarTower : ∀ i,
      IsScalarTower K (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionIsScalarTower
      (d i).base (d i).extension
  let localizedFinite : ∀ i,
      FiniteDimensional (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionModuleFinite
      (d i).base (d i).base_isNontrivial
      (d i).extension
  let localizedGalois : ∀ i,
      IsGalois (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ HilbertRamification.algebraicLocalization_isGalois
      (d i).base (d i).extension
  let localAction : ∀ i,
      MulDistribMulAction
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
    fun i ↦ decompositionGroupLocalUnitsAction
      (d i).base (d i).base_isNontrivial
      (d i).extension
  let blockAction : ∀ i,
      MulDistribMulAction (L ≃ₐ[K] L)
        (LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension) :=
    fun i ↦ inducedMulDistribMulAction
      (absoluteValueDecompositionGroup K
        (d i).extension.1)
  let familyAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (LocalBlockFamily d) :=
    piMulDistribMulAction (L ≃ₐ[K] L)
      (fun i ↦ LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension)
  let decompositionFintype : ∀ i,
      Fintype
        (absoluteValueDecompositionGroup K
          (d i).extension.1) :=
    fun _ ↦ Fintype.ofFinite _
  let localFinite : ∀ i,
      Finite
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            σ hgen)) :=
    fun i ↦ localHerbrandHMinusOneFinite
      (d i).base (d i).base_isNontrivial
      (d i).extension σ hgen
  exact Finite.of_equiv
    (∀ i,
      HerbrandHMinusOne
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          σ hgen))
    (localBlockFamilyHerbrandHMinusOneEquiv
      d σ hgen).symm.toEquiv

/-- In degree minus one, a finite family of local blocks has
degree-minus-one cohomology of cardinality one. -/
theorem localBlockFamilyHerbrandHMinusOne_card_eq_one
    (d : ι → LocalPlaceDatum K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    [∀ i, ValuativeRel (d i).base.Completion]
    [∀ i,
      IsNonarchimedeanLocalField
        (d i).base.Completion] :
    letI _localAction : ∀ i,
        MulDistribMulAction
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ :=
      fun i ↦ decompositionGroupLocalUnitsAction
        (d i).base (d i).base_isNontrivial
        (d i).extension
    letI _blockAction : ∀ i,
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension) :=
      fun i ↦ inducedMulDistribMulAction
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
    letI _familyAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalBlockFamily d) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i ↦ LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension)
    letI _decompositionFintype : ∀ i,
        Fintype
          (absoluteValueDecompositionGroup K
            (d i).extension.1) :=
      fun _ ↦ Fintype.ofFinite _
    letI _familyFinite :
        Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (LocalBlockFamily d) σ) :=
      localBlockFamilyHerbrandHMinusOneFinite
        d σ hgen
    Nat.card
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily d) σ) = 1 := by
  let extensionAlgebra : ∀ i,
      Algebra K (d i).extension.1.Completion :=
    fun i ↦ AbsoluteValue.extensionCompletionAlgebra
      (K := K) (d i).extension.1
  let extensionSmul : ∀ i,
      SMul K (d i).extension.1.Completion :=
    fun i ↦ (extensionAlgebra i).toSMul
  let completionAlgebra : ∀ i,
      Algebra (d i).base.Completion
        (d i).extension.1.Completion :=
    fun i ↦ AbsoluteValue.completionAlgebra
      (d i).base (d i).extension.1
      (d i).extension.2
  let globalAlgebra : ∀ i,
      Algebra K
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionGlobalAlgebra
      (d i).base (d i).extension
  let scalarTower : ∀ i,
      IsScalarTower K (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionIsScalarTower
      (d i).base (d i).extension
  let localizedFinite : ∀ i,
      FiniteDimensional (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionModuleFinite
      (d i).base (d i).base_isNontrivial
      (d i).extension
  let localizedGalois : ∀ i,
      IsGalois (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ HilbertRamification.algebraicLocalization_isGalois
      (d i).base (d i).extension
  let localAction : ∀ i,
      MulDistribMulAction
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
    fun i ↦ decompositionGroupLocalUnitsAction
      (d i).base (d i).base_isNontrivial
      (d i).extension
  let blockAction : ∀ i,
      MulDistribMulAction (L ≃ₐ[K] L)
        (LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension) :=
    fun i ↦ inducedMulDistribMulAction
      (absoluteValueDecompositionGroup K
        (d i).extension.1)
  let familyAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (LocalBlockFamily d) :=
    piMulDistribMulAction (L ≃ₐ[K] L)
      (fun i ↦ LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension)
  let decompositionFintype : ∀ i,
      Fintype
        (absoluteValueDecompositionGroup K
          (d i).extension.1) :=
    fun _ ↦ Fintype.ofFinite _
  let localFinite : ∀ i,
      Finite
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            σ hgen)) :=
    fun i ↦ localHerbrandHMinusOneFinite
      (d i).base (d i).base_isNontrivial
      (d i).extension σ hgen
  let familyFinite :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily d) σ) :=
    localBlockFamilyHerbrandHMinusOneFinite
      d σ hgen
  calc
    Nat.card
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily d) σ) =
      Nat.card
        (∀ i,
          HerbrandHMinusOne
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            (LocalizedCompletion
              (d i).base (d i).extension)ˣ
            (subgroupGeneratorOfGenerator
              (absoluteValueDecompositionGroup K
                (d i).extension.1)
              σ hgen)) :=
      Nat.card_congr
        (localBlockFamilyHerbrandHMinusOneEquiv
          d σ hgen).toEquiv
    _ = ∏ i, Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            σ hgen)) :=
      Nat.card_pi
    _ = ∏ _i : ι, 1 := by
      apply Finset.prod_congr rfl
      intro i _
      exact localHerbrandHMinusOne_card_eq_one
        (d i).base (d i).base_isNontrivial
        (d i).extension σ hgen
    _ = 1 := by simp

/-- The Herbrand quotient of a finite family of local blocks is
the product of the corresponding local degrees. -/
theorem localBlockFamily_herbrandQuotient_eq_product_localDegrees
    (d : ι → LocalPlaceDatum K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    [∀ i, ValuativeRel (d i).base.Completion]
    [∀ i,
      IsNonarchimedeanLocalField
        (d i).base.Completion] :
    letI _extensionAlgebra : ∀ i,
        Algebra K (d i).extension.1.Completion :=
      fun i ↦ AbsoluteValue.extensionCompletionAlgebra
        (K := K) (d i).extension.1
    letI _extensionSmul : ∀ i,
        SMul K (d i).extension.1.Completion :=
      fun i ↦ (inferInstance :
        Algebra K (d i).extension.1.Completion).toSMul
    letI _completionAlgebra : ∀ i,
        Algebra (d i).base.Completion
          (d i).extension.1.Completion :=
      fun i ↦ AbsoluteValue.completionAlgebra
        (d i).base (d i).extension.1
        (d i).extension.2
    letI _globalAlgebra : ∀ i,
        Algebra K
          (LocalizedCompletion
            (d i).base (d i).extension) :=
      fun i ↦ localizedCompletionGlobalAlgebra
        (d i).base (d i).extension
    letI _scalarTower : ∀ i,
        IsScalarTower K (d i).base.Completion
          (LocalizedCompletion
            (d i).base (d i).extension) :=
      fun i ↦ localizedCompletionIsScalarTower
        (d i).base (d i).extension
    letI _localizedFinite : ∀ i,
        FiniteDimensional (d i).base.Completion
          (LocalizedCompletion
            (d i).base (d i).extension) :=
      fun i ↦ localizedCompletionModuleFinite
        (d i).base (d i).base_isNontrivial
        (d i).extension
    letI _localizedGalois : ∀ i,
        IsGalois (d i).base.Completion
          (LocalizedCompletion
            (d i).base (d i).extension) :=
      fun i ↦ HilbertRamification.algebraicLocalization_isGalois
        (d i).base (d i).extension
    letI _localAction : ∀ i,
        MulDistribMulAction
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ :=
      fun i ↦ decompositionGroupLocalUnitsAction
        (d i).base (d i).base_isNontrivial
        (d i).extension
    letI _blockAction : ∀ i,
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension) :=
      fun i ↦ inducedMulDistribMulAction
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
    letI _familyAction :
        MulDistribMulAction (L ≃ₐ[K] L)
          (LocalBlockFamily d) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i ↦ LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension)
    letI _decompositionFintype : ∀ i,
        Fintype
          (absoluteValueDecompositionGroup K
            (d i).extension.1) :=
      fun _ ↦ Fintype.ofFinite _
    letI _familyH0Finite :
        Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (LocalBlockFamily d)) :=
      localBlockFamilyHerbrandH0Finite
        d σ hgen
    letI _familyHMinusOneFinite :
        Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (LocalBlockFamily d) σ) :=
      localBlockFamilyHerbrandHMinusOneFinite
        d σ hgen
    herbrandQuotient
        (G := L ≃ₐ[K] L)
        (A := LocalBlockFamily d) σ =
      ∏ i, (Module.finrank
        (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) : ℚ) := by
  let extensionAlgebra : ∀ i,
      Algebra K (d i).extension.1.Completion :=
    fun i ↦ AbsoluteValue.extensionCompletionAlgebra
      (K := K) (d i).extension.1
  let extensionSmul : ∀ i,
      SMul K (d i).extension.1.Completion :=
    fun i ↦ (extensionAlgebra i).toSMul
  let completionAlgebra : ∀ i,
      Algebra (d i).base.Completion
        (d i).extension.1.Completion :=
    fun i ↦ AbsoluteValue.completionAlgebra
      (d i).base (d i).extension.1
      (d i).extension.2
  let globalAlgebra : ∀ i,
      Algebra K
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionGlobalAlgebra
      (d i).base (d i).extension
  let scalarTower : ∀ i,
      IsScalarTower K (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionIsScalarTower
      (d i).base (d i).extension
  let localizedFinite : ∀ i,
      FiniteDimensional (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ localizedCompletionModuleFinite
      (d i).base (d i).base_isNontrivial
      (d i).extension
  let localizedGalois : ∀ i,
      IsGalois (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) :=
    fun i ↦ HilbertRamification.algebraicLocalization_isGalois
      (d i).base (d i).extension
  let localAction : ∀ i,
      MulDistribMulAction
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
    fun i ↦ decompositionGroupLocalUnitsAction
      (d i).base (d i).base_isNontrivial
      (d i).extension
  let blockAction : ∀ i,
      MulDistribMulAction (L ≃ₐ[K] L)
        (LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension) :=
    fun i ↦ inducedMulDistribMulAction
      (absoluteValueDecompositionGroup K
        (d i).extension.1)
  let familyAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (LocalBlockFamily d) :=
    piMulDistribMulAction (L ≃ₐ[K] L)
      (fun i ↦ LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension)
  let decompositionFintype : ∀ i,
      Fintype
        (absoluteValueDecompositionGroup K
          (d i).extension.1) :=
    fun _ ↦ Fintype.ofFinite _
  let localH0Finite : ∀ i,
      Finite
        (HerbrandH0
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ) :=
    fun i ↦ localHerbrandH0Finite
      (d i).base (d i).base_isNontrivial
      (d i).extension σ hgen
  let localHMinusOneFinite : ∀ i,
      Finite
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            σ hgen)) :=
    fun i ↦ localHerbrandHMinusOneFinite
      (d i).base (d i).base_isNontrivial
      (d i).extension σ hgen
  let blockH0Finite : ∀ i,
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension)) :=
    fun i ↦ Finite.of_equiv
      (HerbrandH0
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ)
      (localPlaceBlockHerbrandH0Equiv
        (d i).base (d i).base_isNontrivial
        (d i).extension σ hgen).symm.toEquiv
  let blockHMinusOneFinite : ∀ i,
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension) σ) :=
    fun i ↦ Finite.of_equiv
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K
          (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          σ hgen))
      (localPlaceBlockHerbrandHMinusOneEquiv
        (d i).base (d i).base_isNontrivial
        (d i).extension σ hgen).symm.toEquiv
  let familyH0Finite :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (LocalBlockFamily d)) :=
    localBlockFamilyHerbrandH0Finite
      d σ hgen
  let familyHMinusOneFinite :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (LocalBlockFamily d) σ) :=
    localBlockFamilyHerbrandHMinusOneFinite
      d σ hgen
  calc
    herbrandQuotient
        (G := L ≃ₐ[K] L)
        (A := LocalBlockFamily d) σ =
        ∏ i, herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension) σ :=
      herbrandQuotient_pi
        (fun i ↦ LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension) σ
    _ = ∏ i, (Module.finrank
        (d i).base.Completion
        (LocalizedCompletion
          (d i).base (d i).extension) : ℚ) := by
      apply Finset.prod_congr rfl
      intro i _
      have hH0 :
          Nat.card
              (HerbrandH0 (L ≃ₐ[K] L)
                (LocalPlaceBlock
                  (d i).base
                  (d i).base_isNontrivial
                  (d i).extension)) =
            Module.finrank
              (d i).base.Completion
              (LocalizedCompletion
                (d i).base (d i).extension) := by
        calc
          Nat.card
              (HerbrandH0 (L ≃ₐ[K] L)
                (LocalPlaceBlock
                  (d i).base
                  (d i).base_isNontrivial
                  (d i).extension)) =
            Nat.card
              (HerbrandH0
                (absoluteValueDecompositionGroup K
                  (d i).extension.1)
                (LocalizedCompletion
                  (d i).base (d i).extension)ˣ) :=
            Nat.card_congr
              (localPlaceBlockHerbrandH0Equiv
                (d i).base
                (d i).base_isNontrivial
                (d i).extension σ hgen).toEquiv
          _ = Module.finrank
              (d i).base.Completion
              (LocalizedCompletion
                (d i).base (d i).extension) :=
            localHerbrandH0_card_eq_localDegree
              (d i).base
              (d i).base_isNontrivial
              (d i).extension σ hgen
      have hHMinusOne :
          Nat.card
              (HerbrandHMinusOne (L ≃ₐ[K] L)
                (LocalPlaceBlock
                  (d i).base
                  (d i).base_isNontrivial
                  (d i).extension) σ) = 1 := by
        calc
          Nat.card
              (HerbrandHMinusOne (L ≃ₐ[K] L)
                (LocalPlaceBlock
                  (d i).base
                  (d i).base_isNontrivial
                  (d i).extension) σ) =
            Nat.card
              (HerbrandHMinusOne
                (absoluteValueDecompositionGroup K
                  (d i).extension.1)
                (LocalizedCompletion
                  (d i).base (d i).extension)ˣ
                (subgroupGeneratorOfGenerator
                  (absoluteValueDecompositionGroup K
                    (d i).extension.1)
                  σ hgen)) :=
            Nat.card_congr
              (localPlaceBlockHerbrandHMinusOneEquiv
                (d i).base
                (d i).base_isNontrivial
                (d i).extension σ hgen).toEquiv
          _ = 1 :=
            localHerbrandHMinusOne_card_eq_one
              (d i).base
              (d i).base_isNontrivial
              (d i).extension σ hgen
      rw [herbrandQuotient_eq_card_ratio,
        hH0, hHMinusOne]
      simp

end LocalClassFieldTheory
