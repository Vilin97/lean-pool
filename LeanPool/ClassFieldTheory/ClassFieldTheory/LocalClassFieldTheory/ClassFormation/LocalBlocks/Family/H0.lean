/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.Instances
/-!
# Degree-zero cohomology of finite local-block families
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

universe u v w

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Degree-zero cohomology for a finite family of local blocks. -/
noncomputable def localBlockFamilyHerbrandH0Equiv
    {ι : Type w}
    (d : ι → LocalPlaceDatum K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI _localAction : ∀ i,
        MulDistribMulAction
          (absoluteValueDecompositionGroup K (d i).extension.1)
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
        (absoluteValueDecompositionGroup K (d i).extension.1)
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
      ∀ i,
        HerbrandH0
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ := by
  letI localAction := localBlockFamilyLocalAction d
  letI blockAction := localBlockFamilyBlockAction d
  letI familyAction := localBlockFamilyCohomologyAction d
  letI decompositionFintype :=
    localBlockFamilyDecompositionFintype d
  exact
    (herbrandH0PiEquiv
      (G := L ≃ₐ[K] L)
      (fun i ↦ LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension)).trans
      (MulEquiv.piCongrRight fun i ↦
        localPlaceBlockHerbrandH0Equiv
          (d i).base (d i).base_isNontrivial
          (d i).extension σ hgen)

end LocalClassFieldTheory
