/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Induced
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Product
/-!
# Finite families of local idele blocks

This file combines the local induced-module calculation over a finite
family of places. It is the finite-support part of the localized class formation.
-/

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

universe u v w

variable (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- A chosen extension `w` of a nontrivial base absolute value.  These are
exactly the concrete inputs needed to form one local block. -/
structure LocalPlaceDatum where
  /-- The base absolute value. -/
  base : AbsoluteValue K ℝ
  /-- Nontriviality of the base absolute value. -/
  base_isNontrivial : base.IsNontrivial
  /-- A chosen extension of the base absolute value to `L`. -/
  extension : AbsoluteValueExtension base L

variable {K L}

/-- Product of the local blocks attached to a family of chosen places. -/
abbrev LocalBlockFamily {ι : Type w}
    (d : ι → LocalPlaceDatum K L) :=
  ∀ i, LocalPlaceBlock
    (d i).base (d i).base_isNontrivial
    (d i).extension


/-- Canonical componentwise decomposition-group action for a local-block
family. -/
@[reducible]
noncomputable def localBlockFamilyLocalAction
    {ι : Type w} (d : ι → LocalPlaceDatum K L) :
    ∀ i, MulDistribMulAction
      (absoluteValueDecompositionGroup K (d i).extension.1)
      (LocalizedCompletion
        (d i).base (d i).extension)ˣ :=
  fun i =>
    decompositionGroupLocalUnitsAction
      (d i).base (d i).base_isNontrivial
      (d i).extension

/-- Canonical induced action on every local block in a family. -/
@[reducible]
noncomputable def localBlockFamilyBlockAction
    {ι : Type w} (d : ι → LocalPlaceDatum K L) :
    ∀ i, MulDistribMulAction (L ≃ₐ[K] L)
      (LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension) := by
  letI := localBlockFamilyLocalAction d
  exact fun i =>
    inducedMulDistribMulAction
      (absoluteValueDecompositionGroup K
        (d i).extension.1)

/-- Canonical componentwise action on the product of a local-block family. -/
@[reducible]
noncomputable def localBlockFamilyCohomologyAction
    {ι : Type w} (d : ι → LocalPlaceDatum K L) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (LocalBlockFamily d) := by
  letI := localBlockFamilyLocalAction d
  letI := localBlockFamilyBlockAction d
  exact
    piMulDistribMulAction (L ≃ₐ[K] L)
      (fun i ↦ LocalPlaceBlock
        (d i).base (d i).base_isNontrivial
        (d i).extension)

/-- Canonical finite structures on the decomposition groups in a local-block
family. -/
@[reducible]
noncomputable def localBlockFamilyDecompositionFintype
    {ι : Type w} (d : ι → LocalPlaceDatum K L) :
    ∀ i, Fintype
      (absoluteValueDecompositionGroup K
        (d i).extension.1) :=
  fun _ => Fintype.ofFinite _

end LocalClassFieldTheory
