/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.Induced
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
/-!
# Local blocks of the idele group

For a place `w` of a Galois extension above a base absolute value `v`, its
decomposition group acts on the local multiplicative group.  The product of
all conjugate local factors is therefore the induced module from that
decomposition group. This is the algebraic content of the induced local block.

The local field is expressed as the canonical algebraic localization.
For finite extensions this is the entire metric completion by
`absoluteValueExtension_finiteLocalization_eq_top`.
-/

@[expose] public section

open scoped TensorProduct

noncomputable
section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]

/-- The decomposition group acts on the units of the chosen local field,
through the canonical global-to-local Galois equivalence. -/
@[reducible]
noncomputable def decompositionGroupLocalUnitsAction
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      (LocalizedCompletion vK w)ˣ :=
  MulDistribMulAction.compHom
    (LocalizedCompletion vK w)ˣ
    (decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w).toMonoidHom

omit [FiniteDimensional K L] in
@[simp]
theorem decompositionGroup_smul_localUnit_coe
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : absoluteValueDecompositionGroup K w.1)
    (x : (LocalizedCompletion vK w)ˣ) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    ((σ • x : (LocalizedCompletion vK w)ˣ) :
        LocalizedCompletion vK w) =
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w σ (x : LocalizedCompletion vK w) :=
  rfl

/-- The block of local multiplicative groups above `v`, after choosing
one extension `w`.  It is the induced module from the decomposition group
at `w`. -/
abbrev LocalPlaceBlock
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :=
  @InducedModule
    (G := L ≃ₐ[K] L)
    (B := (LocalizedCompletion vK w)ˣ)
    inferInstance
    (absoluteValueDecompositionGroup K w.1)
    inferInstance
    (decompositionGroupLocalUnitsAction vK hvK w)

/-- In cyclic coordinates, the local block is a finite product
of conjugate copies of the chosen completion. -/
noncomputable def localPlaceBlockEquivProduct
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    LocalPlaceBlock vK hvK w ≃*
      (Fin (absoluteValueDecompositionGroup K w.1).index →
        (LocalizedCompletion vK w)ˣ) :=
  by
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    exact inducedCoordinatesOfFiniteCyclic
      (absoluteValueDecompositionGroup K w.1) σ hgen

/-- Degree-zero cohomology for one local block. -/
noncomputable def localPlaceBlockHerbrandH0Equiv
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    HerbrandH0 (L ≃ₐ[K] L)
        (LocalPlaceBlock vK hvK w) ≃*
      HerbrandH0 (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion vK w)ˣ :=
  by
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    exact inducedHerbrandH0EquivOfFiniteCyclic
      (absoluteValueDecompositionGroup K w.1) σ hgen

/-- Degree-minus-one cohomology for one local block. -/
noncomputable def localPlaceBlockHerbrandHMinusOneEquiv
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalPlaceBlock vK hvK w) σ ≃*
      HerbrandHMinusOne
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K w.1) σ hgen) :=
  by
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    exact inducedHerbrandHMinusOneEquivOfFiniteCyclic
      (absoluteValueDecompositionGroup K w.1) σ hgen

end LocalClassFieldTheory
