/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBVectorFiberElimination
public import Mathlib.Tactic
/-!
# Route B: finite coordinate split for a selected vector block

This file performs the algebraic coordinate bookkeeping needed after vector-fiber
elimination.  It deliberately does not assume that the `p` local scalar sites at
a selected vertex determine distinct quotient parameters.  Instead, the
collar-specific adapter must provide an explicit equivalence

`MovableParameter hp C ≃ Rest ⊕ Fin p`.

The right summand is the selected vector block and the left summand contains all
remaining movable scalar-orbit parameters.  From this index equivalence we
construct an equivalence of parameter spaces, prove its inverse formulas, and
isolate the single measure-preservation obligation needed by Step 5.
-/

@[expose] public section

namespace NRR

open MeasureTheory

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar
namespace RouteB

open Parameters
open RelativeGenericity
open EquivariantPrismGenericPerturbation

variable {p N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

/-- A finite decomposition of all movable scalar-orbit indices into the
selected `p`-coordinate vector block and its complement. -/
structure SelectedVectorCoordinateSplit where
  /-- The index type of movable coordinates outside the selected vector block. -/
  Rest : Type
  instFintypeRest : Fintype Rest
  instDecidableEqRest : DecidableEq Rest
  /-- Split movable coordinate indices into the remaining coordinates and one full vector block. -/
  indexEquiv : MovableParameter hp C ≃ Rest ⊕ Fin p

attribute [instance]
  SelectedVectorCoordinateSplit.instFintypeRest
  SelectedVectorCoordinateSplit.instDecidableEqRest

namespace SelectedVectorCoordinateSplit

/-- The movable parameter represented by coordinate `j` of the selected block. -/
noncomputable def selectedParameter
    (S : SelectedVectorCoordinateSplit hp C) (j : Fin p) : MovableParameter hp C :=
  S.indexEquiv.symm (Sum.inr j)

/-- The movable parameter represented by one complementary coordinate. -/
noncomputable def restParameter
    (S : SelectedVectorCoordinateSplit hp C) (r : S.Rest) : MovableParameter hp C :=
  S.indexEquiv.symm (Sum.inl r)

/-- The selected parameters are pairwise distinct. -/
theorem selectedParameter_injective
    (S : SelectedVectorCoordinateSplit hp C) :
    Function.Injective (selectedParameter (hp := hp) (C := C) S) := by
  intro i j hij
  apply Sum.inr.inj
  apply S.indexEquiv.symm.injective
  exact hij

/-- No selected parameter is a complementary parameter. -/
theorem selectedParameter_ne_restParameter
    (S : SelectedVectorCoordinateSplit hp C) (j : Fin p) (r : S.Rest) :
    selectedParameter (hp := hp) (C := C) S j ≠ restParameter (hp := hp) (C := C) S r := by
  intro h
  have := congrArg S.indexEquiv h
  simp [selectedParameter, restParameter] at this

/-- Split a movable assignment into complementary coordinates and the selected
`p`-vector block. -/
noncomputable def split
    (S : SelectedVectorCoordinateSplit hp C) :
    MovableParameterSpace hp C → (S.Rest → Real) × (Fin p → Real) :=
  fun x =>
    (fun r => x (restParameter (hp := hp) (C := C) S r),
     fun j => x (selectedParameter (hp := hp) (C := C) S j))

/-- Reassemble a movable assignment from complementary coordinates and the
selected vector block. -/
noncomputable def merge
    (S : SelectedVectorCoordinateSplit hp C) :
    ((S.Rest → Real) × (Fin p → Real)) → MovableParameterSpace hp C :=
  fun y q =>
    match S.indexEquiv q with
    | Sum.inl r => y.1 r
    | Sum.inr j => y.2 j

@[simp] theorem merge_apply_rest
    (S : SelectedVectorCoordinateSplit hp C)
    (y : (S.Rest → Real) × (Fin p → Real)) (r : S.Rest) :
    merge (hp := hp) (C := C) S y (restParameter (hp := hp) (C := C) S r) = y.1 r := by
  simp [merge, restParameter]

@[simp] theorem merge_apply_selected
    (S : SelectedVectorCoordinateSplit hp C)
    (y : (S.Rest → Real) × (Fin p → Real)) (j : Fin p) :
    merge (hp := hp) (C := C) S y (selectedParameter (hp := hp) (C := C) S j) = y.2 j := by
  simp [merge, selectedParameter]

@[simp] theorem split_merge
    (S : SelectedVectorCoordinateSplit hp C)
    (y : (S.Rest → Real) × (Fin p → Real)) :
    split (hp := hp) (C := C) S (merge (hp := hp) (C := C) S y) = y := by
  apply Prod.ext
  · funext r
    simp [split]
  · funext j
    simp [split]

@[simp] theorem merge_split
    (S : SelectedVectorCoordinateSplit hp C)
    (x : MovableParameterSpace hp C) :
    merge (hp := hp) (C := C) S (split (hp := hp) (C := C) S x) = x := by
  funext q
  cases h : S.indexEquiv q with
  | inl r =>
      have hq : q = restParameter (hp := hp) (C := C) S r := by
        apply S.indexEquiv.injective
        simp [restParameter, h]
      subst q
      simp [split]
  | inr j =>
      have hq : q = selectedParameter (hp := hp) (C := C) S j := by
        apply S.indexEquiv.injective
        simp [selectedParameter, h]
      subst q
      simp [split]

/-- The parameter-space coordinate permutation induced by the finite index
split. -/
noncomputable def parameterEquiv
    (S : SelectedVectorCoordinateSplit hp C) :
    MovableParameterSpace hp C ≃ (S.Rest → Real) × (Fin p → Real) where
  toFun := split (hp := hp) (C := C) S
  invFun := merge (hp := hp) (C := C) S
  left_inv := merge_split (hp := hp) (C := C) S
  right_inv := split_merge (hp := hp) (C := C) S

@[simp] theorem parameterEquiv_apply
    (S : SelectedVectorCoordinateSplit hp C)
    (x : MovableParameterSpace hp C) :
    parameterEquiv (hp := hp) (C := C) S x = split (hp := hp) (C := C) S x := rfl

@[simp] theorem parameterEquiv_symm_apply
    (S : SelectedVectorCoordinateSplit hp C)
    (y : (S.Rest → Real) × (Fin p → Real)) :
    (parameterEquiv (hp := hp) (C := C) S).symm y = merge (hp := hp) (C := C) S y := rfl

end SelectedVectorCoordinateSplit

/-- A selected coordinate split together with the analytic fact that its finite
coordinate permutation preserves product Lebesgue measure.

Keeping this as a separate field makes the exact remaining Mathlib adapter
visible: the algebraic decomposition above is unconditional, while this field
is discharged by the standard finite-coordinate permutation theorem. -/
structure MeasurePreservingSelectedVectorSplit
    (hp : Nat.Prime p)
    (C : RelativeAffineCellSystem hp N₀ N₁ M L) where
  /-- The finite-coordinate decomposition underlying the measure-preserving parameter split. -/
  coordinateSplit : SelectedVectorCoordinateSplit hp C
  /-- The measurable parameter-space equivalence separating the selected vector block. -/
  measurableEquiv :
    MeasurableEquiv
      (MovableParameterSpace hp C)
      ((coordinateSplit.Rest → Real) × (Fin p → Real))
  measurableEquiv_toEquiv :
    measurableEquiv.toEquiv = coordinateSplit.parameterEquiv
  measurePreserving : MeasurePreserving measurableEquiv

/-- Transport nullity from split coordinates back to the original movable
parameter space. -/
theorem volume_preimage_eq_zero_of_measurePreservingSplit
    (S : MeasurePreservingSelectedVectorSplit hp C)
    (t : Set ((S.coordinateSplit.Rest → Real) × (Fin p → Real)))
    (ht : ((volume : Measure (S.coordinateSplit.Rest → Real)).prod volume) t = 0) :
    volume (S.measurableEquiv ⁻¹' t) = 0 := by
  rw [S.measurePreserving.measure_preimage (NullMeasurableSet.of_null ht)]
  exact ht

/-- The split-coordinate image of one complete mixed-face bad set. -/
def splitMixedFaceBadSet
    (base : Assignment hp C)
    (κ : MixedFaceCase hp C)
    (S : SelectedVectorCoordinateSplit hp C) :
    Set ((S.Rest → Real) × (Fin p → Real)) :=
  SelectedVectorCoordinateSplit.parameterEquiv hp C S '' mixedFaceBadSet hp C base κ

/-- Builder reducing a collar-specific vector-block certificate to:

1. a finite coordinate split;
2. measure preservation of that split;
3. measurability and vector-fiber nullity of the bad set in split coordinates.
-/
noncomputable def mixedFaceVectorBlockCertificateOfSplit
    (base : Assignment hp C)
    (κ : MixedFaceCase hp C)
    (S : MeasurePreservingSelectedVectorSplit hp C)
    (hmeas : MeasurableSet
      (splitMixedFaceBadSet hp C base κ S.coordinateSplit))
    (hfiber : ∀ rest : S.coordinateSplit.Rest → Real,
      volume {u : Fin p → Real |
        (rest, u) ∈ splitMixedFaceBadSet hp C base κ S.coordinateSplit} = 0)
    (htransport :
      volume (mixedFaceBadSet hp C base κ) =
        ((volume : Measure (S.coordinateSplit.Rest → Real)).prod volume)
          (splitMixedFaceBadSet hp C base κ S.coordinateSplit)) :
    MixedFaceVectorBlockCertificate hp C base κ where
  data :=
    { Rest := S.coordinateSplit.Rest → Real
      badInSplitCoordinates :=
        splitMixedFaceBadSet hp C base κ S.coordinateSplit
      measurable_bad := hmeas
      fiber_null := hfiber }
  split := SelectedVectorCoordinateSplit.parameterEquiv hp C S.coordinateSplit
  bad_image := rfl
  measure_transport := htransport

end RouteB
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
