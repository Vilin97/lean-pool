/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableFullCollarRouteBGeometry
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableFullCollarRouteBFacetGeometry

/-!
# Unconditional Route B perturbation on the affine-pullback full collar

This module combines the two concrete geometric certificates proved for the Step 4 collar:

* frozen positive-support ray safety; and
* nontriviality of every boundary-restricted facet determinant polynomial.

The open-neighborhood theorem in `RouteBSmallGenericPerturbation` converts the second
certificate into a positive-radius facet-regular perturbation ball.  The generic Route B selection
theorem then produces a small, frozen-boundary-preserving, prime-equivariant perturbation in full
positive-ray general position while retaining half of the Step 5 origin margin.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableFullCollarRouteBComplete

open EquivariantCoordinateHomotopy
open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open ExplicitAffineRelativeCollar.RelativeGenericity
open ExplicitAffineRelativeCollar.RouteB
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open EquivariantPrismGenericPerturbation
open StableFullCollarOriginMargin
open StableFullCollarOriginMarginAffinePullback
open StableFullCollarRouteB
open StableFullCollarRouteBGeometry
open StableFullCollarRouteBFacetGeometry

variable {p : Nat}

/-- Item 3.1: the concrete affine-pullback full collar is safe whenever every
positive-weight local vertex is frozen.  This is the exact support-level
hypothesis used by Route B; zero-weight movable vertices are intentionally
irrelevant. -/
theorem frozenPositiveSupportRaySafe_affinePullback
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    FrozenPositiveSupportRaySafe hp
      (baseData hp F₀ F₁ H A₀ A₁).collar.cells
      (baseData hp F₀ F₁ H A₀ A₁).assignment :=
  baseData_frozenPositiveSupportRaySafe hp F₀ F₁ H A₀ A₁

/-- Item 3.2: every positive requested perturbation size admits a genuine
positive-radius neighborhood around a nearby generic center.  Throughout this
ball the reconstructed full assignment stays within the independent control
radius `min eps (margin / 2)` of the Step 4 base assignment and every local
facet remains regular. -/
theorem safePerturbationBall_affinePullback
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    {eps : Real} (heps : 0 < eps) :
    Nonempty (SafePerturbationBall hp
      (baseData hp F₀ F₁ H A₀ A₁).collar.cells
      (baseData hp F₀ F₁ H A₀ A₁).assignment eps
      (baseData hp F₀ F₁ H A₀ A₁).margin) :=
  exists_safePerturbationBall hp
    (baseData hp F₀ F₁ H A₀ A₁).collar.cells
    (baseData hp F₀ F₁ H A₀ A₁).assignment
    heps
    (baseData hp F₀ F₁ H A₀ A₁).margin_pos
    (baseData_allRestrictedFacetPolynomialsNonzero hp F₀ F₁ H A₀ A₁)

/-- A canonical safe perturbation ball, selected noncomputably from Item 3.2. -/
noncomputable def chosenSafePerturbationBallAffinePullback
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    {eps : Real} (heps : 0 < eps) :
    SafePerturbationBall hp
      (baseData hp F₀ F₁ H A₀ A₁).collar.cells
      (baseData hp F₀ F₁ H A₀ A₁).assignment eps
      (baseData hp F₀ F₁ H A₀ A₁).margin :=
  Classical.choice
    (safePerturbationBall_affinePullback hp F₀ F₁ H A₀ A₁ heps)

/-- The selected Item 3.2 neighborhood has positive radius. -/
theorem chosenSafePerturbationBall_affinePullback_radius_pos
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    {eps : Real} (heps : 0 < eps) :
    0 < (chosenSafePerturbationBallAffinePullback
      hp F₀ F₁ H A₀ A₁ heps).radius :=
  (chosenSafePerturbationBallAffinePullback
    hp F₀ F₁ H A₀ A₁ heps).radius_pos

/-- Every point in the selected Item 3.2 neighborhood reconstructs an
assignment within the required control radius of the Step 4 base assignment. -/
theorem chosenSafePerturbationBall_affinePullback_closeToBase
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    {eps : Real} (heps : 0 < eps)
    (x : MovableParameterSpace hp
      (baseData hp F₀ F₁ H A₀ A₁).collar.cells)
    (hx : x ∈ Metric.ball
      (chosenSafePerturbationBallAffinePullback
        hp F₀ F₁ H A₀ A₁ heps).center
      (chosenSafePerturbationBallAffinePullback
        hp F₀ F₁ H A₀ A₁ heps).radius) :
    AssignmentClose
      (assignmentOfMovableParameters hp
        (baseData hp F₀ F₁ H A₀ A₁).collar.cells
        (baseData hp F₀ F₁ H A₀ A₁).assignment x)
      (baseData hp F₀ F₁ H A₀ A₁).assignment
      (perturbationControlRadius eps
        (baseData hp F₀ F₁ H A₀ A₁).margin) :=
  (chosenSafePerturbationBallAffinePullback
    hp F₀ F₁ H A₀ A₁ heps).closeToBase x hx

/-- Every point in the selected Item 3.2 neighborhood is facet-regular on all
cells of the concrete full collar. -/
theorem chosenSafePerturbationBall_affinePullback_facetRegular
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    {eps : Real} (heps : 0 < eps)
    (x : MovableParameterSpace hp
      (baseData hp F₀ F₁ H A₀ A₁).collar.cells)
    (hx : x ∈ Metric.ball
      (chosenSafePerturbationBallAffinePullback
        hp F₀ F₁ H A₀ A₁ heps).center
      (chosenSafePerturbationBallAffinePullback
        hp F₀ F₁ H A₀ A₁ heps).radius) :
    AllCellsFacetRegular hp
      (baseData hp F₀ F₁ H A₀ A₁).collar.cells
      (baseData hp F₀ F₁ H A₀ A₁).assignment x :=
  (chosenSafePerturbationBallAffinePullback
    hp F₀ F₁ H A₀ A₁ heps).facetRegular x hx

/-- The concrete affine-pullback collar supplies every geometric input required by Route B. -/
theorem baseData_geometricInput
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    GeometricInput hp F₀ F₁ H A₀ A₁ :=
  { frozenSupportSafe :=
      baseData_frozenPositiveSupportRaySafe hp F₀ F₁ H A₀ A₁
    facetPolynomialsNonzero :=
      baseData_allRestrictedFacetPolynomialsNonzero hp F₀ F₁ H A₀ A₁ }

/-- Steps 2 and 3 specialized to the concrete Step 4 collar: for every positive requested size,
there is a small generic perturbation preserving the two horizontal boundary assignments,
retaining a positive origin margin, and putting every collar cell in positive-ray general
position. -/
theorem exists_smallGenericPerturbation_affinePullback_unconditional
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    {eps : Real} (heps : 0 < eps) :
    Nonempty (SmallGenericPerturbationResult hp
      (baseData hp F₀ F₁ H A₀ A₁).collar.cells
      (baseData hp F₀ F₁ H A₀ A₁).assignment eps
      (baseData hp F₀ F₁ H A₀ A₁).margin) := by
  let D := baseData hp F₀ F₁ H A₀ A₁
  obtain ⟨B⟩ := safePerturbationBall_affinePullback
    hp F₀ F₁ H A₀ A₁ heps
  exact exists_smallGenericPerturbation hp D.collar.cells D.assignment
    heps D.margin_pos D.coordinateNormMargin
    (frozenPositiveSupportRaySafe_affinePullback hp F₀ F₁ H A₀ A₁) B

/-- An explicit witness form of the unconditional Route B output. -/
theorem smallGenericPerturbation_affinePullback_exists
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    {eps : Real} (heps : 0 < eps) :
    ∃ R : SmallGenericPerturbationResult hp
        (baseData hp F₀ F₁ H A₀ A₁).collar.cells
        (baseData hp F₀ F₁ H A₀ A₁).assignment eps
        (baseData hp F₀ F₁ H A₀ A₁).margin,
      (∀ {s : Parameter hp (baseData hp F₀ F₁ H A₀ A₁).collar.cells},
        IsFrozenParameter hp (baseData hp F₀ F₁ H A₀ A₁).collar.cells s →
        assignmentOfMovableParameters hp
            (baseData hp F₀ F₁ H A₀ A₁).collar.cells
            (baseData hp F₀ F₁ H A₀ A₁).assignment R.move s =
          (baseData hp F₀ F₁ H A₀ A₁).assignment s) ∧
      (∀ q : (baseData hp F₀ F₁ H A₀ A₁).collar.cells.Cell,
        PositiveRayGeneralPosition hp
          (localVertexMap hp
            (baseData hp F₀ F₁ H A₀ A₁).collar.cells
            (assignmentOfMovableParameters hp
              (baseData hp F₀ F₁ H A₀ A₁).collar.cells
              (baseData hp F₀ F₁ H A₀ A₁).assignment R.move) q)) := by
  obtain ⟨R⟩ := exists_smallGenericPerturbation_affinePullback_unconditional
    hp F₀ F₁ H A₀ A₁ heps
  exact ⟨R, (fun hs => R.fixesFrozen hs), R.positiveRayGeneralPosition⟩

/-- The retained margin in the unconditional perturbation is strictly positive. -/
theorem smallGenericPerturbation_affinePullback_retainedMargin_pos
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    0 < (baseData hp F₀ F₁ H A₀ A₁).margin / 2 :=
  half_pos (baseData hp F₀ F₁ H A₀ A₁).margin_pos

end StableFullCollarRouteBComplete
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
