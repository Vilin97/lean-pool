/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableFullCollarRouteB
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBFrozenSupportGeometry

/-!
# Geometric Route B inputs for the affine-pullback full collar

This module proves the frozen positive-support certificate by following the actual three-region
Step 4 decomposition.  The lower iterated endpoint stack is lower-support safe, its composition
with the middle region remains lower-support safe, and the reversed upper stack is upper-support
safe.  The final half-cylinder composition therefore satisfies Route B's exact frozen-parameter
condition.
-/

@[expose] public section

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableFullCollarRouteBGeometry

open RefinedAffineMap
open EquivariantCoordinateHomotopy
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollarCompose
open ExplicitAffineRelativeCollarReverse
open ExplicitAffineRelativeCollarAssignmentCompose
open ExplicitAffineRelativeCollarAssignmentReverse
open ExplicitAffineRelativeCollarComposeDescribed
open CompatibleRefinedChartHomotopy
open CompatibleRefinedChartHomotopyPrism
open ChartMapCollarRepresentation
open EndpointStackIteratedAffinePullback
open RelativeSubdivisionEndpointCollar
open RelativeCollarMiddlePrismEndpoints
open StableFullCollarOriginMargin
open StableFullCollarConstructionAffinePullback
open StableFullCollarOriginMarginAffinePullback
open StableFullCollarRouteB
open RouteBFrozenSupportGeometry
open AffinePositiveRayBoundary

variable {p : Nat}

/-- The transported lower stack is lower-support safe. -/
theorem lowerCollar_lowerPositiveSupportRaySafe
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    LowerPositiveSupportRaySafe hp (lowerCollar hp A0 A1 L).cells
      (lowerAssignment hp A0 A1 L) :=
  castEndpoint_property
    (P := fun _ _ D b => LowerPositiveSupportRaySafe hp D.cells b)
    rfl (lowerLevel_eq A0 A1 L)
    (positiveWitness hp A0.toRegularApproximation.level
      (lowerStackIndex A1 L)).collar
    (build hp A0.toRegularApproximation (lowerStackIndex A1 L)).assignment
    (build_lowerPositiveSupportRaySafe hp A0 (lowerStackIndex A1 L))

/-- The transported reversed upper stack is upper-support safe. -/
theorem upperCollar_upperPositiveSupportRaySafe
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    UpperPositiveSupportRaySafe hp (upperCollar hp A0 A1 L).cells
      (upperAssignment hp A0 A1 L) :=
  castEndpoint_property
    (P := fun _ _ D b => UpperPositiveSupportRaySafe hp D.cells b)
    (upperLevel_eq A0 A1 L) rfl
    (reverseEndpointCollar
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar)
    (reverseAssignment
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar.cells
      (build hp A1.toRegularApproximation (upperStackIndex A0 L)).assignment)
    (upperSafe_reverse hp
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 L)).collar.cells
      (build hp A1.toRegularApproximation (upperStackIndex A0 L)).assignment
      (build_lowerPositiveSupportRaySafe hp A1 (upperStackIndex A0 L)))

/-- The lower two regions remain lower-support safe. -/
theorem lowerMiddleCollar_lowerPositiveSupportRaySafe
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    LowerPositiveSupportRaySafe hp (lowerMiddleCollar hp A0 A1 L).cells
      (lowerMiddleAssignment hp F0 F1 H A0 A1 L) :=
  lowerSafe_combined_left hp (lowerCollar hp A0 A1 L).cells
    (middleCollar hp A0 A1 L).cells (lowerAssignment hp A0 A1 L)
    (middleAssignment hp F0 F1 H A0 A1 L) (lowerSeam hp F0 F1 H A0 A1 L)
    (lowerCollar_lowerPositiveSupportRaySafe hp A0 A1 L)

/-- The complete three-region assignment is frozen-support safe. -/
theorem fullCollar_frozenPositiveSupportRaySafe
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    ExplicitAffineRelativeCollar.RouteB.FrozenPositiveSupportRaySafe hp
      (fullCollar hp A0 A1 L).cells (fullAssignment hp F0 F1 H A0 A1 L) :=
  frozenSafe_combined hp (lowerMiddleCollar hp A0 A1 L).cells
    (upperCollar hp A0 A1 L).cells (lowerMiddleAssignment hp F0 F1 H A0 A1 L)
    (upperAssignment hp A0 A1 L) (upperSeam hp F0 F1 H A0 A1 L)
    (lowerMiddleCollar_lowerPositiveSupportRaySafe hp F0 F1 H A0 A1 L)
    (upperCollar_upperPositiveSupportRaySafe hp A0 A1 L)

/-- The concrete Step 4 assignment satisfies Route B's support-level frozen safety condition. -/
theorem fineFullCollarData_frozenPositiveSupportRaySafe
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) :
    ExplicitAffineRelativeCollar.RouteB.FrozenPositiveSupportRaySafe hp
      (fineFullCollarData hp F0 F1 H A0 A1).collar.cells
      (fineFullCollarData hp F0 F1 H A0 A1).assignment :=
  fullCollar_frozenPositiveSupportRaySafe hp F0 F1 H A0 A1
    (middleRefinement hp F0 F1 H A0 A1)

/-- Frozen-support safety for the concrete quantitative Step 5 data. -/
theorem baseData_frozenPositiveSupportRaySafe
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) :
    ExplicitAffineRelativeCollar.RouteB.FrozenPositiveSupportRaySafe hp
      (baseData hp F0 F1 H A0 A1).collar.cells
      (baseData hp F0 F1 H A0 A1).assignment := by
  simpa [baseData, fullCollarOriginMarginDataAffinePullback,
    FullCollarOriginMarginData.ofFineFullCollarData] using
    fineFullCollarData_frozenPositiveSupportRaySafe hp F0 F1 H A0 A1

end StableFullCollarRouteBGeometry
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
