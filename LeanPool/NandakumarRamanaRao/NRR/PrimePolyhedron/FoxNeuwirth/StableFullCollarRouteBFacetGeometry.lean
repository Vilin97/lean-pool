/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableFullCollarRouteBGeometry
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBFacetTargetComposition
/-!
# Facet-polynomial nontriviality for the affine-pullback full collar

The lower endpoint stack carries lower-relative facet targets by induction.  Reversal gives the
upper-relative targets.  The middle prism is strictly internal in the final three-region collar,
so universal triangular targets suffice there.  The two composition steps therefore yield exact
frozen-relative targets for every final cell and facet.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableFullCollarRouteBFacetGeometry

open RefinedAffineMap
open EquivariantCoordinateHomotopy
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
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
open RouteBEndpointFacetTargets
open RouteBFacetTargetComposition
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open ExplicitAffineRelativeCollar.RouteB

variable {p : Nat}

/-- Every iterated lower endpoint stack admits boundary-respecting regular facet targets. -/
theorem build_lowerFacetTargets
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : StableRegularApproximation hp F) :
    ∀ k : Nat,
      LowerFacetTargets hp
        (positiveWitness hp A.toRegularApproximation.level k).collar.cells
        (build hp A.toRegularApproximation k).assignment
  | 0 => by
      simpa [positiveWitness, EndpointStackIteratedAffinePullback.build,
        RelativeSubdivisionEndpointCollar.oneStepWitness,
        RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar,
        RelativeSubdivisionOneStepCollar.relativeCollar] using
        oneStep_lowerFacetTargets hp A
  | k + 1 => by
      let D0 := build hp A.toRegularApproximation k
      let K := baseOriginalPLMap hp A.toRegularApproximation
      let C0 := (positiveWitness hp A.toRegularApproximation.level k).collar
      let E := (oneStepWitness hp
        (A.toRegularApproximation.level + (k + 1))).collar
      let b : Assignment hp E.cells := by
        simpa [E, RelativeSubdivisionEndpointCollar.oneStepWitness,
          RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar,
          RelativeSubdivisionOneStepCollar.relativeCollar] using
          CompatibleChartMapOneStep.assignment hp (K.refine (k + 1))
      have hbRep : Represents E.cells K (vectorValue hp E.cells b) := by
        simpa [E, b, RelativeSubdivisionEndpointCollar.oneStepWitness,
          RelativeSubdivisionOneStepCollar.endpointIdentifiedCollar,
          RelativeSubdivisionOneStepCollar.relativeCollar] using
          oneStepAssignment_represents_base hp K (k + 1)
      let hseam := seamCompatible C0.cells E.cells K
        (vectorValue hp C0.cells D0.assignment) (vectorValue hp E.cells b)
        D0.represents hbRep
      simpa [positiveWitness, EndpointStackIteratedAffinePullback.build,
        C0, E, b, hseam,
        RelativeSubdivisionEndpointCollar.composeWitness,
        ExplicitAffineRelativeCollarCompose.endpointIdentifiedCollar,
        ExplicitAffineRelativeCollarCompose.relativeCollar] using
        lowerFacetTargets_combined_left hp C0.cells E.cells
          D0.assignment b hseam (build_lowerFacetTargets hp A k)

/-- The transported lower stack carries lower-relative facet targets. -/
theorem lowerCollar_lowerFacetTargets
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    LowerFacetTargets hp (lowerCollar hp A0 A1 L).cells
      (lowerAssignment hp A0 A1 L) :=
  castEndpoint_property
    (P := fun _ _ D b => LowerFacetTargets hp D.cells b)
    rfl (lowerLevel_eq A0 A1 L)
    (positiveWitness hp A0.toRegularApproximation.level
      (lowerStackIndex A0 A1 L)).collar
    (build hp A0.toRegularApproximation (lowerStackIndex A0 A1 L)).assignment
    (build_lowerFacetTargets hp A0 (lowerStackIndex A0 A1 L))

/-- The transported reversed upper stack carries upper-relative facet targets. -/
theorem upperCollar_upperFacetTargets
    (hp : Nat.Prime p)
    {F0 F1 : ZeroFreeMap hp}
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    UpperFacetTargets hp (upperCollar hp A0 A1 L).cells
      (upperAssignment hp A0 A1 L) :=
  castEndpoint_property
    (P := fun _ _ D b => UpperFacetTargets hp D.cells b)
    (upperLevel_eq A0 A1 L) rfl
    (reverseEndpointCollar
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 A1 L)).collar)
    (reverseAssignment
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 A1 L)).collar.cells
      (build hp A1.toRegularApproximation (upperStackIndex A0 A1 L)).assignment)
    (upperFacetTargets_reverse hp
      (positiveWitness hp A1.toRegularApproximation.level
        (upperStackIndex A0 A1 L)).collar.cells
      (build hp A1.toRegularApproximation (upperStackIndex A0 A1 L)).assignment
      (build_lowerFacetTargets hp A1 (upperStackIndex A0 A1 L)))

/-- The lower two regions keep lower-relative facet targets. -/
theorem lowerMiddleCollar_lowerFacetTargets
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    LowerFacetTargets hp (lowerMiddleCollar hp A0 A1 L).cells
      (lowerMiddleAssignment hp F0 F1 H A0 A1 L) :=
  lowerFacetTargets_combined_left hp (lowerCollar hp A0 A1 L).cells
    (middleCollar hp A0 A1 L).cells (lowerAssignment hp A0 A1 L)
    (middleAssignment hp F0 F1 H A0 A1 L) (lowerSeam hp F0 F1 H A0 A1 L)
    (lowerCollar_lowerFacetTargets hp A0 A1 L)

/-- The complete three-region collar carries frozen-relative facet targets. -/
theorem fullCollar_frozenFacetTargets
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map)
    (L : Nat) :
    FrozenFacetTargets hp (fullCollar hp A0 A1 L).cells
      (fullAssignment hp F0 F1 H A0 A1 L) :=
  frozenFacetTargets_combined hp (lowerMiddleCollar hp A0 A1 L).cells
    (upperCollar hp A0 A1 L).cells (lowerMiddleAssignment hp F0 F1 H A0 A1 L)
    (upperAssignment hp A0 A1 L) (upperSeam hp F0 F1 H A0 A1 L)
    (lowerMiddleCollar_lowerFacetTargets hp F0 F1 H A0 A1 L)
    (upperCollar_upperFacetTargets hp A0 A1 L)

/-- The concrete Step 4 collar has a frozen-relative regular target for every local facet. -/
theorem fineFullCollarData_frozenFacetTargets
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) :
    FrozenFacetTargets hp
      (fineFullCollarData hp F0 F1 H A0 A1).collar.cells
      (fineFullCollarData hp F0 F1 H A0 A1).assignment :=
  fullCollar_frozenFacetTargets hp F0 F1 H A0 A1
    (middleRefinement hp F0 F1 H A0 A1)

/-- Pointwise regularity witnesses for every boundary-restricted facet polynomial. -/
theorem baseData_allFacetRegularityWitnesses
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) :
    AllFacetRegularityWitnesses hp
      (baseData hp F0 F1 H A0 A1).collar.cells
      (baseData hp F0 F1 H A0 A1).assignment := by
  apply allFacetRegularityWitnesses_of_frozenFacetTargets
  simpa [baseData, fullCollarOriginMarginData_affinePullback,
    FullCollarOriginMarginData.ofFineFullCollarData] using
    fineFullCollarData_frozenFacetTargets hp F0 F1 H A0 A1

/-- Every restricted facet determinant polynomial for the concrete collar is nonzero. -/
theorem baseData_allRestrictedFacetPolynomialsNonzero
    (hp : Nat.Prime p)
    (F0 F1 : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F0 F1)
    (A0 : StableRegularApproximation hp F0.map)
    (A1 : StableRegularApproximation hp F1.map) :
    AllRestrictedFacetPolynomialsNonzero hp
      (baseData hp F0 F1 H A0 A1).collar.cells
      (baseData hp F0 F1 H A0 A1).assignment :=
  allRestrictedFacetPolynomialsNonzero_of_witnesses hp
    (baseData hp F0 F1 H A0 A1).collar.cells
    (baseData hp F0 F1 H A0 A1).assignment
    (baseData_allFacetRegularityWitnesses hp F0 F1 H A0 A1)

end StableFullCollarRouteBFacetGeometry
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
