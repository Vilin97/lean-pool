/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.ObstructionValue
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.FacetShuffleEquiv
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.TopIncidenceComplex
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrderComplexRealization
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.FiniteAffineZeroCount
import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.TopFlagSubdivision
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.TopFlagTerminalCancellation
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.MaximalFlagCode
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.MaximalFlagBridge
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ReferenceAffineOrbitCount

/-!
# AAK simplest route

This module records the hybrid route.  The order-complex realization supplies the
compact glued configuration model, while the top cycle is defined by the genuine cellular
incidence sum.
-/

namespace NRR
namespace AAK

variable {p : Nat}

/-- The first completed reduction: actual boundary coefficients are extension multiplicities. -/
theorem simplestRoute_actualBoundaryReduction
    (hp : Nat.Prime p) (a : BarredPermutation p) :
    FoxNeuwirth.actualTopBoundaryCoefficient a =
      (FoxNeuwirth.topExtensionMultiplicity a : ZMod p) *
        (a.orientationSign : ZMod p) :=
  FoxNeuwirth.actualTopBoundaryCoefficient_eq_multiplicity hp a

/-- The finite shuffle-cardinality theorem is sufficient to construct the genuine cellular
incidence cycle. -/
noncomputable def simplestRoute_cellularCycle
    (hp : Nat.Prime p)
    (H : FoxNeuwirth.FacetShuffleCardinality hp) :
    FiniteIncidenceCycle (ZMod p) :=
  FoxNeuwirth.actualFiniteIncidenceCycle hp H

/-- The facet--shuffle theorem is unconditional. -/
theorem simplestRoute_facetTheorem
    (p : Nat) (hp : Nat.Prime p) :
    FoxNeuwirth.FacetShuffleCardinality hp :=
  FoxNeuwirth.facetShuffleCardinality hp

/-- The genuine cellular-cycle stage is closed for every prime. -/
theorem simplestRoute_cellularStage
    (p : Nat) (hp : Nat.Prime p) :
    Nonempty (FiniteIncidenceCycle.{0, 0, 0} (ZMod p)) :=
  ⟨FoxNeuwirth.primeActualFiniteIncidenceCycle hp⟩

/-- The exact two-term top incidence complex is unconditional.  No lower-dimensional
Fox--Neuwirth incidence convention is assumed. -/
theorem simplestRoute_topIncidenceStage
    (p : Nat) (hp : Nat.Prime p) :
    FoxNeuwirth.topIncidenceBoundary
        (FoxNeuwirth.orientedTopChain hp) =
          (fun _ => (0 : ZMod p)) ∧
      FoxNeuwirth.zeroFacetBoundary
        (FoxNeuwirth.topIncidenceBoundary
          (FoxNeuwirth.orientedTopChain hp)) =
            (fun _ => (0 : ZMod p)) := by
  constructor
  · exact FoxNeuwirth.topIncidenceBoundary_orientedTopChain_eq_zero hp
  · exact FoxNeuwirth.zeroFacetBoundary_comp_topIncidenceBoundary _

end AAK
end NRR

namespace NRR
namespace AAK

open Geometry

/-- The exact analytic/topological theorem needed after the finite cellular and affine stages.
Its output is a locally constant orbit obstruction on the complement of the projected zero set. -/
def SimplestRouteObstructionTheorem : Prop :=
  ∀ (p : Nat) (hp : Nat.Prime p)
    (K : Geometry.ConvexBody Plane) (A : Real) (hA : 0 < A)
    [Nonempty (BodySpace K A)]
    (phi : NiceMV (BodySpace K (A / (p : Real)))),
      Nonempty
        (ComplementObstructionValue
          (BodySpace K A)
          ((FoxNeuwirthOrderComplex.orderComplexModel hp).projectedAllChildrenZeroSet
            hA phi)
          (ZMod p))

/-- A locally constant obstruction on the order-complex model produces a model-independent
prime-refinement step. -/
noncomputable def simplestRoute_step
    (H : SimplestRouteObstructionTheorem)
    (p : Nat) (hp : Nat.Prime p)
    (K : Geometry.ConvexBody Plane) (A : Real) (hA : 0 < A)
    [Nonempty (BodySpace K A)]
    (phi : NiceMV (BodySpace K (A / (p : Real)))) :
    FlexiblePrimeRefinementStep hp hA phi := by
  let M := FoxNeuwirthOrderComplex.orderComplexModel hp
  let D := Classical.choice (H p hp K A hA phi)
  let S : TopBottomSeparator (BodySpace K A) :=
    D.toTopBottomSeparator (M.isClosed_projectedAllChildrenZeroSet hA phi)
  exact
    { model := M
      certificate :=
        { separator := S
          lifts := by
            intro C y hy
            change (C, y) ∈ M.projectedAllChildrenZeroSet hA phi at hy
            exact hy } }

/-- The locally constant obstruction theorem closes the flexible prime-refinement interface. -/
theorem simplestRoute_implies_flexiblePrimeRefinement
    (H : SimplestRouteObstructionTheorem) :
    FlexiblePrimeRefinementTheorem := by
  intro p hp K A hA _ phi
  exact ⟨simplestRoute_step H p hp K A hA phi⟩

/-- The locally constant obstruction theorem and the model-independent prime-factor iteration yield the full arbitrary-number conclusion. -/
theorem avvakumov_akopyan_karasev_of_simplestRoute
    (H : SimplestRouteObstructionTheorem) :
    ∀ (K : Geometry.ConvexBody Plane) (n : Nat), 0 < n →
      ∃ P : ConvexPartition K n, P.IsFair :=
  avvakumov_akopyan_karasev_flexible
    (simplestRoute_implies_flexiblePrimeRefinement H)

end AAK
end NRR
