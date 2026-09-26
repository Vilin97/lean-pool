/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.ObstructionValue
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.FacetShuffleEquiv
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.TopIncidenceComplex
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrderComplexRealization
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.FiniteAffineZeroCount
public import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.TopFlagSubdivision
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.TopFlagTerminalCancellation
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.MaximalFlagCode
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.MaximalFlagBridge
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ReferenceAffineOrbitCount

/-!
# AAK simplest route

This module records the hybrid route.  The order-complex realization supplies the
compact glued configuration model, while the top cycle is defined by the genuine cellular
incidence sum.
-/

@[expose] public section

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
noncomputable def simplestRouteCellularCycle
    (hp : Nat.Prime p)
    (H : FoxNeuwirth.FacetShuffleCardinality p) :
    FiniteIncidenceCycle (ZMod p) :=
  FoxNeuwirth.actualFiniteIncidenceCycle hp H

/-- The facet--shuffle theorem is unconditional. -/
theorem simplestRoute_facetTheorem
    (p : Nat) (hp : Nat.Prime p) :
    FoxNeuwirth.FacetShuffleCardinality p :=
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
        (FoxNeuwirth.orientedTopChain p) =
          (fun _ => (0 : ZMod p)) ∧
      FoxNeuwirth.zeroFacetBoundary
        (FoxNeuwirth.topIncidenceBoundary
          (FoxNeuwirth.orientedTopChain p)) =
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
noncomputable def simplestRouteStep
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
  exact ⟨simplestRouteStep H p hp K A hA phi⟩

/-- The locally constant obstruction theorem and the model-independent prime-factor iteration yield
the full arbitrary-number conclusion. -/
theorem avvakumov_akopyan_karasev_of_simplestRoute
    (H : SimplestRouteObstructionTheorem) :
    ∀ (K : Geometry.ConvexBody Plane) (n : Nat), 0 < n →
      ∃ P : ConvexPartition K n, P.IsFair :=
  avvakumov_akopyan_karasev_flexible
    (simplestRoute_implies_flexiblePrimeRefinement H)

end AAK
end NRR
