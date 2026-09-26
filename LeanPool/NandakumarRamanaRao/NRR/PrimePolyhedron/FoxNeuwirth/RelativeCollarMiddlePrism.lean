/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollar
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.SubdivisionPrismAffine
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismGenericityNonzero
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismGlobalCancellation
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ReferenceAffineOrbitCount

/-!
# The common-level staircase prism as an explicit relative-collar cell system

This module turns the already formalized fully refined staircase prism into the concrete cell-system
interface used by the endpoint-identified relative collar.  The cells are prime-orbit
representatives; equivariant values on all translates are reconstructed later by the decorated
vertex-parameter quotient.

The horizontal boundary of this cell system is at the combined spatial level `N + L`.  A later
module identifies its horizontal facet quotient with `RefinedAffineMap.TopCell hp (N + L)` and
packages the exact signed incidence formula.
-/

@[expose] public section

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeCollarMiddlePrism

open ExplicitAffineRelativeCollar
open EquivariantPrismGlobalCancellation
open EquivariantPrismGenericityNonzero
open SubdivisionPrismCharts
open SubdivisionPrismAffine
open EquivariantPrismVertexParameters
open RefinedAffineMap
open ReferenceAffineOrbitCount

variable {p : Nat}

/-- A selected top orbit used only to witness that the finite middle-prism cell type is nonempty. -/
noncomputable def selectedTopOrbit (hp : Nat.Prime p) : PrimeOrbitCycle.TopOrbit hp :=
  ((selectedOrbitEquivTopSupport hp)
    (Quotient.mk'' BarredPermutation.TopCell.evenRepresentative)).1

/-- A canonical refined spatial cell at any level. -/
noncomputable def defaultTopCell (hp : Nat.Prime p) (N : Nat) : TopCell hp N :=
  (selectedTopOrbit hp, fun _ => Equiv.refl _)

/-- A canonical fully refined prism cell. -/
noncomputable def defaultPrismCell
    (hp : Nat.Prime p) (N L : Nat) : PrismCell hp N L :=
  ((defaultTopCell hp N, ⟨0, hp.pos⟩), fun _ => Equiv.refl _)

/-- The geometric cylinder vertex of one fully refined middle-prism cell. -/
noncomputable def vertex
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) (i : Fin (p + 1)) : CylinderPoint p :=
  CylinderPoint.ofProd (SubdivisionPrismCharts.vertex hp N L q i)

/-- The geometric affine chart of one fully refined middle-prism cell. -/
noncomputable def chart
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) (w : Delta p) : CylinderPoint p :=
  CylinderPoint.ofProd (SubdivisionPrismCharts.chart hp N L q w)

@[simp] theorem chart_vertex
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) (i : Fin (p + 1)) :
    chart hp N L q (SphereOddDegree.FiniteSimplex.vertex (S := Real) i) = vertex hp N L q i :=
  rfl

/-- The existing refined staircase prism supplies a genuine explicit finite cell system whose two
horizontal triangulations both have combined level `N + L`. -/
noncomputable abbrev cellSystem
    (hp : Nat.Prime p) (N L : Nat) :
    RelativeAffineCellSystem hp (N + L) (N + L) (N + L) L where
  lower_le_common := le_rfl
  upper_le_common := le_rfl
  Cell := PrismCell hp N L
  cell_nonempty := ⟨defaultPrismCell hp N L⟩
  instCellFintype := inferInstance
  instCellDecidableEq := inferInstance
  coefficient := prismCoefficient hp N L
  vertex := vertex hp N L
  chart := chart hp N L
  chart_vertex := chart_vertex hp N L
  chart_spatial_affine := by
    intro q w c
    change
      ((EquivariantPrismSubdivisionMargin.basePrismChart hp N q.1)
        ((affineCompMap p L q.2) w)).1 c =
        ∑ i, w i * (SubdivisionPrismCharts.vertex hp N L q i).1 c
    exact SubdivisionPrismAffine.chart_spatial_affine hp N L q w c
  chart_time_affine := by
    intro q w
    change
      ((EquivariantPrismSubdivisionMargin.basePrismChart hp N q.1)
        ((affineCompMap p L q.2) w)).2 =
        ∑ i, w i * (SubdivisionPrismCharts.vertex hp N L q i).2
    exact SubdivisionPrismAffine.chart_time_affine hp N L q w
  chart_injective := by
    intro q x y hxy
    apply EquivariantPrismGenericityNonzero.prism_chart_injective hp N L q
    simpa [chart] using congrArg CylinderPoint.toProd hxy
  vertex_injective := by
    intro q i j hij
    apply EquivariantPrismGenericityNonzero.prism_vertex_injective hp N L q
    simpa [vertex] using congrArg CylinderPoint.toProd hij
  vertex_orbit_injective := by
    intro q g i j hij
    simpa [vertex] using
      EquivariantPrismGenericityNonzero.prism_vertex_orbit_injective hp N L q g i j hij

/-- The generic quotient action specialized to the explicit middle-prism carrier. -/
noncomputable instance middleGlobalVertexAction (hp : Nat.Prime p) (N L : Nat) :
    MulAction (PrimeSymmetry p) (Parameters.GlobalVertex hp (cellSystem hp N L)) :=
  Parameters.globalVertexAction hp (cellSystem hp N L)

end RelativeCollarMiddlePrism
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
