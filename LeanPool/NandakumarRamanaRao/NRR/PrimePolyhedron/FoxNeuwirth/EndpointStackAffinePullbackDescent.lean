/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EndpointStackAffinePullbackCore
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollar
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RefinedChartCarrierEquivariant
/-!
# Global descent interface for affine-pullback endpoint-stack values

The composable simplex-local convention assigns to every one-step-cylinder vertex the value of the
parent endpoint PL map at that vertex's spatial barycentric point.  This file packages the exact
shared-face compatibility theorem needed for those values to descend through the global vertex and
prime-orbit quotients. The compatibility theorem lets the quotient assignment reconstruct the
simplex-local affine-pullback values, so origin avoidance follows from
`EndpointStackAffinePullbackEndpointStackAffinePullbackCore.affine_pullbackEndpointValue_ne_zero`.

The upper values are the ordinary PL values at the next
barycentric-subdivision vertices.  Hence this convention is seam-compatible under iteration.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace EndpointStackAffinePullbackDescent

open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open EquivariantPrismVertexParameters
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap


variable {p : Nat}

private abbrev parentIndex (p : Nat) :
    Fin (p - 1 + 1) → Fin (p - 1 + 1) :=
  EndpointStackAffinePullbackCore.parentIndex p

private abbrev cylinderIndex (hp : Nat.Prime p) : Fin (p + 1) → Fin (p - 1 + 2) :=
  EndpointStackAffinePullbackCore.cylinderIndex hp

/-- The one-step endpoint cylinder used throughout this module. -/
noncomputable abbrev Cells (hp : Nat.Prime p) (N : Nat) :=
  RelativeSubdivisionOneStepCells.cellSystem hp N

/-- Parent-PL pullback value at one local one-step-cylinder vertex occurrence. -/
noncomputable def pullbackVector
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (s : (Cells hp A.level).VertexSlot) : Fin p → Real :=
  EndpointStackAffinePullbackCore.pullbackVertexValue (p - 1) s.1.2
    (fun j => A.map (RefinedAffineMap.vertex hp A.level s.1.1
      (parentIndex p j))) (cylinderIndex hp s.2)

/-- Prime-decorated local pullback value. -/
noncomputable def decoratedPullbackVector
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (s : CoverVertexSlot hp (Cells hp A.level)) : Fin p → Real :=
  s.1 • pullbackVector hp A s.2

/-- Exact shared-face theorem required for the affine-pullback values to define a global vertex
assignment.  It states the geometric carrier compatibility: parent endpoint PL formulas agree
on every shared refined face and commute with the prime action. -/
def OneStepAffinePullbackCompatible
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) : Prop :=
  ∀ a b : CoverVertexSlot hp (Cells hp A.level),
    coverPoint hp (Cells hp A.level) a = coverPoint hp (Cells hp A.level) b →
      decoratedPullbackVector hp A a = decoratedPullbackVector hp A b


/-- Spatial standard-simplex point represented by one local one-step-cylinder vertex. -/
noncomputable def localSpatialWeight
    (hp : Nat.Prime p) (N : Nat)
    (s : (Cells hp N).VertexSlot) : StandardSimplex (p - 1) :=
  StandardSimplex.ofDelta
    (RelativeSubdivisionOneStepCells.localPoint hp s.1.2 (stdSimplex.vertex (S := Real) s.2)).1

/-- A local pullback vector is literally the parent refined affine value at the represented
spatial point. -/
theorem pullbackVector_eq_value
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (s : (Cells hp A.level).VertexSlot) :
    pullbackVector hp A s =
      RefinedAffineMap.value hp A.level A.map s.1.1
        (localSpatialWeight hp A.level s) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp.pos)
  have h := EndpointStackAffinePullbackCore.affine_pullbackEndpointValue_eq_value hp A s.1.1 s.1.2
    (stdSimplex.vertex (S := Real) s.2)
  funext c
  have hc := congrFun h c
  simp [RelativeSubdivisionOneStepCells.localWeight,
    Nat.sub_add_cancel hp.pos] at hc
  rw [show RelativeSubdivisionCylinderCombinatorics.spatialPoint k s.1.2
      (stdSimplex.vertex (S := Real) s.2) =
      (RelativeSubdivisionCylinderCombinatorics.vertex k s.1.2 s.2).1 by
    exact congrArg Prod.fst
      (RelativeSubdivisionCylinderCombinatorics.chart_vertex k s.1.2 s.2)] at hc
  simpa [pullbackVector, localSpatialWeight,
    EndpointStackAffinePullbackCore.pullbackVertexValue,
    EndpointStackAffinePullbackCore.parentIndex,
    EndpointStackAffinePullbackCore.cylinderIndex,
    RelativeSubdivisionOneStepCells.localPoint,
    RelativeSubdivisionOneStepCells.localWeight, parentIndex, cylinderIndex,
    Nat.sub_add_cancel hp.pos, Pi.single_apply] using hc

/-- The affine-pullback convention satisfies the required global shared-face compatibility.
The proof uses the chart-independent carrier theorem and equivariance of the sampled endpoint map. -/
theorem oneStepAffinePullbackCompatible
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) :
    OneStepAffinePullbackCompatible hp A := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp.pos)
  intro a b hab
  have hspatial := congrArg CylinderPoint.spatial hab
  have hchart :
      a.1 • RefinedAffineMap.chart hp A.level a.2.1.1
          (StandardSimplex.toDelta (localSpatialWeight hp A.level a.2)) =
        b.1 • RefinedAffineMap.chart hp A.level b.2.1.1
          (StandardSimplex.toDelta (localSpatialWeight hp A.level b.2)) := by
    simpa [ExplicitAffineRelativeCollar.Parameters.coverPoint,
      RelativeAffineCellSystem.slotPoint, Cells, localSpatialWeight,
      RelativeSubdivisionOneStepCells.cellSystem,
      RelativeSubdivisionOneStepCells.vertex, RelativeSubdivisionOneStepCells.chart,
      RelativeSubdivisionOneStepCells.liftPoint,
      EquivariantPrismVertexParameters.CylinderPoint.ofProd] using hspatial
  rw [decoratedPullbackVector, decoratedPullbackVector,
    pullbackVector_eq_value hp A a.2, pullbackVector_eq_value hp A b.2]
  exact RefinedChartCarrierEquivariant.decorated_value_eq_of_decorated_chart_eq
    hp A.level A.map A.equivariant
      a.2.1.1 b.2.1.1 a.1 b.1
      (localSpatialWeight hp A.level a.2)
      (localSpatialWeight hp A.level b.2) hchart

/-- Compatible affine-pullback values descend to global collar vertices. -/
noncomputable def globalPullbackVector
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepAffinePullbackCompatible hp A) :
    GlobalVertex hp (Cells hp A.level) → Fin p → Real :=
  Quotient.lift (decoratedPullbackVector hp A) (by
    intro a b hab
    exact hcompat a b hab)

@[simp] theorem globalPullbackVector_mk
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepAffinePullbackCompatible hp A)
    (s : CoverVertexSlot hp (Cells hp A.level)) :
    globalPullbackVector hp A hcompat (Quotient.mk _ s) =
      decoratedPullbackVector hp A s := rfl

/-- The descended global vector assignment is prime-equivariant. -/
theorem globalPullbackVector_smul
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepAffinePullbackCompatible hp A)
    (g : PrimeSymmetry p)
    (x : GlobalVertex hp (Cells hp A.level)) :
    globalPullbackVector hp A hcompat (g • x) =
      g • globalPullbackVector hp A hcompat x := by
  refine Quotient.inductionOn x ?_
  intro s
  rfl

/-- Scalar site value obtained from the descended global vector assignment. -/
noncomputable def pullbackSiteValue
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepAffinePullbackCompatible hp A)
    (s : ScalarSite hp (Cells hp A.level)) : Real :=
  globalPullbackVector hp A hcompat s.1 s.2

/-- The scalar site value is constant on diagonal prime orbits. -/
theorem pullbackSiteValue_eq_of_orbitRel
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepAffinePullbackCompatible hp A)
    {a b : ScalarSite hp (Cells hp A.level)}
    (hab : MulAction.orbitRel (PrimeSymmetry p)
      (ScalarSite hp (Cells hp A.level)) a b) :
    pullbackSiteValue hp A hcompat a = pullbackSiteValue hp A hcompat b := by
  rw [MulAction.orbitRel_apply] at hab
  rcases hab with ⟨g, rfl⟩
  have h := congrFun (globalPullbackVector_smul hp A hcompat g b.1) (g • b.2)
  simpa [pullbackSiteValue, PrimeSymmetry.smul_coordinate_apply,
    PrimeSymmetry.smul_label] using h

/-- Genuine compatible equivariant assignment obtained from affine pullback. -/
noncomputable def assignment
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepAffinePullbackCompatible hp A) :
    Assignment hp (Cells hp A.level) :=
  fun q => Quotient.liftOn q (pullbackSiteValue hp A hcompat) (by
    intro a b hab
    exact pullbackSiteValue_eq_of_orbitRel hp A hcompat hab)


/-- Canonical one-step affine-pullback assignment, with compatibility discharged internally. -/
noncomputable def canonicalAssignment
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) :
    Assignment hp (Cells hp A.level) :=
  assignment hp A (oneStepAffinePullbackCompatible hp A)

/-- The quotient assignment reconstructs the intended local pullback value. -/
theorem vectorValue_assignment_sample
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepAffinePullbackCompatible hp A)
    (s : (Cells hp A.level).VertexSlot) :
    vectorValue hp (Cells hp A.level) (assignment hp A hcompat)
      (sampleVertex hp (Cells hp A.level) s) = pullbackVector hp A s := by
  rfl

/-- Local vertex values of the descended assignment are exactly the simplex-local affine pullback. -/
theorem localVertexMap_assignment_value
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepAffinePullbackCompatible hp A)
    (q : (Cells hp A.level).Cell)
    (i : Fin (p + 1)) :
    (localVertexMap hp (Cells hp A.level) (assignment hp A hcompat) q).value i =
      EndpointStackAffinePullbackCore.pullbackVertexValue (p - 1) q.2
        (fun j => A.map (RefinedAffineMap.vertex hp A.level q.1
          (parentIndex p j))) (cylinderIndex hp i) := by
  exact vectorValue_assignment_sample hp A hcompat (q, i)

/-- Every one-step affine-pullback cell of the descended assignment avoids the origin. -/
theorem assignment_avoidsOrigin
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (hcompat : OneStepAffinePullbackCompatible hp A)
    (q : (Cells hp A.level).Cell) :
    AvoidsOrigin
      (localVertexMap hp (Cells hp A.level) (assignment hp A hcompat) q) := by
  intro w
  change
    (fun c => ∑ i : Fin (p + 1), w i *
      (localVertexMap hp (Cells hp A.level) (assignment hp A hcompat) q).value i c) ≠ 0
  convert EndpointStackAffinePullbackCore.affine_pullbackEndpointValue_ne_zero
      hp A q.1 q.2 (StandardSimplex.toDelta w) using 1
  funext c
  apply Finset.sum_congr rfl
  intro x hx
  rfl

/-- Local values of the canonical assignment use the affine-pullback formula. -/
theorem localVertexMap_canonicalAssignment_value
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (q : (Cells hp A.level).Cell)
    (i : Fin (p + 1)) :
    (localVertexMap hp (Cells hp A.level) (canonicalAssignment hp A) q).value i =
      EndpointStackAffinePullbackCore.pullbackVertexValue (p - 1) q.2
        (fun j => A.map (RefinedAffineMap.vertex hp A.level q.1
          (parentIndex p j))) (cylinderIndex hp i) :=
  localVertexMap_assignment_value hp A
    (oneStepAffinePullbackCompatible hp A) q i

/-- Every cell of the canonical one-step assignment avoids the origin. -/
theorem canonicalAssignment_avoidsOrigin
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (q : (Cells hp A.level).Cell) :
    AvoidsOrigin
      (localVertexMap hp (Cells hp A.level) (canonicalAssignment hp A) q) :=
  assignment_avoidsOrigin hp A (oneStepAffinePullbackCompatible hp A) q

end EndpointStackAffinePullbackDescent
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
