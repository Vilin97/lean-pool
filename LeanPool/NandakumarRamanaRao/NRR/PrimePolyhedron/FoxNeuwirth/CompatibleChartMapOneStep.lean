/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.CompatibleRefinedChartHomotopy
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarAssignmentCompose
/-!
# One-step collar assignments from compatible affine chart maps

This module removes `RegularApproximation` from the one-step endpoint-stack construction.  The
actual invariant carried through a stack is a compatible chart map which is affine on every chart.
The original endpoint PL interpolation has this property, and further subdivision preserves it.

The assignment on a one-step cylinder evaluates the chart map at the spatial point represented by
that cylinder vertex.  Compatibility makes the value descend to global collar vertices.  Affinity
identifies the local affine interpolation with evaluation of the same chart map at the spatial
image of the cell, so zero-freeness is inherited without a new estimate.
-/

@[expose] public section

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace CompatibleChartMapOneStep

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open AffinePositiveRayBoundary
open CompatibleRefinedChartHomotopy
open ExplicitAffineRelativeCollarAssignmentCompose
open ExplicitAffineRelativeCollar.Polynomials
open AffinePositiveRayBoundary.VertexMap
open EndpointFaceRefinement


variable {p : Nat}

/-- When the prime is written as `m + 1` the reindexing of a barycentric coordinate used by the
local one-step cylinder is definitionally the identity. -/
theorem localWeight_succ {m : Nat} (hp : Nat.Prime (m + 1)) (w : Delta (m + 1)) :
    RelativeSubdivisionOneStepCells.localWeight hp w = w := rfl

/-- A chart map is affine when its value is reconstructed from its values on the standard
vertices.  This orientation is convenient for rewriting local affine collar values. -/
def ChartMap.IsAffine
    {hp : Nat.Prime p} {N : Nat} (K : ChartMap hp N) : Prop :=
  ∀ (q : TopCell hp N) (w : StandardSimplex (p - 1)),
    K.value q w = fun c =>
      ∑ i : Fin (p - 1 + 1), w i *
        K.value q (StandardSimplex.ofDelta (SphereOddDegree.FiniteSimplex.vertex (S := Real) i)) c

/-- The endpoint PL chart map is affine by construction. -/
theorem baseOriginalPLMap_isAffine
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) :
    ChartMap.IsAffine (baseOriginalPLMap hp A) := by
  intro q w
  funext c
  simp [baseOriginalPLMap, RefinedAffineMap.value,
    RefinedAffineMap.vertexValue, StandardSimplex.ofDelta,
    Pi.single_apply, ite_mul, Finset.sum_ite_eq']

/-- Affinity is preserved when a chart map is pulled back through further barycentric
subdivision. -/
theorem ChartMap.IsAffine.refine
    {hp : Nat.Prime p} {N : Nat} {K : ChartMap hp N}
    (hK : ChartMap.IsAffine K) (k : Nat) :
    ChartMap.IsAffine (K.refine k) := by
  intro q w
  funext c
  set r := ancestorTopCell hp N k q with hr
  have hval : ∀ u : StandardSimplex (p - 1),
      K.value r u c =
        ∑ j : Fin (p - 1 + 1), (u : Fin (p - 1 + 1) → Real) j *
          K.value r (StandardSimplex.ofDelta
            (SphereOddDegree.FiniteSimplex.vertex (S := Real) j)) c :=
    fun u => congrFun (hK r u) c
  have hL : (K.refine k).value q w c =
      ∑ j : Fin (p - 1 + 1),
        (ancestorWeight N k q w : Fin (p - 1 + 1) → Real) j *
          K.value r (StandardSimplex.ofDelta
            (SphereOddDegree.FiniteSimplex.vertex (S := Real) j)) c := by
    change K.value r (ancestorWeight N k q w) c = _
    rw [hval]
  have hR : ∀ x : Fin (p - 1 + 1),
      (K.refine k).value q
          (StandardSimplex.ofDelta (SphereOddDegree.FiniteSimplex.vertex (S := Real) x)) c =
        ∑ j : Fin (p - 1 + 1),
          (ancestorWeight N k q (StandardSimplex.ofDelta
              (SphereOddDegree.FiniteSimplex.vertex (S := Real) x)) : Fin (p - 1 + 1) → Real) j *
            K.value r (StandardSimplex.ofDelta
              (SphereOddDegree.FiniteSimplex.vertex (S := Real) j)) c := by
    intro x
    change K.value r (ancestorWeight N k q _) c = _
    rw [hval]
  have hcoord : ∀ j : Fin (p - 1 + 1),
      (ancestorWeight N k q w : Fin (p - 1 + 1) → Real) j =
        ∑ x : Fin (p - 1 + 1), (w : Fin (p - 1 + 1) → Real) x *
          (ancestorWeight N k q (StandardSimplex.ofDelta
            (SphereOddDegree.FiniteSimplex.vertex (S := Real) x)) : Fin (p - 1 + 1) → Real) j := by
    intro j
    exact affineCompMap_coordinate_eq_sum_vertices
      (p - 1) k (fun j => Simplex.refinementIndexPerm (ancestorTail N k q j))
      (StandardSimplex.toDelta w) j
  change (K.refine k).value q w c = _
  rw [hL]
  simp_rw [hcoord, hR, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => by ring

/-- Every representation of the original endpoint PL map at a later subdivision level is affine. -/
theorem originalPLMap_isAffine
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) (k : Nat) :
    ChartMap.IsAffine (originalPLMap hp A k) :=
  (baseOriginalPLMap_isAffine hp A).refine k

/-- The one-step cell system at the level of a compatible chart map. -/
noncomputable abbrev Cells (hp : Nat.Prime p) (N : Nat) :=
  RelativeSubdivisionOneStepCells.cellSystem hp N

/-- Spatial coordinate, in the current top-simplex chart, represented by one local cylinder
vertex. -/
noncomputable def localSpatialWeight
    (hp : Nat.Prime p) (N : Nat)
    (s : (Cells hp N).VertexSlot) : StandardSimplex (p - 1) :=
  StandardSimplex.ofDelta
    (RelativeSubdivisionOneStepCells.localPoint hp s.1.2 (SphereOddDegree.FiniteSimplex.vertex
      (S := Real) s.2)).1

/-- Local value supplied by a compatible chart map. -/
noncomputable def localVector
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N)
    (s : (Cells hp N).VertexSlot) : Fin p → Real :=
  K.value s.1.1 (localSpatialWeight hp N s)

/-- Prime-decorated local value. -/
noncomputable def decoratedVector
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N)
    (s : CoverVertexSlot hp (Cells hp N)) : Fin p → Real :=
  s.1 • localVector hp K s.2

/-- Equality of represented collar vertices implies equality of decorated chart-map values. -/
theorem decoratedVector_eq_of_coverPoint_eq
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N)
    {a b : CoverVertexSlot hp (Cells hp N)}
    (hab : coverPoint hp (Cells hp N) a = coverPoint hp (Cells hp N) b) :
    decoratedVector hp K a = decoratedVector hp K b := by
  have hspatial := congrArg EquivariantPrismVertexParameters.CylinderPoint.spatial hab
  apply K.decorated_compatible a.1 b.1 a.2.1.1 b.2.1.1
      (localSpatialWeight hp N a.2) (localSpatialWeight hp N b.2)
  simpa [coverPoint, RelativeAffineCellSystem.slotPoint, Cells,
    RelativeSubdivisionOneStepCells.cellSystem,
    localSpatialWeight, RelativeSubdivisionOneStepCells.vertex,
      RelativeSubdivisionOneStepCells.chart, RelativeSubdivisionOneStepCells.liftPoint,
    EquivariantPrismVertexParameters.CylinderPoint.ofProd] using hspatial

/-- Global vector obtained by quotient descent. -/
noncomputable def globalVector
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N) :
    GlobalVertex hp (Cells hp N) → Fin p → Real :=
  Quotient.lift (decoratedVector hp K) (by
    intro a b hab
    exact decoratedVector_eq_of_coverPoint_eq hp K hab)

@[simp] theorem globalVector_mk
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N)
    (s : CoverVertexSlot hp (Cells hp N)) :
    globalVector hp K (Quotient.mk _ s) = decoratedVector hp K s := rfl

/-- The descended vector is prime-equivariant. -/
theorem globalVector_smul
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N)
    (g : PrimeSymmetry p) (x : GlobalVertex hp (Cells hp N)) :
    globalVector hp K (g • x) = g • globalVector hp K x := by
  refine Quotient.inductionOn x ?_
  intro s
  rfl

/-- Canonical one-step assignment associated with a compatible chart map. -/
noncomputable def assignment
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N) :
    Assignment hp (Cells hp N) :=
  assignmentOfEquivariantVector (Cells hp N) (globalVector hp K)
    (globalVector_smul hp K)

@[simp] theorem vectorValue_assignment_sample
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N)
    (s : (Cells hp N).VertexSlot) :
    vectorValue hp (Cells hp N) (assignment hp K)
        (sampleVertex hp (Cells hp N) s) =
      localVector hp K s := by
  rfl

/-- The local affine value of a one-step assignment is evaluation of the same affine chart map at
the cell's represented spatial point. -/
theorem affineValue_localVertexMap_assignment
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N)
    (hK : ChartMap.IsAffine K)
    (q : (Cells hp N).Cell) (w : StandardSimplex p) :
    affineValue (localVertexMap hp (Cells hp N) (assignment hp K) q) w =
      K.value q.1
        (StandardSimplex.ofDelta
          (RelativeSubdivisionOneStepCells.localPoint hp q.2 (StandardSimplex.toDelta w)).1) := by
  funext c
  have hval : ∀ u : StandardSimplex (p - 1),
      K.value q.1 u c =
        ∑ j : Fin (p - 1 + 1), (u : Fin (p - 1 + 1) → Real) j *
          K.value q.1 (StandardSimplex.ofDelta
            (SphereOddDegree.FiniteSimplex.vertex (S := Real) j)) c :=
    fun u => congrFun (hK q.1 u) c
  have hlhs : affineValue (localVertexMap hp (Cells hp N) (assignment hp K) q) w c
      = ∑ i : Fin (p + 1), (w : Fin (p + 1) → Real) i *
          K.value q.1 (localSpatialWeight hp N (q, i)) c := rfl
  have hL : (∑ i : Fin (p + 1), (w : Fin (p + 1) → Real) i *
        K.value q.1 (localSpatialWeight hp N (q, i)) c)
      = ∑ i : Fin (p + 1), ∑ j : Fin (p - 1 + 1),
          ((w : Fin (p + 1) → Real) i *
            (localSpatialWeight hp N (q, i) : Fin (p - 1 + 1) → Real) j) *
            K.value q.1 (StandardSimplex.ofDelta
              (SphereOddDegree.FiniteSimplex.vertex (S := Real) j)) c := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hval, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hlhs, hL, Finset.sum_comm]
  conv_rhs => rw [hval]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  simp only [localSpatialWeight, RelativeSubdivisionOneStepCells.localPoint,
    localWeight_succ,
    RelativeSubdivisionCylinderCombinatorics.chart_vertex,
    StandardSimplex.ofDelta]
  exact (RelativeSubdivisionCylinderCombinatorics.chart_spatial_affine m q.2
    (StandardSimplex.toDelta w) j).symm

/-- Every one-step cell avoids the origin. -/
theorem assignment_avoidsOrigin
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N)
    (hK : ChartMap.IsAffine K)
    (q : (Cells hp N).Cell) :
    AvoidsOrigin (localVertexMap hp (Cells hp N) (assignment hp K) q) := by
  intro w
  rw [affineValue_localVertexMap_assignment hp K hK q w]
  exact K.zeroFree _ _

/-- Lower-boundary samples are the current chart-map values at native vertices. -/
theorem lower_sample
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N)
    (q : TopCell hp N) (i : Fin p) :
    vectorValue hp (Cells hp N) (assignment hp K)
        (sampleVertex hp (Cells hp N)
          ((q, RelativeSubdivisionCylinderCombinatorics.lowerCell (p - 1)), i.succ)) =
      K.value q (StandardSimplex.ofDelta (SphereOddDegree.FiniteSimplex.vertex (S := Real)
        (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  rw [vectorValue_assignment_sample]
  simp [localVector, localSpatialWeight,
    RelativeSubdivisionOneStepCells.localPoint,
    RelativeSubdivisionOneStepCells.localWeight,
    RelativeSubdivisionCylinderCombinatorics.chart_vertex,
    RelativeSubdivisionCylinderCombinatorics.vertex_succ_lower,
    RelativeSubdivisionCylinderCombinatorics.lowerBoundaryVertex,
    StandardSimplex.ofDelta]

/-- Upper-boundary samples are exactly the native vertex values of the refined chart map. -/
theorem upper_sample_refine
    (hp : Nat.Prime p) {N : Nat} (K : ChartMap hp N)
    (q : TopCell hp N) (pi : Equiv.Perm (Fin p)) (i : Fin p) :
    vectorValue hp (Cells hp N) (assignment hp K)
        (sampleVertex hp (Cells hp N)
          ((q, RelativeSubdivisionCylinderCombinatorics.upperCell (p - 1)
            (by simpa [Nat.sub_add_cancel hp.pos] using pi)), i.succ)) =
      (K.refine 1).value (q.1, Fin.snoc q.2 pi)
        (StandardSimplex.ofDelta (SphereOddDegree.FiniteSimplex.vertex (S := Real)
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  rw [vectorValue_assignment_sample]
  simp [localVector, localSpatialWeight,
    RelativeSubdivisionOneStepCells.localPoint,
    RelativeSubdivisionOneStepCells.localWeight, ChartMap.refine,
    ancestorTopCell, ancestorTail, ancestorWeight, splitRefinementWord,
    RelativeSubdivisionCylinderCombinatorics.chart_vertex,
    RelativeSubdivisionCylinderCombinatorics.vertex_succ_upper,
    RelativeSubdivisionCylinderCombinatorics.upperBoundaryVertex,
    StandardSimplex.ofDelta, Simplex.refinementIndexPerm,
    affineCompMap_succ, affineSubdivContinuousMap]
  congr 1
  · have hword :
        (fun i : Fin N =>
          Fin.snoc (α := fun _ => Equiv.Perm (Fin (m + 1))) q.2 pi (Fin.castAdd 1 i)) = q.2 := by
      funext i
      exact Fin.snoc_castSucc (α := fun _ => Equiv.Perm (Fin (m + 1))) pi q.2 i
    rw [hword]
  · have hlast :
        Fin.snoc (α := fun _ => Equiv.Perm (Fin (m + 1))) q.2 pi (Fin.natAdd N 0) = pi :=
      Fin.snoc_last (α := fun _ => Equiv.Perm (Fin (m + 1))) pi q.2
    apply Subtype.ext
    dsimp only
    rw [hlast]
    exact congrArg Subtype.val (affineSubdivMap_vertex m pi i).symm

end CompatibleChartMapOneStep
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
