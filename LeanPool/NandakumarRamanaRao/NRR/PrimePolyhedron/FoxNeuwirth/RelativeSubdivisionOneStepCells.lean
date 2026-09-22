/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeSubdivisionCylinderCombinatorics
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarMiddlePrism
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.SubdivisionPrismAffine
/-!
# One-step relative subdivision cells over the Fox--Neuwirth cycle

This module lifts the recursive affine triangulation of `Delta (p - 1) x I` over every level-`N`
refined Fox--Neuwirth top simplex.  The resulting finite cell system has the exact coarse lower
level `N` and barycentrically subdivided upper level `N + 1`.

The pointwise quotient-facet boundary formula is proved in the following module.  Here we construct
the genuine cells and prove all nondegeneracy and prime-orbit separation fields required by
`RelativeAffineCellSystem`.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeSubdivisionOneStepCells

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open RefinedAffineMap
open ExplicitAffineRelativeCollar
open EquivariantPrismGenericityNonzero
open EquivariantPrismVertexParameters
open SubdivisionPrismAffine


variable {p : Nat}

/-- One global cell is a refined Fox--Neuwirth top simplex together with one cell of the recursive
one-step cylinder of its standard-simplex domain. -/
abbrev Cell (hp : Nat.Prime p) (N : Nat) :=
  TopCell hp N × RelativeSubdivisionCylinderCombinatorics.Cell (p - 1)

noncomputable instance (hp : Nat.Prime p) (N : Nat) : Fintype (Cell hp N) := inferInstance
noncomputable instance (hp : Nat.Prime p) (N : Nat) : DecidableEq (Cell hp N) := inferInstance

/-- Reinterpret a `Delta p` coordinate as the domain `Delta ((p - 1) + 1)` of the local cylinder.
Primality gives `0 < p`, hence `(p - 1) + 1 = p`. -/
noncomputable def localWeight
    (hp : Nat.Prime p) (w : Delta p) : Delta ((p - 1) + 1) := by
  rw [Nat.sub_add_cancel hp.pos]
  exact w

/-- Local recursive-cylinder point represented by a global source barycentric coordinate. -/
noncomputable def localPoint
    (hp : Nat.Prime p) (q : RelativeSubdivisionCylinderCombinatorics.Cell (p - 1)) (w : Delta p) :
    Delta (p - 1) × Set.Icc (0 : Real) 1 :=
  RelativeSubdivisionCylinderCombinatorics.chart (p - 1) q (localWeight hp w)

/-- Lift a local cylinder point through one refined Fox--Neuwirth chart. -/
noncomputable def liftPoint
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N)
    (z : Delta (p - 1) × Set.Icc (0 : Real) 1) : CylinderPoint p :=
  CylinderPoint.ofProd (RefinedAffineMap.chart hp N q z.1, z.2)

/-- Affine chart of one global one-step subdivision-cylinder cell. -/
noncomputable def chart
    (hp : Nat.Prime p) (N : Nat) (q : Cell hp N) (w : Delta p) : CylinderPoint p :=
  liftPoint hp N q.1 (localPoint hp q.2 w)

/-- Geometric vertices are defined by restriction of the global affine chart. -/
noncomputable def vertex
    (hp : Nat.Prime p) (N : Nat) (q : Cell hp N) (i : Fin (p + 1)) : CylinderPoint p :=
  chart hp N q (stdSimplex.vertex (S := Real) i)

@[simp] theorem chart_vertex
    (hp : Nat.Prime p) (N : Nat) (q : Cell hp N) (i : Fin (p + 1)) :
    chart hp N q (stdSimplex.vertex (S := Real) i) = vertex hp N q i := rfl

/-- One coordinate of a refined realization chart as a linear functional of its standard-simplex
barycentric coordinate vector. -/
noncomputable def refinedCoordinateLinear
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N) (c : BarredPermutation p) :
    (Fin (p - 1 + 1) → Real) →ₗ[Real] Real :=
  (realizationCoordinateLinear (ReferenceAffineOrbitCount.topRepr hp q.1) c).comp
    (affineCompLinear (p - 1) N
      (fun k => Simplex.refinementIndexPerm (q.2 k)))

/-- Coordinate formula for the refined chart in terms of the explicit linear map above. -/
theorem refinedChart_coordinate_eq_linear
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N)
    (w : Delta (p - 1)) (c : BarredPermutation p) :
    RefinedAffineMap.chart hp N q w c = refinedCoordinateLinear hp N q c w.1 := by
  simp [refinedCoordinateLinear, RefinedAffineMap.chart,
    Simplex.refinedContinuousMap, Simplex.realizationContinuousMap,
    Simplex.realizationPoint,  StandardSimplex.ofDelta,
     realizationCoordinateLinear]
  change (∑ i, if (ReferenceAffineOrbitCount.topRepr hp q.1) i = c then
    (affineCompMap (p - 1) N (fun k => Simplex.refinementIndexPerm (q.2 k)) w) i else 0) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (affineCompMap (p - 1) N
    (fun k => Simplex.refinementIndexPerm (q.2 k)) w) i =
    (affineCompLinear (p - 1) N
      (fun k => Simplex.refinementIndexPerm (q.2 k))) w.val i from
    congrFun (affineCompMap_coe _ _ _ w) i]

/-- A refined realization chart preserves every finite barycentric combination. -/
theorem refinedChart_barycentric
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N)
    (w : Delta p) (v : Fin (p + 1) → Delta (p - 1))
    (x : Delta (p - 1))
    (hx : ∀ c : Fin (p - 1 + 1), x c = ∑ i : Fin (p + 1), w i * v i c)
    (c : BarredPermutation p) :
    RefinedAffineMap.chart hp N q x c =
      ∑ i : Fin (p + 1), w i * RefinedAffineMap.chart hp N q (v i) c := by
  rw [refinedChart_coordinate_eq_linear]
  have hxvec : x.1 = ∑ i : Fin (p + 1), w i • (v i).1 := by
    funext r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hx r
  rw [hxvec, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  simp only [smul_eq_mul]
  rw [← refinedChart_coordinate_eq_linear]

/-- The spatial component of the lifted chart is affine in the source barycentric coordinates. -/
theorem chart_spatial_affine
    (hp : Nat.Prime p) (N : Nat) (q : Cell hp N)
    (w : Delta p) (c : BarredPermutation p) :
    (chart hp N q w).spatial c =
      ∑ i : Fin (p + 1), w i * (vertex hp N q i).spatial c := by
  cases p with
  | zero => exact (hp.ne_zero rfl).elim
  | succ p =>
  apply refinedChart_barycentric hp N q.1 w
    (fun i => (localPoint hp q.2 (stdSimplex.vertex (S := Real) i)).1)
    (localPoint hp q.2 w).1
  intro r
  change (RelativeSubdivisionCylinderCombinatorics.chart
    p q.2 (localWeight hp w)).1 r = _
  rw [RelativeSubdivisionCylinderCombinatorics.chart_spatial_affine]
  simpa [localWeight, localPoint, vertex, chart, liftPoint, CylinderPoint.ofProd,
    RelativeSubdivisionCylinderCombinatorics.chart_vertex]

/-- The time component of the lifted chart is affine in the source barycentric coordinates. -/
theorem chart_time_affine
    (hp : Nat.Prime p) (N : Nat) (q : Cell hp N) (w : Delta p) :
    (chart hp N q w).time.1 =
      ∑ i : Fin (p + 1), w i * (vertex hp N q i).time.1 := by
  cases p with
  | zero => exact (hp.ne_zero rfl).elim
  | succ p =>
  change (RelativeSubdivisionCylinderCombinatorics.chart
    p q.2 (localWeight hp w)).2.1 = _
  rw [RelativeSubdivisionCylinderCombinatorics.chart_time_affine]
  simpa [localWeight, localPoint, vertex, chart, liftPoint, CylinderPoint.ofProd,
    RelativeSubdivisionCylinderCombinatorics.chart_vertex,
    Nat.sub_add_cancel hp.pos]

/-- A prime translate of two points of the same refined spatial simplex can agree only for the
identity symmetry. -/
theorem refinedChart_orbit_separated
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N)
    (x y : Delta (p - 1)) (g : PrimeSymmetry p)
    (h : g • RefinedAffineMap.chart hp N q x = RefinedAffineMap.chart hp N q y) :
    g = 1 := by
  let s : Simplex p (p - 1) := ReferenceAffineOrbitCount.topRepr hp q.1
  let rho : Fin N → Equiv.Perm (Fin (p - 1 + 1)) :=
    fun k => Simplex.refinementIndexPerm (q.2 k)
  let wx : StandardSimplex (p - 1) := StandardSimplex.ofDelta
    (affineCompMap (p - 1) N rho x)
  let wy : StandardSimplex (p - 1) := StandardSimplex.ofDelta
    (affineCompMap (p - 1) N rho y)
  apply realizationPoint_orbit_separated p s wx wy g
  simpa [RefinedAffineMap.chart, Simplex.refinedContinuousMap,
    Simplex.realizationContinuousMap, s, rho, wx, wy] using h

/-- Every lifted one-step cell chart is injective. -/
theorem chart_injective
    (hp : Nat.Prime p) (N : Nat) (q : Cell hp N) :
    Function.Injective (chart hp N q) := by
  intro x y hxy
  have hspatial := congrArg CylinderPoint.spatial hxy
  have hlocalSpatial : (localPoint hp q.2 x).1 = (localPoint hp q.2 y).1 := by
    apply refined_chart_injective hp N q.1
    simpa [chart, liftPoint,
      EquivariantPrismVertexParameters.CylinderPoint.ofProd] using hspatial
  have htime := congrArg (fun z : CylinderPoint p => z.time) hxy
  have hlocal : localPoint hp q.2 x = localPoint hp q.2 y := by
    apply Prod.ext
    · exact hlocalSpatial
    · simpa [chart, liftPoint,
        EquivariantPrismVertexParameters.CylinderPoint.ofProd] using htime
  have hw : localWeight hp x = localWeight hp y :=
    RelativeSubdivisionCylinderCombinatorics.chart_injective_all (p - 1) q.2 hlocal
  simpa [localWeight, Nat.sub_add_cancel hp.pos] using hw

/-- The ordered vertices of every lifted one-step cell are pairwise distinct. -/
theorem vertex_injective
    (hp : Nat.Prime p) (N : Nat) (q : Cell hp N) :
    Function.Injective (vertex hp N q) := by
  intro i j hij
  have hstd :
      (stdSimplex.vertex (S := Real) i : Delta p) =
        stdSimplex.vertex (S := Real) j :=
    chart_injective hp N q hij
  by_contra hne
  have hi := congrArg (fun w : Delta p => w i) hstd
  simpa [stdSimplex.vertex, hne] using hi

/-- No two vertices of a lifted cell lie in the same nontrivial prime orbit. -/
theorem vertex_orbit_injective
    (hp : Nat.Prime p) (N : Nat) (q : Cell hp N)
    (g : PrimeSymmetry p) (i j : Fin (p + 1))
    (h : g • vertex hp N q i = vertex hp N q j) :
    g = 1 ∧ i = j := by
  have hspatial :
      g • (vertex hp N q i).spatial = (vertex hp N q j).spatial :=
    congrArg CylinderPoint.spatial h
  have hg : g = 1 := refinedChart_orbit_separated hp N q.1
    (localPoint hp q.2 (stdSimplex.vertex (S := Real) i)).1
    (localPoint hp q.2 (stdSimplex.vertex (S := Real) j)).1 g (by
      simpa [vertex, chart, liftPoint,
        EquivariantPrismVertexParameters.CylinderPoint.ofProd] using hspatial)
  subst g
  exact ⟨rfl, vertex_injective hp N q (by simpa using h)⟩

/-- Coefficient of a lifted top cell: the refined orbit-cycle coefficient times the recursive
one-step-cylinder orientation coefficient. -/
noncomputable def coefficient
    (hp : Nat.Prime p) (N : Nat) (q : Cell hp N) : ZMod p :=
  RefinedAffineMap.coefficient hp N q.1 *
    RelativeSubdivisionCylinderCombinatorics.Oriented.coefficient (ZMod p) (p - 1) q.2

/-- Explicit finite affine one-step cylinder between refinement levels `N` and `N + 1`. -/
noncomputable def cellSystem
    (hp : Nat.Prime p) (N : Nat) :
    RelativeAffineCellSystem hp N (N + 1) (N + 1) 0 where
  lower_le_common := Nat.le_succ N
  upper_le_common := le_rfl
  Cell := Cell hp N
  cell_nonempty := ⟨(RelativeCollarMiddlePrism.defaultTopCell hp N,
    RelativeSubdivisionCylinderCombinatorics.lowerCell (p - 1))⟩
  instCellFintype := inferInstance
  instCellDecidableEq := inferInstance
  coefficient := coefficient hp N
  vertex := vertex hp N
  chart := chart hp N
  chart_vertex := chart_vertex hp N
  chart_spatial_affine := chart_spatial_affine hp N
  chart_time_affine := chart_time_affine hp N
  chart_injective := chart_injective hp N
  vertex_injective := vertex_injective hp N
  vertex_orbit_injective := vertex_orbit_injective hp N

end RelativeSubdivisionOneStepCells
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
