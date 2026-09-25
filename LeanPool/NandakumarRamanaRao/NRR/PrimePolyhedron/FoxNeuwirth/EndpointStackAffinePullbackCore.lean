/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeSubdivisionOneStepEndpoints
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.SubdivisionZeroFreeApproximation
/-!
# Affine pullback values on one endpoint-subdivision cylinder

The earlier last-vertex convention is not stable under iteration: its upper values generally do
not equal the lower values selected by the next one-step layer.  The composable convention is the
affine pullback of the *same parent PL map*.

For a parent simplex with vertex data `V`, every local cylinder vertex has a spatial barycentric
coordinate in that parent simplex.  We assign to it the affine value of `V` at that coordinate.
Affine interpolation over a cylinder cell then recovers the parent affine map at the cell's spatial
point exactly.  Hence origin avoidance is inherited verbatim, and upper-boundary values are the
ordinary barycentric-subdivision vertex values needed by the next layer.

This file proves the complete simplex-local statement.  Global iteration only needs the standard
face-gluing theorem saying that the parent PL values agree on shared refined faces.
-/

@[expose] public section

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace EndpointStackAffinePullbackCore

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open RefinedAffineMap


variable {p d n : Nat}

/-- The identity correspondence between parent vertex indices. -/
def parentIndex (p : Nat) : Fin (p - 1 + 1) → Fin (p - 1 + 1) :=
  id

/-- Cast cylinder vertex indices to the dimension convention for the endpoint stack. -/
def cylinderIndex (hp : Nat.Prime p) : Fin (p + 1) → Fin (p - 1 + 2) :=
  Fin.cast (by have := hp.pos; omega)

/-- Evaluate parent-simplex affine vertex data at the spatial point of one local cylinder vertex. -/
noncomputable def pullbackVertexValue
    (d : Nat) (q : RelativeSubdivisionCylinderCombinatorics.Cell d)
    (V : Fin (d + 1) → Fin n → Real)
    (i : Fin (d + 2)) : Fin n → Real :=
  fun c => ∑ j : Fin (d + 1), (RelativeSubdivisionCylinderCombinatorics.vertex d q i).1 j * V j c

/-- Interpolating the pulled-back values over a cylinder cell is exactly evaluation of the parent
affine map at the spatial barycentric image of the cell point. -/
theorem affine_pullbackVertexValue_eq_spatial
    (d : Nat) (q : RelativeSubdivisionCylinderCombinatorics.Cell d)
    (V : Fin (d + 1) → Fin n → Real)
    (w : Delta (d + 1)) :
    (fun c => ∑ i : Fin (d + 2), w i * pullbackVertexValue d q V i c) =
      fun c => ∑ j : Fin (d + 1), RelativeSubdivisionCylinderCombinatorics.spatialPoint d q w j
        * V j c := by
  funext c
  simp only [pullbackVertexValue,
    RelativeSubdivisionCylinderCombinatorics.spatialPoint, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  change (∑ i, w i *
      ((RelativeSubdivisionCylinderCombinatorics.vertex d q i).1 j * V j c)) =
    (∑ i, w i * (RelativeSubdivisionCylinderCombinatorics.vertex d q i).1 j) * V j c
  simpa [mul_assoc] using
    (Finset.sum_mul Finset.univ
      (fun i => w i * (RelativeSubdivisionCylinderCombinatorics.vertex d q i).1 j)
      (V j c)).symm

/-- The affine-pullback convention fixes every coarse lower-boundary vertex literally. -/
@[simp] theorem pullbackVertexValue_lower
    (d : Nat) (V : Fin (d + 1) → Fin n → Real) (i : Fin (d + 1)) :
    pullbackVertexValue d (RelativeSubdivisionCylinderCombinatorics.lowerCell d) V i.succ = V i
      := by
  funext c
  simp [pullbackVertexValue,
    RelativeSubdivisionCylinderCombinatorics.lowerBoundaryVertex,
    SphereOddDegree.FiniteSimplex.vertex, Pi.single_apply]

/-- On an upper barycentric facet, affine pullback gives the parent affine value at the
corresponding prefix barycenter. -/
@[simp] theorem pullbackVertexValue_upper
    (d : Nat) (pi : Equiv.Perm (Fin (d + 1)))
    (V : Fin (d + 1) → Fin n → Real) (i : Fin (d + 1)) :
    pullbackVertexValue d (RelativeSubdivisionCylinderCombinatorics.upperCell d pi) V i.succ =
      fun c => ∑ j : Fin (d + 1), prefixBarycenter d pi i j * V j c := by
  funext c
  simp [pullbackVertexValue,
    RelativeSubdivisionCylinderCombinatorics.upperBoundaryVertex]

/-- Endpoint specialization: the local affine interpolation is exactly the stored endpoint PL
value at the spatial point of the one-step cylinder cell. -/
theorem affine_pullbackEndpointValue_eq_value
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (q : TopCell hp A.level)
    (r : RelativeSubdivisionCylinderCombinatorics.Cell (p - 1))
    (w : Delta p) :
    (fun c => ∑ i : Fin (p + 1), w i *
        pullbackVertexValue (p - 1) r
          (fun j => A.map (RefinedAffineMap.vertex hp A.level q
            (parentIndex p j)))
          (cylinderIndex (p := p) hp i) c) =
      RefinedAffineMap.value hp A.level A.map q
        (StandardSimplex.ofDelta (RelativeSubdivisionCylinderCombinatorics.spatialPoint (p - 1) r
          (RelativeSubdivisionOneStepCells.localWeight hp w))) := by
  have h := affine_pullbackVertexValue_eq_spatial
      (d := p - 1) (q := r)
      (V := fun j => A.map (RefinedAffineMap.vertex hp A.level q j))
      (w := RelativeSubdivisionOneStepCells.localWeight hp w)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp.pos)
  convert h using 1
  · funext c
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
  · funext c
    unfold RefinedAffineMap.value RefinedAffineMap.vertexValue
    apply Finset.sum_congr rfl
    intro i hi
    congr 1

/-- Every affine-pullback one-step endpoint cell avoids the origin because it is an exact
restriction of the already zero-free endpoint PL map. -/
theorem affine_pullbackEndpointValue_ne_zero
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (q : TopCell hp A.level)
    (r : RelativeSubdivisionCylinderCombinatorics.Cell (p - 1))
    (w : Delta p) :
    (fun c => ∑ i : Fin (p + 1), w i *
        pullbackVertexValue (p - 1) r
          (fun j => A.map (RefinedAffineMap.vertex hp A.level q
            (parentIndex p j)))
          (cylinderIndex (p := p) hp i) c) ≠ 0 := by
  rw [affine_pullbackEndpointValue_eq_value hp A q r w]
  have h := A.zeroFreeStraightLine q
    (StandardSimplex.ofDelta (RelativeSubdivisionCylinderCombinatorics.spatialPoint (p - 1) r
      (RelativeSubdivisionOneStepCells.localWeight hp w)))
    (⟨1, by constructor <;> norm_num⟩ : Set.Icc (0 : Real) 1)
  simpa using h

/-- Upper pullback values are exactly the parent affine values at the vertices of the appended
barycentric-subdivision simplex. -/
theorem pullbackEndpointValue_upper_eq_refinedVertexValue
    (hp : Nat.Prime p)
    {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F)
    (q : TopCell hp A.level)
    (pi : Equiv.Perm (Fin p))
    (i : Fin p) :
    pullbackVertexValue (p - 1)
        (RelativeSubdivisionCylinderCombinatorics.upperCell (p - 1) (by
          simpa [Nat.sub_add_cancel hp.pos] using pi))
        (fun j => A.map (RefinedAffineMap.vertex hp A.level q
          (parentIndex p j)))
        (cylinderIndex (p := p) hp i.succ) =
      RefinedAffineMap.value hp A.level A.map q
        (StandardSimplex.ofDelta (prefixBarycenter (p - 1)
          (by simpa [Nat.sub_add_cancel hp.pos] using pi)
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp.pos)
  change pullbackVertexValue k
      (RelativeSubdivisionCylinderCombinatorics.upperCell k pi)
      (fun j => A.map (RefinedAffineMap.vertex hp A.level q j)) i.succ = _
  rw [pullbackVertexValue_upper]
  funext c
  change (∑ x, prefixBarycenter k pi i x *
      A.map (RefinedAffineMap.vertex hp A.level q x) c) = _
  rfl

end EndpointStackAffinePullbackCore
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
