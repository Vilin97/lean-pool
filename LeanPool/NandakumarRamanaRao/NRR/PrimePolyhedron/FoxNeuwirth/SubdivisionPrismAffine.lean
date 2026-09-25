/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.SubdivisionPrismCharts
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.IteratedSubdivisionSmallSimplex
/-!
# Affine-coordinate formulas for refined staircase prisms

The refined staircase chart is assembled from linear barycentric-subdivision maps, the linear
staircase spatial/time maps, and the linear realization chart of one strict Fox--Neuwirth simplex.
This module packages that observation as explicit linear maps and proves that every chart coordinate
is the barycentric interpolation of its values at the `p + 1` vertices.

These formulas are used by the concrete common-level middle-prism constructor for the explicit
relative collar.
-/

@[expose] public section

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open SphereOddDegree.BarycentricSubdivisionDiameter
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace SubdivisionPrismAffine

open SubdivisionPrismCharts

variable {p : Nat}

/-- The staircase spatial-coordinate map, extended linearly to all coordinate vectors. -/
noncomputable def staircaseSpatialLinear
    (p : Nat) (k : Fin p) :
    (Fin (p + 1) → Real) →ₗ[Real] (Fin p → Real) where
  toFun u i :=
    ∑ j : Fin (p + 1), if staircaseSpatial p k j = i then u j else 0
  map_add' := by
    intro u v
    funext i
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  map_smul' := by
    intro a u
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring

/-- The staircase interval-coordinate map, extended linearly to all coordinate vectors. -/
noncomputable def staircaseTimeLinear
    (k : Fin p) : (Fin (p + 1) → Real) →ₗ[Real] Real where
  toFun u :=
    ∑ j : Fin (p + 1), if staircaseTime k j = 1 then u j else 0
  map_add' := by
    intro u v
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  map_smul' := by
    intro a u
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring

/-- Reindex maximal-simplex coordinate vectors along `p - 1 + 1 = p`. -/
noncomputable def maximalCoordinateReindexLinear
    (hp : Nat.Prime p) :
    (Fin p → Real) →ₗ[Real] (Fin (p - 1 + 1) → Real) where
  toFun u i := u (Fin.cast (Nat.sub_add_cancel hp.pos) i)
  map_add' := by
    intro u v
    rfl
  map_smul' := by
    intro a u
    rfl

/-- One coordinate of the realization chart of a strict simplex, as a linear functional of its
barycentric coordinates. -/
noncomputable def realizationCoordinateLinear
    (s : Simplex p (p - 1)) (c : BarredPermutation p) :
    (Fin (p - 1 + 1) → Real) →ₗ[Real] Real where
  toFun u := ∑ i : Fin (p - 1 + 1), if s i = c then u i else 0
  map_add' := by
    intro u v
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  map_smul' := by
    intro a u
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring

/-- A linear map on barycentric coordinate vectors is determined by its values on the standard
vertices. -/
theorem linearMap_apply_eq_sum_vertices
    {n : Nat} {E : Type} [AddCommMonoid E] [Module Real E]
    (f : (Fin (n + 1) → Real) →ₗ[Real] E) (w : Delta n) :
    f w.1 = ∑ i : Fin (n + 1), w i • f (stdVerts n i) := by
  classical
  have hw : w.1 = ∑ i : Fin (n + 1), w i • stdVerts n i := by
    funext j
    change w j = (∑ i : Fin (n + 1), w i • stdVerts n i) j
    simp [stdVerts, Pi.single_apply, Finset.sum_ite_eq]
  rw [hw, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]

/-- Linear functional computing one spatial realization coordinate of a fully refined prism chart.
-/
noncomputable def prismSpatialCoordinateLinear
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L)
    (c : BarredPermutation p) :
    (Fin (p + 1) → Real) →ₗ[Real] Real :=
  (realizationCoordinateLinear (ReferenceAffineOrbitCount.topRepr hp q.1.1.1) c).comp
    ((affineCompLinear (p - 1) N
      (fun k => Simplex.refinementIndexPerm (q.1.1.2 k))).comp
      ((maximalCoordinateReindexLinear hp).comp
        ((staircaseSpatialLinear p q.1.2).comp
          (affineCompLinear p L q.2))))

/-- Linear functional computing the interval coordinate of a fully refined prism chart. -/
noncomputable def prismTimeCoordinateLinear
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L) :
    (Fin (p + 1) → Real) →ₗ[Real] Real :=
  (staircaseTimeLinear q.1.2).comp (affineCompLinear p L q.2)

/-- The spatial coordinate of the refined prism chart is the corresponding explicit linear
functional of the source barycentric coordinate vector. -/
theorem chart_spatial_eq_linear
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L)
    (w : Delta p) (c : BarredPermutation p) :
    (SubdivisionPrismCharts.chart hp N L q w).1 c =
      prismSpatialCoordinateLinear hp N L q c w.1 := by
  have hspatial :
      spatialWeight hp q.1.2
          ⟨affineCompLinear p L q.2 w.1, by
            rw [← affineCompMap_coe]
            exact (affineCompMap p L q.2 w).property⟩ =
        maximalCoordinateReindexLinear hp
          (staircaseSpatialLinear p q.1.2
            (affineCompLinear p L q.2 w.1)) := by
    funext i
    simp [spatialWeight, maximalCoordinateReindexLinear,
      staircaseSpatialLinear, Fin.ext_iff]
  simp only [chart, RefinedAffineMap.chart, Simplex.refinedContinuousMap,
    Simplex.realizationContinuousMap, Simplex.realizationPoint, StandardSimplex.ofDelta,
    StandardSimplex.toDelta, staircasePoint, spatialPoint, affineCompMap_coe,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, hspatial, maximalCoordinateReindexLinear,
    Nat.succ_eq_add_one, Nat.reduceAdd, staircaseSpatialLinear, Fin.ext_iff, LinearMap.coe_mk,
    AddHom.coe_mk, Fin.val_cast, prismSpatialCoordinateLinear, realizationCoordinateLinear,
    LinearMap.coe_comp, Function.comp_apply]
  change (ReferenceAffineOrbitCount.topRepr hp q.1.1.1).chartWeight
      (StandardSimplex.ofDelta (affineCompMap (p - 1) N
        (fun k => Simplex.refinementIndexPerm (q.1.1.2 k)) _)) c = _
  unfold Simplex.chartWeight StandardSimplex.ofDelta
  rw [affineCompMap_coe]

/-- The interval coordinate of the refined prism chart is the corresponding explicit linear
functional of the source barycentric coordinate vector. -/
theorem chart_time_eq_linear
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L)
    (w : Delta p) :
    (SubdivisionPrismCharts.chart hp N L q w).2.1 =
      prismTimeCoordinateLinear hp N L q w.1 := by
  simp [SubdivisionPrismCharts.chart, prismTimeCoordinateLinear,
    staircaseTimeLinear, staircasePoint, intervalPoint, intervalWeight,
    StandardSimplex.ofDelta, affineCompMap_coe]

/-- Every spatial coordinate of the refined prism chart is the barycentric interpolation of its
vertex coordinates. -/
theorem chart_spatial_affine
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L)
    (w : Delta p) (c : BarredPermutation p) :
    (SubdivisionPrismCharts.chart hp N L q w).1 c =
      ∑ i : Fin (p + 1), w i * (SubdivisionPrismCharts.vertex hp N L q i).1 c := by
  rw [chart_spatial_eq_linear]
  rw [linearMap_apply_eq_sum_vertices]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_eq_mul]
  change w i *
      prismSpatialCoordinateLinear hp N L q c
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) i).1 =
    w i * (SubdivisionPrismCharts.vertex hp N L q i).1 c
  rw [← chart_spatial_eq_linear hp N L q (SphereOddDegree.FiniteSimplex.vertex (S := Real) i) c]
  rfl

/-- The interval coordinate of the refined prism chart is the barycentric interpolation of its
vertex times. -/
theorem chart_time_affine
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L)
    (w : Delta p) :
    (SubdivisionPrismCharts.chart hp N L q w).2.1 =
      ∑ i : Fin (p + 1), w i * (SubdivisionPrismCharts.vertex hp N L q i).2.1 := by
  rw [chart_time_eq_linear]
  rw [linearMap_apply_eq_sum_vertices]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_eq_mul]
  change w i *
      prismTimeCoordinateLinear hp N L q
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) i).1 =
    w i * (SubdivisionPrismCharts.vertex hp N L q i).2.1
  rw [← chart_time_eq_linear hp N L q (SphereOddDegree.FiniteSimplex.vertex (S := Real) i)]
  rfl

end SubdivisionPrismAffine
end FoxNeuwirthOrderComplex
end NRR
