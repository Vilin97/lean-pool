/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RefinedAffineMap
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.AffineSubdivisionDeterminant

/-!
# Regularity of the S5 reference map on every barycentric refinement

The S5 reference coordinate map is affine on each original maximal order-complex simplex.  On a
refined simplex its augmented difference matrix is the original augmented matrix multiplied by the
barycentric vertex matrix of the subdivision chart.  Both factors have nonzero determinant.
-/

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

namespace FoxNeuwirthOrderComplex
namespace RefinedAffineMap

variable {p : Nat}

/-- Augmented matrix of an original affine vertex map on one maximal simplex. -/
noncomputable def originalAugmentedMatrix
    (hp : Nat.Prime p) (F : CoordinateAffineVertexMap p)
    (s : Simplex p (p - 1)) : Matrix (Fin (p - 1 + 1)) (Fin (p - 1 + 1)) Real :=
  (F.deviation hp).augmentedMatrix s


/-- Global affine interpolation on the realization chart of a simplex is the barycentric
interpolation of the vertex data on that simplex. -/
theorem CoordinateAffineVertexMap.globalValue_realizationPoint
    (F : CoordinateAffineVertexMap p) (s : Simplex p (p - 1))
    (w : StandardSimplex (p - 1)) :
    F.globalValue (s.realizationPoint w) = F.value s w := by
  classical
  funext a
  simp only [CoordinateAffineVertexMap.globalValue,
    CoordinateAffineVertexMap.value, Simplex.realizationPoint_apply,
    Simplex.chartWeight]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (s i)]
  · simp
  · intro c hc hci
    simp [Ne.symm hci]
  · simp

/-- Sampling an original affine map on a refined simplex multiplies the original augmented matrix
by the subdivision vertex matrix. -/
theorem augmentedMatrix_ofCoordinateAffineVertexMap_eq_mul
    (hp : Nat.Prime p) (N : Nat)
    (F : CoordinateAffineVertexMap p) (q : TopCell hp N) :
    augmentedMatrix hp N (ofCoordinateAffineVertexMap F) q =
      originalAugmentedMatrix hp F (ReferenceAffineOrbitCount.topRepr hp q.1) *
        AffineSubdivisionDeterminant.iterVertexMatrix (p - 1) N
          (fun k => Simplex.refinementIndexPerm (q.2 k)) := by
  classical
  ext r i
  refine Fin.lastCases ?_ (fun k => ?_) r
  · simp only [augmentedMatrix, originalAugmentedMatrix, Matrix.mul_apply,
      AffineSubdivisionDeterminant.iterVertexMatrix,
      AffineVertexMap.augmentedMatrix, Fin.lastCases_last, one_mul]
    exact (SphereOddDegree.FiniteSimplex.sum_eq_one
      (affineCompMap (p - 1) N
        (fun k => Simplex.refinementIndexPerm (q.2 k))
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) i))).symm
  · let s := ReferenceAffineOrbitCount.topRepr hp q.1
    let rho : Fin N → Equiv.Perm (Fin (p - 1 + 1)) :=
      fun t => Simplex.refinementIndexPerm (q.2 t)
    have hglobal (j : Fin (p - 1 + 1)) :
        F.globalValue
            (s.realizationPoint
              (StandardSimplex.ofDelta
                (affineCompMap (p - 1) N rho
                  (SphereOddDegree.FiniteSimplex.vertex (S := Real) j)))) =
          F.value s
            (StandardSimplex.ofDelta
              (affineCompMap (p - 1) N rho
                (SphereOddDegree.FiniteSimplex.vertex (S := Real) j))) :=
      CoordinateAffineVertexMap.globalValue_realizationPoint F s _
    simp only [augmentedMatrix, deviationVertexValue, vertexValue, vertex,
      chart, ofCoordinateAffineVertexMap, originalAugmentedMatrix,
      AffineVertexMap.augmentedMatrix, CoordinateAffineVertexMap.deviation,
      Matrix.mul_apply, AffineSubdivisionDeterminant.iterVertexMatrix,
      Fin.lastCases_castSucc]
    change
      F.globalValue
          (s.realizationPoint
            (StandardSimplex.ofDelta
              (affineCompMap (p - 1) N rho
                (SphereOddDegree.FiniteSimplex.vertex (S := Real) i))))
          (ReferenceAffineOrbitCount.coordinateLabel hp k) -
        F.globalValue
          (s.realizationPoint
            (StandardSimplex.ofDelta
              (affineCompMap (p - 1) N rho
                (SphereOddDegree.FiniteSimplex.vertex (S := Real) i))))
          (ReferenceAffineOrbitCount.lastLabel hp) = _
    rw [hglobal i]
    simp only [CoordinateAffineVertexMap.value, StandardSimplex.ofDelta]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    congr 1 <;>
    · apply Finset.sum_congr rfl
      intro j hj
      exact mul_comm _ _

/-- Determinant factorization for an original affine map on a refined simplex. -/
theorem determinant_ofCoordinateAffineVertexMap
    (hp : Nat.Prime p) (N : Nat)
    (F : CoordinateAffineVertexMap p) (q : TopCell hp N) :
    determinant hp N (ofCoordinateAffineVertexMap F) q =
      (F.deviation hp).determinant (ReferenceAffineOrbitCount.topRepr hp q.1) *
        Matrix.det (AffineSubdivisionDeterminant.iterVertexMatrix (p - 1) N
          (fun k => Simplex.refinementIndexPerm (q.2 k))) := by
  unfold determinant
  rw [augmentedMatrix_ofCoordinateAffineVertexMap_eq_mul, Matrix.det_mul]
  rfl

/-- Any original regular affine deviation map remains regular on every iterated subdivision. -/
theorem regular_on_refinement_of_regular
    (hp : Nat.Prime p) (N : Nat)
    (F : CoordinateAffineVertexMap p)
    (hF : (F.deviation hp).IsRegular) :
    ∀ q : TopCell hp N,
      determinant hp N (ofCoordinateAffineVertexMap F) q ≠ 0 := by
  intro q
  rw [determinant_ofCoordinateAffineVertexMap]
  exact mul_ne_zero
    (hF (ReferenceAffineOrbitCount.topRepr hp q.1))
    (AffineSubdivisionDeterminant.det_iterVertexMatrix_ne_zero (p - 1) N
      (fun k => Simplex.refinementIndexPerm (q.2 k)))


end RefinedAffineMap
end FoxNeuwirthOrderComplex
end NRR
