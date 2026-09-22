/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.SubdivisionCharts
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ReferenceAffineOrbitCount
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.AffinePrismObstruction
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionOperator

/-!
# Affine maps on iterated subdivisions of the Fox--Neuwirth cycle

The original S6 interface only allowed affine data on the vertices of the unrefined order complex.
This module supplies the correct refined object.  A refined top cell consists of an S4 top-orbit
representative together with a word of barycentric-subdivision permutations.  A continuous global
coordinate map is sampled at the vertices of that refined simplex and extended affinely.
-/

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

namespace FoxNeuwirthOrderComplex
namespace RefinedAffineMap

variable {p : Nat}

/-- One top simplex of the `N`-fold subdivision of the prime-orbit cycle. -/
abbrev TopCell (hp : Nat.Prime p) (N : Nat) :=
  PrimeOrbitCycle.TopOrbit hp × RefinementWord p N

noncomputable instance (hp : Nat.Prime p) (N : Nat) : Fintype (TopCell hp N) := inferInstance
noncomputable instance (hp : Nat.Prime p) (N : Nat) : DecidableEq (TopCell hp N) := inferInstance

/-- Sign of an iterated barycentric-subdivision summand. -/
noncomputable def subdivisionSign (N : Nat) (rho : RefinementWord p N) : ZMod p :=
  ∏ r : Fin N, ((Equiv.Perm.sign (rho r) : ℤ) : ZMod p)

/-- Integer version of the subdivision sign. -/
noncomputable def subdivisionSignInt (N : Nat) (rho : RefinementWord p N) : Int :=
  ∏ r : Fin N, (Equiv.Perm.sign (rho r) : Int)

/-- Continuous coordinate maps on the global realization. -/
abbrev ContinuousCoordinateMap (p : Nat) := C(Realization p, Fin p → Real)

/-- Refined chart attached to a top-orbit representative and a subdivision word. -/
noncomputable def chart
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N) :
    C(Delta (p - 1), Realization p) :=
  (ReferenceAffineOrbitCount.topRepr hp q.1).refinedContinuousMap N q.2

/-- Vertices of a refined top simplex. -/
noncomputable def vertex
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N) (i : Fin (p - 1 + 1)) : Realization p :=
  chart hp N q (stdSimplex.vertex (S := Real) i)

/-- Vertex samples of a continuous coordinate map on one refined simplex. -/
noncomputable def vertexValue
    (hp : Nat.Prime p) (N : Nat)
    (F : ContinuousCoordinateMap p) (q : TopCell hp N)
    (i : Fin (p - 1 + 1)) (j : Fin p) : Real :=
  F (vertex hp N q i) j

/-- Affine interpolation of the sampled full coordinate vector. -/
noncomputable def value
    (hp : Nat.Prime p) (N : Nat)
    (F : ContinuousCoordinateMap p) (q : TopCell hp N)
    (w : StandardSimplex (p - 1)) : Fin p → Real :=
  fun j => ∑ i : Fin (p - 1 + 1), w i * vertexValue hp N F q i j

/-- Difference-coordinate vertex samples. -/
noncomputable def deviationVertexValue
    (hp : Nat.Prime p) (N : Nat)
    (F : ContinuousCoordinateMap p) (q : TopCell hp N)
    (i : Fin (p - 1 + 1)) (r : Fin (p - 1)) : Real :=
  vertexValue hp N F q i (ReferenceAffineOrbitCount.coordinateLabel hp r) -
    vertexValue hp N F q i (ReferenceAffineOrbitCount.lastLabel hp)

/-- Augmented matrix controlling affine regularity on a refined simplex. -/
noncomputable def augmentedMatrix
    (hp : Nat.Prime p) (N : Nat)
    (F : ContinuousCoordinateMap p) (q : TopCell hp N) :
    Matrix (Fin (p - 1 + 1)) (Fin (p - 1 + 1)) Real :=
  fun r i => Fin.lastCases (1 : Real)
    (fun k => deviationVertexValue hp N F q i k) r

/-- Refined-simplex determinant. -/
noncomputable def determinant
    (hp : Nat.Prime p) (N : Nat)
    (F : ContinuousCoordinateMap p) (q : TopCell hp N) : Real :=
  Matrix.det (augmentedMatrix hp N F q)

/-- Relative-interior positive-ray intersection on a refined top simplex. -/
def HasPositiveInteriorZero
    (hp : Nat.Prime p) (N : Nat)
    (F : ContinuousCoordinateMap p) (q : TopCell hp N) : Prop :=
  ∃ w : StandardSimplex (p - 1),
    StandardSimplex.IsInterior w ∧
      (∀ r : Fin (p - 1),
        value hp N F q w (ReferenceAffineOrbitCount.coordinateLabel hp r) =
          value hp N F q w (ReferenceAffineOrbitCount.lastLabel hp)) ∧
      0 < coordinateMean p (value hp N F q w)

noncomputable instance hasPositiveInteriorZeroDecidable
    (hp : Nat.Prime p) (N : Nat)
    (F : ContinuousCoordinateMap p) (q : TopCell hp N) :
    Decidable (HasPositiveInteriorZero hp N F q) :=
  Classical.propDecidable _

/-- Signed local positive-ray index on one refined simplex. -/
noncomputable def localIndex
    (hp : Nat.Prime p) (N : Nat)
    (F : ContinuousCoordinateMap p) (q : TopCell hp N) : ZMod p :=
  if HasPositiveInteriorZero hp N F q then
    AffineVertexMap.determinantIndex (determinant hp N F q)
  else 0

/-- Coefficient of a refined top cell: original orbit-cycle coefficient times subdivision sign. -/
noncomputable def coefficient
    (hp : Nat.Prime p) (N : Nat) (q : TopCell hp N) : ZMod p :=
  (PrimeOrbitCycle.orbitCycle hp).coefficient q.1 * subdivisionSign N q.2

/-- Refined positive orbit count. -/
noncomputable def zeroCount
    (hp : Nat.Prime p) (N : Nat) (F : ContinuousCoordinateMap p) : ZMod p :=
  ∑ q : TopCell hp N, coefficient hp N q * localIndex hp N F q

/-- Straight-line combination of two continuous coordinate maps. -/
noncomputable def segment
    (F G : ContinuousCoordinateMap p) (t : Real) : ContinuousCoordinateMap p where
  toFun x := (1 - t) • F x + t • G x
  continuous_toFun :=
    (F.continuous.const_smul (1 - t)).add (G.continuous.const_smul t)

@[simp] theorem segment_zero (F G : ContinuousCoordinateMap p) : segment F G 0 = F := by
  ext x i
  simp [segment]

@[simp] theorem segment_one (F G : ContinuousCoordinateMap p) : segment F G 1 = G := by
  ext x i
  simp [segment]

/-- A continuous map obtained from an original affine vertex map. -/
noncomputable def ofCoordinateAffineVertexMap
    (F : CoordinateAffineVertexMap p) : ContinuousCoordinateMap p where
  toFun := F.globalValue
  continuous_toFun := F.continuous_globalValue

end RefinedAffineMap
end FoxNeuwirthOrderComplex
end NRR

namespace NRR.FoxNeuwirthOrderComplex.RefinedAffineMap

variable {p : Nat}

/-- Refined augmented matrices depend affinely on straight-line combinations of global maps. -/
theorem augmentedMatrix_segment
    (hp : Nat.Prime p) (N : Nat)
    (F G : ContinuousCoordinateMap p) (t : Real) (q : TopCell hp N) :
    augmentedMatrix hp N (segment F G t) q =
      (1 - t) • augmentedMatrix hp N F q + t • augmentedMatrix hp N G q := by
  ext r i
  refine Fin.lastCases ?_ (fun k => ?_) r
  · simp [augmentedMatrix]
  · simp [augmentedMatrix, deviationVertexValue, vertexValue, segment]
    ring

end NRR.FoxNeuwirthOrderComplex.RefinedAffineMap
