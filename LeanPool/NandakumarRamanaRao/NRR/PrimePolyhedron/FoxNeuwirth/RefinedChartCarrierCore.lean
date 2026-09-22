/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.AffineBarycentricSubdivisionCarrier
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.MaximalFlagClassification
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.SubdivisionCharts
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RefinedAffineMap
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.PrimeOrbitCycle
/-!
# Carrier coordinates for maximal Fox--Neuwirth charts

Every maximal order-complex simplex is ranked by dual dimension.  Consequently, if two maximal
simplices share a barred-permutation vertex, that vertex occurs at the same index in both flags.
This elementary rank rigidity makes overlap in the global barycentric realization coordinatewise:
at every rank, either the two maximal flags have the same vertex and the two barycentric
coordinates agree, or the coordinate is zero on the first chart.

These statements isolate the Fox--Neuwirth-specific part of refined chart gluing.  After applying
them to the outputs of two iterated affine-subdivision maps, the compatibility statement reduces to barycentric subdivisions of one standard simplex.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace RefinedChartCarrierCore

open MaximalFlagCode

variable {p : Nat}

/-- The arithmetic cast from a maximal-simplex index to a stage and back is the identity. -/
@[simp] theorem simplexIndex_stageIndex
    (hp : Nat.Prime p) (i : Fin (p - 1 + 1)) :
    simplexIndex hp (stageIndex hp i) = i := by
  apply Fin.ext
  rfl

/-- The raw maximal-simplex index records the dual dimension of its barred-permutation vertex. -/
theorem maximal_vertex_dualDimension_raw
    (hp : Nat.Prime p) (s : Simplex p (p - 1))
    (i : Fin (p - 1 + 1)) :
    (s i).dualDimension = (stageIndex hp i).1 := by
  rw [← simplexIndex_stageIndex hp i]
  exact Simplex.maximal_dualDimension hp s (stageIndex hp i)

/-- Shared vertices of two maximal flags occur at the same rank. -/
theorem maximal_raw_index_eq_of_vertex_eq
    (hp : Nat.Prime p) (s t : Simplex p (p - 1))
    {i j : Fin (p - 1 + 1)} (h : s i = t j) :
    i = j := by
  have hdim := congrArg BarredPermutation.dualDimension h
  rw [maximal_vertex_dualDimension_raw hp s i,
    maximal_vertex_dualDimension_raw hp t j] at hdim
  apply Fin.ext
  exact hdim

/-- In a second maximal chart, the coordinate of a vertex of the first chart is either the
coordinate at the same rank or zero. -/
theorem chartWeight_at_maximal_vertex
    (hp : Nat.Prime p)
    (s t : Simplex p (p - 1))
    (w : StandardSimplex (p - 1))
    (i : Fin (p - 1 + 1)) :
    t.chartWeight w (s i) = if t i = s i then w i else 0 := by
  classical
  unfold Simplex.chartWeight
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  intro j _ hji
  rw [ite_eq_right]
  intro hjc
  exact hji (maximal_raw_index_eq_of_vertex_eq hp t s hjc)

/-- Equality of maximal-chart realization points gives the exact coordinate relation at each
ranked vertex. -/
theorem coordinate_eq_if_vertex_eq_of_realizationPoint_eq
    (hp : Nat.Prime p)
    (s t : Simplex p (p - 1))
    (w v : StandardSimplex (p - 1))
    (h : s.realizationPoint w = t.realizationPoint v)
    (i : Fin (p - 1 + 1)) :
    w i = if t i = s i then v i else 0 := by
  have hcoord := congrArg (fun x : Realization p => x (s i)) h
  simpa [Simplex.realizationPoint_apply,
    chartWeight_at_maximal_vertex hp s s w i,
    chartWeight_at_maximal_vertex hp s t v i] using hcoord

/-- A nonzero coordinate of the first chart forces the same vertex and the same coordinate in the
second maximal chart. -/
theorem vertex_eq_and_coordinate_eq_of_ne_zero
    (hp : Nat.Prime p)
    (s t : Simplex p (p - 1))
    (w v : StandardSimplex (p - 1))
    (h : s.realizationPoint w = t.realizationPoint v)
    (i : Fin (p - 1 + 1))
    (hi : w i ≠ 0) :
    t i = s i ∧ v i = w i := by
  have hc := coordinate_eq_if_vertex_eq_of_realizationPoint_eq hp s t w v h i
  by_cases hst : t i = s i
  · exact ⟨hst, by simpa [hst] using hc.symm⟩
  · have : w i = 0 := by simpa [hst] using hc
    exact (hi this).elim

/-- The support of the first coordinate vector is contained rankwise in the common face of the two
maximal flags. -/
theorem vertex_eq_of_mem_support
    (hp : Nat.Prime p)
    (s t : Simplex p (p - 1))
    (w v : StandardSimplex (p - 1))
    (h : s.realizationPoint w = t.realizationPoint v)
    (i : Fin (p - 1 + 1))
    (hi : w i ≠ 0) :
    t i = s i :=
  (vertex_eq_and_coordinate_eq_of_ne_zero hp s t w v h i hi).1

/-- On every active rank, the two maximal-chart barycentric coordinates agree. -/
theorem coordinate_eq_of_ne_zero
    (hp : Nat.Prime p)
    (s t : Simplex p (p - 1))
    (w v : StandardSimplex (p - 1))
    (h : s.realizationPoint w = t.realizationPoint v)
    (i : Fin (p - 1 + 1))
    (hi : w i ≠ 0) :
    v i = w i :=
  (vertex_eq_and_coordinate_eq_of_ne_zero hp s t w v h i hi).2

end RefinedChartCarrierCore
end FoxNeuwirthOrderComplex
end NRR

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace RefinedChartCarrierCore

open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open RefinedAffineMap

variable {p : Nat}

/-- Transport a label-indexed refinement word to the maximal-simplex vertex index type. -/
noncomputable def maximalRefinementWord
    (N : Nat) (rho : RefinementWord p N) :
    Fin N → Equiv.Perm (Fin (p - 1 + 1)) :=
  fun k => Simplex.refinementIndexPerm (p := p) (rho k)

@[simp] theorem maximalRefinementWord_apply
    (N : Nat) (rho : RefinementWord p N) (k : Fin N) :
    maximalRefinementWord N rho k = Simplex.refinementIndexPerm (p := p) (rho k) := rfl

/-- Equality of global realization points in two maximal charts forces equality of their ranked
standard-simplex coordinate vectors.  Ranks where the maximal flags differ have zero coordinate in
both charts. -/
theorem maximal_source_eq_of_realizationPoint_eq
    (hp : Nat.Prime p)
    (s t : Simplex p (p - 1))
    (w v : StandardSimplex (p - 1))
    (h : s.realizationPoint w = t.realizationPoint v) :
    w = v := by
  apply Subtype.ext
  funext i
  have hforward :=
    coordinate_eq_if_vertex_eq_of_realizationPoint_eq hp s t w v h i
  by_cases hst : t i = s i
  · simpa [hst] using hforward
  · have hw : w i = 0 := by simpa [hst] using hforward
    have hreverse :=
      coordinate_eq_if_vertex_eq_of_realizationPoint_eq hp t s v w h.symm i
    have hts : s i ≠ t i := Ne.symm hst
    have hv : v i = 0 := by simpa [hts] using hreverse
    exact hw.trans hv.symm

/-- Equal points in two refined Fox--Neuwirth charts have equal inner standard-simplex realization
coordinates. -/
theorem refined_innerPoint_eq_of_chart_eq
    (hp : Nat.Prime p) (N : Nat)
    (q r : TopCell hp N)
    (x y : Delta (p - 1))
    (h : chart hp N q x = chart hp N r y) :
    affineCompMap (p - 1) N (maximalRefinementWord N q.2) x =
      affineCompMap (p - 1) N (maximalRefinementWord N r.2) y := by
  let s : Simplex p (p - 1) := ReferenceAffineOrbitCount.topRepr hp q.1
  let t : Simplex p (p - 1) := ReferenceAffineOrbitCount.topRepr hp r.1
  have hreal :
      s.realizationPoint
          (StandardSimplex.ofDelta (affineCompMap (p - 1) N (maximalRefinementWord N q.2) x)) =
        t.realizationPoint
          (StandardSimplex.ofDelta (affineCompMap (p - 1) N (maximalRefinementWord N r.2) y)) := by
    change s.realizationPoint
        (StandardSimplex.ofDelta
          (affineCompMap (p - 1) N (maximalRefinementWord N q.2) x)) =
      t.realizationPoint
        (StandardSimplex.ofDelta
          (affineCompMap (p - 1) N (maximalRefinementWord N r.2) y)) at h
    exact h
  have hstd := maximal_source_eq_of_realizationPoint_eq hp s t
    (StandardSimplex.ofDelta (affineCompMap (p - 1) N (maximalRefinementWord N q.2) x))
    (StandardSimplex.ofDelta (affineCompMap (p - 1) N (maximalRefinementWord N r.2) y)) hreal
  simpa using congrArg StandardSimplex.toDelta hstd

/-- An active refined-chart source vertex and its coefficient are independent of the chosen
maximal Fox--Neuwirth chart and refinement word. -/
theorem refined_active_vertex_and_coefficient_eq
    (hp : Nat.Prime p) (N : Nat)
    (q r : TopCell hp N)
    (x y : Delta (p - 1))
    (h : chart hp N q x = chart hp N r y)
    (i : Fin (p - 1 + 1)) (hi : 0 < x i) :
    vertex hp N q i = vertex hp N r i ∧ y i = x i := by
  let s : Simplex p (p - 1) := ReferenceAffineOrbitCount.topRepr hp q.1
  let t : Simplex p (p - 1) := ReferenceAffineOrbitCount.topRepr hp r.1
  let u : Delta (p - 1) := affineCompMap (p - 1) N (maximalRefinementWord N q.2) x
  let v : Delta (p - 1) := affineCompMap (p - 1) N (maximalRefinementWord N r.2) y
  have hinner : u = v := by
    simpa [u, v] using refined_innerPoint_eq_of_chart_eq hp N q r x y h
  have hiter := affineCompMap_active_vertex_and_coefficient_eq
    (p - 1) N (maximalRefinementWord N q.2)
      (maximalRefinementWord N r.2) x y hinner
    i hi
  let z : Delta (p - 1) :=
    affineCompMap (p - 1) N (maximalRefinementWord N q.2)
      (SphereOddDegree.FiniteSimplex.vertex (S := Real) i)
  have hzEq : z =
      affineCompMap (p - 1) N (maximalRefinementWord N r.2)
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) i) := by
    simpa [z] using hiter.1
  have hreal :
      s.realizationPoint (StandardSimplex.ofDelta u) =
        t.realizationPoint (StandardSimplex.ofDelta v) := by
    change s.realizationPoint (StandardSimplex.ofDelta u) =
      t.realizationPoint (StandardSimplex.ofDelta v) at h
    exact h
  have hglobal :
      s.realizationPoint (StandardSimplex.ofDelta z) =
        t.realizationPoint (StandardSimplex.ofDelta z) := by
    apply Realization.ext
    intro c
    classical
    simp only [Simplex.realizationPoint_apply]
    unfold Simplex.chartWeight
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hzj : z j = 0
    · change (if s j = c then z j else 0) =
        (if t j = c then z j else 0)
      simp [hzj]
    · have hzpos : 0 < z j :=
        lt_of_le_of_ne (SphereOddDegree.FiniteSimplex.zero_le z j) (Ne.symm hzj)
      have hupos : 0 < u j := by
        exact affineCompMap_vertex_support_subset
          (p - 1) N (maximalRefinementWord N q.2) x
          i j hi
          (by simpa [z] using hzpos)
      have hst : t j = s j :=
        vertex_eq_of_mem_support hp s t
          (StandardSimplex.ofDelta u) (StandardSimplex.ofDelta v)
          hreal j (ne_of_gt hupos)
      by_cases hsc : s j = c
      · have htc : t j = c := hst.trans hsc
        simp [StandardSimplex.ofDelta, hsc, htc]
      · have htc : t j ≠ c := by
          intro htc
          exact hsc (hst.symm.trans htc)
        simp [ hsc, htc]
  have hglobal' :
      s.realizationPoint
          (StandardSimplex.ofDelta
            (affineCompMap (p - 1) N (maximalRefinementWord N q.2)
              (SphereOddDegree.FiniteSimplex.vertex (S := Real) i))) =
        t.realizationPoint
          (StandardSimplex.ofDelta
            (affineCompMap (p - 1) N (maximalRefinementWord N r.2)
              (SphereOddDegree.FiniteSimplex.vertex (S := Real) i))) := by
    calc
      _ = s.realizationPoint (StandardSimplex.ofDelta z) := by rfl
      _ = t.realizationPoint (StandardSimplex.ofDelta z) := hglobal
      _ = _ := by rw [hzEq]
  constructor
  · change s.realizationPoint
        (StandardSimplex.ofDelta
          (affineCompMap (p - 1) N (maximalRefinementWord N q.2)
            (SphereOddDegree.FiniteSimplex.vertex (S := Real) i))) =
        t.realizationPoint
          (StandardSimplex.ofDelta
            (affineCompMap (p - 1) N (maximalRefinementWord N r.2)
              (SphereOddDegree.FiniteSimplex.vertex (S := Real) i)))
    exact hglobal'
  · simpa [Nat.sub_add_cancel hp.pos] using hiter.2

/-- The refined affine interpolation of one global sampling map is independent of the refined
chart representing the point. -/
theorem refinedAffineValue_eq_of_chart_eq
    (hp : Nat.Prime p) (N : Nat)
    (F : ContinuousCoordinateMap p)
    (q r : TopCell hp N)
    (w v : StandardSimplex (p - 1))
    (h : chart hp N q (StandardSimplex.toDelta w) =
      chart hp N r (StandardSimplex.toDelta v)) :
    value hp N F q w = value hp N F r v := by
  funext c
  unfold value
  apply Finset.sum_congr rfl
  intro i hiMem
  by_cases hwi : w i = 0
  · have hvi : v i = 0 := by
      by_contra hvi
      have hvpos : 0 < v i :=
        lt_of_le_of_ne (v.nonneg i) (Ne.symm hvi)
      have hrev := refined_active_vertex_and_coefficient_eq
        hp N r q (StandardSimplex.toDelta v) (StandardSimplex.toDelta w)
        h.symm i (by
          change 0 < v i
          exact hvpos)
      have hcoord := hrev.2
      change w i = v i at hcoord
      exact hvi (hcoord.symm.trans hwi)
    simp [hwi, hvi]
  · have hwpos : 0 < w i :=
      lt_of_le_of_ne (w.nonneg i) (Ne.symm hwi)
    have hactive := refined_active_vertex_and_coefficient_eq
      hp N q r (StandardSimplex.toDelta w) (StandardSimplex.toDelta v)
      h i (by
        change 0 < w i
        exact hwpos)
    have hsample : vertexValue hp N F q i c = vertexValue hp N F r i c := by
      simp [vertexValue, hactive.1]
    have hcoeff := hactive.2
    change v i = w i at hcoeff
    rw [hsample, hcoeff]

end RefinedChartCarrierCore
end FoxNeuwirthOrderComplex
end NRR
