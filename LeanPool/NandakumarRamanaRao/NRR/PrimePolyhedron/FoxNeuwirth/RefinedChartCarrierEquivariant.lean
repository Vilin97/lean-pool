/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RefinedChartCarrierCore
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.CoordinateEquivariance
/-!
# Equivariant refined-chart carrier compatibility

This module upgrades the raw overlap theorem for refined maximal charts to symmetry-decorated
occurrences.  It is the exact compatibility statement needed by the endpoint-stack quotient:
when two decorated refined charts represent the same global realization point, the corresponding
affine interpolants of one equivariant sampling map are related by the same decorations.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace RefinedChartCarrierEquivariant

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open RefinedAffineMap
open RefinedChartCarrierCore

variable {p : Nat}

/-- Reindex a label by the vertex-coordinate type of a maximal simplex. -/
def maximalCoordinateIndex (i : Fin p) : Fin (p - 1 + 1) :=
  Fin.cast (Nat.sub_add_cancel (Nat.pos_of_ne_zero (by
    intro h
    subst p
    exact Fin.elim0 i))).symm i

/-- Relabelling a maximal simplex commutes with its realization chart. -/
theorem realizationPoint_prime_smul
    (p : Nat) (g : PrimeSymmetry p)
    (s : Simplex p (p - 1)) (w : StandardSimplex (p - 1)) :
    (g • s).realizationPoint w = g • s.realizationPoint w := by
  apply Realization.ext
  intro c
  classical
  simp only [Simplex.realizationPoint_apply, Simplex.chartWeight,
    Realization.prime_smul_apply, Simplex.prime_smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : g • s i = c
  · have h' : s i = c.relabel (PrimeSymmetry.toPerm p g).symm := by
      have := congrArg (fun z : BarredPermutation p =>
        z.relabel (PrimeSymmetry.toPerm p g).symm) h
      simpa using this
    simp [ h']
  · have h' : s i ≠ c.relabel (PrimeSymmetry.toPerm p g).symm := by
      intro hs
      apply h
      have := congrArg (fun z : BarredPermutation p =>
        z.relabel (PrimeSymmetry.toPerm p g)) hs
      simpa using this
    rw [ite_eq_right h']
    change (if g • (s i : BarredPermutation p) = c then w i else 0) = 0
    exact ite_eq_right h

/-- Prime relabelling commutes with every iterated refined chart. -/
theorem refinedPoint_prime_smul
    (p : Nat) (g : PrimeSymmetry p)
    (s : Simplex p (p - 1)) (N : Nat) (rho : RefinementWord p N)
    (w : StandardSimplex (p - 1)) :
    (g • s).refinedPoint N rho w = g • s.refinedPoint N rho w := by
  change (g • s).realizationPoint
      (StandardSimplex.ofDelta (affineCompMap (p - 1) N
        (maximalRefinementWord N rho) (StandardSimplex.toDelta w))) =
    g • s.realizationPoint
      (StandardSimplex.ofDelta (affineCompMap (p - 1) N
        (maximalRefinementWord N rho) (StandardSimplex.toDelta w)))
  exact realizationPoint_prime_smul p g s _

/-- Prime relabelling commutes with every represented refined vertex. -/
theorem refinedVertex_prime_smul
    (p : Nat) (g : PrimeSymmetry p)
    (s : Simplex p (p - 1)) (N : Nat) (rho : RefinementWord p N)
    (i : Fin p) :
    (g • s).refinedVertex N rho i = g • s.refinedVertex N rho i := by
  simpa [Simplex.refinedVertex, maximalCoordinateIndex] using
    refinedPoint_prime_smul p g s N rho
      (StandardSimplex.ofDelta
        (stdSimplex.vertex (S := Real) (maximalCoordinateIndex i)))

/-- Affine interpolation of samples of `F` on an arbitrary refined maximal simplex. -/
noncomputable def simplexValue
    (s : Simplex p (p - 1)) (N : Nat) (rho : RefinementWord p N)
    (F : ContinuousCoordinateMap p) (w : StandardSimplex (p - 1)) : Fin p → Real :=
  fun c => ∑ i : Fin p,
    w (maximalCoordinateIndex i) *
      F (s.refinedVertex N rho i) c

/-- Active refined vertices and their source coefficients are independent of the maximal chart. -/
theorem simplex_active_vertex_and_coefficient_eq
    (hp : Nat.Prime p) (N : Nat)
    (s t : Simplex p (p - 1))
    (rho sigma : RefinementWord p N)
    (x y : Delta (p - 1))
    (h : s.refinedPoint N rho (StandardSimplex.ofDelta x) =
      t.refinedPoint N sigma (StandardSimplex.ofDelta y))
    (i : Fin p) (hi : 0 < x (maximalCoordinateIndex i)) :
    s.refinedVertex N rho i = t.refinedVertex N sigma i ∧ y (maximalCoordinateIndex i) = x (maximalCoordinateIndex i) := by
  let u : Delta (p - 1) := affineCompMap (p - 1) N (maximalRefinementWord N rho) x
  let v : Delta (p - 1) := affineCompMap (p - 1) N (maximalRefinementWord N sigma) y
  have hreal :
      s.realizationPoint (StandardSimplex.ofDelta u) =
        t.realizationPoint (StandardSimplex.ofDelta v) := by
    change s.realizationPoint (StandardSimplex.ofDelta u) =
      t.realizationPoint (StandardSimplex.ofDelta v) at h
    exact h
  have hinner : u = v := by
    have hstd := maximal_source_eq_of_realizationPoint_eq hp s t
      (StandardSimplex.ofDelta u) (StandardSimplex.ofDelta v) hreal
    simpa using congrArg StandardSimplex.toDelta hstd
  have hiter := affineCompMap_active_vertex_and_coefficient_eq
    (p - 1) N (maximalRefinementWord N rho) (maximalRefinementWord N sigma) x y hinner
    (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)
    (by
      change 0 < x (Fin.cast (Nat.sub_add_cancel hp.pos).symm i) at hi
      exact hi)
  let z : Delta (p - 1) :=
    affineCompMap (p - 1) N (maximalRefinementWord N rho)
      (stdSimplex.vertex (S := Real)
        (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))
  have hzEq : z =
      affineCompMap (p - 1) N (maximalRefinementWord N sigma)
        (stdSimplex.vertex (S := Real)
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
    simpa [z] using hiter.1
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
    · have hzj' : (StandardSimplex.ofDelta z) j = 0 := hzj
      simp [hzj']
    · have hzpos : 0 < z j :=
        lt_of_le_of_ne (stdSimplex.zero_le z j) (Ne.symm hzj)
      have hupos : 0 < u j :=
        affineCompMap_vertex_support_subset
          (p - 1) N (maximalRefinementWord N rho) x
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i) j
          (by
            change 0 < x (Fin.cast (Nat.sub_add_cancel hp.pos).symm i) at hi
            exact hi)
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
  constructor
  · change
      s.realizationPoint (StandardSimplex.ofDelta z) =
        t.realizationPoint (StandardSimplex.ofDelta
          (affineCompMap (p - 1) N (maximalRefinementWord N sigma)
            (stdSimplex.vertex (S := Real)
              (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))))
    rw [← hzEq]
    exact hglobal
  · have hcoeff := hiter.2
    change y (maximalCoordinateIndex i) = x (maximalCoordinateIndex i) at hcoeff
    exact hcoeff

/-- Affine interpolation of globally sampled values agrees on arbitrary overlapping refined
maximal charts. -/
theorem simplexValue_eq_of_refinedPoint_eq
    (hp : Nat.Prime p) (N : Nat)
    (s t : Simplex p (p - 1))
    (rho sigma : RefinementWord p N)
    (F : ContinuousCoordinateMap p)
    (w v : StandardSimplex (p - 1))
    (h : s.refinedPoint N rho w = t.refinedPoint N sigma v) :
    simplexValue s N rho F w = simplexValue t N sigma F v := by
  funext c
  unfold simplexValue
  apply Finset.sum_congr rfl
  intro i hiMem
  by_cases hwi : w (maximalCoordinateIndex i) = 0
  · have hvi : v (maximalCoordinateIndex i) = 0 := by
      by_contra hvi
      have hvpos : 0 < v (maximalCoordinateIndex i) := lt_of_le_of_ne (v.nonneg (maximalCoordinateIndex i)) (Ne.symm hvi)
      have hrev := simplex_active_vertex_and_coefficient_eq hp N
        t s sigma rho (StandardSimplex.toDelta v) (StandardSimplex.toDelta w)
        h.symm i (by
          change 0 < v (maximalCoordinateIndex i)
          exact hvpos)
      apply hvi
      have heq := hrev.2.symm
      change v (maximalCoordinateIndex i) = w (maximalCoordinateIndex i) at heq
      exact heq.trans hwi
    simp [hwi, hvi]
  · have hwpos : 0 < w (maximalCoordinateIndex i) := lt_of_le_of_ne (w.nonneg (maximalCoordinateIndex i)) (Ne.symm hwi)
    have hactive := simplex_active_vertex_and_coefficient_eq hp N
      s t rho sigma (StandardSimplex.toDelta w) (StandardSimplex.toDelta v)
      h i (by
        change 0 < w (maximalCoordinateIndex i)
        exact hwpos)
    rw [hactive.1]
    have heq := hactive.2
    change v (maximalCoordinateIndex i) = w (maximalCoordinateIndex i) at heq
    rw [heq]

/-- Sampling an equivariant map after relabelling the whole refined simplex relabels the affine
interpolant by the same prime symmetry. -/
theorem simplexValue_prime_smul
    (p : Nat) (g : PrimeSymmetry p)
    (s : Simplex p (p - 1)) (N : Nat) (rho : RefinementWord p N)
    (F : ContinuousCoordinateMap p) (hF : IsEquivariantCoordinateMap p F)
    (w : StandardSimplex (p - 1)) :
    simplexValue (g • s) N rho F w = g • simplexValue s N rho F w := by
  funext c
  simp only [simplexValue, PrimeSymmetry.smul_coordinate_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [refinedVertex_prime_smul p g s N rho i, hF g]
  rfl

/-- Symmetry-decorated refined affine values agree whenever the decorated chart points agree. -/
theorem decorated_value_eq_of_decorated_chart_eq
    (hp : Nat.Prime p) (N : Nat)
    (F : ContinuousCoordinateMap p) (hF : IsEquivariantCoordinateMap p F)
    (q r : TopCell hp N)
    (g h : PrimeSymmetry p)
    (w v : StandardSimplex (p - 1))
    (hpoint : g • chart hp N q (StandardSimplex.toDelta w) =
      h • chart hp N r (StandardSimplex.toDelta v)) :
    g • value hp N F q w = h • value hp N F r v := by
  let s : Simplex p (p - 1) := ReferenceAffineOrbitCount.topRepr hp q.1
  let t : Simplex p (p - 1) := ReferenceAffineOrbitCount.topRepr hp r.1
  have hpoint' : g • s.refinedPoint N q.2 w =
      h • t.refinedPoint N r.2 v := by
    simpa [chart, Simplex.refinedPoint, s, t] using hpoint
  have hrefined :
      (g • s).refinedPoint N q.2 w =
        (h • t).refinedPoint N r.2 v := by
    calc
      _ = g • s.refinedPoint N q.2 w := refinedPoint_prime_smul p g s N q.2 w
      _ = h • t.refinedPoint N r.2 v := hpoint'
      _ = _ := (refinedPoint_prime_smul p h t N r.2 v).symm
  have hlocal := simplexValue_eq_of_refinedPoint_eq hp N
    (g • s) (h • t) q.2 r.2 F w v hrefined
  have hg := simplexValue_prime_smul p g s N q.2 F hF w
  have hh := simplexValue_prime_smul p h t N r.2 F hF v
  have hresult := hg.symm.trans (hlocal.trans hh)
  have hsvalue : simplexValue s N q.2 F w = value hp N F q w := by
    funext j
    unfold simplexValue value vertexValue vertex chart
    change (∑ x : Fin p, w (maximalCoordinateIndex x) *
      F (s.refinedVertex N q.2 x) j) = _
    convert
      (Equiv.sum_comp (Fin.castOrderIso (Nat.sub_add_cancel hp.pos).symm).toEquiv
        (fun i => w i * F
          ((ReferenceAffineOrbitCount.topRepr hp q.1).refinedContinuousMap N q.2
            (stdSimplex.vertex (S := Real) i)) j)) using 1 <;>
      simp [s, maximalCoordinateIndex, Simplex.refinedVertex]
  have htvalue : simplexValue t N r.2 F v = value hp N F r v := by
    funext j
    unfold simplexValue value vertexValue vertex chart
    change (∑ x : Fin p, v (maximalCoordinateIndex x) *
      F (t.refinedVertex N r.2 x) j) = _
    convert
      (Equiv.sum_comp (Fin.castOrderIso (Nat.sub_add_cancel hp.pos).symm).toEquiv
        (fun i => v i * F
          ((ReferenceAffineOrbitCount.topRepr hp r.1).refinedContinuousMap N r.2
            (stdSimplex.vertex (S := Real) i)) j)) using 1 <;>
      simp [t, maximalCoordinateIndex, Simplex.refinedVertex]
  rw [← hsvalue, ← htvalue]
  exact hresult

end RefinedChartCarrierEquivariant
end FoxNeuwirthOrderComplex
end NRR
