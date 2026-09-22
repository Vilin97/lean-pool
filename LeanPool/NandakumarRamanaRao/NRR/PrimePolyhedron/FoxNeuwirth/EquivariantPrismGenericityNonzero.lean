/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismGenericityPolynomials
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.AffineSubdivisionDeterminant
/-!
# Nontriviality of the equivariant prism genericity polynomials

The finite perturbation theorem applies only after every determinant polynomial in the combined
family is known to be nonzero.  The essential point is that the scalar orbit parameters occurring
at the vertices of one refined prism simplex are independent: two local scalar sites can represent
the same diagonal prime orbit only when both the local vertex and the coordinate label agree.

Once this local independence is exposed, an arbitrary collection of vectors can be prescribed at
the vertices of one fixed prism simplex.  For a facet determinant we prescribe a triangular
augmented-deviation matrix with diagonal one.  For a codimension-two minor we prescribe the
identity deviation matrix.  Evaluation at the corresponding assignments proves that the two
polynomial families, and hence the combined family, are nonzero.
-/

namespace NRR

open scoped BigOperators
open MvPolynomial
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismGenericityNonzero

open EquivariantPrismVertexParameters
open EquivariantPrismGenericityPolynomials
open SubdivisionPrismCharts
open AffinePositiveRayBoundary
open ReferenceAffineOrbitCount

variable {p : Nat}

/-! ## Injectivity of the affine subdivision charts -/

/-- One barycentric-subdivision affine map is injective. -/
theorem affineSubdivMap_injective
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1))) :
    Function.Injective (affineSubdivMap n pi) := by
  intro x y hxy
  have hmul :
      Matrix.mulVec (AffineSubdivisionDeterminant.stepVertexMatrix n pi)
          (fun i => x i - y i) = 0 := by
    funext r
    have hr := congrArg (fun z : Delta n => z r) hxy
    simp only [Matrix.mulVec, AffineSubdivisionDeterminant.stepVertexMatrix,
      affineSubdivMap_apply, Pi.zero_apply] at *
    calc
      _ = ∑ k, (x k - y k) * (prefixBarycenter n pi k).val r := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = (∑ k, x k * (prefixBarycenter n pi k).val r) -
          ∑ k, y k * (prefixBarycenter n pi k).val r := by
        simp only [sub_mul, Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hr
  have hz : (fun i => x i - y i) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero
      (AffineSubdivisionDeterminant.det_stepVertexMatrix_ne_zero n pi) hmul
  apply Subtype.ext
  funext i
  have hi := congrFun hz i
  change x i = y i
  exact sub_eq_zero.mp hi

/-- Every iterated barycentric-subdivision affine composite is injective. -/
theorem affineCompMap_injective
    (n N : Nat) (rho : Fin N → Equiv.Perm (Fin (n + 1))) :
    Function.Injective (affineCompMap n N rho) := by
  revert rho
  induction N with
  | zero =>
      intro rho x y hxy
      simpa using hxy
  | succ N ih =>
      intro rho x y hxy
      rw [affineCompMap_succ] at hxy
      have hinner := ih (fun i => rho i.castSucc) hxy
      exact affineSubdivMap_injective n (rho (Fin.last N)) hinner

/-- The affine realization chart of a strict order-complex simplex is injective. -/
theorem simplex_realizationPoint_injective
    {d : Nat} (s : Simplex p d) :
    Function.Injective s.realizationPoint := by
  intro w v hwv
  apply Subtype.ext
  funext i
  have hi := congrArg (fun x : Realization p => x (s i)) hwv
  simpa [Simplex.realizationPoint, Simplex.chartWeight,
    s.vertex_injective.eq_iff] using hi

/-- A refined spatial chart is injective. -/
theorem refined_chart_injective
    (hp : Nat.Prime p) (N : Nat) (q : RefinedAffineMap.TopCell hp N) :
    Function.Injective (RefinedAffineMap.chart hp N q) := by
  intro x y hxy
  let s : Simplex p (p - 1) := ReferenceAffineOrbitCount.topRepr hp q.1
  let rho' : Fin N → Equiv.Perm (Fin (p - 1 + 1)) :=
    fun k => Simplex.refinementIndexPerm (q.2 k)
  have hreal :
      s.realizationPoint
          (StandardSimplex.ofDelta (affineCompMap (p - 1) N rho' x)) =
        s.realizationPoint
          (StandardSimplex.ofDelta (affineCompMap (p - 1) N rho' y)) := by
    simpa [RefinedAffineMap.chart, Simplex.refinedContinuousMap,
      Simplex.realizationContinuousMap, s] using hxy
  have hdelta : affineCompMap (p - 1) N rho' x =
      affineCompMap (p - 1) N rho' y := by
    have hstd := simplex_realizationPoint_injective s hreal
    simpa using congrArg StandardSimplex.toDelta hstd
  exact affineCompMap_injective (p - 1) N rho' hdelta

/-! The staircase map is an affine isomorphism onto the selected prism simplex.  The following
coordinate proof recovers every barycentric coefficient from the spatial aggregate and interval
coordinate. -/

/-- Transport a spatial label to the maximal-simplex indexing type. -/
def spatialIndex (hp : Nat.Prime p) (i : Fin p) : Fin (p - 1 + 1) :=
  Fin.cast (Nat.sub_add_cancel hp.pos).symm i

/-- Spatial weights away from the doubled staircase vertex recover a unique domain coordinate. -/
theorem spatialWeight_eq_of_lt
    (hp : Nat.Prime p) (k : Fin p) (w : StandardSimplex p)
    (i : Fin p) (hi : i.1 < k.1) :
    spatialWeight hp k w (spatialIndex hp i) = w i.castSucc := by
  classical
  unfold spatialWeight
  simp only [spatialIndex, Fin.cast_inj]
  rw [Finset.sum_eq_single i.castSucc]
  · rw [ite_eq_left]
    exact by
      simp [staircaseSpatial, Fin.ext_iff]
      omega
  · intro j hj hji
    have hne : staircaseSpatial p k j ≠ i := by
      intro h
      simp only [staircaseSpatial] at h
      split_ifs at h with hjk
      · have : j.1 = i.1 := by simpa using congrArg Fin.val h
        exact hji (Fin.ext this)
      · have hklt : k.1 < j.1 := Nat.lt_of_not_ge hjk
        have : j.1 - 1 = i.1 := by simpa using congrArg Fin.val h
        omega
    exact ite_eq_right hne
  · simp

/-- Spatial weights above the doubled staircase vertex recover the successor domain coordinate. -/
theorem spatialWeight_eq_of_gt
    (hp : Nat.Prime p) (k : Fin p) (w : StandardSimplex p)
    (i : Fin p) (hi : k.1 < i.1) :
    spatialWeight hp k w (spatialIndex hp i) =
      w ⟨i.1 + 1, by have := i.2; omega⟩ := by
  classical
  let j : Fin (p + 1) := ⟨i.1 + 1, by have := i.2; omega⟩
  unfold spatialWeight
  simp only [spatialIndex, Fin.cast_inj]
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left]
    exact by
      simp [j, staircaseSpatial, Fin.ext_iff]
      omega
  · intro j' hj' hjne
    have hne : staircaseSpatial p k j' ≠ i := by
      intro h
      simp only [staircaseSpatial] at h
      split_ifs at h with hjk
      · have hjle : j'.1 ≤ k.1 := hjk
        have : j'.1 = i.1 := by simpa using congrArg Fin.val h
        omega
      · have : j'.1 - 1 = i.1 := by simpa using congrArg Fin.val h
        have hpos : 0 < j'.1 := by
          have := Nat.lt_of_not_ge hjk
          omega
        have : j'.1 = i.1 + 1 := by omega
        exact hjne (Fin.ext this)
    exact ite_eq_right hne
  · simp

/-- The doubled spatial coordinate is the sum of the two staircase coordinates. -/
theorem spatialWeight_pivot
    (hp : Nat.Prime p) (k : Fin p) (w : StandardSimplex p) :
    spatialWeight hp k w (spatialIndex hp k) =
      w k.castSucc + w ⟨k.1 + 1, by have := k.2; omega⟩ := by
  classical
  unfold spatialWeight
  simp only [spatialIndex, Fin.cast_inj]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem
    (by simp : k.castSucc ∈ (Finset.univ : Finset (Fin (p + 1))))]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem
    (by
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
      intro h
      have := congrArg Fin.val h
      simp at this : (⟨k.1 + 1, by have := k.2; omega⟩ : Fin (p + 1)) ∈
        (Finset.univ : Finset (Fin (p + 1))) \ {k.castSucc})]
  simp [staircaseSpatial]
  apply Finset.sum_eq_zero
  intro j hj
  have hjmem := Finset.mem_sdiff.mp hj
  have hj0 : j ≠ k.castSucc := by
    simpa only [Finset.mem_singleton] using (Finset.mem_sdiff.mp hjmem.1).2
  have hj1 : j ≠ (⟨k.1 + 1, by have := k.2; omega⟩ : Fin (p + 1)) := by
    simpa only [Finset.mem_singleton] using hjmem.2
  have hne : staircaseSpatial p k j ≠ k := by
    intro h
    simp only [staircaseSpatial] at h
    split_ifs at h with hjk
    · have : j.1 = k.1 := by simpa using congrArg Fin.val h
      exact hj0 (Fin.ext this)
    · have : j.1 - 1 = k.1 := by simpa using congrArg Fin.val h
      have hjpos : 0 < j.1 := by
        have := Nat.lt_of_not_ge hjk
        omega
      have : j.1 = k.1 + 1 := by omega
      exact hj1 (Fin.ext this)
  exact ite_eq_right hne

/-- The interval coordinate is the sum of all domain coordinates strictly above the staircase
cut. -/
theorem intervalWeight_eq_sum_gt
    (k : Fin p) (w : StandardSimplex p) :
    intervalWeight k w =
      ∑ j : Fin (p + 1), if k.1 < j.1 then w j else 0 := by
  apply Finset.sum_congr rfl
  intro j hj
  simp [ staircaseTime]

/-- The interval coordinate splits into the upper pivot coordinate and the spatial tail. -/
theorem intervalWeight_eq_pivot_add_spatial_tail
    (hp : Nat.Prime p) (k : Fin p) (w : StandardSimplex p) :
    intervalWeight k w =
      w ⟨k.1 + 1, by have := k.2; omega⟩ +
        ∑ i : Fin p, if k.1 < i.1 then
          spatialPoint hp k w (spatialIndex hp i) else 0 := by
  classical
  rw [intervalWeight_eq_sum_gt]
  let kp : Fin (p + 1) := ⟨k.1 + 1, by have := k.2; omega⟩
  rw [Fin.sum_univ_succAbove (fun j : Fin (p + 1) =>
    if k.1 < j.1 then w j else 0) kp]
  have hpivot : (if k.1 < kp.1 then w kp else 0) = w kp := by
    simp [kp]
  rw [hpivot]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hki : k.1 < i.1
  · have hle : kp ≤ i.castSucc := by
      apply Fin.mk_le_mk.mpr
      simp []
      omega
    rw [Fin.succAbove_of_le_castSucc kp i hle]
    rw [ite_eq_left hki, ite_eq_left]
    · exact (spatialWeight_eq_of_gt hp k w i hki).symm
    · simp
      omega
  · have hlt : i.castSucc < kp := by
      apply Fin.mk_lt_mk.mpr
      simp []
      omega
    rw [Fin.succAbove_of_castSucc_lt kp i hlt]
    rw [ite_eq_right hki, ite_eq_right]
    simp
    omega

/-- The staircase chart is injective. -/
theorem staircasePoint_injective
    (hp : Nat.Prime p) (k : Fin p) :
    Function.Injective (staircasePoint hp k) := by
  intro w v hwv
  have hsp : spatialPoint hp k w = spatialPoint hp k v :=
    congrArg Prod.fst hwv
  have hit : intervalPoint k w = intervalPoint k v :=
    congrArg Prod.snd hwv
  let kp : Fin (p + 1) := ⟨k.1 + 1, by have := k.2; omega⟩
  have htail :
      (∑ i : Fin p, if k.1 < i.1 then spatialPoint hp k w (spatialIndex hp i) else 0) =
        ∑ i : Fin p, if k.1 < i.1 then spatialPoint hp k v (spatialIndex hp i) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [congrArg (fun u : StandardSimplex (p - 1) => u (spatialIndex hp i)) hsp]
  have htime : intervalWeight k w = intervalWeight k v :=
    congrArg Subtype.val hit
  have hkp : w kp = v kp := by
    have hwrec := intervalWeight_eq_pivot_add_spatial_tail hp k w
    have hvrec := intervalWeight_eq_pivot_add_spatial_tail hp k v
    change intervalWeight k w = w kp + _ at hwrec
    change intervalWeight k v = v kp + _ at hvrec
    linarith
  apply Subtype.ext
  funext j
  by_cases hjlt : j.1 < k.1
  · let i : Fin p := ⟨j.1, by have := k.2; omega⟩
    have h := congrArg (fun u : StandardSimplex (p - 1) =>
        u (spatialIndex hp i)) hsp
    simpa [spatialPoint,
      spatialWeight_eq_of_lt hp k w i hjlt,
      spatialWeight_eq_of_lt hp k v i hjlt, i] using h
  by_cases hjpivot : j.1 = k.1
  · have hj : j = k.castSucc := Fin.ext hjpivot
    subst j
    have hpivot := congrArg (fun u : StandardSimplex (p - 1) =>
      u (spatialIndex hp k)) hsp
    simp [spatialPoint, spatialWeight_pivot, kp, hkp] at hpivot
    linarith
  by_cases hjupper : j.1 = k.1 + 1
  · have hj : j = kp := Fin.ext hjupper
    subst j
    exact hkp
  · have hjgt : k.1 + 1 < j.1 := by omega
    have hjle : j.1 ≤ p := Nat.le_of_lt_succ j.2
    let i : Fin p := ⟨j.1 - 1, by omega⟩
    have hi : k.1 < i.1 := by simp [i]; omega
    have h := congrArg (fun u : StandardSimplex (p - 1) =>
      u (spatialIndex hp i)) hsp
    have hjform : (⟨i.1 + 1, by have := i.2; omega⟩ : Fin (p + 1)) = j := by
      apply Fin.ext
      simp [i]
      omega
    simpa [spatialPoint, spatialWeight_eq_of_gt hp k w i hi,
      spatialWeight_eq_of_gt hp k v i hi, hjform] using h

/-- Every refined prism chart is injective. -/
theorem prism_chart_injective
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L) :
    Function.Injective (SubdivisionPrismCharts.chart hp N L q) := by
  intro x y hxy
  let ux : StandardSimplex p :=
    StandardSimplex.ofDelta (affineCompMap p L q.2 x)
  let uy : StandardSimplex p :=
    StandardSimplex.ofDelta (affineCompMap p L q.2 y)
  let sx := staircasePoint hp q.1.2 ux
  let sy := staircasePoint hp q.1.2 uy
  have ht : sx.2 = sy.2 := by
    simpa [SubdivisionPrismCharts.chart, ux, uy, sx, sy] using congrArg Prod.snd hxy
  have hsreal :
      RefinedAffineMap.chart hp N q.1.1 (StandardSimplex.toDelta sx.1) =
        RefinedAffineMap.chart hp N q.1.1 (StandardSimplex.toDelta sy.1) := by
    simpa [SubdivisionPrismCharts.chart, ux, uy, sx, sy] using congrArg Prod.fst hxy
  have hs : sx.1 = sy.1 := by
    have := refined_chart_injective hp N q.1.1 hsreal
    simpa using congrArg StandardSimplex.ofDelta this
  have hst : sx = sy := Prod.ext hs ht
  have hu : ux = uy := staircasePoint_injective hp q.1.2 hst
  have hdelta : affineCompMap p L q.2 x = affineCompMap p L q.2 y := by
    simpa [ux, uy] using congrArg StandardSimplex.toDelta hu
  exact affineCompMap_injective p L q.2 hdelta

/-- The vertices of one refined prism simplex are pairwise distinct. -/
theorem prism_vertex_injective
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L) :
    Function.Injective (SubdivisionPrismCharts.vertex hp N L q) := by
  intro i j hij
  have hstd :
      (SphereOddDegree.FiniteSimplex.vertex (S := Real) i : Delta p) =
        SphereOddDegree.FiniteSimplex.vertex (S := Real) j :=
    prism_chart_injective hp N L q hij
  by_contra hne
  have hi := congrArg (fun w : Delta p => w i) hstd
  simpa [SphereOddDegree.FiniteSimplex.vertex, hne] using hi

/-! ## Separation under the prime action -/

/-- A prime translate of a point in one strict simplex can lie in that same simplex only for the
identity group element. -/
theorem realizationPoint_orbit_separated
    (p : Nat) {d : Nat} (s : Simplex p d)
    (w v : StandardSimplex d) (g : PrimeSymmetry p)
    (h : g • s.realizationPoint w = s.realizationPoint v) :
    g = 1 := by
  classical
  have hnonempty : ∃ i : Fin (d + 1), w i ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hsum := w.sum_eq_one
    simp [hnone] at hsum
  obtain ⟨i, hi⟩ := hnonempty
  have hcoord : s.realizationPoint v (g • s i) ≠ 0 := by
    have hi' : s.realizationPoint w (s i) = w i := by
      simp [Simplex.realizationPoint, Simplex.chartWeight,
        s.vertex_injective.eq_iff]
    have hgcoord := congrArg (fun x : Realization p => x (g • s i)) h
    have hleft : (g • s.realizationPoint w) (g • s i) = w i := by
      rw [Realization.prime_smul_apply]
      simpa [Simplex.realizationPoint, Simplex.chartWeight,
        s.vertex_injective.eq_iff]
    change (g • s.realizationPoint w) (g • s i) =
      s.realizationPoint v (g • s i) at hgcoord
    rw [hleft] at hgcoord
    rw [← hgcoord]
    exact hi
  obtain ⟨j, hj⟩ :=
    s.exists_vertex_of_chartWeight_ne_zero v (g • s i) hcoord
  have hij : i = j := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hd := (s.properFace hlt).2
      have heq : (s j).dualDimension = (s i).dualDimension := by
        rw [hj]
        simp
      omega
    · have hd := (s.properFace hgt).2
      have heq : (s i).dualDimension = (s j).dualDimension := by
        rw [hj]
        simp
      omega
  subst j
  apply BarredPermutation.primeSymmetry_action_free p
  simpa using hj.symm

/-- No two different vertices of one refined prism simplex lie in the same prime orbit. -/
theorem prism_vertex_orbit_injective
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L)
    (g : PrimeSymmetry p) (i j : Fin (p + 1))
    (h : g • CylinderPoint.ofProd (SubdivisionPrismCharts.vertex hp N L q i) =
      CylinderPoint.ofProd (SubdivisionPrismCharts.vertex hp N L q j)) :
    g = 1 ∧ i = j := by
  have hspatial :
      g • (SubdivisionPrismCharts.vertex hp N L q i).1 =
        (SubdivisionPrismCharts.vertex hp N L q j).1 :=
    congrArg CylinderPoint.spatial h
  let s : Simplex p (p - 1) :=
    ReferenceAffineOrbitCount.topRepr hp q.1.1.1
  let ui : StandardSimplex p := StandardSimplex.ofDelta
    (affineCompMap p L q.2 (SphereOddDegree.FiniteSimplex.vertex (S := Real) i))
  let uj : StandardSimplex p := StandardSimplex.ofDelta
    (affineCompMap p L q.2 (SphereOddDegree.FiniteSimplex.vertex (S := Real) j))
  let sti := staircasePoint hp q.1.2 ui
  let stj := staircasePoint hp q.1.2 uj
  let rho' : Fin N → Equiv.Perm (Fin (p - 1 + 1)) :=
    fun t => Simplex.refinementIndexPerm (q.1.1.2 t)
  let wi : StandardSimplex (p - 1) := StandardSimplex.ofDelta
    (affineCompMap (p - 1) N rho' (StandardSimplex.toDelta sti.1))
  let wj : StandardSimplex (p - 1) := StandardSimplex.ofDelta
    (affineCompMap (p - 1) N rho' (StandardSimplex.toDelta stj.1))
  have hreal : g • s.realizationPoint wi = s.realizationPoint wj := by
    simpa [SubdivisionPrismCharts.vertex, SubdivisionPrismCharts.chart,
      RefinedAffineMap.chart, Simplex.refinedContinuousMap,
      Simplex.realizationContinuousMap, s, ui, uj, sti, stj, wi, wj] using hspatial
  have hg : g = 1 := realizationPoint_orbit_separated p s wi wj g hreal
  subst g
  have hv : SubdivisionPrismCharts.vertex hp N L q i =
      SubdivisionPrismCharts.vertex hp N L q j := by
    exact Prod.ext
      (congrArg CylinderPoint.spatial h)
      (congrArg CylinderPoint.time h)
  exact ⟨rfl, prism_vertex_injective hp N L q hv⟩

/-! ## Local scalar-site independence and assignment realization -/

/-- Parameter represented by one scalar coordinate at one local prism vertex. -/
noncomputable def localParameter
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L)
    (i : Fin (p + 1)) (j : Fin p) : Parameter hp N L :=
  Quotient.mk _ (sampleVertex hp N L (q, i), j)

/-- Scalar sites at the vertices of one fixed refined prism simplex give distinct orbit
parameters. -/
theorem localParameter_injective
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L) :
    Function.Injective (fun z : Fin (p + 1) × Fin p =>
      localParameter hp N L q z.1 z.2) := by
  intro a b hab
  have horbit :
      MulAction.orbitRel (PrimeSymmetry p)
        (ScalarSite hp N L)
        (sampleVertex hp N L (q, a.1), a.2)
        (sampleVertex hp N L (q, b.1), b.2) :=
    Quotient.exact hab
  rw [MulAction.orbitRel_apply] at horbit
  obtain ⟨g, hg⟩ := horbit
  have hx : g • sampleVertex hp N L (q, b.1) =
      sampleVertex hp N L (q, a.1) := congrArg Prod.fst hg
  have hj : g • b.2 = a.2 := congrArg Prod.snd hg
  have hpoint :
      g • CylinderPoint.ofProd (SubdivisionPrismCharts.vertex hp N L q b.1) =
        CylinderPoint.ofProd (SubdivisionPrismCharts.vertex hp N L q a.1) := by
    have := congrArg (globalPoint hp N L) hx
    simpa [globalPoint_smul, globalPoint_sampleVertex, slotPoint] using this
  obtain ⟨hg1, hij⟩ := prism_vertex_orbit_injective hp N L q g b.1 a.1 hpoint
  apply Prod.ext
  · exact hij.symm
  · simpa [hg1] using hj.symm

/-- Assignment obtained by prescribing arbitrary full coordinate vectors at the vertices of one
fixed refined prism simplex. -/
noncomputable def localRealizingAssignment
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L)
    (target : Fin (p + 1) → Fin p → Real) : Assignment hp N L :=
  fun u => ∑ z : Fin (p + 1) × Fin p,
    if u = localParameter hp N L q z.1 z.2 then target z.1 z.2 else 0

/-- The local realizing assignment takes the prescribed scalar values. -/
@[simp] theorem localRealizingAssignment_apply
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L)
    (target : Fin (p + 1) → Fin p → Real)
    (i : Fin (p + 1)) (j : Fin p) :
    localRealizingAssignment hp N L q target
        (localParameter hp N L q i j) = target i j := by
  classical
  unfold localRealizingAssignment
  rw [Finset.sum_eq_single (i, j)]
  · simp
  · intro z hz hzne
    have hparam : localParameter hp N L q i j ≠
        localParameter hp N L q z.1 z.2 := by
      intro h
      apply hzne
      exact localParameter_injective hp N L q h.symm
    simp [hparam]
  · simp

/-- The prescribed vectors are reconstructed at every vertex of the selected local simplex. -/
@[simp] theorem localVertexValue_localRealizingAssignment
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L)
    (target : Fin (p + 1) → Fin p → Real)
    (i : Fin (p + 1)) :
    localVertexValue hp N L
      (localRealizingAssignment hp N L q target) q i = target i := by
  funext j
  change localRealizingAssignment hp N L q target
      (localParameter hp N L q i j) = target i j
  exact localRealizingAssignment_apply hp N L q target i j

/-! ## Explicit witnesses for the two determinant families -/

/-- The fixed difference-coordinate labels are injective. -/
theorem coordinateLabel_injective
    (hp : Nat.Prime p) : Function.Injective (coordinateLabel hp) := by
  intro r s hrs
  have hval : (coordinateLabel hp r).1 = (coordinateLabel hp s).1 :=
    congrArg Fin.val hrs
  exact Fin.ext hval

/-- No fixed difference-coordinate label is the omitted label. -/
theorem coordinateLabel_ne_last
    (hp : Nat.Prime p) (r : Fin (p - 1)) :
    coordinateLabel hp r ≠ lastLabel hp := by
  intro h
  have := congrArg Fin.val h
  simp [coordinateLabel, lastLabel] at this
  omega

/-- Target values making the selected facet matrix lower triangular with diagonal one. -/
noncomputable def facetWitnessTarget
    (hp : Nat.Prime p) (k : Fin (p + 1)) :
    Fin (p + 1) → Fin p → Real :=
  fun v j =>
    if hv : ∃ c : Fin p, v = k.succAbove c then
      let c := Classical.choose hv
      Fin.lastCases 0
        (fun r => if j = coordinateLabel hp r then 1 else 0)
        (AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp c)
    else 0

/-- Values of the facet witness on retained vertices. -/
theorem facetWitnessTarget_succAbove
    (hp : Nat.Prime p) (k : Fin (p + 1))
    (c : Fin p) (j : Fin p) :
    facetWitnessTarget hp k (k.succAbove c) j =
      Fin.lastCases 0
        (fun r => if j = coordinateLabel hp r then 1 else 0)
        (AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp c) := by
  classical
  let hv : ∃ c' : Fin p, k.succAbove c = k.succAbove c' := ⟨c, rfl⟩
  rw [facetWitnessTarget, dif_pos hv]
  have hc : Classical.choose hv = c := by
    exact (Fin.succAbove_right_injective (p := k)) (Classical.choose_spec hv).symm
  simp []

/-- The real facet matrix produced by the witness assignment is triangular with diagonal one. -/
theorem facetMatrix_witness
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) (k : Fin (p + 1)) :
    AffinePositiveRayBoundary.VertexMap.facetMatrix hp
      (localVertexMap hp N L
        (localRealizingAssignment hp N L q (facetWitnessTarget hp k)) q) k =
      fun r c => Fin.lastCases (1 : Real)
        (fun s => Fin.lastCases 0 (fun t => if s = t then 1 else 0)
          (AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp c))
        (AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp r) := by
  ext r c
  unfold AffinePositiveRayBoundary.VertexMap.facetMatrix
  generalize hr : AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp r = r'
  refine Fin.lastCases ?_ (fun s => ?_) r'
  · simp
  · simp [AffinePositiveRayBoundary.VertexMap.deviation,
      AffinePositiveRayBoundary.VertexMap.facetValue, localVertexMap,
      facetWitnessTarget_succAbove]
    generalize hc : AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp c = c'
    refine Fin.lastCases ?_ (fun t => ?_) c'
    · simp []
    · have hinj : coordinateLabel hp s = coordinateLabel hp t ↔ s = t :=
        (coordinateLabel_injective hp).eq_iff
      have hlast : lastLabel hp ≠ coordinateLabel hp t :=
        (coordinateLabel_ne_last hp t).symm
      simp [hinj, hlast]

/-- The explicit facet witness has determinant one. -/
theorem facetDeterminant_witness
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) (k : Fin (p + 1)) :
    AffinePositiveRayBoundary.VertexMap.facetDeterminant hp
      (localVertexMap hp N L
        (localRealizingAssignment hp N L q (facetWitnessTarget hp k)) q) k = 1 := by
  rw [AffinePositiveRayBoundary.VertexMap.facetDeterminant,
    facetMatrix_witness]
  let M : Matrix (Fin p) (Fin p) Real := fun r c => Fin.lastCases (1 : Real)
    (fun s => Fin.lastCases 0 (fun t => if s = t then 1 else 0)
      (AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp c))
    (AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp r)
  change Matrix.det M = 1
  rw [Matrix.det_of_isLowerTriangular]
  · have hd : ∀ i, M i i = 1 := by
      intro i
      dsimp [M]
      generalize hi : AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp i = i'
      refine Fin.lastCases ?_ (fun s => ?_) i' <;> simp
    simp [hd]
  · intro i j hij
    dsimp [M]
    have hij' : i.val < j.val := hij
    generalize hi : AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp i = i'
    generalize hj : AffinePositiveRayBoundary.VertexMap.augmentedRowEquiv hp j = j'
    have hiv : i.val = i'.val := congrArg Fin.val hi
    have hjv : j.val = j'.val := congrArg Fin.val hj
    have hord : i'.val < j'.val := by omega
    revert hord
    refine Fin.lastCases (motive := fun x => x.val < j'.val →
        Fin.lastCases (1 : Real)
          (fun s => Fin.lastCases (0 : Real)
            (fun t => if s = t then (1 : Real) else 0) j') x = (0 : Real))
      ?_ (fun s hord => ?_) i'
    · intro hord
      exfalso
      exact (not_lt_of_ge (Fin.le_last j')) hord
    · rw [Fin.lastCases_castSucc]
      revert hord
      refine Fin.lastCases (motive := fun x => s.castSucc.val < x.val →
          Fin.lastCases (0 : Real) (fun t => if s = t then (1 : Real) else 0) x =
            (0 : Real))
        ?_ (fun t hord => ?_) j'
      · intro hord
        rw [Fin.lastCases_last]
      · rw [Fin.lastCases_castSucc]
        rw [ite_eq_right]
        intro hst
        exact (ne_of_lt hord) (congrArg Fin.val (congrArg Fin.castSucc hst))

/-- Target values making a selected codimension-two deviation matrix the identity. -/
noncomputable def codimTwoWitnessTarget
    (hp : Nat.Prime p) (f : CodimTwoFace p) :
    Fin (p + 1) → Fin p → Real :=
  fun v j =>
    if hv : ∃ i : Fin (p - 1), v = codimTwoVertex hp f i then
      if j = coordinateLabel hp (Classical.choose hv) then 1 else 0
    else 0

/-- Values of the codimension-two witness on retained vertices. -/
theorem codimTwoWitnessTarget_vertex
    (hp : Nat.Prime p) (f : CodimTwoFace p)
    (i : Fin (p - 1)) (j : Fin p) :
    codimTwoWitnessTarget hp f (codimTwoVertex hp f i) j =
      if j = coordinateLabel hp i then 1 else 0 := by
  classical
  let hv : ∃ i' : Fin (p - 1),
      codimTwoVertex hp f i = codimTwoVertex hp f i' := ⟨i, rfl⟩
  rw [codimTwoWitnessTarget, dif_pos hv]
  have hi : Classical.choose hv = i := by
    have houter := (Fin.succAbove_right_injective (p := f.1))
      (Classical.choose_spec hv).symm
    have hcast : (secondOmissionIndex hp f).succAbove (Classical.choose hv) =
        (secondOmissionIndex hp f).succAbove i := by
      exact (Fin.cast_inj _).mp houter
    exact (Fin.succAbove_right_injective (p := secondOmissionIndex hp f)) hcast
  simp [hi]

/-- The codimension-two witness evaluates to the identity deviation matrix. -/
theorem codimTwoDeviationMatrix_witness
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) (f : CodimTwoFace p) :
    codimTwoDeviationMatrix hp N L
      (localRealizingAssignment hp N L q (codimTwoWitnessTarget hp f)) q f = 1 := by
  ext r i
  simp [codimTwoDeviationMatrix,
    AffinePositiveRayBoundary.VertexMap.deviation,
    codimTwoWitnessTarget_vertex]
  have hinj : coordinateLabel hp r = coordinateLabel hp i ↔ r = i :=
    (coordinateLabel_injective hp).eq_iff
  have hlast : lastLabel hp ≠ coordinateLabel hp i :=
    (coordinateLabel_ne_last hp i).symm
  simp [Matrix.one_apply, hinj, hlast]

/-- Every facet determinant polynomial is nonzero. -/
theorem facetDeterminantPolynomial_ne_zero
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) (k : Fin (p + 1)) :
    facetDeterminantPolynomial hp N L q k ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval
      (localRealizingAssignment hp N L q (facetWitnessTarget hp k))) hzero
  rw [eval_facetDeterminantPolynomial, facetDeterminant_witness] at heval
  simpa using heval

/-- Every codimension-two minor polynomial is nonzero. -/
theorem codimTwoMinorPolynomial_ne_zero
    (hp : Nat.Prime p) (N L : Nat)
    (q : PrismCell hp N L) (f : CodimTwoFace p) :
    codimTwoMinorPolynomial hp N L q f ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval
      (localRealizingAssignment hp N L q (codimTwoWitnessTarget hp f))) hzero
  rw [eval_codimTwoMinorPolynomial, codimTwoDeviationMatrix_witness] at heval
  simpa using heval

/-- Every polynomial in the combined finite prism-genericity family is nonzero. -/
theorem genericityPolynomial_ne_zero
    (hp : Nat.Prime p) (N L : Nat) :
    ∀ i : GenericityIndex hp N L,
      genericityPolynomial hp N L i ≠ 0 := by
  intro i
  cases i with
  | inl qk =>
      exact facetDeterminantPolynomial_ne_zero hp N L qk.1 qk.2
  | inr qf =>
      exact codimTwoMinorPolynomial_ne_zero hp N L qf.1 qf.2

end EquivariantPrismGenericityNonzero

namespace EquivariantPrismGenericityPolynomials

/-- Public nontriviality theorem for the combined finite genericity family. -/
theorem genericityPolynomial_ne_zero
    (hp : Nat.Prime p) (N L : Nat) :
    ∀ i : GenericityIndex hp N L,
      genericityPolynomial hp N L i ≠ 0 :=
  EquivariantPrismGenericityNonzero.genericityPolynomial_ne_zero hp N L

end EquivariantPrismGenericityPolynomials
end FoxNeuwirthOrderComplex
end NRR
