/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismNonhorizontalCancellation
/-!
# Horizontal endpoint identification for the refined equivariant prism

The global prism boundary has already been split into lower-horizontal, upper-horizontal, and
nonhorizontal contributions, and the nonhorizontal term has been shown to vanish. This file
reindexes each horizontal contribution as the positive-ray count on the corresponding endpoint
triangulation.
-/

@[expose] public section

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismHorizontalEndpointIdentification

open AffinePositiveRayBoundary
open EquivariantPrismVertexParameters
open EquivariantPrismGenericityPolynomials
open EquivariantPrismGenericPerturbation
open EquivariantPrismGlobalCancellation
open EquivariantPrismNonhorizontalCancellation
open SubdivisionPrismCharts
open RefinedAffineMap

variable {p : Nat}

/-- Interpret a spatial refinement word on the definitionally different simplex-index type. -/
noncomputable def endpointRefinementWord
    (hp : Nat.Prime p) (L : Nat) (eta : RefinementWord p L) :
    Fin L → Equiv.Perm (Fin (p - 1 + 1)) := by
  simpa [Nat.sub_add_cancel hp.pos] using eta

/-- The transported generic subdivision sign is the Fox--Neuwirth subdivision sign. -/
theorem endpointRefinementWord_sign
    (hp : Nat.Prime p) (L : Nat) (eta : RefinementWord p L) :
    iteratedSign (n := p - 1) (ZMod p) L (endpointRefinementWord hp L eta) =
      subdivisionSign L eta := by
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ p =>
      simp [endpointRefinementWord, iteratedSign, subdivisionSign, permSignCoeff]

/-- Transport an endpoint top simplex to the cardinality expected by the boundary theorem. -/
noncomputable def endpointTopMap
    (hp : Nat.Prime p) {X : Type} (sigma : Delta p → X) :
    Delta (p - 1 + 1) → X := by
  rw [Nat.sub_add_cancel hp.pos]
  exact sigma

/-- Transported endpoint facet map with the natural `Fin (p+1)` indexing. -/
noncomputable def endpointIteratedFacetMap
    (hp : Nat.Prime p) {X : Type} (L : Nat) (sigma : Delta p → X)
    (rho : Fin L → Equiv.Perm (Fin (p + 1))) (k : Fin (p + 1)) :
    Delta (p - 1) → X := by
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ n => exact iteratedFacetMap n L sigma rho k

/-- Transported endpoint boundary map with the natural endpoint indexing. -/
noncomputable def endpointIteratedBoundaryMap
    (hp : Nat.Prime p) {X : Type} (L : Nat) (sigma : Delta p → X)
    (j : Fin (p + 1)) (eta : RefinementWord p L) : Delta (p - 1) → X := by
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ n => exact iteratedBoundaryMap n L sigma j eta

/-- Endpoint face sign with the natural `Fin (p+1)` indexing. -/
def endpointFaceSign (hp : Nat.Prime p) (j : Fin (p + 1)) : ZMod p := by
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ n => exact SimplicialChain.faceSign j

/-- Endpoint-index form of the iterated weighted-boundary theorem. This packages the single
`Fin p` versus `Fin (p - 1 + 1)` transport used by every horizontal endpoint calculation. -/
theorem endpoint_iterated_weighted_boundary
    {X : Type} (hp : Nat.Prime p) (L : Nat)
    (sigma : Delta p → X)
    (W : (Delta (p - 1) → X) → ZMod p) :
    (∑ rho : Fin L → Equiv.Perm (Fin (p + 1)),
      iteratedSign (ZMod p) L rho *
        ∑ k : Fin (p + 1),
          endpointFaceSign hp k *
            W (endpointIteratedFacetMap hp L sigma rho k)) =
      ∑ j : Fin (p + 1),
        endpointFaceSign hp j *
          ∑ eta : RefinementWord p L,
            subdivisionSign L eta *
              W (endpointIteratedBoundaryMap hp L sigma j eta) := by
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ p =>
      have h := iterated_weighted_boundary
        (R := ZMod (p + 1)) (X := X) p L sigma W
      simpa [endpointIteratedFacetMap, endpointIteratedBoundaryMap, endpointFaceSign,
        endpointRefinementWord_sign, iteratedSign, subdivisionSign, permSignCoeff] using h

/-- The spatial simplex obtained by applying the final `L` barycentric refinements to an already
level-`N` refined top cell. -/
noncomputable def endpointSpatialMap
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N)
    (eta : RefinementWord p L) :
    Delta (p - 1) → Realization p :=
  fun x => RefinedAffineMap.chart hp N q
    (affineCompMap (p - 1) L (endpointRefinementWord hp L eta) x)

/-- In successor dimension the transported endpoint spatial map is the original refinement
word applied in the original chart. -/
theorem endpointSpatialMap_succ
    (hp : Nat.Prime (p + 1)) (N L : Nat) (q : TopCell hp N)
    (eta : RefinementWord (p + 1) L) :
    endpointSpatialMap hp N L q eta = fun x =>
      RefinedAffineMap.chart hp N q (affineCompMap p L eta x) := by
  funext x
  simp [endpointSpatialMap, endpointRefinementWord]

/-- Positive-ray count represented by the lower horizontal boundary of a compatible prism
assignment. -/
noncomputable def lowerEndpointRefinedCount
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) : ZMod p :=
  ∑ q : TopCell hp N,
    ((PrimeOrbitCycle.orbitCycle hp).coefficient q.1 * subdivisionSign N q.2) *
      ∑ eta : RefinementWord p L,
        subdivisionSign L eta *
          realizedFacetWeight hp N L a
            (lowerEndpointMap (endpointSpatialMap hp N L q eta))

/-- Positive-ray count represented by the upper horizontal boundary of a compatible prism
assignment. -/
noncomputable def upperEndpointRefinedCount
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) : ZMod p :=
  ∑ q : TopCell hp N,
    ((PrimeOrbitCycle.orbitCycle hp).coefficient q.1 * subdivisionSign N q.2) *
      ∑ eta : RefinementWord p L,
        subdivisionSign L eta *
          realizedFacetWeight hp N L a
            (upperEndpointMap (endpointSpatialMap hp N L q eta))

/-- Weight which retains only lower-horizontal realized facets. -/
noncomputable def lowerHorizontalMapWeight
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) : ZMod p := by
  classical
  exact if MapIsLowerHorizontal tau then realizedFacetWeight hp N L a tau else 0

/-- Weight which retains only upper-horizontal realized facets. -/
noncomputable def upperHorizontalMapWeight
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) : ZMod p := by
  classical
  exact if MapIsUpperHorizontal tau then realizedFacetWeight hp N L a tau else 0

/-- Occurrence expansion of the lower-horizontal signature contribution. -/
theorem lowerHorizontalContribution_eq_occurrence_sum
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L) :
    lowerHorizontalContribution hp N L a =
      ∑ o : FacetOccurrence hp N L,
        occurrenceCoefficient hp N L o *
          lowerHorizontalMapWeight hp N L a (occurrenceFacetMap hp N L o) := by
  classical
  unfold lowerHorizontalContribution signatureBoundaryCoefficient
  calc
    (∑ s : FacetSignature hp N L,
        if IsLowerHorizontal hp N L s then
          (∑ o : FacetOccurrence hp N L,
            if facetSignature hp N L o = s then occurrenceCoefficient hp N L o else 0) *
              signatureWeight hp N L a s
        else 0) =
      ∑ s : FacetSignature hp N L,
        ∑ o : FacetOccurrence hp N L,
          if IsLowerHorizontal hp N L s then
            if facetSignature hp N L o = s then
              occurrenceCoefficient hp N L o * signatureWeight hp N L a s
            else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hlow : IsLowerHorizontal hp N L s
      · simp [hlow, Finset.sum_mul]
      · simp [hlow]
    _ = ∑ o : FacetOccurrence hp N L,
        ∑ s : FacetSignature hp N L,
          if IsLowerHorizontal hp N L s then
            if facetSignature hp N L o = s then
              occurrenceCoefficient hp N L o * signatureWeight hp N L a s
            else 0
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ o : FacetOccurrence hp N L,
        occurrenceCoefficient hp N L o *
          lowerHorizontalMapWeight hp N L a (occurrenceFacetMap hp N L o) := by
      apply Finset.sum_congr rfl
      intro o ho
      have hl : MapIsLowerHorizontal (occurrenceFacetMap hp N L o) ↔
          IsLowerHorizontal hp N L (facetSignature hp N L o) := by
        constructor <;> intro h i
        · have hi := h i
          rw [occurrenceFacetMap_vertex] at hi
          change (SubdivisionPrismCharts.vertex hp N L o.1 (o.2.succAbove i)).2.1 = 0
          exact hi
        · have hi := h i
          change (SubdivisionPrismCharts.vertex hp N L o.1 (o.2.succAbove i)).2.1 = 0 at hi
          rw [occurrenceFacetMap_vertex]
          exact hi
      unfold lowerHorizontalMapWeight
      rw [realizedFacetWeight_occurrence]
      by_cases hlow : IsLowerHorizontal hp N L (facetSignature hp N L o)
      · have hmap : MapIsLowerHorizontal (occurrenceFacetMap hp N L o) := hl.mpr hlow
        rw [Finset.sum_eq_single (facetSignature hp N L o)]
        · simp [hmap, hlow]
        · intro s hs hne
          simp [hne.symm]
        · simp
      · have hmap : ¬ MapIsLowerHorizontal (occurrenceFacetMap hp N L o) :=
          fun h => hlow (hl.mp h)
        rw [ite_eq_right hmap, mul_zero]
        apply Finset.sum_eq_zero
        intro s hs
        by_cases heq : facetSignature hp N L o = s
        · subst s
          simp [ hlow]
        · simp [heq]

/-- Occurrence expansion of the upper-horizontal signature contribution. -/
theorem upperHorizontalContribution_eq_occurrence_sum
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L) :
    upperHorizontalContribution hp N L a =
      ∑ o : FacetOccurrence hp N L,
        occurrenceCoefficient hp N L o *
          upperHorizontalMapWeight hp N L a (occurrenceFacetMap hp N L o) := by
  classical
  unfold upperHorizontalContribution signatureBoundaryCoefficient
  calc
    (∑ s : FacetSignature hp N L,
        if IsUpperHorizontal hp N L s then
          (∑ o : FacetOccurrence hp N L,
            if facetSignature hp N L o = s then occurrenceCoefficient hp N L o else 0) *
              signatureWeight hp N L a s
        else 0) =
      ∑ s : FacetSignature hp N L,
        ∑ o : FacetOccurrence hp N L,
          if IsUpperHorizontal hp N L s then
            if facetSignature hp N L o = s then
              occurrenceCoefficient hp N L o * signatureWeight hp N L a s
            else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hupp : IsUpperHorizontal hp N L s
      · simp [hupp, Finset.sum_mul]
      · simp [hupp]
    _ = ∑ o : FacetOccurrence hp N L,
        ∑ s : FacetSignature hp N L,
          if IsUpperHorizontal hp N L s then
            if facetSignature hp N L o = s then
              occurrenceCoefficient hp N L o * signatureWeight hp N L a s
            else 0
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ o : FacetOccurrence hp N L,
        occurrenceCoefficient hp N L o *
          upperHorizontalMapWeight hp N L a (occurrenceFacetMap hp N L o) := by
      apply Finset.sum_congr rfl
      intro o ho
      have hu : MapIsUpperHorizontal (occurrenceFacetMap hp N L o) ↔
          IsUpperHorizontal hp N L (facetSignature hp N L o) := by
        constructor <;> intro h i
        · have hi := h i
          rw [occurrenceFacetMap_vertex] at hi
          change (SubdivisionPrismCharts.vertex hp N L o.1 (o.2.succAbove i)).2.1 = 1
          exact hi
        · have hi := h i
          change (SubdivisionPrismCharts.vertex hp N L o.1 (o.2.succAbove i)).2.1 = 1 at hi
          rw [occurrenceFacetMap_vertex]
          exact hi
      unfold upperHorizontalMapWeight
      rw [realizedFacetWeight_occurrence]
      by_cases hupp : IsUpperHorizontal hp N L (facetSignature hp N L o)
      · have hmap : MapIsUpperHorizontal (occurrenceFacetMap hp N L o) := hu.mpr hupp
        rw [Finset.sum_eq_single (facetSignature hp N L o)]
        · simp [hmap, hupp]
        · intro s hs hne
          simp [hne.symm]
        · simp
      · have hmap : ¬ MapIsUpperHorizontal (occurrenceFacetMap hp N L o) :=
          fun h => hupp (hu.mp h)
        rw [ite_eq_right hmap, mul_zero]
        apply Finset.sum_eq_zero
        intro s hs
        by_cases heq : facetSignature hp N L o = s
        · subst s
          simp [ hupp]
        · simp [heq]

/-- Lower endpoint maps are lower-horizontal and not upper-horizontal. -/
theorem lowerEndpointMap_horizontal
    (hp : Nat.Prime p) (sigma : Delta (p - 1) → Realization p) :
    MapIsLowerHorizontal (lowerEndpointMap sigma) ∧
      ¬ MapIsUpperHorizontal (lowerEndpointMap sigma) := by
  constructor
  · intro i
    rfl
  · intro h
    let i : Fin p := ⟨0, hp.pos⟩
    have hi := h i
    norm_num [lowerEndpointMap] at hi

/-- Upper endpoint maps are upper-horizontal and not lower-horizontal. -/
theorem upperEndpointMap_horizontal
    (hp : Nat.Prime p) (sigma : Delta (p - 1) → Realization p) :
    MapIsUpperHorizontal (upperEndpointMap sigma) ∧
      ¬ MapIsLowerHorizontal (upperEndpointMap sigma) := by
  constructor
  · intro i
    rfl
  · intro h
    let i : Fin p := ⟨0, hp.pos⟩
    have hi := h i
    norm_num [upperEndpointMap] at hi

/-- An affine barycentric-subdivision chart sends a strictly positive simplex point to a
strictly positive simplex point. -/
theorem affineSubdivMap_pos_of_forall_pos
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1))) (x : Delta n)
    (hx : ∀ i, 0 < x i) (j : Fin (n + 1)) :
    0 < affineSubdivMap n pi x j := by
  let r := pi.symm j
  have hr := affineSubdivMap_cut_pos n pi x r (hx r)
  simpa [r] using hr

/-- Iterated affine barycentric-subdivision charts preserve strict positivity. -/
theorem affineCompMap_pos_of_forall_pos
    (n N : Nat) (rho : Fin N → Equiv.Perm (Fin (n + 1))) (x : Delta n)
    (hx : ∀ i, 0 < x i) (j : Fin (n + 1)) :
    0 < affineCompMap n N rho x j := by
  induction N generalizing x with
  | zero => simpa using hx j
  | succ N ih =>
      rw [affineCompMap_succ]
      change 0 < affineCompMap n N (fun i => rho i.castSucc)
        (affineSubdivMap n (rho (Fin.last N)) x) j
      apply ih (fun i => rho i.castSucc)
      intro i
      exact affineSubdivMap_pos_of_forall_pos n (rho (Fin.last N)) x hx i

/-- After at least one refinement, the last domain vertex maps to a strictly positive point. -/
theorem affineCompMap_succ_last_vertex_pos
    (n N : Nat) (rho : Fin (N + 1) → Equiv.Perm (Fin (n + 1)))
    (j : Fin (n + 1)) :
    0 < affineCompMap n (N + 1) rho
      (SphereOddDegree.FiniteSimplex.vertex (S := Real) (Fin.last n)) j := by
  rw [affineCompMap_succ]
  apply affineCompMap_pos_of_forall_pos n N (fun i => rho i.castSucc)
  intro i
  change 0 < affineSubdivMap n (rho (Fin.last N))
    (SphereOddDegree.FiniteSimplex.vertex (S := Real) (Fin.last n)) i
  rw [affineSubdivMap_vertex, prefixBarycenter_apply]
  have hi : i ∈ prefixSet n (rho (Fin.last N)) (Fin.last n) := by
    rw [mem_prefixSet]
    exact Fin.le_last _
  rw [ite_eq_left hi]
  positivity

/-- A strictly positive barycentric point has strictly interior staircase time. -/
theorem genericStaircaseIntervalPoint_pos_lt_one
    (n : Nat) (k : Fin (n + 1)) (w : Delta (n + 1))
    (hw : ∀ i, 0 < w i) :
    0 < (genericStaircaseIntervalPoint n k w).1 ∧
      (genericStaircaseIntervalPoint n k w).1 < 1 := by
  let f : Fin (n + 2) → Real := fun j =>
    if genericStaircaseTime k j = 1 then w j else 0
  have hf_nonneg : ∀ j, 0 ≤ f j := by
    intro j
    dsimp [f]
    split_ifs
    · exact w.2.1 j
    · exact le_rfl
  have hlast : f (Fin.last (n + 1)) = w (Fin.last (n + 1)) := by
    dsimp [f, genericStaircaseTime]
    have hnle : ¬ n + 1 ≤ k.1 := by omega
    simp [hnle]
  have hzero : f 0 = 0 := by
    simp [f, genericStaircaseTime]
  have hsum : (genericStaircaseIntervalPoint n k w).1 = ∑ j, f j := rfl
  constructor
  · rw [hsum]
    have hle : f (Fin.last (n + 1)) ≤ ∑ j, f j :=
      Finset.single_le_sum (fun j _ => hf_nonneg j) (Finset.mem_univ _)
    rw [hlast] at hle
    exact lt_of_lt_of_le (hw _) hle
  · rw [hsum]
    have hdecomp : (∑ j, w j) = (∑ j, f j) + ∑ j, (w j - f j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have htotal : (∑ j, w j) = 1 := w.2.2
    have hcomp_nonneg : 0 ≤ ∑ j, (w j - f j) := by
      apply Finset.sum_nonneg
      intro j hj
      dsimp [f]
      split_ifs <;> simp []
    have hcomp_pos : 0 < ∑ j, (w j - f j) := by
      have hterm : ∀ j : Fin (n + 2), 0 ≤ w j - f j := by
        intro j
        dsimp [f]
        split_ifs <;> simp []
      have hle : w 0 - f 0 ≤ ∑ j : Fin (n + 2), (w j - f j) :=
        Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ 0)
      rw [hzero, sub_zero] at hle
      exact lt_of_lt_of_le (hw 0) hle
    linarith

/-- Transporting a strictly positive simplex point preserves strict positivity. -/
theorem deltaCast_pos_of_forall_pos {m n : Nat} (e : m = n) (x : Delta m)
    (hx : ∀ i, 0 < x i) (j : Fin (n + 1)) :
    0 < deltaCast e x j := by
  subst n
  exact hx j

/-- A refined staircase side map is never lower-horizontal. -/
theorem refinedSidePrismMap_not_lowerHorizontal
    (hp : Nat.Prime (p + 1)) (N : Nat) (orbit : TopCell hp N)
    (r : Fin (p + 1)) (h : Fin p)
    (L : Nat) (eta : Fin L → Equiv.Perm (Fin (p + 1))) :
    ¬ MapIsLowerHorizontal (fun x =>
      sidePrismMap p (RefinedAffineMap.chart hp N orbit) r h
        (affineCompMap p L eta x)) := by
  intro hlower
  let i : Fin (p + 1) := Fin.last p
  have hi := hlower i
  cases L with
  | zero =>
      have hp0 : 0 < p := Fin.pos_iff_nonempty.mpr ⟨h⟩
      simp only [sidePrismMap] at hi
      simp [staircasePrismMap, affineCompMap, i, VertexMap.facetCoordinateIndex,
        genericStaircaseIntervalPoint, genericStaircaseTime, Pi.single_apply] at hi
      have hsum :
          (∑ x : Fin ((p - 1) + 2),
            if h.1 < x.1 then
              if x = Fin.last ((p - 1) + 1) then (1 : Real) else 0
            else 0) = 1 := by
        rw [Finset.sum_eq_single (Fin.last ((p - 1) + 1))]
        · simp [Fin.last, Nat.sub_add_cancel hp0, h.isLt]
        · intro x hx hne
          simp [hne]
        · simp
      linarith
  | succ L =>
      have hw : ∀ j : Fin (p + 1),
          0 < affineCompMap p (L + 1) eta
            (SphereOddDegree.FiniteSimplex.vertex (S := Real) (Fin.last p)) j :=
        affineCompMap_succ_last_vertex_pos p L eta
      have hp0 : 0 < p := Fin.pos_iff_nonempty.mpr ⟨h⟩
      let h' : Fin ((p - 1) + 1) := Fin.cast (by omega) h
      let x : Delta p := affineCompMap p (L + 1) eta
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) (Fin.last p))
      let e : p = (p - 1) + 1 := (Nat.sub_add_cancel hp0).symm
      let w : Delta ((p - 1) + 1) := deltaCast e x
      have hw' : ∀ j, 0 < w j := by
        intro j
        exact deltaCast_pos_of_forall_pos e x hw j
      have ht := genericStaircaseIntervalPoint_pos_lt_one (p - 1) h' w hw'
      simp only [sidePrismMap] at hi
      change (genericStaircaseIntervalPoint (p - 1) h' w).1 = 0 at hi
      exact (ne_of_gt ht.1) hi

/-- A refined staircase side map is never upper-horizontal. -/
theorem refinedSidePrismMap_not_upperHorizontal
    (hp : Nat.Prime (p + 1)) (N : Nat) (orbit : TopCell hp N)
    (r : Fin (p + 1)) (h : Fin p)
    (L : Nat) (eta : Fin L → Equiv.Perm (Fin (p + 1))) :
    ¬ MapIsUpperHorizontal (fun x =>
      sidePrismMap p (RefinedAffineMap.chart hp N orbit) r h
        (affineCompMap p L eta x)) := by
  intro hupper
  cases L with
  | zero =>
      let i : Fin (p + 1) := ⟨0, Nat.succ_pos p⟩
      have hi := hupper i
      simp [sidePrismMap, staircasePrismMap, affineCompMap, i,
        VertexMap.facetCoordinateIndex, genericStaircaseIntervalPoint,
        genericStaircaseTime, Pi.single_apply] at hi
      have hzero :
          (∑ x : Fin ((p - 1) + 2),
            if h.1 < x.1 then if x = 0 then (1 : Real) else 0 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        by_cases hlt : h.1 < x.1
        · have hx0 : x ≠ 0 := by
            intro heq
            subst x
            simp at hlt
          simp [hlt, hx0]
        · simp [hlt]
      linarith
  | succ L =>
      let i : Fin (p + 1) := Fin.last p
      have hi := hupper i
      have hw : ∀ j : Fin (p + 1),
          0 < affineCompMap p (L + 1) eta
            (SphereOddDegree.FiniteSimplex.vertex (S := Real) (Fin.last p)) j :=
        affineCompMap_succ_last_vertex_pos p L eta
      have hp0 : 0 < p := Fin.pos_iff_nonempty.mpr ⟨h⟩
      let h' : Fin ((p - 1) + 1) := Fin.cast (by omega) h
      let x : Delta p := affineCompMap p (L + 1) eta
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) (Fin.last p))
      let e : p = (p - 1) + 1 := (Nat.sub_add_cancel hp0).symm
      let w : Delta ((p - 1) + 1) := deltaCast e x
      have hw' : ∀ j, 0 < w j := fun j => deltaCast_pos_of_forall_pos e x hw j
      have ht := genericStaircaseIntervalPoint_pos_lt_one (p - 1) h' w hw'
      simp only [sidePrismMap] at hi
      change (genericStaircaseIntervalPoint (p - 1) h' w).1 = 1 at hi
      exact (ne_of_lt ht.2) hi
/-- The lower horizontal contribution is the negative of the refined lower endpoint count. -/
theorem lowerHorizontalContribution_eq_neg_lowerEndpointRefinedCount
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L) :
    lowerHorizontalContribution hp N L a =
      -lowerEndpointRefinedCount hp N L a := by
  classical
  rw [lowerHorizontalContribution_eq_occurrence_sum]
  rw [Fintype.sum_prod_type]
  simp only [occurrenceCoefficient, prismCoefficient, prismSign,
    Int.cast_mul, Int.cast_prod]
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ p =>
    conv_lhs =>
      enter [2, cell, 2, j]
      rw [occurrenceFacetMap_eq_iteratedFacetMap_succ]
    have hfacetFaceIndex (j : Fin (p + 2)) : facetFaceIndex hp j = j := by
      apply Fin.ext
      rfl
    simp_rw [hfacetFaceIndex]
    simp only [subdivisionSign, staircaseSign]
    ring_nf
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_prod_type]
    ring_nf
    conv_lhs =>
      enter [2, orbit, 2, spatial, 2, rho, 2, j]
      rw [mul_assoc]
    conv_lhs =>
      enter [2, orbit, 2, spatial, 2, rho]
      rw [← Finset.mul_sum, mul_assoc]
    conv_lhs =>
      enter [2, orbit, 2, spatial]
      rw [← Finset.mul_sum]
    conv_lhs =>
      enter [2, orbit, 2, spatial, 2]
      change ∑ rho, iteratedSign (ZMod (p + 1)) L rho *
        ∑ j, SimplicialChain.faceSign j *
          lowerHorizontalMapWeight hp N L a
            (iteratedFacetMap p L
              (staircasePrismMap p (RefinedAffineMap.chart hp N orbit) spatial) rho j)
      rw [iterated_weighted_boundary
        (R := ZMod (p + 1))
        (X := Realization (p + 1) × Set.Icc (0 : Real) 1)
        (n := p) (N := L)]
    ring_nf
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
    conv_lhs =>
      enter [2, orbit, 2, spatial]
      rw [mul_assoc]
    conv_lhs =>
      enter [2, orbit]
      rw [← Finset.mul_sum]
    conv_lhs =>
      enter [2, orbit, 2]
      rw [show
        (∑ spatial : Fin (p + 1), ((-1 : ZMod (p + 1)) ^ spatial.1) *
          ∑ j : Fin (p + 2), SimplicialChain.faceSign j *
            ∑ eta : Fin L → Equiv.Perm (Fin (p + 1)),
              iteratedSign (ZMod (p + 1)) L eta *
                lowerHorizontalMapWeight hp N L a
                  (iteratedBoundaryMap p L
                    (staircasePrismMap p (RefinedAffineMap.chart hp N orbit) spatial) j eta)) =
        ∑ eta : Fin L → Equiv.Perm (Fin (p + 1)),
          iteratedSign (ZMod (p + 1)) L eta *
            ∑ spatial : Fin (p + 1), ((-1 : ZMod (p + 1)) ^ spatial.1) *
              ∑ j : Fin (p + 2), SimplicialChain.faceSign j *
                lowerHorizontalMapWeight hp N L a
                  (fun x => staircasePrismMap p
                    (RefinedAffineMap.chart hp N orbit) spatial
                    (cofacePoint p j (affineCompMap p L eta x))) by
          simp_rw [Finset.mul_sum]
          conv_lhs =>
            enter [2, spatial]
            rw [Finset.sum_comm]
          rw [Finset.sum_comm]
          ac_rfl]
    conv_lhs =>
      enter [2, orbit, 2]
      enter [2, eta, 2]
      rw [staircase_weighted_boundary
        (W := fun tau => lowerHorizontalMapWeight hp N L a
          (fun x => tau (affineCompMap p L eta x)))]
    simp only [lowerHorizontalMapWeight,
      refinedSidePrismMap_not_lowerHorizontal hp N _ _ _ L _, ite_false]
    simp only [MapIsLowerHorizontal,
      lowerEndpointMap, upperEndpointMap]
    simp only [iteratedSign,  permSignCoeff]
    have hlower (sigma : Delta p → Realization (p + 1)) :
        realizedFacetWeight hp N L a (lowerEndpointMap sigma) =
          realizedFacetWeight hp N L a (fun x => (sigma x, ⟨0, by constructor <;> norm_num⟩)) := rfl
    simp [lowerEndpointRefinedCount, endpointSpatialMap_succ, hlower,
      subdivisionSign]
    rfl
/-- The upper horizontal contribution is the refined upper endpoint count. -/
theorem upperHorizontalContribution_eq_upperEndpointRefinedCount
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L) :
    upperHorizontalContribution hp N L a =
      upperEndpointRefinedCount hp N L a := by
  classical
  rw [upperHorizontalContribution_eq_occurrence_sum]
  rw [Fintype.sum_prod_type]
  simp only [occurrenceCoefficient, prismCoefficient, prismSign,
    Int.cast_mul, Int.cast_prod]
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ p =>
    conv_lhs =>
      enter [2, cell, 2, j]
      rw [occurrenceFacetMap_eq_iteratedFacetMap_succ]
    have hfacetFaceIndex (j : Fin (p + 2)) : facetFaceIndex hp j = j := by
      apply Fin.ext
      rfl
    simp_rw [hfacetFaceIndex]
    simp only [subdivisionSign, staircaseSign]
    ring_nf
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_prod_type]
    ring_nf
    conv_lhs =>
      enter [2, orbit, 2, spatial, 2, rho, 2, j]
      rw [mul_assoc]
    conv_lhs =>
      enter [2, orbit, 2, spatial, 2, rho]
      rw [← Finset.mul_sum, mul_assoc]
    conv_lhs =>
      enter [2, orbit, 2, spatial]
      rw [← Finset.mul_sum]
    conv_lhs =>
      enter [2, orbit, 2, spatial, 2]
      change ∑ rho, iteratedSign (ZMod (p + 1)) L rho *
        ∑ j, SimplicialChain.faceSign j *
          upperHorizontalMapWeight hp N L a
            (iteratedFacetMap p L
              (staircasePrismMap p (RefinedAffineMap.chart hp N orbit) spatial) rho j)
      rw [iterated_weighted_boundary
        (R := ZMod (p + 1))
        (X := Realization (p + 1) × Set.Icc (0 : Real) 1)
        (n := p) (N := L)]
    ring_nf
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
    conv_lhs =>
      enter [2, orbit, 2, spatial]
      rw [mul_assoc]
    conv_lhs =>
      enter [2, orbit]
      rw [← Finset.mul_sum]
    conv_lhs =>
      enter [2, orbit, 2]
      rw [show
        (∑ spatial : Fin (p + 1), ((-1 : ZMod (p + 1)) ^ spatial.1) *
          ∑ j : Fin (p + 2), SimplicialChain.faceSign j *
            ∑ eta : Fin L → Equiv.Perm (Fin (p + 1)),
              iteratedSign (ZMod (p + 1)) L eta *
                upperHorizontalMapWeight hp N L a
                  (iteratedBoundaryMap p L
                    (staircasePrismMap p (RefinedAffineMap.chart hp N orbit) spatial) j eta)) =
        ∑ eta : Fin L → Equiv.Perm (Fin (p + 1)),
          iteratedSign (ZMod (p + 1)) L eta *
            ∑ spatial : Fin (p + 1), ((-1 : ZMod (p + 1)) ^ spatial.1) *
              ∑ j : Fin (p + 2), SimplicialChain.faceSign j *
                upperHorizontalMapWeight hp N L a
                  (fun x => staircasePrismMap p
                    (RefinedAffineMap.chart hp N orbit) spatial
                    (cofacePoint p j (affineCompMap p L eta x))) by
          simp_rw [Finset.mul_sum]
          conv_lhs =>
            enter [2, spatial]
            rw [Finset.sum_comm]
          rw [Finset.sum_comm]
          ac_rfl]
    conv_lhs =>
      enter [2, orbit, 2]
      enter [2, eta, 2]
      rw [staircase_weighted_boundary
        (W := fun tau => upperHorizontalMapWeight hp N L a
          (fun x => tau (affineCompMap p L eta x)))]
    simp only [upperHorizontalMapWeight,
      refinedSidePrismMap_not_upperHorizontal hp N _ _ _ L _, ite_false]
    simp only [ MapIsUpperHorizontal,
      lowerEndpointMap, upperEndpointMap]
    simp only [iteratedSign,  permSignCoeff]
    have hupper (sigma : Delta p → Realization (p + 1)) :
        realizedFacetWeight hp N L a (upperEndpointMap sigma) =
          realizedFacetWeight hp N L a (fun x => (sigma x, ⟨1, by constructor <;> norm_num⟩)) := rfl
    simp [upperEndpointRefinedCount, endpointSpatialMap_succ, hupper,
      subdivisionSign]
    rfl

/-- Horizontal balance identifies the two refined endpoint counts represented by any compatible
assignment. -/
theorem lowerEndpointRefinedCount_eq_upperEndpointRefinedCount
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L)
    (hgp : ∀ q : PrismCell hp N L,
      AffinePositiveRayBoundary.VertexMap.GeneralPosition hp
        (localVertexMap hp N L a q)) :
    lowerEndpointRefinedCount hp N L a =
      upperEndpointRefinedCount hp N L a := by
  have hside :=
    EquivariantPrismNonhorizontalCancellation.nonhorizontalContribution_eq_zero_core
      hp N L a
  have hbalance :=
    lowerHorizontalContribution_eq_neg_upper_of_nonhorizontal_eq_zero
      hp N L a hgp hside
  rw [lowerHorizontalContribution_eq_neg_lowerEndpointRefinedCount,
    upperHorizontalContribution_eq_upperEndpointRefinedCount] at hbalance
  exact neg_injective hbalance

/-- Endpoint-count equality specialized to the compatible generic perturbation. -/
theorem Result.lowerEndpointRefinedCount_eq_upperEndpointRefinedCount
    (hp : Nat.Prime p) (N L : Nat)
    {F0 F1 : EquivariantCoordinateHomotopy.ZeroFreeMap hp}
    (H : EquivariantCoordinateHomotopy.ZeroFreeHomotopy hp F0 F1)
    (m : Real) (R : Result hp N L H m) :
    lowerEndpointRefinedCount hp N L R.assignment =
      upperEndpointRefinedCount hp N L R.assignment :=
  lowerEndpointRefinedCount_eq_upperEndpointRefinedCount
    hp N L R.assignment R.generalPosition

end EquivariantPrismHorizontalEndpointIdentification
end FoxNeuwirthOrderComplex
end NRR
