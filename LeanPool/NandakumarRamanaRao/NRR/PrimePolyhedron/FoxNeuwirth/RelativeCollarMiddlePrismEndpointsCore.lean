/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarMiddlePrism
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EndpointFaceRefinement
/-!
# Canonical endpoint occurrences of the common-level middle prism

This module contains only the geometry of the lower and upper endpoint facets.  It is deliberately
independent of the stable endpoint interpolation and global Stokes modules, so both can use the same
endpoint cells without an import cycle.
-/

namespace NRR

open SphereOddDegree
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeCollarMiddlePrismEndpointsCore

open EndpointFaceRefinement
open SphereOddDegree.AffineBarycentricSubdivision
open EquivariantPrismVertexParameters
open EquivariantPrismNonhorizontalCancellation
open EquivariantPrismHorizontalEndpointIdentification
open ExplicitAffineRelativeCollar
open RelativeCollarMiddlePrism
open RefinedAffineMap
open SubdivisionPrismCharts

variable {p : Nat}

/-- Final staircase simplex.  Its final facet is the lower horizontal copy. -/
def lowerStaircaseIndex (hp : Nat.Prime p) : Fin p :=
  ⟨p - 1, by
    have hp0 := hp.pos
    omega⟩

@[simp] theorem lowerStaircaseIndex_val (hp : Nat.Prime p) :
    (lowerStaircaseIndex hp).1 = p - 1 := rfl

/-- In an unrefined staircase simplex, a facet is entirely at time zero only when it is the
final facet of the final staircase simplex. -/
theorem lowerStaircaseFacet_indices
    (hp : Nat.Prime p) (k : Fin p) (j : Fin (p + 1))
    (h : ∀ i : Fin p, staircaseTime k (j.succAbove i) = 0) :
    k = lowerStaircaseIndex hp ∧ j = Fin.last p := by
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ n =>
      have hj : j = Fin.last (n + 1) := by
        by_contra hne
        have hlast := h (Fin.last n)
        rw [Fin.succAbove_ne_last_last hne] at hlast
        have hlt : k.1 < (Fin.last (n + 1)).1 := by simpa using k.2
        rw [staircaseTime_upper k (Fin.last (n + 1)) hlt] at hlast
        exact (by decide : (1 : Fin 2) ≠ 0) hlast
      subst j
      have hlast := h (lowerStaircaseIndex hp)
      have hle : (lowerStaircaseIndex hp).1 ≤ k.1 := by
        by_contra hnot
        have hlt : k.1 <
            ((Fin.last (n + 1)).succAbove (lowerStaircaseIndex hp)).1 := by
          simpa using Nat.lt_of_not_ge hnot
        rw [staircaseTime_upper k _ hlt] at hlast
        exact (by decide : (1 : Fin 2) ≠ 0) hlast
      have hk : k = lowerStaircaseIndex hp := by
        apply Fin.ext
        simpa [lowerStaircaseIndex] using
          Nat.le_antisymm (Nat.le_of_lt_succ k.2) hle
      exact ⟨hk, rfl⟩

/-- In an unrefined staircase simplex, a facet is entirely at time one only when it is the initial
facet of the initial staircase simplex. -/
theorem upperStaircaseFacet_indices
    (hp : Nat.Prime p) (k : Fin p) (j : Fin (p + 1))
    (h : ∀ i : Fin p, staircaseTime k (j.succAbove i) = 1) :
    k = (⟨0, hp.pos⟩ : Fin p) ∧ j = 0 := by
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ n =>
      have hj : j = 0 := by
        by_contra hne
        have hzero := h (0 : Fin (n + 1))
        rw [Fin.succAbove_ne_zero_zero hne,
          staircaseTime_lower k 0 (Nat.zero_le _)] at hzero
        exact (by decide : (0 : Fin 2) ≠ 1) hzero
      subst j
      let i : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
      have hone := h i
      have hklt : k.1 < 1 := by
        by_contra hnot
        have hle : ((0 : Fin (n + 2)).succAbove i).1 ≤ k.1 := by
          simpa [i] using Nat.le_of_not_gt hnot
        rw [staircaseTime_lower k _ hle] at hone
        exact (by decide : (0 : Fin 2) ≠ 1) hone
      have hk : k = (⟨0, hp.pos⟩ : Fin (n + 1)) := by
        apply Fin.ext
        exact Nat.lt_one_iff.mp hklt
      exact ⟨hk, rfl⟩

/-- Refined prism cell whose endpoint face is the lower boundary simplex. -/
noncomputable def lowerPrismCell
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) : PrismCell hp N L :=
  ((q, lowerStaircaseIndex hp),
    liftBoundaryRefinementWord L (Fin.last p) eta)

/-- Refined prism cell whose endpoint face is the upper boundary simplex. -/
noncomputable def upperPrismCell
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) : PrismCell hp N L :=
  ((q, (⟨0, hp.pos⟩ : Fin p)), liftBoundaryRefinementWord L 0 eta)

/-- Canonical lower horizontal facet occurrence. -/
noncomputable def lowerOccurrence
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    (RelativeCollarMiddlePrism.cellSystem hp N L).FacetOccurrence :=
  (lowerPrismCell hp N L q eta, endpointOmittedPrime L (Fin.last p))

/-- Canonical upper horizontal facet occurrence. -/
noncomputable def upperOccurrence
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    (RelativeCollarMiddlePrism.cellSystem hp N L).FacetOccurrence :=
  (upperPrismCell hp N L q eta, endpointOmittedPrime L 0)


private theorem lowerOccurrenceFacetMap_eq_core
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap hp N L
        (lowerOccurrence hp N L q eta) =
      lowerEndpointMap (endpointSpatialMap hp N L q eta) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp.pos)
  change EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap hp N L
      (((q, lowerStaircaseIndex hp),
        liftBoundaryRefinementWord L (Fin.last (n + 1)) eta),
        endpointOmittedPrime L (Fin.last (n + 1))) = _
  rw [EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap_eq_iteratedFacetMap_succ]
  have hk : lowerStaircaseIndex hp = Fin.last n := by
    apply Fin.ext
    simp [lowerStaircaseIndex]
  have hface (j : Fin (n + 2)) :
      EquivariantPrismGlobalCancellation.facetFaceIndex hp j = j := by
    apply Fin.ext
    rfl
  funext x
  simp only [EquivariantPrismNonhorizontalCancellation.iteratedFacetMap, hface]
  rw [affineCompMap_liftBoundaryRefinementWord n L (Fin.last (n + 1)) eta x,
    hk]
  have h := congrFun
    (EquivariantPrismNonhorizontalCancellation.staircase_lower_face_eq n
      (RefinedAffineMap.chart hp N q))
    (affineCompMap n L eta x)
  rw [endpointSpatialMap_succ]
  exact h

private theorem upperOccurrenceFacetMap_eq_core
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap hp N L
        (upperOccurrence hp N L q eta) =
      upperEndpointMap (endpointSpatialMap hp N L q eta) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp.pos)
  change EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap hp N L
      (((q, (⟨0, hp.pos⟩ : Fin (n + 1))),
        liftBoundaryRefinementWord L 0 eta), endpointOmittedPrime L 0) = _
  rw [EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap_eq_iteratedFacetMap_succ]
  have hface (j : Fin (n + 2)) :
      EquivariantPrismGlobalCancellation.facetFaceIndex hp j = j := by
    apply Fin.ext
    rfl
  funext x
  simp only [EquivariantPrismNonhorizontalCancellation.iteratedFacetMap, hface]
  rw [affineCompMap_liftBoundaryRefinementWord n L 0 eta x]
  have h := congrFun
    (EquivariantPrismNonhorizontalCancellation.staircase_upper_face_eq n
      (RefinedAffineMap.chart hp N q))
    (affineCompMap n L eta x)
  rw [endpointSpatialMap_succ]
  exact h

/-- The lower occurrence is horizontal at time zero. -/
theorem lowerOccurrence_isLower
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    (RelativeCollarMiddlePrism.cellSystem hp N L).IsLowerFacetOccurrence
      (lowerOccurrence hp N L q eta) := by
  intro i
  have h := congrFun (lowerOccurrenceFacetMap_eq_core hp N L q eta)
    (stdSimplex.vertex (S := Real)
      (AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex i))
  rw [EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap_vertex] at h
  have ht := congrArg
    (fun z : Realization p × Set.Icc (0 : Real) 1 => z.2) h
  change (SubdivisionPrismCharts.vertex hp N L (lowerOccurrence hp N L q eta).1
    ((lowerOccurrence hp N L q eta).2.succAbove i)).2.1 = 0
  calc
    _ = (lowerEndpointMap (endpointSpatialMap hp N L q eta)
        (stdSimplex.vertex (AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex i))).2.1 :=
      congrArg Subtype.val ht
    _ = 0 := rfl

/-- The upper occurrence is horizontal at time one. -/
theorem upperOccurrence_isUpper
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    (RelativeCollarMiddlePrism.cellSystem hp N L).IsUpperFacetOccurrence
      (upperOccurrence hp N L q eta) := by
  intro i
  have h := congrFun (upperOccurrenceFacetMap_eq_core hp N L q eta)
    (stdSimplex.vertex (S := Real)
      (AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex i))
  rw [EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap_vertex] at h
  have ht := congrArg
    (fun z : Realization p × Set.Icc (0 : Real) 1 => z.2) h
  change (SubdivisionPrismCharts.vertex hp N L (upperOccurrence hp N L q eta).1
    ((upperOccurrence hp N L q eta).2.succAbove i)).2.1 = 1
  calc
    _ = (upperEndpointMap (endpointSpatialMap hp N L q eta)
        (stdSimplex.vertex (AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex i))).2.1 :=
      congrArg Subtype.val ht
    _ = 1 := rfl

/-- The actual lower occurrence map is the refined spatial endpoint map at time zero. -/
theorem lowerOccurrenceFacetMap_eq
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap hp N L
        (lowerOccurrence hp N L q eta) =
      lowerEndpointMap (endpointSpatialMap hp N L q eta) :=
  lowerOccurrenceFacetMap_eq_core hp N L q eta

/-- The actual upper occurrence map is the refined spatial endpoint map at time one. -/
theorem upperOccurrenceFacetMap_eq
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap hp N L
        (upperOccurrence hp N L q eta) =
      upperEndpointMap (endpointSpatialMap hp N L q eta) :=
  upperOccurrenceFacetMap_eq_core hp N L q eta

/-- Vertex-signature form of the lower endpoint identity. -/
theorem lowerOccurrence_facetSignature
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) (i : Fin p) :
    (RelativeCollarMiddlePrism.cellSystem hp N L).facetSignature
        (lowerOccurrence hp N L q eta) i =
      ExplicitAffineRelativeCollar.lowerCylinderPoint
        (RefinedAffineMap.vertex hp (N + L)
          (endpointTopCell hp N L q eta)
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  have hindex : AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex i =
      Fin.cast (Nat.sub_add_cancel hp.pos).symm i := by
    apply Fin.ext
    rfl
  have h := congrFun (lowerOccurrenceFacetMap_eq_core hp N L q eta)
    (stdSimplex.vertex (S := Real)
      (AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex i))
  rw [EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap_vertex] at h
  have hc := congrArg CylinderPoint.ofProd h
  convert hc using 1 <;> simp [RelativeCollarMiddlePrism.cellSystem,
    RelativeAffineCellSystem.facetSignature, RelativeCollarMiddlePrism.vertex,
    endpointSpatialMap_eq_chart, lowerEndpointMap,
    ExplicitAffineRelativeCollar.lowerCylinderPoint, RefinedAffineMap.vertex,
    hindex, CylinderPoint.ofProd]

/-- Vertex-signature form of the upper endpoint identity. -/
theorem upperOccurrence_facetSignature
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) (i : Fin p) :
    (RelativeCollarMiddlePrism.cellSystem hp N L).facetSignature
        (upperOccurrence hp N L q eta) i =
      ExplicitAffineRelativeCollar.upperCylinderPoint
        (RefinedAffineMap.vertex hp (N + L)
          (endpointTopCell hp N L q eta)
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  have hindex : AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex i =
      Fin.cast (Nat.sub_add_cancel hp.pos).symm i := by
    apply Fin.ext
    rfl
  have h := congrFun (upperOccurrenceFacetMap_eq_core hp N L q eta)
    (stdSimplex.vertex (S := Real)
      (AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex i))
  rw [EquivariantPrismNonhorizontalCancellation.occurrenceFacetMap_vertex] at h
  have hc := congrArg CylinderPoint.ofProd h
  convert hc using 1 <;> simp [RelativeCollarMiddlePrism.cellSystem,
    RelativeAffineCellSystem.facetSignature, RelativeCollarMiddlePrism.vertex,
    endpointSpatialMap_eq_chart, upperEndpointMap,
    ExplicitAffineRelativeCollar.upperCylinderPoint, RefinedAffineMap.vertex,
    hindex, CylinderPoint.ofProd]

end RelativeCollarMiddlePrismEndpointsCore
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
