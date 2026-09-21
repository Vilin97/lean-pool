/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarMiddlePrism
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismNonhorizontalCancellation
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismHorizontalEndpointIdentification
/-!
# Pointwise boundary formula for the common-level middle prism

The older prism development proves cancellation only after weighting facets by the positive-ray
index of a compatible assignment.  An explicit relative collar needs the stronger pointwise chain
statement: the signed incidence of every prime-orbit facet equals upper boundary coefficient minus
lower boundary coefficient.

This module extracts the underlying weighted boundary theorem for an arbitrary prime-invariant
facet-map weight.  Applying it to the characteristic function of one prime-orbit facet gives the
required pointwise incidence formula.  The resulting object is a genuine
`FoxNeuwirthRelativeAffineCollar` at the common endpoint level `N + L`.
-/

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeCollarMiddlePrismBoundary

open ExplicitAffineRelativeCollar
open RelativeCollarMiddlePrism
open EquivariantPrismVertexParameters
open EquivariantPrismGlobalCancellation
open EquivariantPrismNonhorizontalCancellation
open EquivariantPrismHorizontalEndpointIdentification
open SubdivisionPrismCharts
open RefinedAffineMap

variable {p : Nat}

/-- The concrete middle-prism cell system. -/
noncomputable abbrev Cells (hp : Nat.Prime p) (N L : Nat) :=
  RelativeCollarMiddlePrism.cellSystem hp N L

/-- Ordered geometric vertices of an arbitrary affine facet map. -/
def mapVertexSignature
    (hp : Nat.Prime p)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) :
    Fin p → CylinderPoint p :=
  fun i => CylinderPoint.ofProd (tau (stdSimplex.vertex (S := Real) ((AffinePositiveRayBoundary.VertexMap.facetIndexEquiv hp).symm i)))

/-- Prime translation of an affine facet map. -/
def translateFacetMap
    (hp : Nat.Prime p) (g : PrimeSymmetry hp)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) :
    Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1 :=
  fun x => (g • (tau x).1, (tau x).2)

@[simp] theorem mapVertexSignature_translateFacetMap
    (hp : Nat.Prime p) (g : PrimeSymmetry hp)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) :
    mapVertexSignature hp (translateFacetMap hp g tau) =
      fun i => g • mapVertexSignature hp tau i := by
  funext i
  rfl

/-- The old affine occurrence map and the new explicit-cell occurrence have the same ordered
geometric vertex signature. -/
theorem mapVertexSignature_occurrenceFacetMap
    (hp : Nat.Prime p) (N L : Nat)
    (o : (Cells hp N L).FacetOccurrence) :
    mapVertexSignature hp (occurrenceFacetMap hp N L o) =
      (Cells hp N L).facetSignature o := by
  funext i
  have hi :
      (AffinePositiveRayBoundary.VertexMap.facetIndexEquiv hp).symm i =
        AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex i := by
    apply (AffinePositiveRayBoundary.VertexMap.facetIndexEquiv hp).injective
    simp
  rw [show mapVertexSignature hp (occurrenceFacetMap hp N L o) i =
      CylinderPoint.ofProd
        (occurrenceFacetMap hp N L o
          (stdSimplex.vertex (S := Real)
            (AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex i))) by
      simp [mapVertexSignature, hi]]
  rw [occurrenceFacetMap_vertex]
  rfl

/-- Characteristic weight of one ordered prime-orbit facet.  It is defined on all affine facet maps
so it can be used in the generic staircase and subdivision boundary identities. -/
noncomputable def facetOrbitIndicator
    (hp : Nat.Prime p) (N L : Nat)
    (s : (Cells hp N L).Facet)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) : ZMod p := by
  classical
  exact if ∃ o : (Cells hp N L).FacetOccurrence,
      (Cells hp N L).facetClass o = s ∧
        ∃ g : PrimeSymmetry hp,
          mapVertexSignature hp tau =
            fun i => g • (Cells hp N L).facetSignature o i
  then 1 else 0

/-- The facet-orbit characteristic weight is invariant under simultaneous prime translation. -/
theorem facetOrbitIndicator_translate
    (hp : Nat.Prime p) (N L : Nat)
    (s : (Cells hp N L).Facet)
    (g : PrimeSymmetry hp)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) :
    facetOrbitIndicator hp N L s (translateFacetMap hp g tau) =
      facetOrbitIndicator hp N L s tau := by
  classical
  unfold facetOrbitIndicator
  have hiff :
      (∃ o : (Cells hp N L).FacetOccurrence,
          (Cells hp N L).facetClass o = s ∧
            ∃ h : PrimeSymmetry hp,
              mapVertexSignature hp (translateFacetMap hp g tau) =
                fun i => h • (Cells hp N L).facetSignature o i) ↔
      (∃ o : (Cells hp N L).FacetOccurrence,
          (Cells hp N L).facetClass o = s ∧
            ∃ h : PrimeSymmetry hp,
              mapVertexSignature hp tau =
                fun i => h • (Cells hp N L).facetSignature o i) := by
    constructor
    · rintro ⟨o, ho, h, hh⟩
      refine ⟨o, ho, g⁻¹ * h, ?_⟩
      funext i
      have hi := congrFun hh i
      simp only [mapVertexSignature_translateFacetMap] at hi
      have := congrArg (fun z : CylinderPoint p => g⁻¹ • z) hi
      simpa [mul_smul] using this
    · rintro ⟨o, ho, h, hh⟩
      refine ⟨o, ho, g * h, ?_⟩
      funext i
      simp [mapVertexSignature_translateFacetMap, hh, mul_smul]
  simp only [hiff]

open scoped Classical in
/-- On an actual occurrence, the orbit characteristic weight is exactly the Kronecker delta of its
quotient facet class. -/
theorem facetOrbitIndicator_occurrence
    (hp : Nat.Prime p) (N L : Nat)
    (s : (Cells hp N L).Facet)
    (o : (Cells hp N L).FacetOccurrence) :
    facetOrbitIndicator hp N L s (occurrenceFacetMap hp N L o) =
      if (Cells hp N L).facetClass o = s then 1 else 0 := by
  classical
  by_cases hos : (Cells hp N L).facetClass o = s
  · have hex : ∃ o' : (Cells hp N L).FacetOccurrence,
        (Cells hp N L).facetClass o' = s ∧
          ∃ g : PrimeSymmetry hp,
            mapVertexSignature hp (occurrenceFacetMap hp N L o) =
              fun i => g • (Cells hp N L).facetSignature o' i := by
      refine ⟨o, hos, 1, ?_⟩
      simpa using mapVertexSignature_occurrenceFacetMap hp N L o
    unfold facetOrbitIndicator
    rw [if_pos hex, if_pos hos]
  · have hnot : ¬ ∃ o' : (Cells hp N L).FacetOccurrence,
        (Cells hp N L).facetClass o' = s ∧
          ∃ g : PrimeSymmetry hp,
            mapVertexSignature hp (occurrenceFacetMap hp N L o) =
              fun i => g • (Cells hp N L).facetSignature o' i := by
      rintro ⟨o', ho', g, hg⟩
      apply hos
      have hsig : (fun i => g • (Cells hp N L).facetSignature o' i) =
          (Cells hp N L).facetSignature o := by
        rw [← mapVertexSignature_occurrenceFacetMap hp N L o]
        exact hg.symm
      have hclass : (Cells hp N L).facetClass o' =
          (Cells hp N L).facetClass o :=
        Quotient.sound ⟨g, hsig⟩
      exact hclass.symm.trans ho'
    unfold facetOrbitIndicator
    rw [if_neg hnot, if_neg hos]

/-! ## Generic weighted boundary formulas -/

/-- Keep only lower-horizontal affine facet maps. -/
noncomputable def lowerMapWeight
    (W : (Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) → ZMod p)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) : ZMod p := by
  classical
  exact if MapIsLowerHorizontal tau then W tau else 0

/-- Keep only upper-horizontal affine facet maps. -/
noncomputable def upperMapWeight
    (W : (Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) → ZMod p)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) : ZMod p := by
  classical
  exact if MapIsUpperHorizontal tau then W tau else 0

/-- Keep only nonhorizontal affine facet maps. -/
noncomputable def sideMapWeight
    (W : (Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) → ZMod p)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) : ZMod p := by
  classical
  exact if ¬ MapIsLowerHorizontal tau ∧ ¬ MapIsUpperHorizontal tau then W tau else 0

/-- A facet map cannot be both lower and upper horizontal. -/
theorem not_lower_and_upper_map
    (hp : Nat.Prime p)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) :
    ¬ (MapIsLowerHorizontal tau ∧ MapIsUpperHorizontal tau) := by
  rintro ⟨hl, hu⟩
  let i : Fin p := ⟨0, hp.pos⟩
  have h0 := hl i
  have h1 := hu i
  linarith

/-- Every facet-map weight splits into lower, upper, and nonhorizontal parts. -/
theorem lower_add_upper_add_side
    (hp : Nat.Prime p)
    (W : (Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) → ZMod p)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) :
    lowerMapWeight W tau + upperMapWeight W tau + sideMapWeight W tau = W tau := by
  classical
  unfold lowerMapWeight upperMapWeight sideMapWeight
  by_cases hl : MapIsLowerHorizontal tau
  · have hu : ¬ MapIsUpperHorizontal tau := by
      intro h
      exact not_lower_and_upper_map hp tau ⟨hl, h⟩
    simp [hl, hu]
  · by_cases hu : MapIsUpperHorizontal tau
    · simp [hl, hu]
    · simp [hl, hu]

/-- Expanded occurrence pairing for an arbitrary facet-map weight. -/
noncomputable def occurrencePairing
    (hp : Nat.Prime p) (N L : Nat)
    (W : (Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) → ZMod p) : ZMod p :=
  ∑ o : EquivariantPrismGlobalCancellation.FacetOccurrence hp N L,
    occurrenceCoefficient hp N L o * W (occurrenceFacetMap hp N L o)

/-- Lower endpoint pairing at the combined spatial level. -/
noncomputable def lowerEndpointPairing
    (hp : Nat.Prime p) (N L : Nat)
    (W : (Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) → ZMod p) : ZMod p :=
  ∑ q : TopCell hp N,
    ((PrimeOrbitCycle.orbitCycle hp).coefficient q.1 * subdivisionSign N q.2) *
      ∑ eta : Fin L → Equiv.Perm (Fin p),
        subdivisionSign L eta *
          W (lowerEndpointMap (endpointSpatialMap hp N L q eta))

/-- Upper endpoint pairing at the combined spatial level. -/
noncomputable def upperEndpointPairing
    (hp : Nat.Prime p) (N L : Nat)
    (W : (Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) → ZMod p) : ZMod p :=
  ∑ q : TopCell hp N,
    ((PrimeOrbitCycle.orbitCycle hp).coefficient q.1 * subdivisionSign N q.2) *
      ∑ eta : Fin L → Equiv.Perm (Fin p),
        subdivisionSign L eta *
          W (upperEndpointMap (endpointSpatialMap hp N L q eta))

/-- Lower-horizontal part of the arbitrary weighted occurrence pairing. -/
theorem occurrencePairing_lower
    (hp : Nat.Prime p) (N L : Nat)
    (W : (Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) → ZMod p) :
    occurrencePairing hp N L (lowerMapWeight W) =
      -lowerEndpointPairing hp N L W := by
  classical
  unfold occurrencePairing
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
          lowerMapWeight W
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
                lowerMapWeight W
                  (iteratedBoundaryMap p L
                    (staircasePrismMap p (RefinedAffineMap.chart hp N orbit) spatial) j eta)) =
        ∑ eta : Fin L → Equiv.Perm (Fin (p + 1)),
          iteratedSign (ZMod (p + 1)) L eta *
            ∑ spatial : Fin (p + 1), ((-1 : ZMod (p + 1)) ^ spatial.1) *
              ∑ j : Fin (p + 2), SimplicialChain.faceSign j *
                lowerMapWeight W
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
        (W := fun tau => lowerMapWeight W
          (fun x => tau (affineCompMap p L eta x)))]
    simp only [lowerMapWeight,
      refinedSidePrismMap_not_lowerHorizontal hp N _ _ _ L _, if_false]
    simp only [MapIsLowerHorizontal, MapIsUpperHorizontal,
      lowerEndpointMap, upperEndpointMap]
    simp only [iteratedSign, subdivisionSign, permSignCoeff]
    have hlower (sigma : Delta p → Realization (p + 1)) :
        lowerEndpointMap sigma = fun x => (sigma x, 0) := rfl
    simp [lowerEndpointPairing, endpointSpatialMap_succ, endpointSpatialMap,
      endpointRefinementWord, lowerEndpointMap,
      subdivisionSign, permSignCoeff, hlower]
    rfl

/-- Upper-horizontal part of the arbitrary weighted occurrence pairing. -/
theorem occurrencePairing_upper
    (hp : Nat.Prime p) (N L : Nat)
    (W : (Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) → ZMod p) :
    occurrencePairing hp N L (upperMapWeight W) =
      upperEndpointPairing hp N L W := by
  classical
  unfold occurrencePairing
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
          upperMapWeight W
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
                upperMapWeight W
                  (iteratedBoundaryMap p L
                    (staircasePrismMap p (RefinedAffineMap.chart hp N orbit) spatial) j eta)) =
        ∑ eta : Fin L → Equiv.Perm (Fin (p + 1)),
          iteratedSign (ZMod (p + 1)) L eta *
            ∑ spatial : Fin (p + 1), ((-1 : ZMod (p + 1)) ^ spatial.1) *
              ∑ j : Fin (p + 2), SimplicialChain.faceSign j *
                upperMapWeight W
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
        (W := fun tau => upperMapWeight W
          (fun x => tau (affineCompMap p L eta x)))]
    simp only [upperMapWeight,
      refinedSidePrismMap_not_upperHorizontal hp N _ _ _ L _, if_false]
    simp only [MapIsLowerHorizontal, MapIsUpperHorizontal,
      lowerEndpointMap, upperEndpointMap]
    simp only [iteratedSign, subdivisionSign, permSignCoeff]
    have hupper (sigma : Delta p → Realization (p + 1)) :
        upperEndpointMap sigma = fun x => (sigma x, 1) := rfl
    simp [upperEndpointPairing, endpointSpatialMap_succ, endpointSpatialMap,
      endpointRefinementWord, upperEndpointMap,
      subdivisionSign, permSignCoeff, hupper]
    rfl

/-- Prime invariance is inherited by the nonhorizontal restriction of a weight. -/
theorem sideMapWeight_translate
    (hp : Nat.Prime p)
    (W : (Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) → ZMod p)
    (hW : ∀ (g : PrimeSymmetry hp) tau,
      W (translateFacetMap hp g tau) = W tau)
    (g : PrimeSymmetry hp)
    (tau : Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) :
    sideMapWeight W (translateFacetMap hp g tau) = sideMapWeight W tau := by
  classical
  unfold sideMapWeight
  have hl : MapIsLowerHorizontal (translateFacetMap hp g tau) ↔
      MapIsLowerHorizontal tau := by rfl
  have hu : MapIsUpperHorizontal (translateFacetMap hp g tau) ↔
      MapIsUpperHorizontal tau := by rfl
  by_cases hside : ¬ MapIsLowerHorizontal tau ∧ ¬ MapIsUpperHorizontal tau
  · have hside' : ¬ MapIsLowerHorizontal (translateFacetMap hp g tau) ∧
        ¬ MapIsUpperHorizontal (translateFacetMap hp g tau) := by
      simpa only [hl, hu] using hside
    rw [if_pos hside, if_pos hside', hW g tau]
  · have hside' : ¬ (¬ MapIsLowerHorizontal (translateFacetMap hp g tau) ∧
        ¬ MapIsUpperHorizontal (translateFacetMap hp g tau)) := by
      simpa only [hl, hu] using hside
    rw [if_neg hside, if_neg hside']

/-- Weight of a staircase side simplex for an arbitrary affine-facet weight.  This is the
weight-independent form of the construction used in nonhorizontal cancellation. -/
noncomputable def arbitrarySpatialSideWeight
    {n : Nat} (hp : Nat.Prime (n + 1)) (L : Nat)
    (V : (Delta n → Realization (n + 1) × Set.Icc (0 : Real) 1) → ZMod (n + 1))
    (eta : Fin L → Equiv.Perm (Fin (n + 1))) (h : Fin n)
    (tau : Delta (n - 1) → Realization (n + 1)) : ZMod (n + 1) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by
    intro hn0
    subst n
    exact Fin.elim0 h)
  let h' : Fin ((n - 1) + 1) := Fin.cast (by omega) h
  exact V (fun x =>
    staircasePrismMap (n - 1) tau h'
      (deltaCast (Nat.sub_add_cancel hn).symm (affineCompMap n L eta x)))

/-- A side simplex of a refined chart is the arbitrary side weight of its iterated spatial facet. -/
theorem refined_side_eq_arbitrarySpatialSideWeight
    {n : Nat} (hp : Nat.Prime (n + 1)) (N L : Nat)
    (V : (Delta n → Realization (n + 1) × Set.Icc (0 : Real) 1) → ZMod (n + 1))
    (orbit : PrimeOrbitCycle.TopOrbit hp)
    (spatial : RefinementWord (n + 1) N)
    (eta : Fin L → Equiv.Perm (Fin (n + 1)))
    (r : Fin (n + 1)) (h : Fin n) :
    let hn : 0 < n := Nat.pos_of_ne_zero (by
      intro hn0
      subst n
      exact Fin.elim0 h)
    let hd : n - 1 + 2 = n + 1 := by omega
    let spatial' : Fin N → Equiv.Perm (Fin (n - 1 + 2)) := fun k =>
      (Equiv.cast (congrArg Fin hd)).trans (spatial k) |>.trans
        (Equiv.cast (congrArg Fin hd.symm))
    let baseSimplex : Delta (n - 1 + 1) → Realization (n + 1) := fun x =>
      (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
        (deltaCast ((Nat.sub_add_cancel hn).trans (Nat.add_sub_cancel n 1).symm) x)
    V (fun x =>
      sidePrismMap n (RefinedAffineMap.chart hp N (orbit, spatial)) r h
        (affineCompMap n L eta x)) =
      arbitrarySpatialSideWeight hp L V eta h
        (iteratedFacetMap (n - 1) N baseSimplex spatial'
          (Fin.cast hd.symm r)) := by
  cases n with
  | zero => exact Fin.elim0 h
  | succ n =>
      dsimp only
      rw [refined_chart_eq_affineCompMap]
      simp [arbitrarySpatialSideWeight, sidePrismMap, deltaCast, Equiv.cast]
      have hspatial :
          (fun k =>
            ((Equiv.cast (congrArg Fin (show n + 1 - 1 + 2 = n + 1 + 1 by omega))).trans
              (spatial k)).trans
              (Equiv.cast (congrArg Fin
                (show n + 1 + 1 = n + 1 - 1 + 2 by omega)))) = spatial := by
        funext k
        apply Equiv.ext
        intro i
        rfl
      change V _ = V _
      congr 1

/-- Successor-dimensional arbitrary-weight side bridge, with transports normalized. -/
theorem refined_side_eq_arbitrarySpatialSideWeight_succ
    {n : Nat} (hp : Nat.Prime (n + 1 + 1)) (N L : Nat)
    (V : (Delta (n + 1) → Realization (n + 1 + 1) × Set.Icc (0 : Real) 1) →
      ZMod (n + 1 + 1))
    (orbit : PrimeOrbitCycle.TopOrbit hp)
    (spatial : RefinementWord (n + 1 + 1) N)
    (eta : Fin L → Equiv.Perm (Fin (n + 1 + 1)))
    (r : Fin (n + 1 + 1)) (h : Fin (n + 1)) :
    V (fun x =>
      sidePrismMap (n + 1) (RefinedAffineMap.chart hp N (orbit, spatial)) r h
        (affineCompMap (n + 1) L eta x)) =
      arbitrarySpatialSideWeight hp L V eta h
        (iteratedFacetMap n N
          (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
          spatial r) := by
  rw [refined_side_eq_arbitrarySpatialSideWeight hp N L V orbit spatial eta r h]
  congr 2

/-- Spatial subdivision boundary identity for an arbitrary fixed side weight. -/
theorem arbitrarySpatialSide_weighted_boundary
    {n : Nat} (hp : Nat.Prime (n + 1 + 1)) (N L : Nat)
    (V : (Delta (n + 1) → Realization (n + 1 + 1) × Set.Icc (0 : Real) 1) →
      ZMod (n + 1 + 1))
    (eta : Fin L → Equiv.Perm (Fin (n + 1 + 1))) (h : Fin (n + 1))
    (orbit : PrimeOrbitCycle.TopOrbit hp) :
    (∑ spatial : RefinementWord (n + 1 + 1) N,
      iteratedSign (ZMod (n + 1 + 1)) N spatial *
        ∑ r : Fin (n + 1 + 1), SimplicialChain.faceSign r *
          arbitrarySpatialSideWeight hp L V eta h
            (iteratedFacetMap n N
              (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
              spatial r)) =
      ∑ j : Fin (n + 1 + 1), SimplicialChain.faceSign j *
        ∑ theta : Fin N → Equiv.Perm (Fin (n + 1)),
          iteratedSign (ZMod (n + 1 + 1)) N theta *
            arbitrarySpatialSideWeight hp L V eta h
              (iteratedBoundaryMap n N
                (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
                j theta) := by
  exact iterated_weighted_boundary
    (R := ZMod (n + 1 + 1)) (X := Realization (n + 1 + 1))
    (n := n) (N := N)
    (sigma := (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap)
    (W := arbitrarySpatialSideWeight hp L V eta h)

/-- Scaled form of the arbitrary spatial side boundary identity used in the final orbit sum. -/
theorem arbitrarySpatialSide_scaled_boundary
    {n : Nat} (hp : Nat.Prime (n + 1 + 1)) (N L : Nat)
    (V : (Delta (n + 1) → Realization (n + 1 + 1) × Set.Icc (0 : Real) 1) →
      ZMod (n + 1 + 1))
    (eta : Fin L → Equiv.Perm (Fin (n + 1 + 1))) (h : Fin (n + 1))
    (orbit : PrimeOrbitCycle.TopOrbit hp) :
    (∑ spatial : RefinementWord (n + 1 + 1) N,
      ∑ r : Fin (n + 1 + 1),
        ((PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
          iteratedSign (ZMod (n + 1 + 1)) N spatial) *
        (iteratedSign (ZMod (n + 1 + 1)) L eta *
          (SimplicialChain.faceSign r *
            (((-1 : ZMod (n + 1 + 1)) ^ h.1) *
              arbitrarySpatialSideWeight hp L V eta h
                (iteratedFacetMap n N
                  (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
                  spatial r))))) =
      ((PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
        iteratedSign (ZMod (n + 1 + 1)) L eta *
        ((-1 : ZMod (n + 1 + 1)) ^ h.1)) *
      (∑ j : Fin (n + 1 + 1), SimplicialChain.faceSign j *
        ∑ theta : Fin N → Equiv.Perm (Fin (n + 1)),
          iteratedSign (ZMod (n + 1 + 1)) N theta *
            arbitrarySpatialSideWeight hp L V eta h
              (iteratedBoundaryMap n N
                (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
                j theta)) := by
  rw [← arbitrarySpatialSide_weighted_boundary hp N L V eta h orbit]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spatial hspatial
  apply Finset.sum_congr rfl
  intro r hr
  ring
/-- The nonhorizontal part of every prime-invariant facet-map weight pairs trivially with the
refined prism boundary. -/
theorem occurrencePairing_side_eq_zero
    (hp : Nat.Prime p) (N L : Nat)
    (W : (Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) → ZMod p)
    (hW : ∀ (g : PrimeSymmetry hp) tau,
      W (translateFacetMap hp g tau) = W tau) :
    occurrencePairing hp N L (sideMapWeight W) = 0 := by
  classical
  have hpdim : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.pos).symm
  generalize hn : p - 1 = n at hpdim ⊢
  subst p
  unfold occurrencePairing
  rw [Fintype.sum_prod_type]
  simp only [occurrenceCoefficient, prismCoefficient, prismSign,
    Int.cast_mul, Int.cast_prod]
  conv_lhs =>
    enter [2, cell, 2, j]
    rw [occurrenceFacetMap_eq_iteratedFacetMap_succ]
  simp only [subdivisionSign, staircaseSign, iteratedSign, permSignCoeff]
  ring_nf
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  ring_nf
  conv_lhs =>
    enter [2, orbit, 2, spatial, 2, k, 2, j]
    rw [mul_assoc]
  conv_lhs =>
    enter [2, orbit, 2, spatial, 2, k]
    rw [← Finset.mul_sum, mul_assoc]
  conv_lhs =>
    enter [2, orbit, 2, spatial]
    rw [← Finset.mul_sum]
  have hfacetFaceIndex (j : Fin (n + 2)) : facetFaceIndex hp j = j := by
    apply Fin.ext
    simp [occurrenceCoefficient, SimplicialChain.faceSign, facetFaceIndex]
  simp_rw [hfacetFaceIndex]
  conv_lhs =>
    enter [2, orbit, 2, spatial, 2]
    change ∑ rho, iteratedSign (ZMod (n + 1)) L rho *
      ∑ j, SimplicialChain.faceSign j *
        sideMapWeight W
          (iteratedFacetMap n L
            (staircasePrismMap n (RefinedAffineMap.chart hp N orbit) spatial) rho j)
    rw [iterated_weighted_boundary
      (R := ZMod (n + 1))
      (X := Realization (n + 1) × Set.Icc (0 : Real) 1)
      (n := n) (N := L)]
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
      (∑ spatial : Fin (n + 1), ((-1 : ZMod (n + 1)) ^ spatial.1) *
        ∑ j : Fin (n + 2), SimplicialChain.faceSign j *
          ∑ eta : Fin L → Equiv.Perm (Fin (n + 1)),
            iteratedSign (ZMod (n + 1)) L eta *
              sideMapWeight W
                (iteratedBoundaryMap n L
                  (staircasePrismMap n (RefinedAffineMap.chart hp N orbit) spatial) j eta)) =
      ∑ eta : Fin L → Equiv.Perm (Fin (n + 1)),
        iteratedSign (ZMod (n + 1)) L eta *
          ∑ spatial : Fin (n + 1), ((-1 : ZMod (n + 1)) ^ spatial.1) *
            ∑ j : Fin (n + 2), SimplicialChain.faceSign j *
              sideMapWeight W
                (fun x => staircasePrismMap n
                  (RefinedAffineMap.chart hp N orbit) spatial
                  (cofacePoint n j (affineCompMap n L eta x))) by
        simp_rw [Finset.mul_sum]
        conv_lhs =>
          enter [2, spatial]
          rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro eta heta
        apply Finset.sum_congr rfl
        intro spatial hspatial
        apply Finset.sum_congr rfl
        intro j hj
        have hmap :
            iteratedBoundaryMap n L
                (staircasePrismMap n (RefinedAffineMap.chart hp N orbit) spatial) j eta =
              fun x => staircasePrismMap n (RefinedAffineMap.chart hp N orbit) spatial
                (cofacePoint n j (affineCompMap n L eta x)) := rfl
        rw [hmap]
        ac_rfl]
  conv_lhs =>
    enter [2, orbit, 2]
    enter [2, eta, 2]
    rw [staircase_weighted_boundary
      (W := fun tau => sideMapWeight W
        (fun x => tau (affineCompMap n L eta x)))]
  have hlower (eta : Fin L → Equiv.Perm (Fin (n + 1)))
      (sigma : Delta n → Realization (n + 1)) :
      sideMapWeight W
          (fun x => lowerEndpointMap sigma (affineCompMap n L eta x)) = 0 := by
    change sideMapWeight W
      (lowerEndpointMap (fun x => sigma (affineCompMap n L eta x))) = 0
    unfold sideMapWeight
    rw [if_neg]
    intro hside
    apply hside.1
    intro i
    rfl
  have hupper (eta : Fin L → Equiv.Perm (Fin (n + 1)))
      (sigma : Delta n → Realization (n + 1)) :
      sideMapWeight W
          (fun x => upperEndpointMap sigma (affineCompMap n L eta x)) = 0 := by
    change sideMapWeight W
      (upperEndpointMap (fun x => sigma (affineCompMap n L eta x))) = 0
    unfold sideMapWeight
    rw [if_neg]
    intro hside
    apply hside.2
    intro i
    rfl
  simp_rw [hlower, hupper]
  simp only [zero_sub, sub_zero]
  rw [Fintype.sum_prod_type]
  cases n with
  | zero => simp
  | succ n =>
    simp only [refined_side_eq_arbitrarySpatialSideWeight_succ
      hp N L (sideMapWeight W)]
    simp_rw [Finset.mul_sum]
    conv_lhs =>
      enter [2, orbit]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs =>
      enter [2, eta, 2, orbit, 2, spatial]
      rw [Finset.sum_comm]
    simp only [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
    rw [neg_eq_zero]
    apply Finset.sum_eq_zero
    intro eta heta
    conv_lhs =>
      enter [2, orbit]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro h hh
    change ∑ orbit, ∑ spatial, ∑ r,
      ((PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
        iteratedSign (ZMod (n + 1 + 1)) N spatial) *
      (iteratedSign (ZMod (n + 1 + 1)) L eta *
        (SimplicialChain.faceSign r *
          (((-1 : ZMod (n + 1 + 1)) ^ h.1) *
            arbitrarySpatialSideWeight hp L (sideMapWeight W) eta h
              (iteratedFacetMap n N
                (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
                spatial r)))) = 0
    conv_lhs =>
      enter [2, orbit]
      rw [arbitrarySpatialSide_scaled_boundary hp N L (sideMapWeight W) eta h orbit]
    simp_rw [Finset.mul_sum]
    conv_lhs =>
      enter [2, orbit]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro theta htheta
    let Vsimplex : Simplex (n + 1 + 1) n → ZMod (n + 1 + 1) := fun f =>
      arbitrarySpatialSideWeight hp L (sideMapWeight W) eta h (fun x =>
        f.realizationPoint
          (StandardSimplex.ofDelta (affineCompMap n N theta x)))
    have hVsimplex : ∀ (g : PrimeSymmetry hp) (f : Simplex (n + 1 + 1) n),
        Vsimplex (g • f) = Vsimplex f := by
      intro g f
      dsimp [Vsimplex, arbitrarySpatialSideWeight]
      calc
        _ = sideMapWeight W
            (translateFacetMap hp g (fun x =>
              staircasePrismMap n (fun y => f.realizationPoint
                (StandardSimplex.ofDelta (affineCompMap n N theta y))) h
                (deltaCast (Nat.sub_add_cancel (Nat.zero_lt_succ n)).symm
                  (affineCompMap (n + 1) L eta x)))) := by
              congr 1
              funext x
              apply Prod.ext
              · simp only [translateFacetMap, staircasePrismMap, Prod.fst]
                exact realizationPoint_prime_smul_any hp g f _
              · rfl
        _ = _ := sideMapWeight_translate hp W hW g _
    have hz := orbit_boundary_pairing_eq_zero hp Vsimplex hVsimplex
    have hmap (orbit : PrimeOrbitCycle.TopOrbit hp) (j : Fin (n + 1 + 1)) :
        arbitrarySpatialSideWeight hp L (sideMapWeight W) eta h
            (iteratedBoundaryMap n N
              (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
              j theta) =
          Vsimplex ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
            (FaceMap.delete j)) := by
      congr 1
      funext x
      apply Realization.ext
      intro c
      simp [Vsimplex, arbitrarySpatialSideWeight, iteratedBoundaryMap,
        ReferenceAffineOrbitCount.topRepr,
        Simplex.realizationContinuousMap, Simplex.realizationPoint,
        Simplex.chartWeight, cofacePoint, stdSimplex.map_coe,
        FunOnFinite.linearMap_apply_apply]
      change (∑ i : Fin (n + 1 + 1),
        if (ReferenceAffineOrbitCount.topRepr hp orbit) i = c then
          (StandardSimplex.ofDelta
            (stdSimplex.map j.succAbove (affineCompMap n N theta x))) i else 0) = _
      have hs := Fin.sum_univ_succAbove (fun i : Fin (n + 1 + 1) =>
        if (ReferenceAffineOrbitCount.topRepr hp orbit) i = c then
          (StandardSimplex.ofDelta
            (stdSimplex.map j.succAbove (affineCompMap n N theta x))) i else 0) j
      rw [hs]
      have hdeleted :
          (StandardSimplex.ofDelta
            (stdSimplex.map j.succAbove (affineCompMap n N theta x))) j = 0 := by
        change (cofacePoint n j (affineCompMap n N theta x)) j = 0
        exact cofacePoint_apply_deleted n j (affineCompMap n N theta x)
      simp only [hdeleted, ite_self, zero_add]
      apply Finset.sum_congr rfl
      intro i hi
      change (if (ReferenceAffineOrbitCount.topRepr hp orbit) (j.succAbove i) = c then _ else 0) =
        if (ReferenceAffineOrbitCount.topRepr hp orbit) (j.succAbove i) = c then _ else 0
      by_cases hic : (ReferenceAffineOrbitCount.topRepr hp orbit) (j.succAbove i) = c
      · rw [if_pos hic, if_pos hic]
        change stdSimplex.map (S := Real) j.succAbove
          (affineCompMap n N theta x) (j.succAbove i) =
            affineCompMap n N theta x i
        rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
        exact Finset.sum_eq_single i (by
          intro q hq hqi
          have hsucc : j.succAbove q ≠ j.succAbove i := by
            intro heq
            exact hqi (Fin.succAbove_right_injective heq)
          have hq' : j.succAbove q = j.succAbove i := by simpa using hq
          exact (hsucc hq').elim) (by simp)
      · rw [if_neg hic, if_neg hic]
    simp_rw [hmap]
    calc
      _ = (iteratedSign (ZMod (n + 1 + 1)) L eta *
            ((-1 : ZMod (n + 1 + 1)) ^ h.1) *
            iteratedSign (ZMod (n + 1 + 1)) N theta) *
          (∑ orbit,
            (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
              ∑ k,
                SimplicialChain.faceSign (orbitFacetIndex hp k) *
                  Vsimplex ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                    (FaceMap.delete (orbitFacetIndex hp k)))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro orbit horbit
            rw [Finset.mul_sum]
            have hreindex :
                (∑ j : Fin (n + 1 + 1),
                  (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
                    iteratedSign (ZMod (n + 1 + 1)) L eta *
                    ((-1 : ZMod (n + 1 + 1)) ^ h.1 *
                    (SimplicialChain.faceSign j *
                      (iteratedSign (ZMod (n + 1 + 1)) N theta *
                        Vsimplex ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                          (FaceMap.delete j))))) =
                  ∑ k : Fin (n + 1 + 1),
                    (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
                      iteratedSign (ZMod (n + 1 + 1)) L eta *
                      ((-1 : ZMod (n + 1 + 1)) ^ h.1 *
                      (SimplicialChain.faceSign (orbitFacetIndex hp k) *
                        (iteratedSign (ZMod (n + 1 + 1)) N theta *
                          Vsimplex ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                            (FaceMap.delete (orbitFacetIndex hp k))))))) := by
              exact (Equiv.sum_comp (orbitFacetEquiv hp) (fun j =>
                (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
                  iteratedSign (ZMod (n + 1 + 1)) L eta *
                  ((-1 : ZMod (n + 1 + 1)) ^ h.1 *
                  (SimplicialChain.faceSign j *
                    (iteratedSign (ZMod (n + 1 + 1)) N theta *
                      Vsimplex ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                        (FaceMap.delete j))))))).symm
            calc
              _ = ∑ j : Fin (n + 1 + 1),
                  (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
                    iteratedSign (ZMod (n + 1 + 1)) L eta *
                    ((-1 : ZMod (n + 1 + 1)) ^ h.1 *
                    (SimplicialChain.faceSign j *
                      (iteratedSign (ZMod (n + 1 + 1)) N theta *
                        Vsimplex ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                          (FaceMap.delete j))))) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ = _ := hreindex
              _ = _ := by
                simp_rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k hk
                ring
      _ = 0 := by simpa only [hz, mul_zero]

/-- Arbitrary prime-invariant weighted boundary formula for the fully refined middle prism. -/
theorem occurrencePairing_eq_upper_sub_lower
    (hp : Nat.Prime p) (N L : Nat)
    (W : (Delta (p - 1) → Realization p × Set.Icc (0 : Real) 1) → ZMod p)
    (hW : ∀ (g : PrimeSymmetry hp) tau,
      W (translateFacetMap hp g tau) = W tau) :
    occurrencePairing hp N L W =
      upperEndpointPairing hp N L W - lowerEndpointPairing hp N L W := by
  classical
  have hsplit : occurrencePairing hp N L W =
      occurrencePairing hp N L (lowerMapWeight W) +
        occurrencePairing hp N L (upperMapWeight W) +
          occurrencePairing hp N L (sideMapWeight W) := by
    unfold occurrencePairing
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro o ho
    rw [← mul_add, ← mul_add, lower_add_upper_add_side hp W]
  rw [hsplit, occurrencePairing_lower, occurrencePairing_upper,
    occurrencePairing_side_eq_zero hp N L W hW]
  ring

/-! ## Pointwise middle-prism collar -/

/-- Lower boundary coefficient of one middle-prism facet orbit. -/
noncomputable def lowerBoundaryCoefficient
    (hp : Nat.Prime p) (N L : Nat)
    (s : (Cells hp N L).Facet) : ZMod p :=
  lowerEndpointPairing hp N L (facetOrbitIndicator hp N L s)

/-- Upper boundary coefficient of one middle-prism facet orbit. -/
noncomputable def upperBoundaryCoefficient
    (hp : Nat.Prime p) (N L : Nat)
    (s : (Cells hp N L).Facet) : ZMod p :=
  upperEndpointPairing hp N L (facetOrbitIndicator hp N L s)

/-- The explicit facet incidence is the arbitrary occurrence pairing evaluated at the orbit
characteristic weight. -/
theorem facetIncidence_eq_occurrencePairing
    (hp : Nat.Prime p) (N L : Nat)
    (s : (Cells hp N L).Facet) :
    (Cells hp N L).facetIncidence s =
      occurrencePairing hp N L (facetOrbitIndicator hp N L s) := by
  classical
  unfold RelativeAffineCellSystem.facetIncidence occurrencePairing
  apply Finset.sum_congr rfl
  intro o ho
  rw [facetOrbitIndicator_occurrence]
  by_cases hs : (Cells hp N L).facetClass o = s
  · simp only [hs, if_true]
    change prismCoefficient hp N L o.1 * (-1 : ZMod p) ^ (o.2 : Nat) = _
    simp [occurrenceCoefficient, SimplicialChain.faceSign, facetFaceIndex]
  · simp [hs]

/-- If a lower endpoint map belongs to an orbit facet, that facet is lower horizontal. -/
theorem isLowerFacet_of_indicator_lower_ne_zero
    (hp : Nat.Prime p) (N L : Nat)
    (s : (Cells hp N L).Facet)
    (sigma : Delta (p - 1) → Realization p)
    (h : facetOrbitIndicator hp N L s (lowerEndpointMap sigma) ≠ 0) :
    (Cells hp N L).IsLowerFacet s := by
  unfold facetOrbitIndicator at h
  split_ifs at h with hcond
  · have ⟨o, hos, g, hmap⟩ := hcond
    -- s = facetClass o, so IsLowerFacet s = IsLowerFacetOccurrence o
    have hfacetsame : s = (Cells hp N L).facetClass o := hos.symm
    rw [hfacetsame]
    simp only [Cells]
    have h1 : RelativeAffineCellSystem.IsLowerFacet (cellSystem hp N L)
        (RelativeAffineCellSystem.facetClass (cellSystem hp N L) o) =
        RelativeAffineCellSystem.IsLowerFacetOccurrence (cellSystem hp N L) o := rfl
    rw [h1]
    -- Need to show IsLowerFacetOccurrence o: all vertices have time = 0
    intro i
    -- From hmap: mapVertexSignature hp (lowerEndpointMap sigma) i = g • Cells.facetSignature o i
    -- lowerEndpointMap has time = 0, and g • z preserves time
    have hmap_i := congrFun hmap i
    rw [mapVertexSignature] at hmap_i
    -- LHS time = 0, RHS time = (Cells.facetSignature o i).time
    have hlhs_time : (CylinderPoint.ofProd (lowerEndpointMap sigma (stdSimplex.vertex ((AffinePositiveRayBoundary.VertexMap.facetIndexEquiv hp).symm i)))).time = ⟨0, by norm_num⟩ := by
      rfl
    rw [hmap_i] at hlhs_time
    simp [CylinderPoint.smul_time] at hlhs_time
    simp only [Cells] at hlhs_time ⊢
    simpa [Set.Icc] using hlhs_time
  · simp at h

/-- If an upper endpoint map belongs to an orbit facet, that facet is upper horizontal. -/
theorem isUpperFacet_of_indicator_upper_ne_zero
    (hp : Nat.Prime p) (N L : Nat)
    (s : (Cells hp N L).Facet)
    (sigma : Delta (p - 1) → Realization p)
    (h : facetOrbitIndicator hp N L s (upperEndpointMap sigma) ≠ 0) :
    (Cells hp N L).IsUpperFacet s := by
  unfold facetOrbitIndicator at h
  split_ifs at h with hcond
  · have ⟨o, hos, g, hmap⟩ := hcond
    have hfacetsame : s = (Cells hp N L).facetClass o := hos.symm
    rw [hfacetsame]
    simp only [Cells]
    have h1 : RelativeAffineCellSystem.IsUpperFacet (cellSystem hp N L)
        (RelativeAffineCellSystem.facetClass (cellSystem hp N L) o) =
        RelativeAffineCellSystem.IsUpperFacetOccurrence (cellSystem hp N L) o := rfl
    rw [h1]
    intro i
    have hmap_i := congrFun hmap i
    rw [mapVertexSignature] at hmap_i
    have hlhs_time :
        (CylinderPoint.ofProd
          (upperEndpointMap sigma
            (stdSimplex.vertex
              ((AffinePositiveRayBoundary.VertexMap.facetIndexEquiv hp).symm i)))).time =
          ⟨1, by norm_num⟩ := by
      rfl
    rw [hmap_i] at hlhs_time
    simp [CylinderPoint.smul_time] at hlhs_time
    simp only [Cells] at hlhs_time ⊢
    simpa [Set.Icc] using hlhs_time
  · simp at h

/-- Lower boundary coefficients vanish away from the lower horizontal boundary. -/
theorem lowerBoundaryCoefficient_zero_of_not_lower
    (hp : Nat.Prime p) (N L : Nat)
    (s : (Cells hp N L).Facet)
    (hs : ¬ (Cells hp N L).IsLowerFacet s) :
    lowerBoundaryCoefficient hp N L s = 0 := by
  classical
  unfold lowerBoundaryCoefficient lowerEndpointPairing
  apply Finset.sum_eq_zero
  intro q hq
  have hinner :
      (∑ eta : RefinementWord p L,
        subdivisionSign L eta *
          facetOrbitIndicator hp N L s
            (lowerEndpointMap (endpointSpatialMap hp N L q eta))) = 0 := by
    apply Finset.sum_eq_zero
    intro eta heta
    have hindicator : facetOrbitIndicator hp N L s
        (lowerEndpointMap (endpointSpatialMap hp N L q eta)) = 0 := by
      by_contra hne
      exact hs (isLowerFacet_of_indicator_lower_ne_zero hp N L s _ hne)
    rw [hindicator, mul_zero]
  rw [hinner, mul_zero]

/-- Upper boundary coefficients vanish away from the upper horizontal boundary. -/
theorem upperBoundaryCoefficient_zero_of_not_upper
    (hp : Nat.Prime p) (N L : Nat)
    (s : (Cells hp N L).Facet)
    (hs : ¬ (Cells hp N L).IsUpperFacet s) :
    upperBoundaryCoefficient hp N L s = 0 := by
  classical
  unfold upperBoundaryCoefficient upperEndpointPairing
  apply Finset.sum_eq_zero
  intro q hq
  have hinner :
      (∑ eta : RefinementWord p L,
        subdivisionSign L eta *
          facetOrbitIndicator hp N L s
            (upperEndpointMap (endpointSpatialMap hp N L q eta))) = 0 := by
    apply Finset.sum_eq_zero
    intro eta heta
    have hindicator : facetOrbitIndicator hp N L s
        (upperEndpointMap (endpointSpatialMap hp N L q eta)) = 0 := by
      by_contra hne
      exact hs (isUpperFacet_of_indicator_upper_ne_zero hp N L s _ hne)
    rw [hindicator, mul_zero]
  rw [hinner, mul_zero]

/-- The common-level staircase prism, with its boundary understood pointwise on prime-orbit facets. -/
noncomputable def collar
    (hp : Nat.Prime p) (N L : Nat) :
    FoxNeuwirthRelativeAffineCollar hp (N + L) (N + L) (N + L) L where
  cells := Cells hp N L
  lowerBoundaryCoefficient := lowerBoundaryCoefficient hp N L
  upperBoundaryCoefficient := upperBoundaryCoefficient hp N L
  lower_zero_of_not_lower := lowerBoundaryCoefficient_zero_of_not_lower hp N L
  upper_zero_of_not_upper := upperBoundaryCoefficient_zero_of_not_upper hp N L
  incidence_eq_boundary := by
    intro s
    rw [facetIncidence_eq_occurrencePairing]
    exact occurrencePairing_eq_upper_sub_lower hp N L
      (facetOrbitIndicator hp N L s)
      (facetOrbitIndicator_translate hp N L s)

end RelativeCollarMiddlePrismBoundary
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
