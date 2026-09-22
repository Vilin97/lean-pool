/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarThinSlabsBoundary
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarMiddlePrismEndpointsCore
/-!
# Endpoint identification for thin-time stacks

The external lower face of the first slab and external upper face of the last slab carry exactly the
original level-`N` Fox--Neuwirth orbit chain.  All intermediate mesh faces were already cancelled by
the telescoping boundary theorem.  This module supplies the endpoint quotient-facet maps, chain
pairing identities, exhaustiveness, and representative geometry required by
`EndpointIdentifiedRelativeAffineCollar`.
-/

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeCollarThinSlabsEndpoints

open ExplicitAffineRelativeCollar
open EquivariantPrismGlobalCancellation
open EquivariantPrismNonhorizontalCancellation
open RelativeCollarMiddlePrism
open RelativeCollarMiddlePrismEndpoints
open RelativeCollarMiddlePrismEndpointsCore
open RelativeCollarThinSlabs
open RelativeCollarThinSlabsBoundary
open RefinedAffineMap

variable {p : Nat}

/-- First slab of a positive stack. -/
def firstSlab (m : Nat) (hm : 0 < m) : Fin m :=
  ⟨0, hm⟩

/-- Last slab of a positive stack. -/
def lastSlab (m : Nat) (hm : 0 < m) : Fin m :=
  ⟨m - 1, by omega⟩

@[simp] theorem firstSlab_val (m : Nat) (hm : 0 < m) :
    (firstSlab m hm).1 = 0 :=
  rfl

@[simp] theorem lastSlab_succ_eq_last (m : Nat) (hm : 0 < m) :
    (lastSlab m hm).succ = Fin.last m := by
  apply Fin.ext
  simp [lastSlab]
  omega

/-- Canonical lower occurrence of a level-`N` spatial top cell in the first slab. -/
noncomputable def lowerOccurrence
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : TopCell hp N) :
    (StackCells hp N m hm).FacetOccurrence :=
  stackOccurrence hp N m hm (firstSlab m hm)
    (RelativeCollarMiddlePrismEndpointsCore.lowerOccurrence hp N 0 q
      (emptyEndpointRefinementWord p))

/-- Canonical upper occurrence of a level-`N` spatial top cell in the last slab. -/
noncomputable def upperOccurrence
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : TopCell hp N) :
    (StackCells hp N m hm).FacetOccurrence :=
  stackOccurrence hp N m hm (lastSlab m hm)
    (RelativeCollarMiddlePrismEndpointsCore.upperOccurrence hp N 0 q
      (emptyEndpointRefinementWord p))

/-- Canonical lower quotient facet. -/
noncomputable def lowerFacet
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : TopCell hp N) : (StackCells hp N m hm).Facet :=
  (StackCells hp N m hm).facetClass (lowerOccurrence hp N m hm q)

/-- Canonical upper quotient facet. -/
noncomputable def upperFacet
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : TopCell hp N) : (StackCells hp N m hm).Facet :=
  (StackCells hp N m hm).facetClass (upperOccurrence hp N m hm q)

/-- Ordered vertices of the canonical lower occurrence are exactly the level-`N` lower endpoint
vertices. -/
theorem lowerOccurrence_facetSignature
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : TopCell hp N) (i : Fin p) :
    (StackCells hp N m hm).facetSignature
        (lowerOccurrence hp N m hm q) i =
      lowerCylinderPoint (RefinedAffineMap.vertex hp N q
        (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  rw [lowerOccurrence, facetSignature_stackOccurrence]
  change slabPoint m hm (firstSlab m hm)
    ((BaseCells hp N).facetSignature
      (RelativeCollarMiddlePrismEndpointsCore.lowerOccurrence hp N 0 q
        (emptyEndpointRefinementWord p)) i) = _
  rw [RelativeCollarMiddlePrismEndpointsCore.lowerOccurrence_facetSignature]
  have he : EndpointFaceRefinement.endpointTopCell hp N 0 q
      (emptyEndpointRefinementWord p) = q := by
    apply Prod.ext
    · rfl
    · have hword : EndpointFaceRefinement.appendRefinementWord N 0 q.2
          (emptyEndpointRefinementWord p) = q.2 := by
        funext i
        change Fin.addCases q.2 (emptyEndpointRefinementWord p)
          (Fin.castAdd 0 i) = q.2 i
        rw [Fin.addCases_left]
      exact hword
  rw [he]
  simp [slabPoint, slabTime, lowerCylinderPoint,
      firstSlab]

/-- Ordered vertices of the canonical upper occurrence are exactly the level-`N` upper endpoint
vertices. -/
theorem upperOccurrence_facetSignature
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : TopCell hp N) (i : Fin p) :
    (StackCells hp N m hm).facetSignature
        (upperOccurrence hp N m hm q) i =
      upperCylinderPoint (RefinedAffineMap.vertex hp N q
        (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  rw [upperOccurrence, facetSignature_stackOccurrence]
  change slabPoint m hm (lastSlab m hm)
    ((BaseCells hp N).facetSignature
      (RelativeCollarMiddlePrismEndpointsCore.upperOccurrence hp N 0 q
        (emptyEndpointRefinementWord p)) i) = _
  rw [RelativeCollarMiddlePrismEndpointsCore.upperOccurrence_facetSignature]
  have he : EndpointFaceRefinement.endpointTopCell hp N 0 q
      (emptyEndpointRefinementWord p) = q := by
    apply Prod.ext
    · rfl
    · have hword : EndpointFaceRefinement.appendRefinementWord N 0 q.2
          (emptyEndpointRefinementWord p) = q.2 := by
        funext i
        change Fin.addCases q.2 (emptyEndpointRefinementWord p)
          (Fin.castAdd 0 i) = q.2 i
        rw [Fin.addCases_left]
      exact hword
  rw [he]
  have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hm
  simp [slabPoint, slabTime, upperCylinderPoint, lastSlab]
  apply Subtype.ext
  norm_num
  have hcast : ((m - 1 : Nat) : Real) + 1 = (m : Real) := by
    exact_mod_cast (show (m - 1 : Nat) + 1 = m by omega)
  rw [hcast, div_self (ne_of_gt hmR)]

/-- Canonical lower facets are lower horizontal. -/
theorem lowerFacet_isLower
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : TopCell hp N) :
    (StackCells hp N m hm).IsLowerFacet (lowerFacet hp N m hm q) := by
  change (StackCells hp N m hm).IsLowerFacetOccurrence
    (lowerOccurrence hp N m hm q)
  intro i
  simp [lowerOccurrence_facetSignature]

/-- Canonical upper facets are upper horizontal. -/
theorem upperFacet_isUpper
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : TopCell hp N) :
    (StackCells hp N m hm).IsUpperFacet (upperFacet hp N m hm q) := by
  change (StackCells hp N m hm).IsUpperFacetOccurrence
    (upperOccurrence hp N m hm q)
  intro i
  simp [upperOccurrence_facetSignature]

/-- Vertex-map signature of the canonical lower occurrence. -/
theorem mapVertexSignature_meshLower
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : TopCell hp N) :
    mapVertexSignature
        (meshEndpointMap m hm 0 (RefinedAffineMap.chart hp N q)) =
      (StackCells hp N m hm).facetSignature
        (lowerOccurrence hp N m hm q) := by
  funext i
  have hindex : AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex i =
      Fin.cast (Nat.sub_add_cancel hp.pos).symm i := by
    apply Fin.ext
    rfl
  simp [mapVertexSignature, meshEndpointMap, meshTime,
    lowerOccurrence_facetSignature, lowerCylinderPoint,
    RefinedAffineMap.vertex, hindex]
  rfl

/-- Vertex-map signature of the canonical upper occurrence. -/
theorem mapVertexSignature_meshUpper
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : TopCell hp N) :
    mapVertexSignature
        (meshEndpointMap m hm (Fin.last m) (RefinedAffineMap.chart hp N q)) =
      (StackCells hp N m hm).facetSignature
        (upperOccurrence hp N m hm q) := by
  funext i
  have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hm
  have hindex : AffinePositiveRayBoundary.VertexMap.facetCoordinateIndex i =
      Fin.cast (Nat.sub_add_cancel hp.pos).symm i := by
    apply Fin.ext
    rfl
  simp [mapVertexSignature, meshEndpointMap, meshTime,
    upperOccurrence_facetSignature, upperCylinderPoint,
    RefinedAffineMap.vertex, hindex, Fin.last, div_self (ne_of_gt hmR)]
  rfl

/-- External lower mesh indicators are the Kronecker weights of canonical lower quotient facets. -/
theorem stackFacetOrbitIndicator_meshLower
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet) (q : TopCell hp N) :
    stackFacetOrbitIndicator hp N m hm s
        (meshEndpointMap m hm 0 (RefinedAffineMap.chart hp N q)) =
      if lowerFacet hp N m hm q = s then 1 else 0 := by
  exact stackFacetOrbitIndicator_occurrence hp N m hm s
    (lowerOccurrence hp N m hm q) _
    (mapVertexSignature_meshLower hp N m hm q)

/-- External upper mesh indicators are the Kronecker weights of canonical upper quotient facets. -/
theorem stackFacetOrbitIndicator_meshUpper
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet) (q : TopCell hp N) :
    stackFacetOrbitIndicator hp N m hm s
        (meshEndpointMap m hm (Fin.last m) (RefinedAffineMap.chart hp N q)) =
      if upperFacet hp N m hm q = s then 1 else 0 := by
  exact stackFacetOrbitIndicator_occurrence hp N m hm s
    (upperOccurrence hp N m hm q) _
    (mapVertexSignature_meshUpper hp N m hm q)

/-- Chain-level lower endpoint pairing identity. -/
theorem lowerBoundaryPairing_eq
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (W : (StackCells hp N m hm).Facet → ZMod p) :
    (∑ s : (StackCells hp N m hm).Facet,
        lowerBoundaryCoefficient hp N m hm s * W s) =
      ∑ q : TopCell hp N,
        coefficient hp N q * W (lowerFacet hp N m hm q) := by
  classical
  unfold lowerBoundaryCoefficient meshEndpointPairing
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp_rw [stackFacetOrbitIndicator_meshLower, mul_ite, mul_one, mul_zero]
  simp only [eq_comm]
  symm
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

/-- Chain-level upper endpoint pairing identity. -/
theorem upperBoundaryPairing_eq
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (W : (StackCells hp N m hm).Facet → ZMod p) :
    (∑ s : (StackCells hp N m hm).Facet,
        upperBoundaryCoefficient hp N m hm s * W s) =
      ∑ q : TopCell hp N,
        coefficient hp N q * W (upperFacet hp N m hm q) := by
  classical
  unfold upperBoundaryCoefficient meshEndpointPairing
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp_rw [stackFacetOrbitIndicator_meshUpper, mul_ite, mul_one, mul_zero]
  simp only [eq_comm]
  symm
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

/-- Equality of base quotient facets lifts to equality of their copies in one fixed slab. -/
theorem stackFacetClass_eq_of_baseFacetClass_eq
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (r : Fin m) {o o' : (BaseCells hp N).FacetOccurrence}
    (h : (BaseCells hp N).facetClass o = (BaseCells hp N).facetClass o') :
    (StackCells hp N m hm).facetClass (stackOccurrence hp N m hm r o) =
      (StackCells hp N m hm).facetClass (stackOccurrence hp N m hm r o') := by
  rcases Quotient.exact h with ⟨g, hg⟩
  apply Quotient.sound
  refine ⟨g, ?_⟩
  funext i
  rw [facetSignature_stackOccurrence, facetSignature_stackOccurrence]
  have hi := congrFun hg i
  simpa using congrArg (slabPoint m hm r) hi

/-- A lower-horizontal stack occurrence necessarily belongs to the first slab and its underlying
base occurrence is lower horizontal. -/
theorem lowerOccurrence_reduction
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (r : Fin m) (o : (BaseCells hp N).FacetOccurrence)
    (h : (StackCells hp N m hm).IsLowerFacetOccurrence
      (stackOccurrence hp N m hm r o)) :
    r = firstSlab m hm ∧ (BaseCells hp N).IsLowerFacetOccurrence o := by
  have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hm
  let i0 : Fin p := ⟨0, hp.pos⟩
  have h0 := h i0
  rw [facetSignature_stackOccurrence, slabPoint_time] at h0
  have hbase0 : (0 : Real) ≤ ((BaseCells hp N).facetSignature o i0).time.1 :=
    ((BaseCells hp N).facetSignature o i0).time.2.1
  have hr0 : (0 : Real) ≤ (r.1 : Real) := by positivity
  have hm0 : (m : Real) ≠ 0 := ne_of_gt hmR
  field_simp [hm0] at h0
  have hr : r.1 = 0 := by
    have : (r.1 : Real) = 0 := by linarith
    exact_mod_cast this
  have rr : r = firstSlab m hm := Fin.ext hr
  refine ⟨rr, ?_⟩
  intro i
  have hi := h i
  rw [facetSignature_stackOccurrence, slabPoint_time] at hi
  field_simp [hm0] at hi
  linarith

/-- An upper-horizontal stack occurrence necessarily belongs to the last slab and its underlying
base occurrence is upper horizontal. -/
theorem upperOccurrence_reduction
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (r : Fin m) (o : (BaseCells hp N).FacetOccurrence)
    (h : (StackCells hp N m hm).IsUpperFacetOccurrence
      (stackOccurrence hp N m hm r o)) :
    r = lastSlab m hm ∧ (BaseCells hp N).IsUpperFacetOccurrence o := by
  have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hm
  have hm0 : (m : Real) ≠ 0 := ne_of_gt hmR
  let i0 : Fin p := ⟨0, hp.pos⟩
  have h0 := h i0
  rw [facetSignature_stackOccurrence, slabPoint_time] at h0
  field_simp [hm0] at h0
  have ht0 := ((BaseCells hp N).facetSignature o i0).time.2.2
  have hrle : (r.1 : Real) + 1 ≤ (m : Real) := by
    exact_mod_cast (Nat.succ_le_iff.mpr r.2)
  have hmle : (m : Real) ≤ (r.1 : Real) + 1 := by linarith
  have hrsuccR : (r.1 : Real) + 1 = (m : Real) := le_antisymm hrle hmle
  have hrsucc : r.1 + 1 = m := by
    exact_mod_cast hrsuccR
  have rr : r = lastSlab m hm := by
    apply Fin.ext
    simp [lastSlab]
    omega
  refine ⟨rr, ?_⟩
  intro i
  have hi := h i
  rw [facetSignature_stackOccurrence, slabPoint_time] at hi
  field_simp [hm0] at hi
  have htle := ((BaseCells hp N).facetSignature o i).time.2.2
  have hrsuccR' : (r.1 : Real) + 1 = (m : Real) := by exact_mod_cast hrsucc
  linarith

/-- Every lower horizontal quotient facet is represented by a canonical level-`N` lower facet. -/
theorem lowerFacet_exhaustive
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet)
    (hs : (StackCells hp N m hm).IsLowerFacet s) :
    ∃ q : TopCell hp N, lowerFacet hp N m hm q = s := by
  refine Quotient.inductionOn s (fun o ho => ?_) hs
  rcases o with ⟨⟨r, qcell⟩, j⟩
  let base : (BaseCells hp N).FacetOccurrence := (qcell, j)
  have hred := lowerOccurrence_reduction hp N m hm r base ho
  rcases hred with ⟨hr, hbase⟩
  rcases RelativeCollarMiddlePrismEndpoints.lowerOccurrence_classification_zero
      hp N base hbase with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [lowerFacet, lowerOccurrence, ← hr]
  exact (stackFacetClass_eq_of_baseFacetClass_eq hp N m hm r hq).symm

/-- Every upper horizontal quotient facet is represented by a canonical level-`N` upper facet. -/
theorem upperFacet_exhaustive
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (s : (StackCells hp N m hm).Facet)
    (hs : (StackCells hp N m hm).IsUpperFacet s) :
    ∃ q : TopCell hp N, upperFacet hp N m hm q = s := by
  refine Quotient.inductionOn s (fun o ho => ?_) hs
  rcases o with ⟨⟨r, qcell⟩, j⟩
  let base : (BaseCells hp N).FacetOccurrence := (qcell, j)
  have hred := upperOccurrence_reduction hp N m hm r base ho
  rcases hred with ⟨hr, hbase⟩
  rcases RelativeCollarMiddlePrismEndpoints.upperOccurrence_classification_zero
      hp N base hbase with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [upperFacet, upperOccurrence, ← hr]
  exact (stackFacetClass_eq_of_baseFacetClass_eq hp N m hm r hq).symm

/-- Every representative of a canonical lower quotient facet has the prescribed endpoint vertices,
up to one simultaneous prime relabelling. -/
theorem lowerFacetOccurrenceVertex_eq
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : TopCell hp N)
    (o : (StackCells hp N m hm).FacetOccurrence)
    (ho : (StackCells hp N m hm).facetClass o = lowerFacet hp N m hm q) :
    ∃ g : PrimeSymmetry p, ∀ i,
      (StackCells hp N m hm).facetSignature o i =
        g • lowerCylinderPoint (RefinedAffineMap.vertex hp N q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  have hclass : (StackCells hp N m hm).facetClass o =
      (StackCells hp N m hm).facetClass (lowerOccurrence hp N m hm q) := by
    simpa [lowerFacet] using ho
  rcases Quotient.exact hclass with ⟨g, hg⟩
  refine ⟨g⁻¹, ?_⟩
  intro i
  have hi := congrFun hg i
  have hi' := congrArg (fun z : EquivariantPrismVertexParameters.CylinderPoint p => g⁻¹ • z) hi
  rw [lowerOccurrence_facetSignature] at hi'
  simpa [mul_smul] using hi'

/-- Every representative of a canonical upper quotient facet has the prescribed endpoint vertices,
up to one simultaneous prime relabelling. -/
theorem upperFacetOccurrenceVertex_eq
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m)
    (q : TopCell hp N)
    (o : (StackCells hp N m hm).FacetOccurrence)
    (ho : (StackCells hp N m hm).facetClass o = upperFacet hp N m hm q) :
    ∃ g : PrimeSymmetry p, ∀ i,
      (StackCells hp N m hm).facetSignature o i =
        g • upperCylinderPoint (RefinedAffineMap.vertex hp N q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  have hclass : (StackCells hp N m hm).facetClass o =
      (StackCells hp N m hm).facetClass (upperOccurrence hp N m hm q) := by
    simpa [upperFacet] using ho
  rcases Quotient.exact hclass with ⟨g, hg⟩
  refine ⟨g⁻¹, ?_⟩
  intro i
  have hi := congrFun hg i
  have hi' := congrArg (fun z : EquivariantPrismVertexParameters.CylinderPoint p => g⁻¹ • z) hi
  rw [upperOccurrence_facetSignature] at hi'
  simpa [mul_smul] using hi'

/-- A positive thin-time stack is a complete endpoint-identified relative affine collar with the
original spatial level fixed at both endpoints. -/
noncomputable def endpointIdentifiedCollar
    (hp : Nat.Prime p) (N m : Nat) (hm : 0 < m) :
    EndpointIdentifiedRelativeAffineCollar hp N N N m where
  toFoxNeuwirthRelativeAffineCollar :=
    RelativeCollarThinSlabsBoundary.collar hp N m hm
  lowerFacet := lowerFacet hp N m hm
  upperFacet := upperFacet hp N m hm
  lowerFacet_isLower := lowerFacet_isLower hp N m hm
  upperFacet_isUpper := upperFacet_isUpper hp N m hm
  lowerFacet_exhaustive := lowerFacet_exhaustive hp N m hm
  upperFacet_exhaustive := upperFacet_exhaustive hp N m hm
  lowerBoundaryPairing_eq := lowerBoundaryPairing_eq hp N m hm
  upperBoundaryPairing_eq := upperBoundaryPairing_eq hp N m hm
  lowerFacetOccurrenceVertex_eq := lowerFacetOccurrenceVertex_eq hp N m hm
  upperFacetOccurrenceVertex_eq := upperFacetOccurrenceVertex_eq hp N m hm

end RelativeCollarThinSlabsEndpoints
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
