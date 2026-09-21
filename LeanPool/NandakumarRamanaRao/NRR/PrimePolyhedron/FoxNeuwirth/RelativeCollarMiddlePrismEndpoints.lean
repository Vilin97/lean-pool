/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarMiddlePrismBoundary
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarMiddlePrismEndpointsCore
/-!
# Canonical horizontal facets of the common-level middle prism

This module constructs the lower and upper horizontal quotient facets attached to every top cell at
combined refinement level `N + L`.  It also records the exact factorization of subdivision signs
under the split refinement word.  These are the endpoint maps needed by the chain-level collar
interface; no choice of a unique quotient-facet representative is made.
-/

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeCollarMiddlePrismEndpoints

/-- Enumerate the facets of the refined middle-prism cell system. -/
noncomputable local instance facetFintype (hp : Nat.Prime p) (N L : Nat) :
    Fintype (RelativeCollarMiddlePrism.cellSystem hp N L).Facet := Fintype.ofFinite _

open ExplicitAffineRelativeCollar
open EquivariantPrismGlobalCancellation
open EquivariantPrismNonhorizontalCancellation
open EquivariantPrismHorizontalEndpointIdentification
open EquivariantPrismVertexParameters
open RelativeCollarMiddlePrism
open RelativeCollarMiddlePrismBoundary
open EndpointFaceRefinement
open RelativeCollarMiddlePrismEndpointsCore
open SubdivisionPrismCharts
open RefinedAffineMap

variable {p : Nat}

/-- Split a combined-level top cell into its level-`N` prefix and length-`L` refinement tail. -/
noncomputable def splitTopCellEquiv
    (hp : Nat.Prime p) (N L : Nat) :
    TopCell hp (N + L) ≃ TopCell hp N × RefinementWord p L where
  toFun q := ((q.1, (splitRefinementWord N L q.2).1),
    (splitRefinementWord N L q.2).2)
  invFun q := endpointTopCell hp N L q.1 q.2
  left_inv := by
    intro q
    rcases q with ⟨orbit, rho⟩
    simp [endpointTopCell]
  right_inv := by
    rintro ⟨⟨orbit, rho⟩, eta⟩
    simp [endpointTopCell]

@[simp] private theorem splitTopCellEquiv_endpointTopCell
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    splitTopCellEquiv hp N L (endpointTopCell hp N L q eta) = (q, eta) :=
  (splitTopCellEquiv hp N L).apply_symm_apply (q, eta)

@[simp] private theorem splitTopCellEquiv_symm_apply
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    (splitTopCellEquiv hp N L).symm (q, eta) =
      endpointTopCell hp N L q eta := rfl

@[simp] private theorem endpointTopCell_splitTopCellEquiv
    (hp : Nat.Prime p) (N L : Nat) (q : TopCell hp (N + L)) :
    endpointTopCell hp N L (splitTopCellEquiv hp N L q).1
        (splitTopCellEquiv hp N L q).2 = q :=
  (splitTopCellEquiv hp N L).symm_apply_apply q

/-- The subdivision sign of a concatenated word factors into the two subdivision signs. -/
theorem subdivisionSign_appendRefinementWord
    (N L : Nat) (rho : RefinementWord p N) (eta : RefinementWord p L) :
    subdivisionSign (N + L) (appendRefinementWord N L rho eta) =
      subdivisionSign N rho * subdivisionSign L eta := by
  unfold subdivisionSign
  rw [Fin.prod_univ_add]
  simp [appendRefinementWord]

/-- The transported generic iterated-subdivision sign is the Fox--Neuwirth subdivision sign. -/
theorem iteratedSign_eq_subdivisionSign
    (hp : Nat.Prime p) (L : Nat) (eta : RefinementWord p L) :
    EquivariantPrismNonhorizontalCancellation.iteratedSign (n := p - 1) (ZMod p) L
        (endpointRefinementWord hp L eta) =
      subdivisionSign L eta :=
  endpointRefinementWord_sign hp L eta

/-- Coefficients factor under the prefix-tail endpoint decomposition. -/
theorem coefficient_endpointTopCell
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    coefficient hp (N + L) (endpointTopCell hp N L q eta) =
      coefficient hp N q * subdivisionSign L eta := by
  simp [coefficient, endpointTopCell, subdivisionSign_appendRefinementWord]
  ring

/-- Canonical lower quotient facet of a combined-level top cell. -/
noncomputable def lowerFacet
    (hp : Nat.Prime p) (N L : Nat) (q : TopCell hp (N + L)) :
    (RelativeCollarMiddlePrism.cellSystem hp N L).Facet :=
  let data := splitTopCellEquiv hp N L q
  (RelativeCollarMiddlePrism.cellSystem hp N L).facetClass
    (lowerOccurrence hp N L data.1 data.2)

/-- Canonical upper quotient facet of a combined-level top cell. -/
noncomputable def upperFacet
    (hp : Nat.Prime p) (N L : Nat) (q : TopCell hp (N + L)) :
    (RelativeCollarMiddlePrism.cellSystem hp N L).Facet :=
  let data := splitTopCellEquiv hp N L q
  (RelativeCollarMiddlePrism.cellSystem hp N L).facetClass
    (upperOccurrence hp N L data.1 data.2)

/-- Every canonical lower endpoint facet belongs to the lower horizontal boundary. -/
theorem lowerFacet_isLower
    (hp : Nat.Prime p) (N L : Nat) (q : TopCell hp (N + L)) :
    (RelativeCollarMiddlePrism.cellSystem hp N L).IsLowerFacet
      (lowerFacet hp N L q) := by
  let data := splitTopCellEquiv hp N L q
  change (RelativeCollarMiddlePrism.cellSystem hp N L).IsLowerFacet
    ((RelativeCollarMiddlePrism.cellSystem hp N L).facetClass
      (lowerOccurrence hp N L data.1 data.2))
  exact lowerOccurrence_isLower hp N L data.1 data.2

/-- Every canonical upper endpoint facet belongs to the upper horizontal boundary. -/
theorem upperFacet_isUpper
    (hp : Nat.Prime p) (N L : Nat) (q : TopCell hp (N + L)) :
    (RelativeCollarMiddlePrism.cellSystem hp N L).IsUpperFacet
      (upperFacet hp N L q) := by
  let data := splitTopCellEquiv hp N L q
  change (RelativeCollarMiddlePrism.cellSystem hp N L).IsUpperFacet
    ((RelativeCollarMiddlePrism.cellSystem hp N L).facetClass
      (upperOccurrence hp N L data.1 data.2))
  exact upperOccurrence_isUpper hp N L data.1 data.2


open scoped Classical in
/-- Canonical lower endpoint map evaluated on its actual occurrence is the Kronecker weight of the
corresponding quotient facet. -/
theorem facetOrbitIndicator_lowerEndpointMap
    (hp : Nat.Prime p) (N L : Nat)
    (s : (RelativeCollarMiddlePrism.cellSystem hp N L).Facet)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    facetOrbitIndicator hp N L s
        (lowerEndpointMap (endpointSpatialMap hp N L q eta)) =
      if lowerFacet hp N L (endpointTopCell hp N L q eta) = s then 1 else 0 := by
  rw [← lowerOccurrenceFacetMap_eq hp N L q eta]
  simpa [lowerFacet] using
    facetOrbitIndicator_occurrence hp N L s (lowerOccurrence hp N L q eta)

open scoped Classical in
/-- Upper endpoint analogue of `facetOrbitIndicator_lowerEndpointMap`. -/
theorem facetOrbitIndicator_upperEndpointMap
    (hp : Nat.Prime p) (N L : Nat)
    (s : (RelativeCollarMiddlePrism.cellSystem hp N L).Facet)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    facetOrbitIndicator hp N L s
        (upperEndpointMap (endpointSpatialMap hp N L q eta)) =
      if upperFacet hp N L (endpointTopCell hp N L q eta) = s then 1 else 0 := by
  rw [← upperOccurrenceFacetMap_eq hp N L q eta]
  simpa [upperFacet] using
    facetOrbitIndicator_occurrence hp N L s (upperOccurrence hp N L q eta)

/-- Pairing the lower boundary coefficients against an arbitrary quotient-facet weight gives the
split refined Fox--Neuwirth endpoint chain. -/
theorem lowerBoundaryPairing_eq_split
    (hp : Nat.Prime p) (N L : Nat)
    (W : (RelativeCollarMiddlePrism.cellSystem hp N L).Facet → ZMod p) :
    (∑ s : (RelativeCollarMiddlePrism.cellSystem hp N L).Facet,
        lowerBoundaryCoefficient hp N L s * W s) =
      ∑ q : TopCell hp N,
        coefficient hp N q *
          ∑ eta : RefinementWord p L,
            subdivisionSign L eta *
              W (lowerFacet hp N L (endpointTopCell hp N L q eta)) := by
  classical
  unfold lowerBoundaryCoefficient lowerEndpointPairing
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  change (∑ s,
      (coefficient hp N q *
        ∑ eta, subdivisionSign L eta *
          facetOrbitIndicator hp N L s
            (lowerEndpointMap (endpointSpatialMap hp N L q eta))) * W s) = _
  calc
    _ = coefficient hp N q *
        ∑ eta, subdivisionSign L eta *
          ∑ s, facetOrbitIndicator hp N L s
            (lowerEndpointMap (endpointSpatialMap hp N L q eta)) * W s := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      ring_nf
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro eta heta
      simp [facetOrbitIndicator_lowerEndpointMap]

/-- Pairing the upper boundary coefficients against an arbitrary quotient-facet weight gives the
split refined Fox--Neuwirth endpoint chain. -/
theorem upperBoundaryPairing_eq_split
    (hp : Nat.Prime p) (N L : Nat)
    (W : (RelativeCollarMiddlePrism.cellSystem hp N L).Facet → ZMod p) :
    (∑ s : (RelativeCollarMiddlePrism.cellSystem hp N L).Facet,
        upperBoundaryCoefficient hp N L s * W s) =
      ∑ q : TopCell hp N,
        coefficient hp N q *
          ∑ eta : RefinementWord p L,
            subdivisionSign L eta *
              W (upperFacet hp N L (endpointTopCell hp N L q eta)) := by
  classical
  unfold upperBoundaryCoefficient upperEndpointPairing
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  change (∑ s,
      (coefficient hp N q *
        ∑ eta, subdivisionSign L eta *
          facetOrbitIndicator hp N L s
            (upperEndpointMap (endpointSpatialMap hp N L q eta))) * W s) = _
  calc
    _ = coefficient hp N q *
        ∑ eta, subdivisionSign L eta *
          ∑ s, facetOrbitIndicator hp N L s
            (upperEndpointMap (endpointSpatialMap hp N L q eta)) * W s := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      ring_nf
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro eta heta
      simp [facetOrbitIndicator_upperEndpointMap]

/-- Chain-level lower endpoint identification at the combined subdivision level. -/
theorem lowerBoundaryPairing_eq
    (hp : Nat.Prime p) (N L : Nat)
    (W : (RelativeCollarMiddlePrism.cellSystem hp N L).Facet → ZMod p) :
    (∑ s : (RelativeCollarMiddlePrism.cellSystem hp N L).Facet,
        lowerBoundaryCoefficient hp N L s * W s) =
      ∑ q : TopCell hp (N + L),
        coefficient hp (N + L) q * W (lowerFacet hp N L q) := by
  rw [lowerBoundaryPairing_eq_split]
  conv_lhs =>
    enter [2, q]
    rw [Finset.mul_sum]
  rw [← Equiv.sum_comp (splitTopCellEquiv hp N L).symm]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro eta heta
  simp only [splitTopCellEquiv_symm_apply, coefficient_endpointTopCell]
  ring

/-- Chain-level upper endpoint identification at the combined subdivision level. -/
theorem upperBoundaryPairing_eq
    (hp : Nat.Prime p) (N L : Nat)
    (W : (RelativeCollarMiddlePrism.cellSystem hp N L).Facet → ZMod p) :
    (∑ s : (RelativeCollarMiddlePrism.cellSystem hp N L).Facet,
        upperBoundaryCoefficient hp N L s * W s) =
      ∑ q : TopCell hp (N + L),
        coefficient hp (N + L) q * W (upperFacet hp N L q) := by
  rw [upperBoundaryPairing_eq_split]
  conv_lhs =>
    enter [2, q]
    rw [Finset.mul_sum]
  rw [← Equiv.sum_comp (splitTopCellEquiv hp N L).symm]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro eta heta
  simp only [splitTopCellEquiv_symm_apply, coefficient_endpointTopCell]
  ring

/-- Every representative of a canonical lower quotient facet has the prescribed endpoint vertices,
up to one simultaneous prime relabelling. -/
theorem lowerFacetOccurrenceVertex_eq
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp (N + L))
    (o : (RelativeCollarMiddlePrism.cellSystem hp N L).FacetOccurrence)
    (ho : (RelativeCollarMiddlePrism.cellSystem hp N L).facetClass o =
      lowerFacet hp N L q) :
    ∃ g : PrimeSymmetry hp, ∀ i,
      (RelativeCollarMiddlePrism.cellSystem hp N L).facetSignature o i =
        g • ExplicitAffineRelativeCollar.lowerCylinderPoint
          (RefinedAffineMap.vertex hp (N + L) q
            (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  let data := splitTopCellEquiv hp N L q
  have hclass : (RelativeCollarMiddlePrism.cellSystem hp N L).facetClass o =
      (RelativeCollarMiddlePrism.cellSystem hp N L).facetClass
        (lowerOccurrence hp N L data.1 data.2) := by
    simpa [lowerFacet, data] using ho
  rcases Quotient.exact hclass with ⟨g, hg⟩
  refine ⟨g⁻¹, ?_⟩
  intro i
  have hi := congrFun hg i
  have hq : endpointTopCell hp N L data.1 data.2 = q := by
    simpa [data, splitTopCellEquiv] using
      (splitTopCellEquiv hp N L).symm_apply_apply q
  have hend := lowerOccurrence_facetSignature hp N L data.1 data.2 i
  have hgi := congrArg (fun z : CylinderPoint p => g⁻¹ • z) hi
  rw [hend, hq] at hgi
  simpa [mul_smul] using hgi

/-- Every representative of a canonical upper quotient facet has the prescribed endpoint vertices,
up to one simultaneous prime relabelling. -/
theorem upperFacetOccurrenceVertex_eq
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp (N + L))
    (o : (RelativeCollarMiddlePrism.cellSystem hp N L).FacetOccurrence)
    (ho : (RelativeCollarMiddlePrism.cellSystem hp N L).facetClass o =
      upperFacet hp N L q) :
    ∃ g : PrimeSymmetry hp, ∀ i,
      (RelativeCollarMiddlePrism.cellSystem hp N L).facetSignature o i =
        g • ExplicitAffineRelativeCollar.upperCylinderPoint
          (RefinedAffineMap.vertex hp (N + L) q
            (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  let data := splitTopCellEquiv hp N L q
  have hclass : (RelativeCollarMiddlePrism.cellSystem hp N L).facetClass o =
      (RelativeCollarMiddlePrism.cellSystem hp N L).facetClass
        (upperOccurrence hp N L data.1 data.2) := by
    simpa [upperFacet, data] using ho
  rcases Quotient.exact hclass with ⟨g, hg⟩
  refine ⟨g⁻¹, ?_⟩
  intro i
  have hi := congrFun hg i
  have hq : endpointTopCell hp N L data.1 data.2 = q := by
    simpa [data, splitTopCellEquiv] using
      (splitTopCellEquiv hp N L).symm_apply_apply q
  have hend := upperOccurrence_facetSignature hp N L data.1 data.2 i
  have hgi := congrArg (fun z : CylinderPoint p => g⁻¹ • z) hi
  rw [hend, hq] at hgi
  simpa [mul_smul] using hgi

/-- The unique empty endpoint refinement word. -/
def emptyEndpointRefinementWord (p : Nat) : RefinementWord p 0 :=
  fun i => Fin.elim0 i

/-- At prism refinement level zero, every lower horizontal occurrence is the canonical lower
occurrence of its spatial top cell. -/
theorem lowerOccurrence_classification_zero
    (hp : Nat.Prime p) (N : Nat)
    (o : (RelativeCollarMiddlePrism.cellSystem hp N 0).FacetOccurrence)
    (ho : (RelativeCollarMiddlePrism.cellSystem hp N 0).IsLowerFacetOccurrence o) :
    ∃ q : TopCell hp N,
      (RelativeCollarMiddlePrism.cellSystem hp N 0).facetClass o =
        (RelativeCollarMiddlePrism.cellSystem hp N 0).facetClass
          (lowerOccurrence hp N 0 q (emptyEndpointRefinementWord p)) := by
  rcases o with ⟨⟨⟨q, k⟩, rho⟩, j⟩
  have htime : ∀ i : Fin p, staircaseTime k (j.succAbove i) = 0 := by
    intro i
    have hi := ho i
    simp [RelativeCollarMiddlePrism.cellSystem,
      RelativeAffineCellSystem.facetSignature,
      RelativeCollarMiddlePrism.vertex, SubdivisionPrismCharts.vertex,
      SubdivisionPrismCharts.chart, staircasePoint, intervalPoint,
      intervalWeight, CylinderPoint.ofProd, StandardSimplex.ofDelta,
      stdSimplex.vertex, Pi.single_apply, affineCompMap] at hi
    apply staircaseTime_lower
    by_contra h
    have hlt : k.val < (j.succAbove i).val := Nat.lt_of_not_ge h
    have hsum :
        (∑ x : Fin (p + 1),
          if k.val < x.val then
            if x = j.succAbove i then (1 : Real) else 0
          else 0) = 1 := by
      rw [Finset.sum_eq_single (j.succAbove i)]
      · simp [hlt]
      · intro b hb hne
        simp [hne]
      · simp
    have hi' :
        (∑ x : Fin (p + 1),
          if k.val < x.val then
            if x = j.succAbove i then (1 : Real) else 0
          else 0) = 0 := by
      simpa [staircaseTime] using hi
    linarith
  rcases lowerStaircaseFacet_indices hp k j htime with ⟨hk, hj⟩
  subst k
  subst j
  have hrho : rho = liftBoundaryRefinementWord 0 (Fin.last p)
      (emptyEndpointRefinementWord p) := Subsingleton.elim _ _
  subst rho
  refine ⟨q, ?_⟩
  rfl

/-- At prism refinement level zero, every upper horizontal occurrence is the canonical upper
occurrence of its spatial top cell. -/
theorem upperOccurrence_classification_zero
    (hp : Nat.Prime p) (N : Nat)
    (o : (RelativeCollarMiddlePrism.cellSystem hp N 0).FacetOccurrence)
    (ho : (RelativeCollarMiddlePrism.cellSystem hp N 0).IsUpperFacetOccurrence o) :
    ∃ q : TopCell hp N,
      (RelativeCollarMiddlePrism.cellSystem hp N 0).facetClass o =
        (RelativeCollarMiddlePrism.cellSystem hp N 0).facetClass
          (upperOccurrence hp N 0 q (emptyEndpointRefinementWord p)) := by
  rcases o with ⟨⟨⟨q, k⟩, rho⟩, j⟩
  have htime : ∀ i : Fin p, staircaseTime k (j.succAbove i) = 1 := by
    intro i
    have hi := ho i
    simp [RelativeCollarMiddlePrism.cellSystem,
      RelativeAffineCellSystem.facetSignature,
      RelativeCollarMiddlePrism.vertex, SubdivisionPrismCharts.vertex,
      SubdivisionPrismCharts.chart, staircasePoint, intervalPoint,
      intervalWeight, CylinderPoint.ofProd, StandardSimplex.ofDelta,
      stdSimplex.vertex, Pi.single_apply, affineCompMap] at hi
    apply staircaseTime_upper
    by_contra h
    have hle : (j.succAbove i).val ≤ k.val := Nat.le_of_not_gt h
    have hsum :
        (∑ x : Fin (p + 1),
          if k.val < x.val then
            if x = j.succAbove i then (1 : Real) else 0
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      by_cases hbj : b = j.succAbove i
      · subst b
        simp [not_lt_of_ge hle]
      · simp [hbj]
    have hi' :
        (∑ x : Fin (p + 1),
          if k.val < x.val then
            if x = j.succAbove i then (1 : Real) else 0
          else 0) = 1 := by
      simpa [staircaseTime] using hi
    linarith
  rcases upperStaircaseFacet_indices hp k j htime with ⟨hk, hj⟩
  subst k
  subst j
  have hrho : rho = liftBoundaryRefinementWord 0 0
      (emptyEndpointRefinementWord p) := Subsingleton.elim _ _
  subst rho
  refine ⟨q, ?_⟩
  rfl

/-- The one remaining combinatorial condition needed to package the common-level middle prism as an
endpoint-identified collar: every geometric horizontal facet must occur in the corresponding
refined endpoint chain. -/
def HorizontalFacetExhaustive
    (hp : Nat.Prime p) (N L : Nat) : Prop :=
  (∀ s, (RelativeCollarMiddlePrism.cellSystem hp N L).IsLowerFacet s →
      ∃ q : TopCell hp (N + L), lowerFacet hp N L q = s) ∧
    (∀ s, (RelativeCollarMiddlePrism.cellSystem hp N L).IsUpperFacet s →
      ∃ q : TopCell hp (N + L), upperFacet hp N L q = s)

/-- Horizontal-facet exhaustiveness is completely explicit before any additional prism
barycentric subdivision. -/
theorem horizontalFacetExhaustive_zero
    (hp : Nat.Prime p) (N : Nat) : HorizontalFacetExhaustive hp N 0 := by
  constructor
  · intro s hs
    refine Quotient.inductionOn s (fun o ho => ?_) hs
    obtain ⟨q, hq⟩ := lowerOccurrence_classification_zero hp N o ho
    refine ⟨endpointTopCell hp N 0 q (emptyEndpointRefinementWord p), ?_⟩
    simp only [lowerFacet, splitTopCellEquiv_endpointTopCell, Prod.fst, Prod.snd]
    calc
      _ = (RelativeCollarMiddlePrism.cellSystem hp N 0).facetClass o := hq.symm
      _ = Quotient.mk _ o := rfl
  · intro s hs
    refine Quotient.inductionOn s (fun o ho => ?_) hs
    obtain ⟨q, hq⟩ := upperOccurrence_classification_zero hp N o ho
    refine ⟨endpointTopCell hp N 0 q (emptyEndpointRefinementWord p), ?_⟩
    simp only [upperFacet, splitTopCellEquiv_endpointTopCell, Prod.fst, Prod.snd]
    calc
      _ = (RelativeCollarMiddlePrism.cellSystem hp N 0).facetClass o := hq.symm
      _ = Quotient.mk _ o := rfl

/-- Horizontal-facet exhaustiveness makes the common-level middle prism a genuine
endpoint-identified relative affine collar.  All incidence, chain-pairing, and endpoint-geometry
fields are already proved above. -/
noncomputable def endpointIdentifiedCollar
    (hp : Nat.Prime p) (N L : Nat)
    (hexhaustive : HorizontalFacetExhaustive hp N L) :
    EndpointIdentifiedRelativeAffineCollar hp (N + L) (N + L) (N + L) L where
  toFoxNeuwirthRelativeAffineCollar := RelativeCollarMiddlePrismBoundary.collar hp N L
  lowerFacet := lowerFacet hp N L
  upperFacet := upperFacet hp N L
  lowerFacet_isLower := lowerFacet_isLower hp N L
  upperFacet_isUpper := upperFacet_isUpper hp N L
  lowerFacet_exhaustive := hexhaustive.1
  upperFacet_exhaustive := hexhaustive.2
  lowerBoundaryPairing_eq := lowerBoundaryPairing_eq hp N L
  upperBoundaryPairing_eq := upperBoundaryPairing_eq hp N L
  lowerFacetOccurrenceVertex_eq := lowerFacetOccurrenceVertex_eq hp N L
  upperFacetOccurrenceVertex_eq := upperFacetOccurrenceVertex_eq hp N L

/-- The unrefined common-level staircase prism is therefore already a complete
endpoint-identified collar. -/
noncomputable def endpointIdentifiedCollarZero
    (hp : Nat.Prime p) (N : Nat) :
    EndpointIdentifiedRelativeAffineCollar hp N N N 0 := by
  simpa using endpointIdentifiedCollar hp N 0 (horizontalFacetExhaustive_zero hp N)



end RelativeCollarMiddlePrismEndpoints
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
