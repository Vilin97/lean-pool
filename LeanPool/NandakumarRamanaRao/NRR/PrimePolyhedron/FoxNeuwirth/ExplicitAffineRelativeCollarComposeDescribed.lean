/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarCompose
/-!
# Composition with described internal endpoints

The fully refined middle prism has canonical lower and upper endpoint facets, exact endpoint chain
pairings, and representative geometry.  What is not available is a standalone theorem saying that
every horizontal quotient facet is one of those canonical facets.  That stronger exhaustiveness
property is unnecessary for an *internal* collar region.

This module separates the data used for seam cancellation from the external-facet exhaustiveness
needed by `EndpointIdentifiedRelativeAffineCollar`.  Two endpoint-described collars compose, and
the result can be packaged as endpoint-identified whenever the left input has exhaustive lower
facets and the right input has exhaustive upper facets.  Thus a refined middle prism can be placed
between two genuine endpoint stacks without assuming an unproved middle-prism exhaustiveness
lemma.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollarComposeDescribed

open scoped BigOperators
open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollarCompose

variable {p N₀ Nmid N₁ M₀ M₁ L₀ L₁ : Nat}
variable {hp : Nat.Prime p}

/-- Endpoint data sufficient for chain-level seam cancellation.  Unlike
`EndpointIdentifiedRelativeAffineCollar`, no exhaustiveness is requested for either horizontal
quotient-facet family. -/
structure EndpointDescribedRelativeAffineCollar
    (hp : Nat.Prime p) (N₀ N₁ M L : Nat)
    extends FoxNeuwirthRelativeAffineCollar hp N₀ N₁ M L where
  lowerFacet : TopCell hp N₀ → cells.Facet
  upperFacet : TopCell hp N₁ → cells.Facet
  lowerFacet_isLower : ∀ q, cells.IsLowerFacet (lowerFacet q)
  upperFacet_isUpper : ∀ q, cells.IsUpperFacet (upperFacet q)
  lowerBoundaryPairing_eq : ∀ W : cells.Facet → ZMod p,
    (∑ s : cells.Facet, lowerBoundaryCoefficient s * W s) =
      ∑ q : TopCell hp N₀, RefinedAffineMap.coefficient hp N₀ q * W (lowerFacet q)
  upperBoundaryPairing_eq : ∀ W : cells.Facet → ZMod p,
    (∑ s : cells.Facet, upperBoundaryCoefficient s * W s) =
      ∑ q : TopCell hp N₁, RefinedAffineMap.coefficient hp N₁ q * W (upperFacet q)
  lowerFacetOccurrenceVertex_eq : ∀ q o,
    cells.facetClass o = lowerFacet q →
      ∃ g : PrimeSymmetry hp, ∀ i, cells.facetSignature o i =
        g • lowerCylinderPoint (RefinedAffineMap.vertex hp N₀ q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))
  upperFacetOccurrenceVertex_eq : ∀ q o,
    cells.facetClass o = upperFacet q →
      ∃ g : PrimeSymmetry hp, ∀ i, cells.facetSignature o i =
        g • upperCylinderPoint (RefinedAffineMap.vertex hp N₁ q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i))

namespace EndpointDescribedRelativeAffineCollar

/-- Forget only endpoint-facet exhaustiveness. -/
noncomputable def ofEndpointIdentified
    (C : EndpointIdentifiedRelativeAffineCollar hp N₀ N₁ M₀ L₀) :
    EndpointDescribedRelativeAffineCollar hp N₀ N₁ M₀ L₀ where
  toFoxNeuwirthRelativeAffineCollar := C.toFoxNeuwirthRelativeAffineCollar
  lowerFacet := C.lowerFacet
  upperFacet := C.upperFacet
  lowerFacet_isLower := C.lowerFacet_isLower
  upperFacet_isUpper := C.upperFacet_isUpper
  lowerBoundaryPairing_eq := C.lowerBoundaryPairing_eq
  upperBoundaryPairing_eq := C.upperBoundaryPairing_eq
  lowerFacetOccurrenceVertex_eq := C.lowerFacetOccurrenceVertex_eq
  upperFacetOccurrenceVertex_eq := C.upperFacetOccurrenceVertex_eq

end EndpointDescribedRelativeAffineCollar

variable
    (C : EndpointDescribedRelativeAffineCollar hp N₀ Nmid M₀ L₀)
    (D : EndpointDescribedRelativeAffineCollar hp Nmid N₁ M₁ L₁)

/-- The two described copies of every common endpoint top cell determine the same combined
quotient facet. -/
theorem internalFacet_eq (q : TopCell hp Nmid) :
    Combined.leftFacet C.cells D.cells (C.upperFacet q) =
      Combined.rightFacet C.cells D.cells (D.lowerFacet q) := by
  obtain ⟨oc, hoc⟩ := Quotient.exists_rep (C.upperFacet q)
  obtain ⟨od, hod⟩ := Quotient.exists_rep (D.lowerFacet q)
  rw [← hoc, ← hod]
  apply Quotient.sound
  obtain ⟨gc, hgc⟩ := C.upperFacetOccurrenceVertex_eq q oc hoc
  obtain ⟨gd, hgd⟩ := D.lowerFacetOccurrenceVertex_eq q od hod
  refine ⟨gd * gc⁻¹, ?_⟩
  funext i
  simp only [Combined.left_facetSignature, Combined.right_facetSignature]
  rw [hgc i, hgd i]
  simp [mul_smul]

/-- External lower coefficient inherited from the left collar. -/
noncomputable def lowerBoundaryCoefficient
    (s : (combinedCells C.cells D.cells).Facet) : ZMod p :=
  ∑ q : TopCell hp N₀,
    RefinedAffineMap.coefficient hp N₀ q *
      Combined.leftIndicator C.cells D.cells s (C.lowerFacet q)

/-- External upper coefficient inherited from the right collar. -/
noncomputable def upperBoundaryCoefficient
    (s : (combinedCells C.cells D.cells).Facet) : ZMod p :=
  ∑ q : TopCell hp N₁,
    RefinedAffineMap.coefficient hp N₁ q *
      Combined.rightIndicator C.cells D.cells s (D.upperFacet q)

/-- The described common endpoint pairings cancel pointwise. -/
theorem internalPairings_eq
    (s : (combinedCells C.cells D.cells).Facet) :
    (∑ t : C.cells.Facet,
      C.upperBoundaryCoefficient t * Combined.leftIndicator C.cells D.cells s t) =
    (∑ t : D.cells.Facet,
      D.lowerBoundaryCoefficient t * Combined.rightIndicator C.cells D.cells s t) := by
  rw [C.upperBoundaryPairing_eq, D.lowerBoundaryPairing_eq]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Combined.leftIndicator, Combined.rightIndicator, internalFacet_eq C D q]

/-- Pointwise boundary formula for composition with described internal endpoints. -/
theorem incidence_eq_boundary
    (s : (combinedCells C.cells D.cells).Facet) :
    (combinedCells C.cells D.cells).facetIncidence s =
      upperBoundaryCoefficient C D s - lowerBoundaryCoefficient C D s := by
  rw [Combined.combined_facetIncidence]
  simp_rw [C.incidence_eq_boundary, D.incidence_eq_boundary]
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [internalPairings_eq C D]
  rw [C.lowerBoundaryPairing_eq, D.upperBoundaryPairing_eq]
  unfold upperBoundaryCoefficient lowerBoundaryCoefficient
  ring

/-- Canonical external lower facets remain lower-horizontal. -/
theorem lowerFacet_isLower (q : TopCell hp N₀) :
    (combinedCells C.cells D.cells).IsLowerFacet
      (Combined.leftFacet C.cells D.cells (C.lowerFacet q)) := by
  obtain ⟨o, ho⟩ := Quotient.exists_rep (C.lowerFacet q)
  rw [← ho]
  change (combinedCells C.cells D.cells).IsLowerFacetOccurrence
    (Combined.leftOccurrence C.cells D.cells o)
  intro i
  have h := C.lowerFacet_isLower q
  rw [← ho] at h
  simp only [Combined.left_facetSignature, leftPoint_time]
  simp [h i]

/-- Canonical external upper facets remain upper-horizontal. -/
theorem upperFacet_isUpper (q : TopCell hp N₁) :
    (combinedCells C.cells D.cells).IsUpperFacet
      (Combined.rightFacet C.cells D.cells (D.upperFacet q)) := by
  obtain ⟨o, ho⟩ := Quotient.exists_rep (D.upperFacet q)
  rw [← ho]
  change (combinedCells C.cells D.cells).IsUpperFacetOccurrence
    (Combined.rightOccurrence C.cells D.cells o)
  intro i
  simp [Combined.right_facetSignature]
  have h := D.upperFacet_isUpper q
  rw [← ho] at h
  linarith [h i]

/-- External lower coefficients vanish away from time zero. -/
theorem lowerBoundaryCoefficient_zero_of_not_lower
    (s : (combinedCells C.cells D.cells).Facet)
    (hs : ¬ (combinedCells C.cells D.cells).IsLowerFacet s) :
    lowerBoundaryCoefficient C D s = 0 := by
  classical
  unfold lowerBoundaryCoefficient
  apply Finset.sum_eq_zero
  intro q hq
  have hne : Combined.leftFacet C.cells D.cells (C.lowerFacet q) ≠ s := by
    intro h
    apply hs
    rw [← h]
    exact lowerFacet_isLower C D q
  simp [Combined.leftIndicator, hne]

/-- External upper coefficients vanish away from time one. -/
theorem upperBoundaryCoefficient_zero_of_not_upper
    (s : (combinedCells C.cells D.cells).Facet)
    (hs : ¬ (combinedCells C.cells D.cells).IsUpperFacet s) :
    upperBoundaryCoefficient C D s = 0 := by
  classical
  unfold upperBoundaryCoefficient
  apply Finset.sum_eq_zero
  intro q hq
  have hne : Combined.rightFacet C.cells D.cells (D.upperFacet q) ≠ s := by
    intro h
    apply hs
    rw [← h]
    exact upperFacet_isUpper C D q
  simp [Combined.rightIndicator, hne]

/-- Lower endpoint chain pairing of the described composition. -/
theorem lowerBoundaryPairing_eq
    (W : (combinedCells C.cells D.cells).Facet → ZMod p) :
    (∑ s : (combinedCells C.cells D.cells).Facet,
      lowerBoundaryCoefficient C D s * W s) =
      ∑ q : TopCell hp N₀, RefinedAffineMap.coefficient hp N₀ q *
        W (Combined.leftFacet C.cells D.cells (C.lowerFacet q)) := by
  classical
  unfold lowerBoundaryCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Combined.leftIndicator, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- Upper endpoint chain pairing of the described composition. -/
theorem upperBoundaryPairing_eq
    (W : (combinedCells C.cells D.cells).Facet → ZMod p) :
    (∑ s : (combinedCells C.cells D.cells).Facet,
      upperBoundaryCoefficient C D s * W s) =
      ∑ q : TopCell hp N₁, RefinedAffineMap.coefficient hp N₁ q *
        W (Combined.rightFacet C.cells D.cells (D.upperFacet q)) := by
  classical
  unfold upperBoundaryCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Combined.rightIndicator, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- Representatives of external lower facets retain the prescribed endpoint geometry. -/
theorem lowerFacetOccurrenceVertex_eq
    (q : TopCell hp N₀)
    (o : (combinedCells C.cells D.cells).FacetOccurrence)
    (ho : (combinedCells C.cells D.cells).facetClass o =
      Combined.leftFacet C.cells D.cells (C.lowerFacet q)) :
    ∃ g : PrimeSymmetry hp, ∀ i,
      (combinedCells C.cells D.cells).facetSignature o i =
        g • lowerCylinderPoint (RefinedAffineMap.vertex hp N₀ q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  rcases o with ⟨cell, k⟩
  cases cell with
  | inl cell =>
      let oc : C.cells.FacetOccurrence := (cell, k)
      have hc : C.cells.facetClass oc = C.lowerFacet q := by
        apply Combined.leftFacet_injective C.cells D.cells
        simpa [oc, Combined.leftOccurrence] using ho
      obtain ⟨g, hg⟩ := C.lowerFacetOccurrenceVertex_eq q oc hc
      refine ⟨g, ?_⟩
      intro i
      simpa [oc, combinedCells, Combined.leftOccurrence,
        ExplicitAffineRelativeCollar.RelativeAffineCellSystem.facetSignature] using
        congrArg leftPoint (hg i)
  | inr cell =>
      have hlower : (combinedCells C.cells D.cells).IsLowerFacet
          ((combinedCells C.cells D.cells).facetClass (Sum.inr cell, k)) := by
        rw [ho]
        exact lowerFacet_isLower C D q
      change (combinedCells C.cells D.cells).IsLowerFacetOccurrence
        (Sum.inr cell, k) at hlower
      let i : Fin p := ⟨0, hp.pos⟩
      have hi := hlower i
      have hnonneg := (D.cells.facetSignature (cell, k) i).time.2.1
      change (1 + (D.cells.facetSignature (cell, k) i).time.1) / 2 = 0 at hi
      exfalso
      linarith

/-- Representatives of external upper facets retain the prescribed endpoint geometry. -/
theorem upperFacetOccurrenceVertex_eq
    (q : TopCell hp N₁)
    (o : (combinedCells C.cells D.cells).FacetOccurrence)
    (ho : (combinedCells C.cells D.cells).facetClass o =
      Combined.rightFacet C.cells D.cells (D.upperFacet q)) :
    ∃ g : PrimeSymmetry hp, ∀ i,
      (combinedCells C.cells D.cells).facetSignature o i =
        g • upperCylinderPoint (RefinedAffineMap.vertex hp N₁ q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  rcases o with ⟨cell, k⟩
  cases cell with
  | inl cell =>
      have hupper : (combinedCells C.cells D.cells).IsUpperFacet
          ((combinedCells C.cells D.cells).facetClass (Sum.inl cell, k)) := by
        rw [ho]
        exact upperFacet_isUpper C D q
      change (combinedCells C.cells D.cells).IsUpperFacetOccurrence
        (Sum.inl cell, k) at hupper
      let i : Fin p := ⟨0, hp.pos⟩
      have hi := hupper i
      have hle := (C.cells.facetSignature (cell, k) i).time.2.2
      change (C.cells.facetSignature (cell, k) i).time.1 / 2 = 1 at hi
      exfalso
      linarith
  | inr cell =>
      let od : D.cells.FacetOccurrence := (cell, k)
      have hd : D.cells.facetClass od = D.upperFacet q := by
        apply Combined.rightFacet_injective C.cells D.cells
        simpa [od, Combined.rightOccurrence] using ho
      obtain ⟨g, hg⟩ := D.upperFacetOccurrenceVertex_eq q od hd
      refine ⟨g, ?_⟩
      intro i
      simpa [od, combinedCells, Combined.rightOccurrence,
        ExplicitAffineRelativeCollar.RelativeAffineCellSystem.facetSignature] using
        congrArg rightPoint (hg i)

/-- Composition preserving all endpoint data used by a later seam. -/
noncomputable def describedCollar :
    EndpointDescribedRelativeAffineCollar hp N₀ N₁ (max M₀ M₁) (L₀ + L₁ + 1) where
  toFoxNeuwirthRelativeAffineCollar := {
    cells := combinedCells C.cells D.cells
    lowerBoundaryCoefficient := lowerBoundaryCoefficient C D
    upperBoundaryCoefficient := upperBoundaryCoefficient C D
    lower_zero_of_not_lower := lowerBoundaryCoefficient_zero_of_not_lower C D
    upper_zero_of_not_upper := upperBoundaryCoefficient_zero_of_not_upper C D
    incidence_eq_boundary := incidence_eq_boundary C D
  }
  lowerFacet q := Combined.leftFacet C.cells D.cells (C.lowerFacet q)
  upperFacet q := Combined.rightFacet C.cells D.cells (D.upperFacet q)
  lowerFacet_isLower := lowerFacet_isLower C D
  upperFacet_isUpper := upperFacet_isUpper C D
  lowerBoundaryPairing_eq := lowerBoundaryPairing_eq C D
  upperBoundaryPairing_eq := upperBoundaryPairing_eq C D
  lowerFacetOccurrenceVertex_eq := lowerFacetOccurrenceVertex_eq C D
  upperFacetOccurrenceVertex_eq := upperFacetOccurrenceVertex_eq C D

/-- Lower-facet exhaustiveness propagates from the left external region; no endpoint
exhaustiveness is required of the right internal region. -/
theorem lowerFacet_exhaustive_of_left
    (hC : ∀ s, C.cells.IsLowerFacet s → ∃ q, C.lowerFacet q = s)
    (s : (combinedCells C.cells D.cells).Facet)
    (hs : (combinedCells C.cells D.cells).IsLowerFacet s) :
    ∃ q : TopCell hp N₀,
      Combined.leftFacet C.cells D.cells (C.lowerFacet q) = s := by
  refine Quotient.inductionOn s (fun o ho => ?_) hs
  rcases o with ⟨cell, k⟩
  cases cell with
  | inl cell =>
      let oc : C.cells.FacetOccurrence := (cell, k)
      have hc : C.cells.IsLowerFacetOccurrence oc := by
        intro i
        have hi := ho i
        change (C.cells.facetSignature oc i).time.1 / 2 = 0 at hi
        linarith
      obtain ⟨q, hq⟩ := hC (C.cells.facetClass oc) hc
      refine ⟨q, ?_⟩
      rw [hq]
      rfl
  | inr cell =>
      let i : Fin p := ⟨0, hp.pos⟩
      have hi := ho i
      have hnonneg := (D.cells.facetSignature (cell, k) i).time.2.1
      change (1 + (D.cells.facetSignature (cell, k) i).time.1) / 2 = 0 at hi
      linarith

/-- Upper-facet exhaustiveness propagates from the right external region. -/
theorem upperFacet_exhaustive_of_right
    (hD : ∀ s, D.cells.IsUpperFacet s → ∃ q, D.upperFacet q = s)
    (s : (combinedCells C.cells D.cells).Facet)
    (hs : (combinedCells C.cells D.cells).IsUpperFacet s) :
    ∃ q : TopCell hp N₁,
      Combined.rightFacet C.cells D.cells (D.upperFacet q) = s := by
  refine Quotient.inductionOn s (fun o ho => ?_) hs
  rcases o with ⟨cell, k⟩
  cases cell with
  | inl cell =>
      let i : Fin p := ⟨0, hp.pos⟩
      have hi := ho i
      have hle := (C.cells.facetSignature (cell, k) i).time.2.2
      change (C.cells.facetSignature (cell, k) i).time.1 / 2 = 1 at hi
      linarith
  | inr cell =>
      let od : D.cells.FacetOccurrence := (cell, k)
      have hd : D.cells.IsUpperFacetOccurrence od := by
        intro i
        have hi := ho i
        change (1 + (D.cells.facetSignature od i).time.1) / 2 = 1 at hi
        linarith
      obtain ⟨q, hq⟩ := hD (D.cells.facetClass od) hd
      refine ⟨q, ?_⟩
      rw [hq]
      rfl

/-- Package a described composition as a genuine endpoint-identified collar when only the two
external endpoint families are exhaustive. -/
noncomputable def endpointIdentifiedCollar
    (hC : ∀ s, C.cells.IsLowerFacet s → ∃ q, C.lowerFacet q = s)
    (hD : ∀ s, D.cells.IsUpperFacet s → ∃ q, D.upperFacet q = s) :
    EndpointIdentifiedRelativeAffineCollar hp N₀ N₁ (max M₀ M₁) (L₀ + L₁ + 1) where
  toFoxNeuwirthRelativeAffineCollar := (describedCollar C D).toFoxNeuwirthRelativeAffineCollar
  lowerFacet := (describedCollar C D).lowerFacet
  upperFacet := (describedCollar C D).upperFacet
  lowerFacet_isLower := (describedCollar C D).lowerFacet_isLower
  upperFacet_isUpper := (describedCollar C D).upperFacet_isUpper
  lowerFacet_exhaustive := lowerFacet_exhaustive_of_left C D hC
  upperFacet_exhaustive := upperFacet_exhaustive_of_right C D hD
  lowerBoundaryPairing_eq := (describedCollar C D).lowerBoundaryPairing_eq
  upperBoundaryPairing_eq := (describedCollar C D).upperBoundaryPairing_eq
  lowerFacetOccurrenceVertex_eq := (describedCollar C D).lowerFacetOccurrenceVertex_eq
  upperFacetOccurrenceVertex_eq := (describedCollar C D).upperFacetOccurrenceVertex_eq

end ExplicitAffineRelativeCollarComposeDescribed
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
