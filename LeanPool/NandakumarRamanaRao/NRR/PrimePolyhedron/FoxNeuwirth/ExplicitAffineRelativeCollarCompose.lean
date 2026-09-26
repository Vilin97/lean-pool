/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module

public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ExplicitAffineRelativeCollarComposeDescribed


/-!
# Composition of endpoint-identified relative affine collars

Two collars with a common intermediate endpoint are placed in the lower and upper half of the
realization cylinder.  Their cell families are joined by disjoint union.  The quotient-facet
relation then identifies the two copies of every intermediate endpoint facet.  The upper boundary
pairing of the first collar and lower boundary pairing of the second collar are the same refined
Fox--Neuwirth chain, hence cancel pointwise after regrouping by combined quotient facets.
-/

@[expose] public section

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollarCompose

open scoped BigOperators
open ExplicitAffineRelativeCollar
open EquivariantPrismVertexParameters
open RefinedAffineMap
open ExplicitAffineRelativeCollarComposeDescribed (EndpointDescribedRelativeAffineCollar)

variable {p N₀ Nmid N₁ M₀ M₁ L₀ L₁ : Nat}
variable {hp : Nat.Prime p}

variable
    (C : EndpointIdentifiedRelativeAffineCollar hp N₀ Nmid M₀ L₀)
    (D : EndpointIdentifiedRelativeAffineCollar hp Nmid N₁ M₁ L₁)

/-- The two copies of every common endpoint facet define the same combined quotient facet. -/
theorem internalFacet_eq (q : TopCell hp Nmid) :
    Combined.leftFacet C.cells D.cells (C.upperFacet q) =
      Combined.rightFacet C.cells D.cells (D.lowerFacet q) := by
  exact ExplicitAffineRelativeCollarComposeDescribed.internalFacet_eq
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) q

/-- External lower coefficient of the composed collar. -/
noncomputable def lowerBoundaryCoefficient
    (s : (combinedCells C.cells D.cells).Facet) : ZMod p :=
  ExplicitAffineRelativeCollarComposeDescribed.lowerBoundaryCoefficient
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) s

/-- External upper coefficient of the composed collar. -/
noncomputable def upperBoundaryCoefficient
    (s : (combinedCells C.cells D.cells).Facet) : ZMod p :=
  ExplicitAffineRelativeCollarComposeDescribed.upperBoundaryCoefficient
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) s

/-- The common endpoint contributions of the two component collars cancel pointwise. -/
theorem internalPairings_eq
    (s : (combinedCells C.cells D.cells).Facet) :
    (∑ t : C.cells.Facet,
      C.upperBoundaryCoefficient t *
        Combined.leftIndicator C.cells D.cells s t) =
    (∑ t : D.cells.Facet,
      D.lowerBoundaryCoefficient t *
        Combined.rightIndicator C.cells D.cells s t) := by
  exact ExplicitAffineRelativeCollarComposeDescribed.internalPairings_eq
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) s

/-- Pointwise boundary formula for the composed collar. -/
theorem incidence_eq_boundary
    (s : (combinedCells C.cells D.cells).Facet) :
    (combinedCells C.cells D.cells).facetIncidence s =
      upperBoundaryCoefficient C D s - lowerBoundaryCoefficient C D s := by
  exact ExplicitAffineRelativeCollarComposeDescribed.incidence_eq_boundary
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) s

/-- Canonical lower endpoint facets are lower horizontal in the combined cylinder. -/
theorem lowerFacet_isLower (q : TopCell hp N₀) :
    (combinedCells C.cells D.cells).IsLowerFacet
      (Combined.leftFacet C.cells D.cells (C.lowerFacet q)) := by
  exact ExplicitAffineRelativeCollarComposeDescribed.lowerFacet_isLower
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) q

/-- Canonical upper endpoint facets are upper horizontal in the combined cylinder. -/
theorem upperFacet_isUpper (q : TopCell hp N₁) :
    (combinedCells C.cells D.cells).IsUpperFacet
      (Combined.rightFacet C.cells D.cells (D.upperFacet q)) := by
  exact ExplicitAffineRelativeCollarComposeDescribed.upperFacet_isUpper
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) q

/-- External lower coefficients vanish away from the lower horizontal boundary. -/
theorem lowerBoundaryCoefficient_zero_of_not_lower
    (s : (combinedCells C.cells D.cells).Facet)
    (hs : ¬ (combinedCells C.cells D.cells).IsLowerFacet s) :
    lowerBoundaryCoefficient C D s = 0 := by
  exact ExplicitAffineRelativeCollarComposeDescribed.lowerBoundaryCoefficient_zero_of_not_lower
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) s hs

/-- External upper coefficients vanish away from the upper horizontal boundary. -/
theorem upperBoundaryCoefficient_zero_of_not_upper
    (s : (combinedCells C.cells D.cells).Facet)
    (hs : ¬ (combinedCells C.cells D.cells).IsUpperFacet s) :
    upperBoundaryCoefficient C D s = 0 := by
  exact ExplicitAffineRelativeCollarComposeDescribed.upperBoundaryCoefficient_zero_of_not_upper
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) s hs

/-- Every lower-horizontal combined quotient facet comes from the external lower boundary. -/
theorem lowerFacet_exhaustive
    (s : (combinedCells C.cells D.cells).Facet)
    (hs : (combinedCells C.cells D.cells).IsLowerFacet s) :
    ∃ q : TopCell hp N₀,
      Combined.leftFacet C.cells D.cells (C.lowerFacet q) = s := by
  exact ExplicitAffineRelativeCollarComposeDescribed.lowerFacet_exhaustive_of_left
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) C.lowerFacet_exhaustive s hs

/-- Every upper-horizontal combined quotient facet comes from the external upper boundary. -/
theorem upperFacet_exhaustive
    (s : (combinedCells C.cells D.cells).Facet)
    (hs : (combinedCells C.cells D.cells).IsUpperFacet s) :
    ∃ q : TopCell hp N₁,
      Combined.rightFacet C.cells D.cells (D.upperFacet q) = s := by
  exact ExplicitAffineRelativeCollarComposeDescribed.upperFacet_exhaustive_of_right
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) D.upperFacet_exhaustive s hs

/-- Chain-level lower endpoint identity for the composed collar. -/
theorem lowerBoundaryPairing_eq
    (W : (combinedCells C.cells D.cells).Facet → ZMod p) :
    (∑ s : (combinedCells C.cells D.cells).Facet,
      lowerBoundaryCoefficient C D s * W s) =
      ∑ q : TopCell hp N₀,
        RefinedAffineMap.coefficient hp N₀ q *
          W (Combined.leftFacet C.cells D.cells (C.lowerFacet q)) := by
  exact ExplicitAffineRelativeCollarComposeDescribed.lowerBoundaryPairing_eq
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) W

/-- Chain-level upper endpoint identity for the composed collar. -/
theorem upperBoundaryPairing_eq
    (W : (combinedCells C.cells D.cells).Facet → ZMod p) :
    (∑ s : (combinedCells C.cells D.cells).Facet,
      upperBoundaryCoefficient C D s * W s) =
      ∑ q : TopCell hp N₁,
        RefinedAffineMap.coefficient hp N₁ q *
          W (Combined.rightFacet C.cells D.cells (D.upperFacet q)) := by
  exact ExplicitAffineRelativeCollarComposeDescribed.upperBoundaryPairing_eq
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) W

/-- Representatives of external lower facets have the prescribed level-`N₀` geometry. -/
theorem lowerFacetOccurrenceVertex_eq
    (q : TopCell hp N₀)
    (o : (combinedCells C.cells D.cells).FacetOccurrence)
    (ho : (combinedCells C.cells D.cells).facetClass o =
      Combined.leftFacet C.cells D.cells (C.lowerFacet q)) :
    ∃ g : PrimeSymmetry p, ∀ i,
      (combinedCells C.cells D.cells).facetSignature o i =
        g • lowerCylinderPoint (RefinedAffineMap.vertex hp N₀ q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  exact ExplicitAffineRelativeCollarComposeDescribed.lowerFacetOccurrenceVertex_eq
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) q o ho

/-- Representatives of external upper facets have the prescribed level-`N₁` geometry. -/
theorem upperFacetOccurrenceVertex_eq
    (q : TopCell hp N₁)
    (o : (combinedCells C.cells D.cells).FacetOccurrence)
    (ho : (combinedCells C.cells D.cells).facetClass o =
      Combined.rightFacet C.cells D.cells (D.upperFacet q)) :
    ∃ g : PrimeSymmetry p, ∀ i,
      (combinedCells C.cells D.cells).facetSignature o i =
        g • upperCylinderPoint (RefinedAffineMap.vertex hp N₁ q
          (Fin.cast (Nat.sub_add_cancel hp.pos).symm i)) := by
  exact ExplicitAffineRelativeCollarComposeDescribed.upperFacetOccurrenceVertex_eq
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D) q o ho

/-- Pointwise composed relative collar. -/
noncomputable def relativeCollar :
    FoxNeuwirthRelativeAffineCollar hp N₀ N₁ (max M₀ M₁) (L₀ + L₁ + 1) :=
  (ExplicitAffineRelativeCollarComposeDescribed.describedCollar
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified
      D)).toFoxNeuwirthRelativeAffineCollar

/-- Composition of endpoint-identified relative affine collars. -/
noncomputable def endpointIdentifiedCollar :
    EndpointIdentifiedRelativeAffineCollar hp N₀ N₁ (max M₀ M₁) (L₀ + L₁ + 1) :=
  ExplicitAffineRelativeCollarComposeDescribed.endpointIdentifiedCollar
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified C)
    (EndpointDescribedRelativeAffineCollar.ofEndpointIdentified D)
    C.lowerFacet_exhaustive D.upperFacet_exhaustive

end ExplicitAffineRelativeCollarCompose
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
