/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import
  LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeSubdivisionOneStepBoundary

/-!
# Endpoint-identified one-step subdivision collar

The pointwise boundary identity from `RelativeSubdivisionOneStepBoundary` is packaged here as a
`FoxNeuwirthRelativeAffineCollar`.  The canonical lower and upper quotient facets constructed in
`RelativeSubdivisionOneStepEndpoints` identify its horizontal boundary with the level-`N` and
level-`N+1` refined Fox--Neuwirth chains.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeSubdivisionOneStepCollar

open scoped BigOperators
open ExplicitAffineRelativeCollar
open RefinedAffineMap


variable {p : Nat}

/-- Lower boundary coefficients vanish on non-lower quotient facets. -/
theorem lowerBoundaryCoefficient_zero_of_not_lower
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet)
    (hs : ¬ (RelativeSubdivisionOneStepCells.cellSystem hp N).IsLowerFacet s) :
    RelativeSubdivisionOneStepBoundary.lowerBoundaryCoefficient hp N s = 0 := by
  classical
  unfold RelativeSubdivisionOneStepBoundary.lowerBoundaryCoefficient
    RelativeSubdivisionOneStepBoundaryBase.lowerEndpointPairing
  apply Finset.sum_eq_zero
  intro q hq
  have hne : RelativeSubdivisionOneStepEndpoints.lowerFacet hp N q ≠ s := by
    intro h
    apply hs
    rw [← h]
    exact RelativeSubdivisionOneStepEndpoints.lowerFacet_isLower hp N q
  simp [RelativeSubdivisionOneStepBoundary.quotientIndicator, hne]

/-- Upper boundary coefficients vanish on non-upper quotient facets. -/
theorem upperBoundaryCoefficient_zero_of_not_upper
    (hp : Nat.Prime p) (N : Nat)
    (s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet)
    (hs : ¬ (RelativeSubdivisionOneStepCells.cellSystem hp N).IsUpperFacet s) :
    RelativeSubdivisionOneStepBoundary.upperBoundaryCoefficient hp N s = 0 := by
  classical
  unfold RelativeSubdivisionOneStepBoundary.upperBoundaryCoefficient
    RelativeSubdivisionOneStepBoundaryBase.upperEndpointPairing
  apply Finset.sum_eq_zero
  intro q hq
  have hne : RelativeSubdivisionOneStepEndpoints.upperFacet hp N q ≠ s := by
    intro h
    apply hs
    rw [← h]
    exact RelativeSubdivisionOneStepEndpoints.upperFacet_isUpper hp N q
  simp [RelativeSubdivisionOneStepBoundary.quotientIndicator, hne]

/-- Pairing the lower pointwise boundary coefficients against any weight recovers exactly the
level-`N` refined orbit chain. -/
theorem lowerBoundaryPairing_eq
    (hp : Nat.Prime p) (N : Nat)
    (W : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet → ZMod p) :
    (∑ s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet,
      RelativeSubdivisionOneStepBoundary.lowerBoundaryCoefficient hp N s * W s) =
      ∑ q : TopCell hp N,
        RefinedAffineMap.coefficient hp N q * W (RelativeSubdivisionOneStepEndpoints.lowerFacet
          hp N q) := by
  classical
  unfold RelativeSubdivisionOneStepBoundary.lowerBoundaryCoefficient
    RelativeSubdivisionOneStepBoundaryBase.lowerEndpointPairing
  calc
    (∑ s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet,
      (∑ q : TopCell hp N,
        RefinedAffineMap.coefficient hp N q *
          RelativeSubdivisionOneStepBoundary.quotientIndicator s
            (RelativeSubdivisionOneStepEndpoints.lowerFacet hp N q)) * W s) =
      ∑ s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet,
        ∑ q : TopCell hp N,
          if RelativeSubdivisionOneStepEndpoints.lowerFacet hp N q = s then
            RefinedAffineMap.coefficient hp N q * W s
          else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q hq
        simp [RelativeSubdivisionOneStepBoundary.quotientIndicator]
    _ = ∑ q : TopCell hp N,
        ∑ s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet,
          if RelativeSubdivisionOneStepEndpoints.lowerFacet hp N q = s then
            RefinedAffineMap.coefficient hp N q * W s
          else 0 := by
        rw [Finset.sum_comm]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        simp only [eq_comm]
        rw [Finset.sum_ite_eq']
        simp

/-- Pairing the upper pointwise boundary coefficients against any weight recovers exactly the
level-`N+1` refined orbit chain. -/
theorem upperBoundaryPairing_eq
    (hp : Nat.Prime p) (N : Nat)
    (W : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet → ZMod p) :
    (∑ s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet,
      RelativeSubdivisionOneStepBoundary.upperBoundaryCoefficient hp N s * W s) =
      ∑ q : TopCell hp (N + 1),
        RefinedAffineMap.coefficient hp (N + 1) q * W
          (RelativeSubdivisionOneStepEndpoints.upperFacet hp N q) := by
  classical
  unfold RelativeSubdivisionOneStepBoundary.upperBoundaryCoefficient
    RelativeSubdivisionOneStepBoundaryBase.upperEndpointPairing
  calc
    (∑ s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet,
      (∑ q : TopCell hp (N + 1),
        RefinedAffineMap.coefficient hp (N + 1) q *
          RelativeSubdivisionOneStepBoundary.quotientIndicator s
            (RelativeSubdivisionOneStepEndpoints.upperFacet hp N q)) * W s) =
      ∑ s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet,
        ∑ q : TopCell hp (N + 1),
          if RelativeSubdivisionOneStepEndpoints.upperFacet hp N q = s then
            RefinedAffineMap.coefficient hp (N + 1) q * W s
          else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q hq
        simp [RelativeSubdivisionOneStepBoundary.quotientIndicator]
    _ = ∑ q : TopCell hp (N + 1),
        ∑ s : (RelativeSubdivisionOneStepCells.cellSystem hp N).Facet,
          if RelativeSubdivisionOneStepEndpoints.upperFacet hp N q = s then
            RefinedAffineMap.coefficient hp (N + 1) q * W s
          else 0 := by
        rw [Finset.sum_comm]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        simp only [eq_comm]
        rw [Finset.sum_ite_eq']
        simp

/-- The genuine one-step affine collar from refinement level `N` to level `N+1`. -/
noncomputable def relativeCollar
    (hp : Nat.Prime p) (N : Nat) :
    FoxNeuwirthRelativeAffineCollar hp N (N + 1) (N + 1) 0 where
  cells := RelativeSubdivisionOneStepCells.cellSystem hp N
  lowerBoundaryCoefficient := RelativeSubdivisionOneStepBoundary.lowerBoundaryCoefficient hp N
  upperBoundaryCoefficient := RelativeSubdivisionOneStepBoundary.upperBoundaryCoefficient hp N
  lower_zero_of_not_lower := lowerBoundaryCoefficient_zero_of_not_lower hp N
  upper_zero_of_not_upper := upperBoundaryCoefficient_zero_of_not_upper hp N
  incidence_eq_boundary := RelativeSubdivisionOneStepBoundary.incidence_eq_boundary hp N

/-- The one-step collar has exactly the independently refined Fox--Neuwirth endpoint chains. -/
noncomputable def endpointIdentifiedCollar
    (hp : Nat.Prime p) (N : Nat) :
    EndpointIdentifiedRelativeAffineCollar hp N (N + 1) (N + 1) 0 where
  toFoxNeuwirthRelativeAffineCollar := relativeCollar hp N
  lowerFacet := RelativeSubdivisionOneStepEndpoints.lowerFacet hp N
  upperFacet := RelativeSubdivisionOneStepEndpoints.upperFacet hp N
  lowerFacet_isLower := RelativeSubdivisionOneStepEndpoints.lowerFacet_isLower hp N
  upperFacet_isUpper := RelativeSubdivisionOneStepEndpoints.upperFacet_isUpper hp N
  lowerFacet_exhaustive := RelativeSubdivisionOneStepEndpoints.lowerFacet_exhaustive hp N
  upperFacet_exhaustive := RelativeSubdivisionOneStepEndpoints.upperFacet_exhaustive hp N
  lowerBoundaryPairing_eq := lowerBoundaryPairing_eq hp N
  upperBoundaryPairing_eq := upperBoundaryPairing_eq hp N
  lowerFacetOccurrenceVertex_eq :=
    RelativeSubdivisionOneStepEndpoints.lowerFacetOccurrenceVertex_eq hp N
  upperFacetOccurrenceVertex_eq :=
    RelativeSubdivisionOneStepEndpoints.upperFacetOccurrenceVertex_eq hp N

/-- Existence form of the one-step relative subdivision collar. -/
theorem relativeAffineCollarExists_succ
    (hp : Nat.Prime p) (N : Nat) :
    RelativeAffineCollarExists hp N (N + 1) (N + 1) 0 :=
  ⟨endpointIdentifiedCollar hp N⟩

end RelativeSubdivisionOneStepCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
