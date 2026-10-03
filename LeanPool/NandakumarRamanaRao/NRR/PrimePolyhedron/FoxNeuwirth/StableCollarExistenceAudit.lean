/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableCollarComparison
/-!
# Necessary conditions for arbitrary stable-collar existence

The concrete `StableCollar` developed by the prism modules uses one standard refined prism
`PrismCell hp N L`.  Consequently both horizontal boundaries are represented on the same
barycentric level `N + L`.  Moreover the prism result carries the strong condition
`AvoidsCodimTwoDeviationZero`; when restricted to a horizontal facet this excludes every
deviation-zero point on the endpoint subdivision skeleton, independently of the sign of the common
coordinate mean.

The public `StableRegularApproximation` interface is weaker in both respects:

* two supplied approximations may have different levels;
* `PositiveRaySkeletonFree` excludes only positive-ray intersections on the skeleton.

This file records the two necessary consequences of an existing concrete collar.  They show that
`StableCollarExistenceTheorem`, as currently stated for arbitrary stable approximations, cannot be
constructed from the available hypotheses.  A genuine arbitrary-endpoint theorem needs a relative
prism complex with independent lower and upper triangulations, and a boundary version of the local
affine theorem requiring only positive-ray skeleton transversality.
-/

public section

namespace NRR

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary

open EquivariantCoordinateHomotopy
open EquivariantPrismGenericPerturbation
open RefinedAffineMap
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open EquivariantPrismVertexParameters
open EquivariantPrismGenericityPolynomials
open EndpointFaceRefinement
open RelativeCollarMiddlePrismEndpointsCore
open SubdivisionPrismCharts

variable {p : Nat}

namespace StableCollar

/-- Both endpoint triangulations of a concrete standard-prism collar necessarily have the common
level `N + L`. -/
theorem lower_level_eq
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (C : StableCollar hp H A₀ A₁) :
    A₀.toRegularApproximation.level = C.N + C.L :=
  C.boundaryFixed.1

/-- Upper endpoint version of `lower_level_eq`. -/
theorem upper_level_eq
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (C : StableCollar hp H A₀ A₁) :
    A₁.toRegularApproximation.level = C.N + C.L :=
  C.boundaryFixed.2.1

/-- A concrete standard-prism stable collar can only connect approximations living on the same
barycentric level. -/
theorem endpoint_levels_eq
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (C : StableCollar hp H A₀ A₁) :
    A₀.toRegularApproximation.level = A₁.toRegularApproximation.level := by
  rw [C.lower_level_eq, C.upper_level_eq]

/-- Equality of the lower endpoint affine interpolation with the lower horizontal interpolant of
the collar assignment. -/
theorem lower_value_eq
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (C : StableCollar hp H A₀ A₁)
    (q : TopCell hp (C.N + C.L))
    (w : StandardSimplex (p - 1)) :
    RefinedAffineMap.value hp (C.N + C.L) A₀.toRegularApproximation.map q w =
      RefinedAffineMap.value hp (C.N + C.L)
        (endpointInterpolant hp C.N C.L .lower C.prism.assignment) q w := by
  classical
  obtain ⟨q₀, eta, rfl⟩ := endpointTopCell_surjective hp C.N C.L q
  funext j
  unfold RefinedAffineMap.value RefinedAffineMap.vertexValue
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have hsample := C.boundaryFixed.2.2.1 q₀ eta
    ((ExplicitAffineRelativeCollar.refinedVertexEquiv hp).symm i)
  have hindex : Fin.cast (Nat.sub_add_cancel hp.pos).symm
      ((ExplicitAffineRelativeCollar.refinedVertexEquiv hp).symm i) = i := by
    apply Fin.ext
    rfl
  rw [hindex] at hsample
  exact congrFun (by
    simpa [RefinedAffineMap.vertex, endpointSpatialMap_eq_chart] using hsample) j

/-- Upper endpoint analogue of `lower_value_eq`. -/
theorem upper_value_eq
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (C : StableCollar hp H A₀ A₁)
    (q : TopCell hp (C.N + C.L))
    (w : StandardSimplex (p - 1)) :
    RefinedAffineMap.value hp (C.N + C.L) A₁.toRegularApproximation.map q w =
      RefinedAffineMap.value hp (C.N + C.L)
        (endpointInterpolant hp C.N C.L .upper C.prism.assignment) q w := by
  classical
  obtain ⟨q₀, eta, rfl⟩ := endpointTopCell_surjective hp C.N C.L q
  funext j
  unfold RefinedAffineMap.value RefinedAffineMap.vertexValue
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have hsample := C.boundaryFixed.2.2.2 q₀ eta
    ((ExplicitAffineRelativeCollar.refinedVertexEquiv hp).symm i)
  have hindex : Fin.cast (Nat.sub_add_cancel hp.pos).symm
      ((ExplicitAffineRelativeCollar.refinedVertexEquiv hp).symm i) = i := by
    apply Fin.ext
    rfl
  rw [hindex] at hsample
  exact congrFun (by
    simpa [RefinedAffineMap.vertex, endpointSpatialMap_eq_chart] using hsample) j

/-- The lower boundary of a concrete collar satisfies sign-independent deviation-skeleton
transversality. -/
theorem lower_deviationSkeletonFree_at_collarLevel
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (C : StableCollar hp H A₀ A₁) :
    DeviationSkeletonFree hp (C.N + C.L) A₀.toRegularApproximation.map := by
  intro q w hdev
  apply endpointInterpolant_deviationSkeletonFree hp C.N C.L .lower
    C.prism.assignment C.prism.avoidsCodimTwo q w
  intro r
  simpa [C.lower_value_eq q w] using hdev r

/-- The upper boundary of a concrete collar satisfies sign-independent deviation-skeleton
transversality. -/
theorem upper_deviationSkeletonFree_at_collarLevel
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (C : StableCollar hp H A₀ A₁) :
    DeviationSkeletonFree hp (C.N + C.L) A₁.toRegularApproximation.map := by
  intro q w hdev
  apply endpointInterpolant_deviationSkeletonFree hp C.N C.L .upper
    C.prism.assignment C.prism.avoidsCodimTwo q w
  intro r
  simpa [C.upper_value_eq q w] using hdev r

end StableCollar

/-- The currently stated arbitrary collar-existence theorem would force every supplied endpoint
pair to have equal subdivision levels.  This consequence is absent from its hypotheses and is the
first structural obstruction to proving it with `StableCollar`. -/
theorem collarExistence_implies_endpoint_level_alignment
    (HC : StableCollarExistenceTheorem) :
    ∀ {p : Nat} (hp : Nat.Prime p)
      (F₀ F₁ : ZeroFreeMap hp)
      (_H : ZeroFreeHomotopy hp F₀ F₁)
      (A₀ : StableRegularApproximation hp F₀.map)
      (A₁ : StableRegularApproximation hp F₁.map),
      A₀.toRegularApproximation.level = A₁.toRegularApproximation.level := by
  intro p hp F₀ F₁ H A₀ A₁
  exact (Classical.choice (HC hp F₀ F₁ H A₀ A₁)).endpoint_levels_eq

/-- The currently stated arbitrary collar-existence theorem would also force every lower
endpoint to satisfy the stronger sign-independent skeleton condition. -/
theorem collarExistence_implies_lower_deviationSkeletonFree
    (HC : StableCollarExistenceTheorem) :
    ∀ {p : Nat} (hp : Nat.Prime p)
      (F₀ F₁ : ZeroFreeMap hp)
      (_H : ZeroFreeHomotopy hp F₀ F₁)
      (A₀ : StableRegularApproximation hp F₀.map)
      (_A₁ : StableRegularApproximation hp F₁.map),
      DeviationSkeletonFree hp A₀.toRegularApproximation.level
        A₀.toRegularApproximation.map := by
  intro p hp F₀ F₁ H A₀ A₁
  let C := Classical.choice (HC hp F₀ F₁ H A₀ A₁)
  rw [C.lower_level_eq]
  exact C.lower_deviationSkeletonFree_at_collarLevel

/-- Upper endpoint version of `collarExistence_implies_lower_deviationSkeletonFree`. -/
theorem collarExistence_implies_upper_deviationSkeletonFree
    (HC : StableCollarExistenceTheorem) :
    ∀ {p : Nat} (hp : Nat.Prime p)
      (F₀ F₁ : ZeroFreeMap hp)
      (_H : ZeroFreeHomotopy hp F₀ F₁)
      (_A₀ : StableRegularApproximation hp F₀.map)
      (A₁ : StableRegularApproximation hp F₁.map),
      DeviationSkeletonFree hp A₁.toRegularApproximation.level
        A₁.toRegularApproximation.map := by
  intro p hp F₀ F₁ H A₀ A₁
  let C := Classical.choice (HC hp F₀ F₁ H A₀ A₁)
  rw [C.upper_level_eq]
  exact C.upper_deviationSkeletonFree_at_collarLevel

end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
