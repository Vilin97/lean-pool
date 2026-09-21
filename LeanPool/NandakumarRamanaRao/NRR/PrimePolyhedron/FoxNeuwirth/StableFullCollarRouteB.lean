/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableFullCollarOriginMarginAffinePullback
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBStepsOneToSix

/-!
# Route B on the concrete affine-pullback full collar

This file specializes the finite-dimensional Route B selection theorem to the Step 4 collar and
its compactness-derived origin margin.  The generic perturbation is then completely automatic from
two geometric certificates on the concrete collar:

* positive-ray safety when every positive-support vertex is frozen; and
* nontriviality of every boundary-restricted facet determinant polynomial.

The latter is converted internally into a genuine positive-radius facet-regular neighborhood by
`RouteB.exists_safePerturbationBall`.
-/

namespace NRR

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableFullCollarRouteB

open EquivariantCoordinateHomotopy
open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.RelativeGenericity
open ExplicitAffineRelativeCollar.RouteB
open StableFullCollarOriginMargin
open StableFullCollarOriginMarginAffinePullback

variable {p : Nat}

/-- Concrete Step 4/5 data used as the base point for Route B. -/
noncomputable abbrev baseData
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    FullCollarOriginMarginData hp H A₀ A₁ :=
  fullCollarOriginMarginDataAffinePullback hp F₀ F₁ H A₀ A₁

/-- Exact geometric input still required to run Route B on the concrete collar.  The safe ball is
not stored: it is constructed from `facetPolynomialsNonzero` by the open-neighborhood
theorem. -/
structure GeometricInput
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) : Prop where
  frozenSupportSafe : FrozenPositiveSupportRaySafe hp
    (baseData hp F₀ F₁ H A₀ A₁).collar.cells
    (baseData hp F₀ F₁ H A₀ A₁).assignment
  facetPolynomialsNonzero : AllRestrictedFacetPolynomialsNonzero hp
    (baseData hp F₀ F₁ H A₀ A₁).collar.cells
    (baseData hp F₀ F₁ H A₀ A₁).assignment

/-- Route B instantiated on the Step 4 collar and Step 5 margin. -/
theorem exists_smallGenericPerturbation_affinePullback
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (G : GeometricInput hp F₀ F₁ H A₀ A₁)
    {eps : Real} (heps : 0 < eps) :
    Nonempty (SmallGenericPerturbationResult hp
      (baseData hp F₀ F₁ H A₀ A₁).collar.cells
      (baseData hp F₀ F₁ H A₀ A₁).assignment eps
      (baseData hp F₀ F₁ H A₀ A₁).margin) := by
  let D := baseData hp F₀ F₁ H A₀ A₁
  obtain ⟨B⟩ := exists_safePerturbationBall hp D.collar.cells D.assignment
    heps D.margin_pos G.facetPolynomialsNonzero
  exact exists_smallGenericPerturbation hp D.collar.cells D.assignment
    heps D.margin_pos D.coordinateNormMargin G.frozenSupportSafe B

/-- The selected perturbation fixes the two horizontal endpoint assignments literally. -/
theorem smallGenericPerturbation_fixesHorizontal
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (G : GeometricInput hp F₀ F₁ H A₀ A₁)
    {eps : Real} (heps : 0 < eps) :
    ∃ R : SmallGenericPerturbationResult hp
        (baseData hp F₀ F₁ H A₀ A₁).collar.cells
        (baseData hp F₀ F₁ H A₀ A₁).assignment eps
        (baseData hp F₀ F₁ H A₀ A₁).margin,
      ∀ {s : Parameter hp (baseData hp F₀ F₁ H A₀ A₁).collar.cells},
        IsFrozenParameter hp (baseData hp F₀ F₁ H A₀ A₁).collar.cells s →
        assignmentOfMovableParameters hp
            (baseData hp F₀ F₁ H A₀ A₁).collar.cells
            (baseData hp F₀ F₁ H A₀ A₁).assignment R.move s =
          (baseData hp F₀ F₁ H A₀ A₁).assignment s := by
  obtain ⟨R⟩ := exists_smallGenericPerturbation_affinePullback
    hp F₀ F₁ H A₀ A₁ G heps
  exact ⟨R, fun hs => R.fixesFrozen hs⟩

end StableFullCollarRouteB
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
