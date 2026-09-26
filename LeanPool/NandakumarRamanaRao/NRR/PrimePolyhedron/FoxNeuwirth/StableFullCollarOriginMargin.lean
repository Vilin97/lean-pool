/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StablePatchedHomotopyFineMargin

/-!
# Full-collar origin-margin packaging

The quantitative middle-prism estimates and the generic compactness theorem reduce the full
origin-margin stage to one geometric input: an endpoint-identified collar assignment which already
avoids the origin on every cell.  This file packages that input separately from the later positive-
ray perturbation argument and proves that it automatically has a uniform positive coordinate
margin.  Every sufficiently small movable replacement then remains origin-free while retaining the
horizontal boundary literally.

The structure `FineFullCollarData` packages a compatible simplicial retraction/PL assignment on
the lower and upper subdivision stacks together with the controlled middle prism. All results in
this file are theorem-level consequences of that data.
-/

@[expose] public section

namespace NRR

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableFullCollarOriginMargin

open EquivariantCoordinateHomotopy
open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open ExplicitAffineRelativeCollar.RelativeGenericity
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open StablePatchedHomotopyFineMargin
open EquivariantPrismGenericPerturbation

variable {p : Nat}

/-- Geometric output required from the completed fine-collar construction, before extracting a
numerical uniform margin.  The endpoint values are literal, and origin avoidance is required on the
entire glued collar, not only on its middle-prism summand. -/
structure FineFullCollarData
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) where
  /-- The common spatial level of the fine full collar. -/
  commonLevel : Nat
  /-- The time-refinement level of the fine full collar. -/
  timeLevel : Nat
  /-- The fine endpoint-identified collar on which the cellwise origin avoidance is verified. -/
  collar : EndpointIdentifiedRelativeAffineCollar hp
    A₀.toRegularApproximation.level A₁.toRegularApproximation.level
    commonLevel timeLevel
  /-- The horizontal-boundary-compatible assignment that avoids the origin on each cell. -/
  assignment : Assignment hp collar.cells
  horizontalVertexFixed : HorizontalVertexFixed hp A₀ A₁ collar assignment
  baseAvoidsOrigin : ∀ q : collar.cells.Cell,
    AvoidsOrigin (localVertexMap hp collar.cells assignment q)

/-- Item 4, expressed as the exact construction proposition still required from the endpoint-stack
geometry.  This is a named target, not an assumed theorem and not a field of the final AAK result.
-/
def FineFullCollarConstructionTheorem : Prop :=
  ∀ {p : Nat} (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map),
      Nonempty (FineFullCollarData hp H A₀ A₁)

/-- Full quantitative output of item 5. -/
structure FullCollarOriginMarginData
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    extends FineFullCollarData hp H A₀ A₁ where
  /-- A positive lower bound for the norm of every affine collar value. -/
  margin : Real
  margin_pos : 0 < margin
  coordinateNormMargin :
    LocalAffineCoordinateNormMargin hp collar.cells assignment margin

namespace FullCollarOriginMarginData

/-- Every finite full-collar assignment which avoids the origin cellwise has a single positive
coordinate margin valid on all cells. -/
noncomputable def ofFineFullCollarData
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (D : FineFullCollarData hp H A₀ A₁) :
    FullCollarOriginMarginData hp H A₀ A₁ :=
  let hmargin := exists_positive_localAffineCoordinateNormMargin hp D.collar.cells
    D.assignment D.baseAvoidsOrigin
  { toFineFullCollarData := D
    margin := Classical.choose hmargin
    margin_pos := (Classical.choose_spec hmargin).1
    coordinateNormMargin := (Classical.choose_spec hmargin).2 }

/-- The stored assignment is origin-free, now as an immediate consequence of its quantitative
margin. -/
theorem assignment_avoidsOrigin
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (D : FullCollarOriginMarginData hp H A₀ A₁)
    (q : D.collar.cells.Cell) :
    AvoidsOrigin (localVertexMap hp D.collar.cells D.assignment q) :=
  avoidsOrigin_of_localAffineCoordinateNormMargin hp D.collar.cells
    D.assignment D.margin_pos D.coordinateNormMargin q

/-- Any full assignment within half of the global collar margin remains origin-free on every
collar cell. -/
theorem perturbed_avoidsOrigin
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (D : FullCollarOriginMarginData hp H A₀ A₁)
    (perturbed : Assignment hp D.collar.cells)
    (hclose : AssignmentClose perturbed D.assignment (D.margin / 2)) :
    ∀ q : D.collar.cells.Cell,
      AvoidsOrigin (localVertexMap hp D.collar.cells perturbed q) :=
  avoidsOrigin_of_assignmentClose_half_margin hp D.collar.cells
    D.assignment perturbed D.margin_pos D.coordinateNormMargin hclose

/-- In particular, a boundary-fixed movable replacement within half of the global margin remains
origin-free.  Exact endpoint values are retained by the definition of `replaceMovable`. -/
theorem replaceMovable_avoidsOrigin
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (D : FullCollarOriginMarginData hp H A₀ A₁)
    (move : MovableParameter hp D.collar.cells → Real)
    (hclose : AssignmentClose
      (replaceMovable hp D.collar.cells D.assignment move)
      D.assignment (D.margin / 2)) :
    ∀ q : D.collar.cells.Cell,
      AvoidsOrigin
        (localVertexMap hp D.collar.cells
          (replaceMovable hp D.collar.cells D.assignment move) q) :=
  D.perturbed_avoidsOrigin
    (replaceMovable hp D.collar.cells D.assignment move) hclose

end FullCollarOriginMarginData

/-- Once item 4 constructs the full fine collar, item 5 follows without any further geometric
hypothesis. -/
theorem fullCollarOriginMargin_of_fineFullCollarConstruction
    (HC : FineFullCollarConstructionTheorem) :
    ∀ {p : Nat} (hp : Nat.Prime p)
      (F₀ F₁ : ZeroFreeMap hp)
      (H : ZeroFreeHomotopy hp F₀ F₁)
      (A₀ : StableRegularApproximation hp F₀.map)
      (A₁ : StableRegularApproximation hp F₁.map),
        Nonempty (FullCollarOriginMarginData hp H A₀ A₁) := by
  intro p hp F₀ F₁ H A₀ A₁
  exact ⟨FullCollarOriginMarginData.ofFineFullCollarData
    (Classical.choice (HC hp F₀ F₁ H A₀ A₁))⟩

end StableFullCollarOriginMargin
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
