/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableFullCollarRouteBInstantiation
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableCollarRelativeSubdivisionExact

/-!
# Exact relative stable collar from the affine-pullback Route B perturbation

This module packages the concrete Route B assignment on the Step 4 affine-pullback collar into the
exact relative-collar interface consumed by finite affine Stokes.

The construction uses the focused Route B API rather than repeating the perturbation selection:

* choose the canonical perturbation with tolerance `1`;
* retain the exact lower and upper horizontal values because all horizontal parameters are frozen;
* use Route B positive-ray general position on every cell;
* convert that package to the local positive-ray Stokes certificate;
* inhabit `ExactRelativeStableCollarConstructionTheorem`.
-/

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableExactRelativeCollarConstructionAffinePullback

open EquivariantCoordinateHomotopy
open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open ExplicitAffineRelativeCollar.RouteB
open StableFullCollarRouteB
open StableFullCollarRouteBComplete
open StableFullCollarRouteBInstantiation
open StableCollarRelativeSubdivisionExact

variable {p : Nat}

/-- A fixed positive tolerance used to select one exact-collar perturbation.  The exact certificate
records no quantitative upper bound, so the value `1` is sufficient. -/
def certificateTolerance : Real := 1

/-- Positivity of the canonical certificate tolerance. -/
theorem certificateTolerance_pos : 0 < certificateTolerance := by
  norm_num [certificateTolerance]

/-- The canonical Route B result used by the exact collar certificate. -/
noncomputable def selectedRouteBResult
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    SmallGenericPerturbationResult hp
      (baseData hp F₀ F₁ H A₀ A₁).collar.cells
      (baseData hp F₀ F₁ H A₀ A₁).assignment certificateTolerance
      (baseData hp F₀ F₁ H A₀ A₁).margin :=
  routeBPerturbation hp F₀ F₁ H A₀ A₁ certificateTolerance certificateTolerance_pos

/-- The full assignment selected by Route B on the concrete affine-pullback collar. -/
noncomputable def perturbedAssignment
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    Assignment hp (baseData hp F₀ F₁ H A₀ A₁).collar.cells :=
  StableFullCollarRouteBInstantiation.perturbedAssignment
    hp F₀ F₁ H A₀ A₁ certificateTolerance certificateTolerance_pos

/-- The selected assignment is the assignment reconstructed from the selected Route B move. -/
theorem perturbedAssignment_eq_assignmentOfMovableParameters
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    perturbedAssignment hp F₀ F₁ H A₀ A₁ =
      assignmentOfMovableParameters hp
        (baseData hp F₀ F₁ H A₀ A₁).collar.cells
        (baseData hp F₀ F₁ H A₀ A₁).assignment
        (selectedRouteBResult hp F₀ F₁ H A₀ A₁).move := by
  rfl

/-- Movable replacement preserves both supplied endpoint assignments exactly. -/
theorem perturbedAssignment_horizontalVertexFixed
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    HorizontalVertexFixed hp A₀ A₁
      (baseData hp F₀ F₁ H A₀ A₁).collar
      (perturbedAssignment hp F₀ F₁ H A₀ A₁) := by
  let D := baseData hp F₀ F₁ H A₀ A₁
  let R := selectedRouteBResult hp F₀ F₁ H A₀ A₁
  constructor
  · intro s hs
    calc
      vectorValue hp D.collar.cells
          (perturbedAssignment hp F₀ F₁ H A₀ A₁)
          (sampleVertex hp D.collar.cells s) =
          vectorValue hp D.collar.cells D.assignment
            (sampleVertex hp D.collar.cells s) := by
        simpa [perturbedAssignment, selectedRouteBResult, D, R,
          StableFullCollarRouteBInstantiation.perturbedAssignment,
          assignmentOfMovableParameters] using
          replaceMovable_horizontal_localValue hp D.collar.cells D.assignment R.move s
            (Or.inl hs)
      _ = A₀.toRegularApproximation.map (D.collar.cells.slotPoint s).spatial :=
        D.horizontalVertexFixed.lowerValue s hs
  · intro s hs
    calc
      vectorValue hp D.collar.cells
          (perturbedAssignment hp F₀ F₁ H A₀ A₁)
          (sampleVertex hp D.collar.cells s) =
          vectorValue hp D.collar.cells D.assignment
            (sampleVertex hp D.collar.cells s) := by
        simpa [perturbedAssignment, selectedRouteBResult, D, R,
          StableFullCollarRouteBInstantiation.perturbedAssignment,
          assignmentOfMovableParameters] using
          replaceMovable_horizontal_localValue hp D.collar.cells D.assignment R.move s
            (Or.inr hs)
      _ = A₁.toRegularApproximation.map (D.collar.cells.slotPoint s).spatial :=
        D.horizontalVertexFixed.upperValue s hs

/-- Route B supplies positive-ray general position for every cell of the selected collar. -/
theorem perturbedAssignment_positiveRayGeneralPosition
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map)
    (q : (baseData hp F₀ F₁ H A₀ A₁).collar.cells.Cell) :
    PositiveRayGeneralPosition hp
      (localVertexMap hp (baseData hp F₀ F₁ H A₀ A₁).collar.cells
        (perturbedAssignment hp F₀ F₁ H A₀ A₁) q) :=
  StableFullCollarRouteBInstantiation.perturbedAssignment_positiveRayGeneralPosition
    hp F₀ F₁ H A₀ A₁ certificateTolerance certificateTolerance_pos q

/-- The concrete Route B perturbation, packaged with exact endpoints and cellwise positive-ray
 general position. -/
noncomputable def exactRelativeStableCollarGeneralPositionDataAffinePullback
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    ExactRelativeStableCollarGeneralPositionData hp H A₀ A₁ where
  commonLevel := (baseData hp F₀ F₁ H A₀ A₁).commonLevel
  timeLevel := (baseData hp F₀ F₁ H A₀ A₁).timeLevel
  collar := (baseData hp F₀ F₁ H A₀ A₁).collar
  assignment := perturbedAssignment hp F₀ F₁ H A₀ A₁
  horizontalVertexFixed :=
    perturbedAssignment_horizontalVertexFixed hp F₀ F₁ H A₀ A₁
  positiveRayGeneralPosition :=
    perturbedAssignment_positiveRayGeneralPosition hp F₀ F₁ H A₀ A₁

/-- Exact local-Stokes collar data obtained from the positive-ray-general-position package. -/
noncomputable def exactRelativeStableCollarDataAffinePullback
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    ExactRelativeStableCollarData hp H A₀ A₁ :=
  (exactRelativeStableCollarGeneralPositionDataAffinePullback hp F₀ F₁ H A₀ A₁).toExactRelativeStableCollarData

/-- The exact certificate retains the endpoint assignments literally. -/
theorem exactRelativeStableCollarData_affinePullback_horizontalVertexFixed
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    HorizontalVertexFixed hp A₀ A₁
      (exactRelativeStableCollarDataAffinePullback hp F₀ F₁ H A₀ A₁).collar
      (exactRelativeStableCollarDataAffinePullback hp F₀ F₁ H A₀ A₁).assignment :=
  (exactRelativeStableCollarDataAffinePullback hp F₀ F₁ H A₀ A₁).horizontalVertexFixed

/-- The exact certificate supplies the local positive-ray Stokes identity on every cell. -/
theorem exactRelativeStableCollarData_affinePullback_localPositiveRayStokes
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    (exactRelativeStableCollarDataAffinePullback hp F₀ F₁ H A₀ A₁).collar.toFoxNeuwirthRelativeAffineCollar.LocalPositiveRayStokes hp
        (exactRelativeStableCollarDataAffinePullback hp F₀ F₁ H A₀ A₁).assignment :=
  (exactRelativeStableCollarDataAffinePullback hp F₀ F₁ H A₀ A₁).localPositiveRayStokes

/-- The exact certificate identifies the two stable endpoint counts. -/
theorem exactRelativeStableCollarData_affinePullback_zeroCount_eq
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    A₀.zeroCount = A₁.zeroCount :=
  (exactRelativeStableCollarDataAffinePullback hp F₀ F₁ H A₀ A₁).zeroCount_eq

/-- The exact relative stable-collar construction proposition is inhabited by the concrete
 affine-pullback collar followed by the unconditional Route B perturbation. -/
theorem exactRelativeStableCollarConstruction_affinePullback :
    ExactRelativeStableCollarConstructionTheorem := by
  intro p hp F₀ F₁ H A₀ A₁
  exact ⟨exactRelativeStableCollarDataAffinePullback hp F₀ F₁ H A₀ A₁⟩

/-- Immediate stable-homotopy invariance consequence of the exact collar construction. -/
theorem stableHomotopyInvariance_affinePullback :
    StableHomotopyInvarianceTheorem :=
  stableHomotopyInvariance_of_exactRelativeStableCollarConstruction
    exactRelativeStableCollarConstruction_affinePullback

end StableExactRelativeCollarConstructionAffinePullback
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
