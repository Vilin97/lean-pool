/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableCollarRelativeSubdivision

/-!
# Exact relative stable-collar interface

The polynomial package in `StableCollarRelativeSubdivision` is one sufficient route to the local
positive-ray Stokes identity.  It is not the mathematical interface consumed by the global
argument.  In particular, requiring an invertible `(p-1) x (p-1)` deviation matrix on every mixed
codimension-two face is too strong when a retained frozen endpoint vertex has zero deviation.

This file records the exact, boundary-compatible interface.  A construction supplies an actual
prime-equivariant assignment, exact horizontal boundary values, and the cellwise Stokes identity.
No discontinuous endpoint-adjusted sampler and no unnecessary codimension-two determinant are
part of the certificate.
-/

namespace NRR

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace StableCollarRelativeSubdivisionExact

open EquivariantCoordinateHomotopy
open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap

variable {p : Nat}

/-! ## Boundary-compatible patched homotopy -/

/-- A global zero-free equivariant endpoint interpolant, together with the straight-line safety
that is stored simplexwise by a regular approximation.  A gluing theorem builds
this bundled map from the compatible local affine formulas. -/
structure ZeroFreeEndpointInterpolant
    (hp : Nat.Prime p) (F : ZeroFreeMap hp) where
  /-- The zero-free interpolating map joined to the original endpoint by a safe straight
  segment. -/
  map : ZeroFreeMap hp
  zeroFreeStraightLine : ∀ x (t : Set.Icc (0 : Real) 1),
    (1 - t.1) • F.map x + t.1 • map.map x ≠ 0

/-- Concatenate the safe segment from the lower interpolant to `F₀`, the supplied homotopy, and
the safe segment from `F₁` to the upper interpolant.  Unlike `endpointAdjustedAssignment`, this is
a continuous boundary-compatible zero-free target prescription on the entire cylinder. -/
noncomputable def patchedHomotopy
    {hp : Nat.Prime p} {F₀ F₁ : ZeroFreeMap hp}
    (I₀ : ZeroFreeEndpointInterpolant hp F₀)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (I₁ : ZeroFreeEndpointInterpolant hp F₁) :
    ZeroFreeHomotopy hp I₀.map I₁.map :=
  (ZeroFreeHomotopy.segment F₀ I₀.map I₀.zeroFreeStraightLine).symm.trans
    (H.trans (ZeroFreeHomotopy.segment F₁ I₁.map I₁.zeroFreeStraightLine))

/-- Exact data consumed by finite affine Stokes.  This is the correct target for a relative PL
construction with independently triangulated endpoints. -/
structure ExactRelativeStableCollarData
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) where
  /-- The common spatial level of the exact relative collar. -/
  commonLevel : Nat
  /-- The time-refinement level of the exact relative collar. -/
  timeLevel : Nat
  /-- The collar whose assignment agrees exactly with the horizontal endpoint data. -/
  collar : EndpointIdentifiedRelativeAffineCollar hp
    A₀.toRegularApproximation.level A₁.toRegularApproximation.level
    commonLevel timeLevel
  /-- The boundary-compatible assignment satisfying the local positive-ray Stokes identity. -/
  assignment : Assignment hp collar.cells
  horizontalVertexFixed : HorizontalVertexFixed hp A₀ A₁ collar assignment
  localPositiveRayStokes :
    collar.toFoxNeuwirthRelativeAffineCollar.LocalPositiveRayStokes hp assignment

namespace ExactRelativeStableCollarData

/-- The exact boundary-compatible collar data imply equality of the two supplied stable counts. -/
theorem zeroCount_eq
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (D : ExactRelativeStableCollarData hp H A₀ A₁) :
    A₀.zeroCount = A₁.zeroCount := by
  let B : EndpointBoundaryFixed hp A₀ A₁ D.collar D.assignment :=
    D.horizontalVertexFixed.toEndpointBoundaryFixed hp A₀ A₁ D.collar D.assignment
  rw [← B.lowerHorizontalContribution_eq_zeroCount,
    ← B.upperHorizontalContribution_eq_zeroCount]
  exact FoxNeuwirthRelativeAffineCollar.lowerHorizontalContribution_eq_upperHorizontalContribution_of_localPositiveRayStokes
      hp D.collar.toFoxNeuwirthRelativeAffineCollar D.assignment D.localPositiveRayStokes

/-- Every certificate built through the older polynomial route satisfies the exact interface. -/
noncomputable def ofExplicitRelativeStableCollarCertificate
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (C : StableCollarRelativeSubdivision.ExplicitRelativeStableCollarCertificate hp H A₀ A₁) :
    ExactRelativeStableCollarData hp H A₀ A₁ where
  commonLevel := C.commonLevel
  timeLevel := C.timeLevel
  collar := C.collar
  assignment := C.assignment
  horizontalVertexFixed := C.horizontalVertexFixed
  localPositiveRayStokes := C.localPositiveRayStokes

end ExactRelativeStableCollarData

/-- A convenient sufficient package: exact endpoint fixing together with the precise local
positive-ray general-position predicate already proved sufficient by the affine Stokes module. -/
structure ExactRelativeStableCollarGeneralPositionData
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) where
  /-- The common spatial level of the collar in positive-ray general position. -/
  commonLevel : Nat
  /-- The time-refinement level of the collar in positive-ray general position. -/
  timeLevel : Nat
  /-- The endpoint-identified collar used for the exact general-position certificate. -/
  collar : EndpointIdentifiedRelativeAffineCollar hp
    A₀.toRegularApproximation.level A₁.toRegularApproximation.level
    commonLevel timeLevel
  /-- The boundary-compatible vertex assignment in positive-ray general position. -/
  assignment : Assignment hp collar.cells
  horizontalVertexFixed : HorizontalVertexFixed hp A₀ A₁ collar assignment
  positiveRayGeneralPosition : ∀ q : collar.cells.Cell,
    PositiveRayGeneralPosition hp (localVertexMap hp collar.cells assignment q)

namespace ExactRelativeStableCollarGeneralPositionData

/-- Exact positive-ray general position produces the exact Stokes certificate. -/
noncomputable def toExactRelativeStableCollarData
    {hp : Nat.Prime p}
    {F₀ F₁ : ZeroFreeMap hp}
    {H : ZeroFreeHomotopy hp F₀ F₁}
    {A₀ : StableRegularApproximation hp F₀.map}
    {A₁ : StableRegularApproximation hp F₁.map}
    (D : ExactRelativeStableCollarGeneralPositionData hp H A₀ A₁) :
    ExactRelativeStableCollarData hp H A₀ A₁ where
  commonLevel := D.commonLevel
  timeLevel := D.timeLevel
  collar := D.collar
  assignment := D.assignment
  horizontalVertexFixed := D.horizontalVertexFixed
  localPositiveRayStokes :=
    FoxNeuwirthRelativeAffineCollar.localPositiveRayStokes_of_positiveRayGeneralPosition
      hp D.collar.toFoxNeuwirthRelativeAffineCollar D.assignment
        D.positiveRayGeneralPosition

end ExactRelativeStableCollarGeneralPositionData

/-- Existence proposition for the geometric construction. -/
def ExactRelativeStableCollarConstructionTheorem : Prop :=
  ∀ {p : Nat} (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map),
      Nonempty (ExactRelativeStableCollarData hp H A₀ A₁)

/-- The exact construction theorem implies the project stable-homotopy-invariance interface. -/
theorem stableHomotopyInvariance_of_exactRelativeStableCollarConstruction
    (HC : ExactRelativeStableCollarConstructionTheorem) :
    StableHomotopyInvarianceTheorem := by
  intro p hp F₀ F₁ H A₀ A₁
  exact (Classical.choice (HC hp F₀ F₁ H A₀ A₁)).zeroCount_eq

/-! ## Formal obstruction to the over-strong mixed-face minor condition -/

/-- If one retained codimension-two vertex has all target coordinates equal, then the corresponding
column of the deviation matrix is identically zero.  Such a vertex is compatible with endpoint
stability when its common coordinate is negative, but it makes the full deviation determinant
condition impossible. -/
theorem codimTwoDeviationMatrix_column_eq_zero_of_constantVertex
    {N₀ N₁ M L : Nat}
    (hp : Nat.Prime p)
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C)
    (q : C.Cell)
    (f : CodimTwoFace p)
    (c : Fin (p - 1))
    (hconstant : ∀ r : Fin (p - 1),
      vectorValue hp C a
          (sampleVertex hp C (q, codimTwoVertex hp f c))
          (ReferenceAffineOrbitCount.coordinateLabel hp r) =
        vectorValue hp C a
          (sampleVertex hp C (q, codimTwoVertex hp f c))
          (ReferenceAffineOrbitCount.lastLabel hp)) :
    ∀ r : Fin (p - 1),
      codimTwoDeviationMatrix hp C a q f r c = 0 := by
  intro r
  simpa [codimTwoDeviationMatrix, VertexMap.deviation, sub_eq_zero] using hconstant r

/-- Consequently the full deviation minor required by the old mixed-face genericity family is
zero.  This is the formal algebraic obstruction to the manuscript's local-completion lemma. -/
theorem codimTwoMinor_eq_zero_of_constantVertex
    {N₀ N₁ M L : Nat}
    (hp : Nat.Prime p)
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C)
    (q : C.Cell)
    (f : CodimTwoFace p)
    (c : Fin (p - 1))
    (hconstant : ∀ r : Fin (p - 1),
      vectorValue hp C a
          (sampleVertex hp C (q, codimTwoVertex hp f c))
          (ReferenceAffineOrbitCount.coordinateLabel hp r) =
        vectorValue hp C a
          (sampleVertex hp C (q, codimTwoVertex hp f c))
          (ReferenceAffineOrbitCount.lastLabel hp)) :
    Matrix.det (codimTwoDeviationMatrix hp C a q f) = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero c
  exact codimTwoDeviationMatrix_column_eq_zero_of_constantVertex
    hp C a q f c hconstant

/-- At a non-purely-horizontal face containing such a retained vertex, the corresponding old
`RelativeGenericityIndex` can never have nonzero `genericityValue`. -/
theorem mixedCodimTwo_genericityValue_eq_zero_of_constantVertex
    {N₀ N₁ M L : Nat}
    (hp : Nat.Prime p)
    (C : RelativeAffineCellSystem hp N₀ N₁ M L)
    (a : Assignment hp C)
    (q : C.Cell)
    (f : CodimTwoFace p)
    (hnonpure : ¬ IsPurelyHorizontalCodimTwo hp C q f)
    (c : Fin (p - 1))
    (hconstant : ∀ r : Fin (p - 1),
      vectorValue hp C a
          (sampleVertex hp C (q, codimTwoVertex hp f c))
          (ReferenceAffineOrbitCount.coordinateLabel hp r) =
        vectorValue hp C a
          (sampleVertex hp C (q, codimTwoVertex hp f c))
          (ReferenceAffineOrbitCount.lastLabel hp)) :
    genericityValue hp C a (Sum.inr ⟨(q, f), hnonpure⟩) = 0 := by
  exact codimTwoMinor_eq_zero_of_constantVertex hp C a q f c hconstant

end StableCollarRelativeSubdivisionExact
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
