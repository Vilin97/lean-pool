/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Method.LowerInterfaces.CoreInterfaces

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Perron-family lower conclusion interfaces (BentSourcePatches)

Part of the Perron existence development using the canonical Perron-family
upper side and lower-side conclusions from the bump argument. Split from
`LowerInterfaces.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/--
Perron's method with the canonical Perron-family upper side, using the
source-shaped bent open-active lower-barrier exterior patch input.

This matches the bump in the source proof more closely than the unbent
quadratic interface: operator continuity supplies a positive vertical lift and
a positive downward identity-Hessian bend, while the remaining input is the
exterior annulus where the bent quadratic is locally below the lower barrier.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentOpenBarrierExterior
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticOpenBarrierExteriorPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_strictLocalPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hF.perronLowerEnvelope_strictLocalPatch_of_bentOpenBarrierExterior
      hcomparison hFell hFinv hCopen hpatch)

/--
Perron's method with the canonical Perron-family upper side, using the
localized bent lower-barrier piecewise patch input.

This is the source-shaped endpoint closest to the piecewise construction in
Section 4: the patch is locally `max(lower, q)` on the active neighborhood and
locally the lower barrier away from it.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentLocalizedLowerPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticLocalizedLowerPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_strictPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hF.perronLowerEnvelope_strictPatch_of_bentLocalizedLowerPatch
      hcomparison hFell hFinv hCopen hpatch)

/--
Perron's method with the canonical Perron-family upper side, using open
patch-set data for the localized bent lower-barrier piecewise patch.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentOpenPiecewisePatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticOpenPiecewisePatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_bentLocalizedLowerPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.localizedLowerPatch

/--
Perron's method with the canonical Perron-family upper side, using
boundary-away open patch-set data for the localized bent lower-barrier
piecewise patch.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentBoundaryAwayOpenPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticBoundaryAwayOpenPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_bentOpenPiecewisePatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.openPiecewisePatch

/--
Perron's method with the canonical Perron-family upper side, using ball-shaped
patch data for the localized bent lower-barrier piecewise patch.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentBallPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticBallPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_bentBoundaryAwayOpenPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.boundaryAwayOpenPatch

/--
Perron's method with the canonical Perron-family upper side, using
closed-ball annulus data for the localized bent lower-barrier patch.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentClosedBallAnnulusPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticClosedBallAnnulusPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_bentBallPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.ballPatch

/--
Perron's method with the canonical Perron-family upper side, using shrinking
closed-ball annulus data for the localized bent lower-barrier patch.

This is the source-shaped ball route: the patch ball is allowed to be smaller
than the open strict-negativity neighborhood supplied by operator continuity.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentShrinkingClosedBallAnnulusPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_strictPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hF.perronLowerEnvelope_strictPatch_of_bentShrinkingLocalizedLowerPatch
      hcomparison hFell hFinv hCopen hpatch.shrinkingPatch)

/--
Perron's method with the canonical Perron-family upper side, using
small-radius closed-ball annulus data for the localized bent lower-barrier
patch.

The radius is chosen small enough to lie in the operator-continuity
strict-negativity neighborhood, then the existing shrinking-annulus route
performs the gluing.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSmallRadiusClosedBallAnnulusPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSmallRadiusClosedBallAnnulusPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_bentShrinkingClosedBallAnnulusPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.shrinking

/--
Perron's method with the canonical Perron-family upper side, using the
source-radius closed-ball annulus lower bump package.

Here the lift of the bent quadratic is chosen together with the patch radius
as in the source proof, rather than being quantified over independently.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceClosedBallAnnulusPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedBallAnnulusPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_strictPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hpatch.strictPatch hcomparison hFell hFinv hCopen)

/--
Perron's method with the canonical Perron-family upper side, using the
source-radius compact-inactive lower bump package.

This route performs the finite old-branch selection inside the Perron proof:
local Perron-family domination on the inactive compact set is converted to one
old Perron branch, then maxed with the bent source quadratic.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceCompactInactivePatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceCompactInactivePatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_strictPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hpatch.strictPatch hcomparison hFell hFinv hCopen)

/--
Perron's method with the canonical Perron-family upper side, using the
source-radius transition-annulus lower bump package.

Finite old-branch selection is required only on the compact transition set;
outside the patch ball the piecewise patch is already the old branch.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceAnnulusSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_strictPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hpatch.strictPatch hcomparison hFell hFinv hCopen)

/--
Perron's method with the canonical Perron-family upper side, using the
concrete closed-annulus version of the source-radius transition package.

The metric transition across the patch sphere is discharged by the bridge to
`PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatch`; the caller only
supplies local Perron-family domination on the explicit annulus
`r / 2 <= dist z x <= r`.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceClosedAnnulusSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceAnnulusSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.annulusSelectionPatch

/--
Perron's method with the canonical Perron-family upper side, using the
lower-semicontinuous pointwise branch version of the closed-annulus source
package.

The pointwise strict branch gap and lower semicontinuity are converted into
local branch domination on the explicit annulus before applying the
closed-annulus theorem.
-/
theorem
    PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceClosedAnnulusLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceClosedAnnulusSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.closedAnnulusSelectionPatch

namespace PerronMethodExistenceTheorem

/--
Perron's method with the canonical Perron-family upper side, using strict
Perron-envelope approximation on the explicit closed annulus plus
lower-semicontinuity of Perron-family branches there.
-/
theorem of_perronFamily_top_and_bentSourceClosedAnnulusEnvelopeLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusEnvelopeLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_bentSourceClosedAnnulusLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.lscSelectionPatch

end PerronMethodExistenceTheorem

namespace PerronMethodExistenceTheorem

/--
Perron's method with the canonical Perron-family upper side, using strict
Perron-envelope approximation on the closed annulus and deriving the required
pointwise Perron-family boundedness from the annulus-domain condition.
-/
theorem of_perronFamily_top_and_bentSourceClosedAnnulusDomainEnvelopeLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusDomainEnvelopeLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_bentSourceClosedAnnulusEnvelopeLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.envelopeLscSelectionPatch

end PerronMethodExistenceTheorem

namespace PerronMethodExistenceTheorem

/--
Perron's method with the canonical Perron-family upper side, using closed-ball
source geometry to supply the domain-controlled closed-annulus package.
-/
theorem of_perronFamily_top_and_bentSourceClosedBallEnvelopeLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedBallEnvelopeLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_bentSourceClosedAnnulusDomainEnvelopeLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.domainEnvelopeLscSelectionPatch

end PerronMethodExistenceTheorem

namespace PerronMethodExistenceTheorem

/--
Perron's method with the canonical Perron-family upper side, using the
outer-transition closed-ball annulus package.

The lower bump input is stated on `3 * r / 4 <= dist z x <= r`, which is still
enough for the piecewise patch transition near the patch sphere and leaves
room for the source subjet estimate.
-/
theorem of_perronFamily_top_and_bentSourceOuterClosedBallLowerEnvelopePatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_upperEnvelopeLocalizedImprovement
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (upperEnvelopeLocalizedImprovement_of_sourceOuterClosedBallLowerEnvelope
      B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
      hupperBddAbove hlowerBddBelow hpatch)

/--
Legacy outer-transition closed-ball annulus package implies the no-LSC method
input by forgetting the branch lower-semicontinuity field.
-/
theorem of_perronFamily_top_and_bentSourceOuterClosedBallLowerEnvelopeLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_bentSourceOuterClosedBallLowerEnvelopePatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.lowerEnvelopePatch

/--
Perron's method with the canonical Perron-family upper side, where operator
continuity and open-domain geometry supply the source outer-closed-ball
lower-envelope patch package directly.
-/
theorem of_perronFamily_top_and_bentSourceOuterClosedBallOpenGeometry
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hboundaryOutside : ∀ z : Point n, z ∈ boundary -> z ∉ C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_bentSourceOuterClosedBallLowerEnvelopePatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow
    (hF.perronLowerEnvelope_sourceOuterClosedBallLowerEnvelopePatch
      (B := B) hCopen hboundaryOutside)

end PerronMethodExistenceTheorem

namespace PerronMethodExistenceTheorem

/--
Perron's method with the canonical Perron-family upper side, using
semijet-driven outer-transition source data.
-/
theorem of_perronFamily_top_and_bentSourceOuterClosedBallSemijetLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_bentSourceOuterClosedBallLowerEnvelopePatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow
    hpatch.outerClosedBallLowerEnvelopePatch

/--
Perron's method with the canonical Perron-family upper side, using
small-radius semijet-driven outer-transition source data.
-/
theorem of_perronFamily_top_and_bentSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_bentSourceOuterClosedBallLowerEnvelopePatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow
    hpatch.outerClosedBallLowerEnvelopePatch

/--
Perron's method with the canonical Perron-family upper side, using geometric
small-radius semijet outer-transition source data. Operator continuity supplies
the source strict-negativity scale.
-/
theorem of_perronFamily_top_and_bentSourceOuterClosedBallGeometricSemijetLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_bentSourceOuterClosedBallLowerEnvelopePatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow
    (hpatch.outerClosedBallLowerEnvelopePatch hF)

/--
Perron's method with the canonical Perron-family upper side, using pure
outer-annulus branch lower-semicontinuity data. Openness of the domain supplies
the closed-ball geometry.
-/
theorem of_perronFamily_top_and_bentSourceOuterAnnulusLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hboundaryOutside : ∀ z : Point n, z ∈ boundary -> z ∉ C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterAnnulusLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_bentSourceOuterClosedBallGeometricSemijetLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow
    (hpatch.geometricSemijetLscSelectionPatch hCopen hboundaryOutside)

/--
Perron's method with the canonical Perron-family upper side, using the named
domain lower-semicontinuity regularity of Perron-family branches. Openness of
the domain converts this branch regularity into the source outer-annulus LSC
package used by the quadratic bump assembly.
-/
theorem of_perronFamily_top_and_perronFamilyLowerSemicontinuousOnDomain
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hboundaryOutside : ∀ z : Point n, z ∈ boundary -> z ∉ C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hreg : PerronFamilyLowerSemicontinuousOnDomain C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_bentSourceOuterAnnulusLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hboundaryOutside hlowerTrace
    hupperTrace hne hupperBddAbove hlowerBddBelow
    (hreg.bentSourceOuterAnnulusLscSelectionPatch hCopen)

end PerronMethodExistenceTheorem

namespace PerronMethodExistenceTheorem

/--
Perron's method with the canonical Perron-family upper side, using closed-ball
source geometry and annulus strictness against the lower relaxed Perron
envelope.
-/
theorem of_perronFamily_top_and_bentSourceClosedBallLowerEnvelopeLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedBallLowerEnvelopeLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_bentSourceClosedBallEnvelopeLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow
    (hpatch.closedBallEnvelopeLscSelectionPatch hlowerBddBelow)

end PerronMethodExistenceTheorem

/--
Perron's method with the canonical Perron-family upper side, where operator
continuity supplies the lifted quadratic and the remaining input is the
compact-inactive selection step.

This is closer to the source bump construction than the branch-separation
patch-selection interface: outside the active quadratic neighborhood, finite
Perron selection makes the old branch dominate; inside the active
neighborhood, the max of the old branch and the local quadratic subsolution
representative certifies the local germ.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticCompactInactiveSelection
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hselect :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSelection C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticGluing
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hF.perronLowerEnvelope_localQuadraticGluing_of_compactInactiveSelection hselect)

/--
Perron's method with the canonical Perron-family upper side and the
active-branch quadratic gluing form of the lower bump construction.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticActiveGluing
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hactive : PerronLowerEnvelopeLocalQuadraticActiveGluing C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticGluing
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    hactive.localQuadraticGluing


end ViscositySolns
