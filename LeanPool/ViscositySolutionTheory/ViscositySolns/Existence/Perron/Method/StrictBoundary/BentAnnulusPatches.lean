/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Method.StrictBoundary.SubsolutionPatches

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Strict-boundary Perron interfaces (BentAnnulusPatches)

Part of Dirichlet-data specializations of the Perron method theorem in the
forms closest to the source document. Split from `StrictBoundary.lean`; see
the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat} {g : Point n -> Real}

/--
Strict-boundary Perron theorem in Dirichlet form, using operator
continuity for the lifted quadratic and an explicit patch-selection input for
the remaining local gluing step.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_localQuadraticPatchSelection
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hselect : PerronLowerEnvelopeLocalQuadraticPatchSelection C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticPatchSelection
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hselect

/--
Strict-boundary Perron theorem in Dirichlet form, using operator
continuity for the lifted quadratic and compact-inactive local patch data for
the remaining source bump step.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_localQuadraticCompactInactivePatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactivePatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticCompactInactivePatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using operator
continuity for the lifted quadratic, compact-inactive local subsolution-patch
data, and comparison for the upper-barrier bound.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_localQuadraticCompactInactiveSubsolution
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSubsolutionPatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveSubsolution
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using
compact-inactive data whose active branch is the lifted quadratic itself on
relative-open local subsolution domains.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_localQuadraticCompactInactiveQuadratic
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveQuadratic
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using certified
compact-inactive active domains for the lifted quadratic. The quadratic
subsolution certification is discharged from degenerate ellipticity and
Hessian-symmetric invariance.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_localQuadraticCompactInactiveCertified
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveCertifiedPatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveCertified
    B hcomparison hF hFell hFinv hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using
symmetrized certified compact-inactive active-domain data. Hessian-symmetric
invariance removes the need to assume the failed subjet Hessian is Hermitian.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_compactInactiveSymCertified
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSymCertifiedPatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveSymCertified
    B hcomparison hF hFell hFinv hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using
boundary-safe compact-inactive data. The boundary condition is checked only
for the lifted quadratic branch.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_compactInactiveBoundary
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveBoundaryPatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveBoundary
    B hcomparison hF hFell hFinv hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using
boundary-covered compact-inactive data. Boundary domination is supplied by the
selected old Perron branch.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_compactInactiveCovered
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveCoveredPatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveCovered
    B hcomparison hF hFell hFinv hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using exterior
compact-inactive data. The active quadratic neighborhood is separated from the
boundary, and the inactive compact covers the exterior in `C ∪ boundary`.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_compactInactiveExterior
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveExteriorPatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveExterior
    B hcomparison hF hFell hFinv hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using lower-barrier
exterior compact-inactive data. On the inactive compact, the lower barrier
itself supplies the old Perron branch.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_barrierExterior
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeLocalQuadraticBarrierExteriorPatch C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_barrierExterior
    B hcomparison hF hFell hFinv hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using open-active
lower-barrier exterior data. Operator continuity supplies the open active
quadratic neighborhood, and openness of `C` supplies the active local domain.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_openBarrierExterior
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeLocalQuadraticOpenBarrierExteriorPatch
      C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_openBarrierExterior
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the bent
open-active lower-barrier exterior data from the source bump construction.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bentOpenBarrierExterior
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeBentQuadraticOpenBarrierExteriorPatch
      C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bentOpenBarrierExterior
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the localized
bent lower-barrier piecewise patch data from the source bump construction.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bentLocalizedLowerPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeBentQuadraticLocalizedLowerPatch
      C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bentLocalizedLowerPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using open
patch-set data for the localized bent lower-barrier piecewise patch.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bentOpenPiecewisePatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeBentQuadraticOpenPiecewisePatch
      C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bentOpenPiecewisePatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using
boundary-away open patch-set data for the localized bent lower-barrier
piecewise patch.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bentBoundaryAwayOpenPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeBentQuadraticBoundaryAwayOpenPatch
      C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bentBoundaryAwayOpenPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using ball-shaped
patch data for the localized bent lower-barrier piecewise patch.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bentBallPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeBentQuadraticBallPatch
      C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bentBallPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using closed-ball
annulus data for the localized bent lower-barrier patch.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bentClosedBallAnnulusPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeBentQuadraticClosedBallAnnulusPatch
      C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bentClosedBallAnnulusPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using shrinking
closed-ball annulus data for the localized bent lower-barrier patch.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bentShrinkingClosedBallAnnulusPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bentShrinkingClosedBallAnnulusPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using
small-radius closed-ball annulus data for the localized bent lower-barrier
patch.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bentSmallRadiusClosedBallAnnulusPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSmallRadiusClosedBallAnnulusPatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSmallRadiusClosedBallAnnulusPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
source-radius closed-ball annulus data from the localized lower bump
construction.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bentSourceClosedBallAnnulusPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedBallAnnulusPatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceClosedBallAnnulusPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
source-radius compact-inactive lower bump package with finite old-branch
selection.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bentSourceCompactInactivePatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceCompactInactivePatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceCompactInactivePatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
source-radius transition-annulus lower bump package.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bentSourceAnnulusSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceAnnulusSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
source-radius closed-annulus transition package.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bentSourceClosedAnnulusSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceClosedAnnulusSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
lower-semicontinuous pointwise branch version of the source-radius
closed-annulus transition package.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bentSourceClosedAnnulusLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatch C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceClosedAnnulusLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

end ViscositySolns
