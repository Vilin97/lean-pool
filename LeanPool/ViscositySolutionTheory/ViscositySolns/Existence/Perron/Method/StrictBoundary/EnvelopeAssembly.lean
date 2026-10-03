/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Method.StrictBoundary.BentAnnulusPatches

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Strict-boundary Perron interfaces (EnvelopeAssembly)

Part of Dirichlet-data specializations of the Perron method theorem in the
forms closest to the source document. Split from `StrictBoundary.lean`; see
the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat} {g : Point n -> Real}

namespace PerronMethodExistenceTheorem

/--
Strict-boundary Perron theorem in Dirichlet form, using strict
Perron-envelope approximation on the explicit closed annulus plus
lower-semicontinuity of Perron-family branches there.
-/
theorem strictBoundary_of_bentSourceClosedAnnulusEnvelopeLscSelectionPatch
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
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusEnvelopeLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  of_perronFamily_top_and_bentSourceClosedAnnulusEnvelopeLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

end PerronMethodExistenceTheorem

namespace PerronMethodExistenceTheorem

/--
Strict-boundary Perron theorem in Dirichlet form, using the
domain-controlled strict Perron-envelope approximation package on the explicit
closed annulus.
-/
theorem strictBoundary_of_bentSourceClosedAnnulusDomainEnvelopeLscSelectionPatch
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
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusDomainEnvelopeLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  of_perronFamily_top_and_bentSourceClosedAnnulusDomainEnvelopeLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

end PerronMethodExistenceTheorem

namespace PerronMethodExistenceTheorem

/--
Strict-boundary Perron theorem in Dirichlet form, using closed-ball
source geometry for the explicit closed-annulus lower bump package.
-/
theorem strictBoundary_of_bentSourceClosedBallEnvelopeLscSelectionPatch
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
      PerronLowerEnvelopeBentQuadraticSourceClosedBallEnvelopeLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  of_perronFamily_top_and_bentSourceClosedBallEnvelopeLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using closed-ball
source geometry with annulus strictness against the lower relaxed Perron
envelope.
-/
theorem strictBoundary_of_bentSourceClosedBallLowerEnvelopeLscSelectionPatch
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
      PerronLowerEnvelopeBentQuadraticSourceClosedBallLowerEnvelopeLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  of_perronFamily_top_and_bentSourceClosedBallLowerEnvelopeLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
outer-transition closed-ball annulus package.
-/
theorem strictBoundary_of_bentSourceOuterClosedBallLowerEnvelopePatch
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
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  of_perronFamily_top_and_bentSourceOuterClosedBallLowerEnvelopePatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the legacy
outer-transition closed-ball annulus package with branch lower-semicontinuity.
-/
theorem strictBoundary_of_bentSourceOuterClosedBallLowerEnvelopeLscSelectionPatch
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
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  strictBoundary_of_bentSourceOuterClosedBallLowerEnvelopePatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.lowerEnvelopePatch

/--
Strict-boundary Perron theorem in Dirichlet form, where operator
continuity and open-domain geometry supply the source outer-closed-ball
lower-envelope patch package directly.
-/
theorem strictBoundary_of_bentSourceOuterClosedBallOpenGeometry
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hboundaryOutside : ∀ z : Point n, z ∈ boundary -> z ∉ C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  of_perronFamily_top_and_bentSourceOuterClosedBallOpenGeometry
    B hcomparison hF hFell hFinv hCopen hboundaryOutside
    hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow

/--
Strict-boundary Perron theorem in Dirichlet form, using the
semijet-driven outer-transition source package.
-/
theorem strictBoundary_of_bentSourceOuterClosedBallSemijetLscSelectionPatch
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
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSemijetLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  of_perronFamily_top_and_bentSourceOuterClosedBallSemijetLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
small-radius semijet-driven outer-transition source package.
-/
theorem strictBoundary_of_bentSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatch
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
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  of_perronFamily_top_and_bentSourceOuterClosedBallSmallRadiusSemijetLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the geometric
small-radius semijet-driven outer-transition source package.
-/
theorem strictBoundary_of_bentSourceOuterClosedBallGeometricSemijetLscSelectionPatch
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
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  of_perronFamily_top_and_bentSourceOuterClosedBallGeometricSemijetLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using pure
outer-annulus branch lower-semicontinuity data.
-/
theorem strictBoundary_of_bentSourceOuterAnnulusLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hboundaryOutside : ∀ z : Point n, z ∈ boundary -> z ∉ C)
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
      PerronLowerEnvelopeBentQuadraticSourceOuterAnnulusLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  of_perronFamily_top_and_bentSourceOuterAnnulusLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hboundaryOutside
    hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using domain
lower-semicontinuity of the Perron-family branches as the remaining branch
regularity input.
-/
theorem strictBoundary_of_perronFamilyLowerSemicontinuousOnDomain
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hboundaryOutside : ∀ z : Point n, z ∈ boundary -> z ∉ C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hreg :
      PerronFamilyLowerSemicontinuousOnDomain
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  of_perronFamily_top_and_perronFamilyLowerSemicontinuousOnDomain
    B hcomparison hF hFell hFinv hCopen hboundaryOutside
    hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hreg

end PerronMethodExistenceTheorem

/--
Strict-boundary Perron theorem in Dirichlet form, using operator
continuity for the lifted quadratic and compact-inactive selection for the
remaining source bump gluing step.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_localQuadraticCompactInactiveSelection
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
    (hselect :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSelection C boundary F
        g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticCompactInactiveSelection
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hselect

/--
Strict-boundary Perron theorem in Dirichlet form, using the
active-branch quadratic gluing version of the lower bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_localQuadraticActiveGluing
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
    (hactive : PerronLowerEnvelopeLocalQuadraticActiveGluing C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticActiveGluing
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hactive

/--
Strict-boundary Perron theorem in Dirichlet form, using
source-shaped interior quadratic bump data for the lower-side construction.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_interiorQuadraticBump
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hinterior : ∀ z : Point n, z ∈ C -> z ∈ interior C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hbump : PerronLowerEnvelopeInteriorQuadraticBump C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_interiorQuadraticBump
    B hcomparison hF hFell hinterior hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hbump

/--
Packaged hypotheses for the Section 4 Perron existence theorem with Dirichlet
data `g`.

The comparison principle remains abstract here, preserving the Perron/comparison
import boundary. Operator continuity, open-domain geometry, and boundary
separation supply the source outer-closed-ball lower-envelope annulus package
internally. The method layer proves the maximality identity `W^* = W` on the
domain and patches directly over `W^*`, so this final wrapper does not expose
the lower bump or abstract localized-improvement payload.
-/
structure PerronStrictBoundarySection4Hypotheses
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) :
    Prop where
  comparison :
    DirichletComparisonPrinciple C boundary F g
  operator_continuous : OperatorContinuous F
  degenerate_elliptic : DegenerateElliptic F
  hessian_symmetric_invariant : HessianSymmetricInvariant F
  domain_open : IsOpen C
  boundary_outside_domain :
    ∀ z : Point n, z ∈ boundary -> z ∉ C
  lower_trace :
    BoundaryLowerTraceOn C boundary g B.lower
  upper_trace :
    BoundaryUpperTraceOn C boundary g B.upper
  nontrivial_nhds :
    ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot
  upper_locally_bounded :
    ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper
  lower_locally_bounded :
    ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower

/--
Packaged hypotheses for the zero-boundary Section 4 Perron existence theorem.
These are the hypotheses of `PerronStrictBoundarySection4Hypotheses` with
`g = 0`.
-/
structure PerronStrictBoundaryZeroSection4Hypotheses
    (C boundary : Set (Point n)) (F : Operator n)
    (B : DirichletBarrierPair C boundary F (fun _ : Point n => (0 : Real))) :
    Prop where
  comparison :
    DirichletComparisonPrinciple C boundary F (fun _ : Point n => (0 : Real))
  operator_continuous : OperatorContinuous F
  degenerate_elliptic : DegenerateElliptic F
  hessian_symmetric_invariant : HessianSymmetricInvariant F
  domain_open : IsOpen C
  boundary_outside_domain :
    ∀ z : Point n, z ∈ boundary -> z ∉ C
  lower_trace :
    BoundaryLowerTraceOn C boundary (fun _ : Point n => (0 : Real)) B.lower
  upper_trace :
    BoundaryUpperTraceOn C boundary (fun _ : Point n => (0 : Real)) B.upper
  nontrivial_nhds :
    ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot
  upper_locally_bounded :
    ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper
  lower_locally_bounded :
    ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower

namespace PerronMethodExistenceTheorem

/--
Final Perron existence theorem in the Section 4 shape, with Dirichlet data `g`.

This is the stable public wrapper around the Perron assembly: upper stability,
comparison with the upper barrier, operator-continuous quadratic bumping, and
open-domain source geometry combine to produce the Perron solution.
-/
theorem strictBoundary
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (h : PerronStrictBoundarySection4Hypotheses C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  strictBoundary_of_bentSourceOuterClosedBallOpenGeometry
    B h.comparison h.operator_continuous h.degenerate_elliptic
    h.hessian_symmetric_invariant h.domain_open h.boundary_outside_domain
    h.lower_trace h.upper_trace h.nontrivial_nhds h.upper_locally_bounded
    h.lower_locally_bounded

/--
Final zero-boundary Perron existence theorem in the Section 4 shape: the case
`g = 0` of `strictBoundary`.
-/
theorem strictBoundary_zero
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F (fun _ : Point n => (0 : Real)))
    (h : PerronStrictBoundaryZeroSection4Hypotheses C boundary F B) :
    DirichletSolutionOn C boundary F (fun _ : Point n => (0 : Real))
      (upperEnvelope C (perronEnvelope C boundary F
        (fun _ : Point n => (0 : Real)) B.lower B.upper)) :=
  strictBoundary B
    ⟨h.comparison, h.operator_continuous, h.degenerate_elliptic,
      h.hessian_symmetric_invariant, h.domain_open, h.boundary_outside_domain,
      h.lower_trace, h.upper_trace, h.nontrivial_nhds, h.upper_locally_bounded,
      h.lower_locally_bounded⟩

end PerronMethodExistenceTheorem

end ViscositySolns
