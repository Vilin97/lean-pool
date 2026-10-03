/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Method.LowerInterfaces

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Strict-boundary Perron interfaces (SubsolutionPatches)

Part of Dirichlet-data specializations of the Perron method theorem in the
forms closest to the source document. Split from `StrictBoundary.lean`; see
the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat} {g : Point n -> Real}

/--
Strict-boundary Perron theorem in Dirichlet form used in the source
document, with comparison kept as an explicit hypothesis.

The remaining analytic input is the source-shaped strict subsolution patch
form of the bump lemma: every failed lower-envelope subjet inequality produces
a Dirichlet subsolution patch above the lower barrier. This theorem packages
the completed Perron assembly around that input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_strictSubsolutionPatch
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
    (hpatch : PerronLowerEnvelopeStrictSubsolutionPatch C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_strictSubsolutionPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
localized-improvement version of the lower bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_localizedImprovement
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
    (himprove : PerronLowerEnvelopeLocalizedImprovement C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_localizedImprovement
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow himprove

/--
Strict-boundary Perron theorem in Dirichlet form, using a direct
localized improvement over the upper Perron envelope. The method layer proves
`W^* = W` on the domain before converting this to the usual localized
improvement contradiction.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_upperEnvelopeLocalizedImprovement
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
    (himprove : PerronUpperEnvelopeLocalizedImprovement C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_upperEnvelopeLocalizedImprovement
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    himprove

/--
Strict-boundary Perron theorem in Dirichlet form, using the
neighborhood-form localized improvement input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_neighborhoodImprovement
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
    (himprove : PerronLowerEnvelopeNeighborhoodImprovement C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_neighborhoodImprovement
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow himprove

/--
Strict-boundary Perron theorem in Dirichlet form, using an already
proved lower-envelope viscosity supersolution property.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_lowerViscosity
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hlowerVisc : ViscositySupersolution C F
      (lowerEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)))
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
  PerronMethodExistenceTheorem.of_perronFamily_top_and_lowerViscosity
    B hcomparison hF hlowerVisc hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow

/--
Strict-boundary Perron theorem in Dirichlet form, using the
lower-envelope subjet inequality supplied by the bump argument.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bumpInequality
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
    (hineq : PerronLowerEnvelopeSubjetInequality C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bumpInequality
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hineq

/--
Strict-boundary Perron theorem in Dirichlet form, using the formal
bump contradiction as the lower-side input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_bumpContradiction
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
    (hbump : PerronLowerEnvelopeBumpContradiction C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_bumpContradiction
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hbump

/--
Strict-boundary Perron theorem in Dirichlet form, using the
pointwise-lower-semicontinuous version of the bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_pointwiseStrictSubsolutionPatch
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
    (hpatch : PerronLowerEnvelopePointwiseStrictSubsolutionPatch C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_pointwiseStrictSubsolutionPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
continuous pointwise version of the bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_continuousStrictPatch
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
    (hpatch : PerronLowerEnvelopeContinuousStrictSubsolutionPatch C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_continuousStrictPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the continuous
Dirichlet-bump version of the lower bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_continuousBump
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
    (hbump : PerronLowerEnvelopeContinuousBump C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_continuousBump
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hbump

/--
Strict-boundary Perron theorem in Dirichlet form, using the continuous
max-patch version of the lower bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_continuousMaxPatch
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
    (hpatch : PerronLowerEnvelopeContinuousMaxPatch C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_continuousMaxPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the continuous
local max-patch version of the lower bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_localMaxPatch
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
    (hpatch : PerronLowerEnvelopeContinuousLocalMaxPatch C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_localMaxPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
branch-local continuous max-patch version of the lower bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_branchMaxPatch
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
    (hpatch : PerronLowerEnvelopeContinuousBranchMaxPatch C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_branchMaxPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
active-branch continuous max-patch version of the lower bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_activeMaxPatch
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
    (hpatch : PerronLowerEnvelopeContinuousActiveMaxPatch C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_activeMaxPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the strict
active-branch continuous max-patch version of the lower bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_strictActivePatch
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
    (hpatch : PerronLowerEnvelopeContinuousStrictActiveMaxPatch C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_strictActivePatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the strict
active subsolution-bump version of the lower bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_strictActiveSubsolutionBump
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
    (hbump : PerronLowerEnvelopeContinuousStrictActiveSubsolutionBump C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_strictActiveSubsolutionBump
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hbump

/--
Strict-boundary Perron theorem in Dirichlet form, using the strict
active Dirichlet-bump version of the lower bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_strictActiveDirichletBump
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
    (hbump : PerronLowerEnvelopeContinuousStrictActiveDirichletBump C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_strictActiveDirichletBump
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hbump

/--
Strict-boundary Perron theorem in Dirichlet form, using the
source-shaped strict patch form of the lower bump lemma.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_strictPatch
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
    (hpatch : PerronLowerEnvelopeStrictPatch C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_strictPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
max-patch form of the localized bump construction.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_maxPatchBump
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
    (hbump : PerronLowerEnvelopeMaxPatchBump C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_maxPatchBump
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hbump

/--
Strict-boundary Perron theorem in Dirichlet form, using the strict
local-patch form of the lower bump construction.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_strictLocalPatch
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
    (hpatch : PerronLowerEnvelopeStrictLocalPatch C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_strictLocalPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
source-shaped local quadratic max-patch version of the lower bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_localQuadraticMaxPatch
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
    (hpatch : PerronLowerEnvelopeLocalQuadraticMaxPatch C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticMaxPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hpatch

/--
Strict-boundary Perron theorem in Dirichlet form, using the
local-germ quadratic gluing version of the lower bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_localQuadraticGluing
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
    (hglue : PerronLowerEnvelopeLocalQuadraticGluing C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticGluing
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hglue

/--
Strict-boundary Perron theorem in Dirichlet form, using the
branch-local quadratic gluing version of the lower bump input.
-/
theorem PerronMethodExistenceTheorem.strictBoundary_of_localQuadraticBranchGluing
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
    (hbranch : PerronLowerEnvelopeLocalQuadraticBranchGluing C boundary F
      g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticBranchGluing
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow hbranch

end ViscositySolns
