/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Method.Core

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Perron-family assembly interfaces

Perron existence theorems using the canonical Perron-family upper side and
several lower bump interfaces.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/--
Perron's method with the upper side represented canonically by the Perron
family and the top filter.

This is the source-shaped assembly interface: comparison remains an explicit
`DirichletComparisonPrinciple`, the upper-envelope subsolution property comes
from supremum stability applied to the Perron family, and the lower-envelope
supersolution property comes from the strict bumped-subsolution form of the
Perron bump lemma.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_strictSubsolutionPatch
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
    (hpatch : PerronLowerEnvelopeStrictSubsolutionPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_strictSubsolutionPatch
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow hpatch).viscosity

/--
Perron's method with the canonical Perron-family upper side and the
pointwise-lower-semicontinuous form of the lower bump lemma.

This is the most local source-shaped interface in this file: the analytic bump
construction only has to produce a Dirichlet subsolution patch whose value at
the failed contact lies strictly above `W_*` and is lower semicontinuous there.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_pointwiseStrictSubsolutionPatch
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
    (hpatch : PerronLowerEnvelopePointwiseStrictSubsolutionPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_pointwiseStrictPatch
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow hpatch).viscosity

/--
Perron's method with the canonical Perron-family upper side and the continuous
pointwise form of the lower bump lemma.

This is the smooth-bump-facing assembly interface: the lower-side analytic
input may provide a continuous Dirichlet subsolution patch at the failed
contact, rather than an already-neighborhood-strict patch.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_continuousStrictPatch
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
    (hpatch : PerronLowerEnvelopeContinuousStrictSubsolutionPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_continuousStrictPatch
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow hpatch).viscosity

/--
Perron's method with the canonical Perron-family upper side and the continuous
Dirichlet-bump form of the lower bump lemma.

The analytic input only has to produce a continuous Dirichlet subsolution bump
strictly above `W_*` at each failed contact. The lower barrier is inserted by
the formal max-patching bridge in `Bump.lean`.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_continuousBump
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
    (hbump : PerronLowerEnvelopeContinuousBump C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_continuousBump
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow hbump).viscosity

/--
Perron's method with the canonical Perron-family upper side and the continuous
max-patch form of the lower bump lemma.

The remaining analytic input is now localized around the patched function:
for each failed contact, produce a continuous bump `w` strictly above `W_*`
such that `max lower w` is a Dirichlet subsolution.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_continuousMaxPatch
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
    (hpatch : PerronLowerEnvelopeContinuousMaxPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_continuousMaxPatch
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow hpatch).viscosity

/--
Perron's method with the canonical Perron-family upper side and the continuous
local max-patch form of the lower bump lemma.

This exposes the local gluing obligation for the patched function
`max lower w`: prove its boundary inequality and supply local subsolution
germs around each point of `C`.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_localMaxPatch
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
    (hpatch : PerronLowerEnvelopeContinuousLocalMaxPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_localMaxPatch
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow hpatch).viscosity

/--
Perron's method with the canonical Perron-family upper side and the
branch-local continuous max-patch form of the lower bump lemma.

This is a branchwise gluing interface: around each point the patched function
`max lower w` may be certified by the lower-barrier branch or by another
local viscosity-subsolution branch.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_branchMaxPatch
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
    (hpatch : PerronLowerEnvelopeContinuousBranchMaxPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_branchMaxPatch
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow hpatch).viscosity

/--
Perron's method with the canonical Perron-family upper side and the
active-branch continuous max-patch form of the lower bump lemma.

This exposes the usual local max-gluing inequalities: near each point, either
the lower barrier dominates the bump or the bump branch dominates and agrees
with a local subsolution representative.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_activeMaxPatch
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
    (hpatch : PerronLowerEnvelopeContinuousActiveMaxPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_activeMaxPatch
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow hpatch).viscosity

/--
Perron's method with the canonical Perron-family upper side and the strict
active-branch continuous max-patch form of the lower bump lemma.

This is a strict branch-separation gluing interface: near each point, either
the bump is strictly below the lower barrier, or it is strictly above and
agrees with a local subsolution branch.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_strictActivePatch
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
    (hpatch : PerronLowerEnvelopeContinuousStrictActiveMaxPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_strictActivePatch
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow hpatch).viscosity

/--
Perron's method with the canonical Perron-family upper side and the strict
active subsolution-bump form of the lower bump lemma.

In this interface the raw bump is already a viscosity subsolution, so the
upper active branch of `max lower bump` uses the bump itself as its local
subsolution representative.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_strictActiveSubsolutionBump
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
    (hbump :
      PerronLowerEnvelopeContinuousStrictActiveSubsolutionBump C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_strictActiveBump
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow hbump).viscosity

/--
Perron's method with the canonical Perron-family upper side and the strict
active Dirichlet-bump form of the lower bump lemma.

Here the raw bump is a Dirichlet subsolution. The only max-gluing input left
is strict branch separation between the bump and the lower barrier.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_strictActiveDirichletBump
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
    (hbump :
      PerronLowerEnvelopeContinuousStrictActiveDirichletBump C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_strictActiveDirichletBump
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow hbump).viscosity

/--
Perron's method with the canonical Perron-family upper side and source-shaped
interior quadratic bump data for the lower side.

This is the quadratic-bump version of the lower Lemma 4.2 interface: each
failed lower-envelope subjet inequality supplies a certified quadratic bump,
and the Perron assembly turns that into existence using only the abstract
comparison principle.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_interiorQuadraticBump
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hinterior : ∀ z : Point n, z ∈ C -> z ∈ interior C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hbump : PerronLowerEnvelopeInteriorQuadraticBump C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_strictActiveDirichletBump
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (B.strictActiveDirichletBump_of_interiorQuadraticBump hFell hinterior hbump)


end ViscositySolns
