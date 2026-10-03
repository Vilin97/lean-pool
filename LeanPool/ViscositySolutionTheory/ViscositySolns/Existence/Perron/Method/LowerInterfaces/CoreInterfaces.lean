/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OpenBumpMaxPatches
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OpenBumpPatches
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Method.PerronFamily

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Perron-family lower conclusion interfaces (CoreInterfaces)

Part of the Perron existence development using the canonical Perron-family
upper side and lower-side conclusions from the bump argument. Split from
`LowerInterfaces.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/--
With the canonical Perron-family upper side, the upper envelope is admissible
and therefore equals the pointwise Perron envelope on the PDE domain.

This is the maximality step used in the source proof before the lower bump is
applied directly to `W`.
-/
theorem PerronMethodExistenceTheorem.perronFamily_top_upperEnvelope_eqOn_domain
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
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    Set.EqOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
      (perronEnvelope C boundary F g B.lower B.upper) C := by
  have hupperVisc : ViscositySubsolution C F
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
    B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  have hupperDir : DirichletSubsolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
    refine ⟨hupperVisc, ?_, B.perronUpperEnvelope_upperSemicontinuousOn hne
      hupperBddAbove hlowerBddBelow⟩
    exact B.perronUpperEnvelope_boundarySubsolution hupperTrace
      (fun x hx => by
        let : (nhdsWithin x C).NeBot := hne x (Or.inr hx)
        exact B.perronEnvelope_isCoboundedUnder_le
          (hlowerBddBelow x (Or.inr hx)))
      (fun x hx => hupperBddAbove x (Or.inr hx))
  exact B.upperEnvelope_perronEnvelope_eqOn_domain hcomparison hupperDir
    hlowerTrace hne hupperBddAbove hlowerBddBelow

/--
Perron's method with the canonical Perron-family upper side and a supplied
lower-envelope viscosity supersolution property.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_lowerViscosity
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hlowerVisc : ViscositySupersolution C F
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ hlowerVisc hlowerTrace hupperTrace
    hne hupperBddAbove hlowerBddBelow
  exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
    (fun x hx => hne x (Or.inl hx))
    (fun x hx => hupperBddAbove x (Or.inl hx))
    (fun x hx => hlowerBddBelow x (Or.inl hx))

/--
Perron's method with the canonical Perron-family upper side and the lower
subjet inequality supplied by the bump argument.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bumpInequality
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
    (hineq : PerronLowerEnvelopeSubjetInequality C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_perronFamily_top_and_lowerViscosity
    B hcomparison hF ?_ hlowerTrace hupperTrace
    hne hupperBddAbove hlowerBddBelow
  exact B.perronLowerEnvelope_viscositySupersolution_of_bumpInequality
    (fun x hx => hne x (Or.inl hx))
    (fun x hx => hupperBddAbove x (Or.inl hx))
    (fun x hx => hlowerBddBelow x (Or.inl hx))
    hineq

/--
Perron's method with the canonical Perron-family upper side and the formal bump
contradiction as the lower-side input.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bumpContradiction
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
    (hbump : PerronLowerEnvelopeBumpContradiction C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_bumpInequality
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (B.perronLowerEnvelope_subjetInequality_of_bumpContradiction hbump)

/--
Perron's method with the canonical Perron-family upper side and the localized
improvement form of the lower bump lemma.

This is close to the payload of CIL Lemma 4.2: every failed lower-envelope
subjet inequality produces a Dirichlet subsolution above the lower barrier
that beats the Perron envelope at points arbitrarily near the failed contact.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_localizedImprovement
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
    (himprove : PerronLowerEnvelopeLocalizedImprovement C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_localizedImprovement
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow himprove).viscosity

/--
Perron's method with the canonical Perron-family upper side and a direct
localized improvement over `W^*`.

The method layer first proves the source-proof maximality identity
`W^* = W` on `C`, then converts the direct improvement into the ordinary
Perron localized-improvement interface.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_upperEnvelopeLocalizedImprovement
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
    (himprove : PerronUpperEnvelopeLocalizedImprovement C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  have hEq :
      Set.EqOn
        (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
        (perronEnvelope C boundary F g B.lower B.upper) C :=
    PerronMethodExistenceTheorem.perronFamily_top_upperEnvelope_eqOn_domain
      B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_localizedImprovement
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (himprove.lowerEnvelopeLocalizedImprovement hEq)

/--
For the canonical Perron-family upper side, source-style strict patch data
supplies direct localized improvement over `W^*`.

The method layer first recovers the source maximality identity `W^* = W` on the
domain, and the bump layer then transfers the strict patch improvement from `W`
to `W^*`.
-/
theorem PerronMethodExistenceTheorem.upperEnvelopeLocalizedImprovement_of_strictPatch
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
    (hpatch : PerronLowerEnvelopeStrictPatch C boundary F g B) :
    PerronUpperEnvelopeLocalizedImprovement C boundary F g B := by
  have hEq :
      Set.EqOn
        (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
        (perronEnvelope C boundary F g B.lower B.upper) C :=
    PerronMethodExistenceTheorem.perronFamily_top_upperEnvelope_eqOn_domain
      B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  exact B.upperEnvelopeLocalizedImprovement_of_strictPatch
    (fun x hx => hne x (Or.inl hx))
    (fun x hx => hupperBddAbove x (Or.inl hx))
    hEq hpatch

namespace PerronMethodExistenceTheorem

/--
For the canonical Perron-family upper side, source outer-annulus lower-envelope
data supplies direct localized improvement over `W^*`.

This instantiates the direct bump bridge with `old = W^*`: upper stability and
comparison make `W^*` admissible, maximality gives `W^* = W` on `C`, and the
source annulus estimate patches over `W^*` without selecting Perron-family
branches.
-/
theorem upperEnvelopeLocalizedImprovement_of_sourceOuterClosedBallLowerEnvelope
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
    PerronUpperEnvelopeLocalizedImprovement C boundary F g B := by
  let W : Point n -> Real := perronEnvelope C boundary F g B.lower B.upper
  let old : Point n -> Real := upperEnvelope C W
  have hupperVisc : ViscositySubsolution C F old := by
    dsimp [old, W]
    exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  have hupperDir : DirichletSubsolutionOn C boundary F g old := by
    refine ⟨hupperVisc, ?_, B.perronUpperEnvelope_upperSemicontinuousOn hne
      hupperBddAbove hlowerBddBelow⟩
    dsimp [old, W]
    exact B.perronUpperEnvelope_boundarySubsolution hupperTrace
      (fun x hx => by
        let : (nhdsWithin x C).NeBot := hne x (Or.inr hx)
        exact B.perronEnvelope_isCoboundedUnder_le
          (hlowerBddBelow x (Or.inr hx)))
      (fun x hx => hupperBddAbove x (Or.inr hx))
  have hold : PerronClass C boundary F g B.lower B.upper old := by
    dsimp [old, W]
    exact B.upperEnvelope_perronEnvelope_mem_perronClass hcomparison
      hupperDir hlowerTrace hne hupperBddAbove hlowerBddBelow
  have hEq : Set.EqOn old W C := by
    dsimp [old, W]
    exact B.upperEnvelope_perronEnvelope_eqOn_domain hcomparison
      hupperDir hlowerTrace hne hupperBddAbove hlowerBddBelow
  have hstrict : PerronLowerEnvelopeStrictPatch C boundary F g B :=
    hpatch.strictPatch_of_old_eq_perronEnvelope
      old hold hEq hcomparison hFell hFinv hCopen hlowerBddBelow
  exact upperEnvelopeLocalizedImprovement_of_strictPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    hstrict

/--
Legacy source outer-annulus lower-envelope data still supplies the direct
localized improvement after forgetting the branch lower-semicontinuity field.
-/
theorem upperEnvelopeLocalizedImprovement_of_sourceOuterClosedBallLowerEnvelopeLscSelection
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
    PerronUpperEnvelopeLocalizedImprovement C boundary F g B :=
  upperEnvelopeLocalizedImprovement_of_sourceOuterClosedBallLowerEnvelope
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.lowerEnvelopePatch

end PerronMethodExistenceTheorem

/--
Perron's method with the canonical Perron-family upper side and the
neighborhood-form localized improvement input.

This exposes the source-document formulation directly: every failed contact
has an improved Dirichlet subsolution that beats the Perron envelope in every
relative neighborhood of that contact.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_neighborhoodImprovement
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
    (himprove : PerronLowerEnvelopeNeighborhoodImprovement C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_neighborhoodImprovement
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow himprove).viscosity

/--
Perron's method with the canonical Perron-family upper side and the
source-shaped strict patch form of the lower bump lemma.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_strictPatch
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
    (hpatch : PerronLowerEnvelopeStrictPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_upperEnvelopeLocalizedImprovement
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (PerronMethodExistenceTheorem.upperEnvelopeLocalizedImprovement_of_strictPatch
      B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
      hpatch)

/--
Perron's method with the canonical Perron-family upper side and the max-patch
form of the lower bump construction.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_maxPatchBump
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
    (hbump : PerronLowerEnvelopeMaxPatchBump C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_bumpContradiction
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (B.perronLowerEnvelope_bumpContradiction_of_maxPatchBump hbump)

/--
Perron's method with the canonical Perron-family upper side and the strict
local-patch form of the lower bump construction.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_strictLocalPatch
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
    (hpatch : PerronLowerEnvelopeStrictLocalPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_maxPatchBump
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (B.perronLowerEnvelope_maxPatchBump_of_strictLocalPatch
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      hpatch)

/--
Perron's method with the canonical Perron-family upper side and the
source-shaped local quadratic max-patch form of the lower bump construction.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticMaxPatch
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
    (hpatch : PerronLowerEnvelopeLocalQuadraticMaxPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_strictLocalPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    hpatch.strictLocalPatch

/--
Perron's method with the canonical Perron-family upper side and the
local-germ quadratic gluing form of the lower bump construction.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticGluing
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
    (hglue : PerronLowerEnvelopeLocalQuadraticGluing C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticMaxPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    hglue.localQuadraticMaxPatch

/--
Perron's method with the canonical Perron-family upper side and the
branch-local quadratic gluing form of the lower bump construction.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticBranchGluing
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
    (hbranch : PerronLowerEnvelopeLocalQuadraticBranchGluing C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticGluing
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    hbranch.localQuadraticGluing

/--
Perron's method with the canonical Perron-family upper side, where operator
continuity supplies the lifted quadratic and the remaining input is the
explicit patch-selection step.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticPatchSelection
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
    (hselect : PerronLowerEnvelopeLocalQuadraticPatchSelection C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticBranchGluing
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hF.perronLowerEnvelope_branchGluing_of_patchSelection hselect)

/--
Perron's method with the canonical Perron-family upper side, where operator
continuity supplies the lifted quadratic and the remaining input is
compact-inactive local max-patch data.

This endpoint permits the active quadratic branch to be certified only on
local domains, which is the natural form produced by a localized bump.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticCompactInactivePatch
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
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactivePatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticMaxPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hF.perronLowerEnvelope_localQuadraticMaxPatch_of_compactInactivePatch hpatch)

/--
Perron's method with the canonical Perron-family upper side, where operator
continuity supplies the lifted quadratic, finite inactive selection supplies
the old branch, and comparison with the upper barrier supplies the global
upper bound for the patched subsolution.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveSubsolution
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
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSubsolutionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticMaxPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hF.perronLowerEnvelope_localQuadraticMaxPatch_of_compactInactiveSubsolution
      hcomparison hpatch)

/--
Perron's method with the canonical Perron-family upper side, where the active
compact-inactive patch input only has to certify the lifted quadratic itself
as a local subsolution on relative-open domains.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveQuadratic
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
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveSubsolution
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    hpatch.subsolutionPatch

/--
Perron's method with the canonical Perron-family upper side, where the active
compact-inactive input supplies only certified local domains for the lifted
quadratic. Degenerate ellipticity and Hessian-symmetric invariance certify the
quadratic active branch as a viscosity subsolution on those domains.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveCertified
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveCertifiedPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveQuadratic
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hpatch.quadraticPatch hFell hFinv)

/--
Perron's method with the canonical Perron-family upper side, using
symmetrized certified active-domain compact-inactive data. This removes the
need for failed subjet Hessians to be supplied as Hermitian.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveSymCertified
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSymCertifiedPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveQuadratic
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hpatch.quadraticPatch hFell hFinv)

/--
Perron's method with the canonical Perron-family upper side, using
boundary-safe compact-inactive data. The caller only proves the boundary
subsolution inequality for the lifted quadratic; the max patch inherits it
from the old Perron branch.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveBoundary
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveBoundaryPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveSymCertified
    B hcomparison hF hFell hFinv hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.symCertifiedPatch

/--
Perron's method with the canonical Perron-family upper side, using
boundary-covered compact-inactive data. Covering the boundary by the inactive
compact set lets finite Perron selection make the old branch dominate there, so
no separate boundary inequality is required for the quadratic branch.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveCovered
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveCoveredPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticMaxPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hF.perronLowerEnvelope_localQuadraticMaxPatch_of_compactInactiveCovered
      hcomparison hFell hFinv hpatch)

/--
Perron's method with the canonical Perron-family upper side, using exterior
compact-inactive data. The active quadratic neighborhood is kept away from the
Dirichlet boundary, so the inactive compact covers the exterior in
`C ∪ boundary` and hence supplies the boundary-covered datum.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveExterior
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveExteriorPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveCovered
    B hcomparison hF hFell hFinv hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.coveredPatch

/--
Perron's method with the canonical Perron-family upper side, using
lower-barrier exterior compact-inactive data. On the inactive compact the
lifted quadratic is locally below the lower barrier, which is already a
Perron-family member.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_barrierExterior
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticBarrierExteriorPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_compactInactiveExterior
    B hcomparison hF hFell hFinv hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.exteriorPatch

/--
Perron's method with the canonical Perron-family upper side, using the
open-active lower-barrier exterior patch input.

Operator continuity supplies an open active strict-negativity neighborhood;
when `C` is open, the active local domain is `C ∩ V`. The remaining exterior
annulus data is stated only for open active neighborhoods.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_openBarrierExterior
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
      PerronLowerEnvelopeLocalQuadraticOpenBarrierExteriorPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_localQuadraticMaxPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hF.perronLowerEnvelope_localQuadraticMaxPatch_of_openBarrierExterior
      hcomparison hFell hFinv hCopen hpatch)

end ViscositySolns
