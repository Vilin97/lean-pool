/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.Contradiction

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Perron bump supersolution consequences

Conversion from lower-envelope contradiction interfaces to lower-envelope
subjet inequalities and Dirichlet supersolution conclusions.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The bump contradiction supplies the lower Perron envelope subjet inequality.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_subjetInequality_of_bumpContradiction
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hbump : PerronLowerEnvelopeBumpContradiction C boundary F g B) :
    PerronLowerEnvelopeSubjetInequality C boundary F g B := by
  intro x hx J hJ
  by_contra hnot
  rcases hbump x hx J hJ (lt_of_not_ge hnot) with ⟨y, hy, w, hw, hlt⟩
  exact B.not_perronEnvelope_lt_perronClass hw hy hlt

/--
The lower Perron envelope is a viscosity supersolution once the bump argument
has supplied the subjet inequality.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_viscositySupersolution_of_subjetInequality
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hperronBddBelow : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hperronCobddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsCoboundedUnder (· >= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hineq : PerronLowerEnvelopeSubjetInequality C boundary F g B) :
    ViscositySupersolution C F
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  ⟨lowerSemicontinuousOn_lowerEnvelope hperronBddBelow hperronCobddAbove, hineq⟩

/--
Barrier-local-bounded version of the lower-envelope supersolution criterion.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_viscositySupersolution_of_bumpInequality
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hne : ∀ x : Point n, x ∈ C -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hineq : PerronLowerEnvelopeSubjetInequality C boundary F g B) :
    ViscositySupersolution C F
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine B.perronLowerEnvelope_viscositySupersolution_of_subjetInequality ?_ ?_ hineq
  · intro x hx
    exact B.perronEnvelope_isBoundedUnder_ge (hlowerBddBelow x hx)
  · intro x hx
    let : (nhdsWithin x C).NeBot := hne x hx
    exact B.perronEnvelope_isCoboundedUnder_ge (hupperBddAbove x hx)

/--
Dirichlet lower-envelope supersolution criterion after boundary trace
inheritance.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_bumpInequality
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hineq : PerronLowerEnvelopeSubjetInequality C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine ⟨?_, B.perronLowerEnvelope_boundarySupersolution hlowerTrace ?_ ?_, ?_⟩
  · refine B.perronLowerEnvelope_viscositySupersolution_of_bumpInequality
      ?_ ?_ ?_ hineq
    · intro x hx
      exact hne x (Or.inl hx)
    · intro x hx
      exact hupperBddAbove x (Or.inl hx)
    · intro x hx
      exact hlowerBddBelow x (Or.inl hx)
  · intro x hx
    exact hlowerBddBelow x (Or.inr hx)
  · intro x hx
    let : (nhdsWithin x C).NeBot := hne x (Or.inr hx)
    exact B.perronEnvelope_isCoboundedUnder_ge (hupperBddAbove x (Or.inr hx))
  · exact B.perronLowerEnvelope_lowerSemicontinuousOn hne
      hupperBddAbove hlowerBddBelow

/--
Dirichlet lower-envelope supersolution from the formal bump contradiction.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_bumpContradiction
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hbump : PerronLowerEnvelopeBumpContradiction C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_bumpInequality hlowerTrace hne
    hupperBddAbove hlowerBddBelow
    (B.perronLowerEnvelope_subjetInequality_of_bumpContradiction hbump)

/--
Dirichlet lower-envelope supersolution from the source-shaped strict patch
form of the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_strictPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeStrictPatch C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_bumpContradiction hlowerTrace hne
    hupperBddAbove hlowerBddBelow
    (B.perronLowerEnvelope_bumpContradiction_of_strictPatch
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      hpatch)

/--
Dirichlet lower-envelope supersolution from the localized-improvement form of
the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_localizedImprovement
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (himprove : PerronLowerEnvelopeLocalizedImprovement C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_bumpContradiction hlowerTrace hne
    hupperBddAbove hlowerBddBelow
    (B.perronLowerEnvelope_bumpContradiction_of_localizedImprovement
      hcomparison himprove)

/--
Dirichlet lower-envelope supersolution from the neighborhood-form localized
improvement version of the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_neighborhoodImprovement
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (himprove : PerronLowerEnvelopeNeighborhoodImprovement C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_localizedImprovement
    hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow
    (B.localizedImprovement_of_neighborhoodImprovement himprove)

/--
Dirichlet lower-envelope supersolution from the source-shaped strict
subsolution patch form of the Perron bump lemma.

The analytic bump construction only has to produce a Dirichlet subsolution
patch above the lower barrier. The comparison principle supplies the missing
upper-barrier bound needed to place the patch in the Perron class.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_strictSubsolutionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeStrictSubsolutionPatch C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_strictPatch hlowerTrace hne
    hupperBddAbove hlowerBddBelow
    (B.strictPatch_of_strictSubsolutionPatch hcomparison hpatch)

/--
Dirichlet lower-envelope supersolution from the pointwise-lower-semicontinuous
form of the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_pointwiseStrictPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopePointwiseStrictSubsolutionPatch C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_strictSubsolutionPatch hcomparison
    hlowerTrace hne hupperBddAbove hlowerBddBelow
    (B.strictSubsolutionPatch_of_pointwiseStrictSubsolutionPatch hpatch)

/--
Dirichlet lower-envelope supersolution from the continuous pointwise form of
the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_continuousStrictPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeContinuousStrictSubsolutionPatch C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_pointwiseStrictPatch hcomparison
    hlowerTrace hne hupperBddAbove hlowerBddBelow hpatch.pointwiseStrict

/--
Dirichlet lower-envelope supersolution from the continuous Dirichlet bump form
of the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_continuousBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hbump : PerronLowerEnvelopeContinuousBump C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_strictSubsolutionPatch hcomparison
    hlowerTrace hne hupperBddAbove hlowerBddBelow
    (B.strictSubsolutionPatch_of_continuousBump hbump)

/--
Dirichlet lower-envelope supersolution from the continuous max-patch form of
the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_continuousMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeContinuousMaxPatch C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_strictSubsolutionPatch hcomparison
    hlowerTrace hne hupperBddAbove hlowerBddBelow
    (B.strictSubsolutionPatch_of_continuousMaxPatch hpatch)

/--
Dirichlet lower-envelope supersolution from the continuous local max-patch
form of the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_localMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeContinuousLocalMaxPatch C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_continuousMaxPatch hcomparison
    hlowerTrace hne hupperBddAbove hlowerBddBelow
    (B.continuousMaxPatch_of_continuousLocalMaxPatch hpatch)

/--
Dirichlet lower-envelope supersolution from the branch-local continuous
max-patch form of the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_branchMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeContinuousBranchMaxPatch C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_localMaxPatch hcomparison
    hlowerTrace hne hupperBddAbove hlowerBddBelow
    (B.continuousLocalMaxPatch_of_branchMaxPatch hpatch)

/--
Dirichlet lower-envelope supersolution from the active-branch continuous
max-patch form of the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_activeMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeContinuousActiveMaxPatch C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_branchMaxPatch hcomparison
    hlowerTrace hne hupperBddAbove hlowerBddBelow
    (B.branchMaxPatch_of_activeMaxPatch hpatch)

/--
Dirichlet lower-envelope supersolution from the strict active-branch
continuous max-patch form of the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_strictActivePatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeContinuousStrictActiveMaxPatch C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_activeMaxPatch hcomparison
    hlowerTrace hne hupperBddAbove hlowerBddBelow
    (B.activeMaxPatch_of_strictActiveMaxPatch hpatch)

/--
Dirichlet lower-envelope supersolution from the strict active subsolution-bump
form of the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_strictActiveBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hbump :
      PerronLowerEnvelopeContinuousStrictActiveSubsolutionBump C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_strictActivePatch hcomparison
    hlowerTrace hne hupperBddAbove hlowerBddBelow
    (B.strictActiveMaxPatch_of_strictActiveSubsolutionBump hbump)

/--
Dirichlet lower-envelope supersolution from the strict active Dirichlet-bump
form of the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_strictActiveDirichletBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hbump :
      PerronLowerEnvelopeContinuousStrictActiveDirichletBump C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_strictActiveBump hcomparison
    hlowerTrace hne hupperBddAbove hlowerBddBelow
    (B.strictActiveSubsolutionBump_of_strictActiveDirichletBump hbump)

/--
Dirichlet lower-envelope supersolution from source-shaped interior quadratic
bump data.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_interiorQuadraticBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F)
    (hinterior : ∀ z : Point n, z ∈ C -> z ∈ interior C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hbump : PerronLowerEnvelopeInteriorQuadraticBump C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_strictActiveDirichletBump
    hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow
    (B.strictActiveDirichletBump_of_interiorQuadraticBump hFell hinterior hbump)

/--
Dirichlet lower-envelope supersolution from a max-patch localized bump
construction.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_maxPatchBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hbump : PerronLowerEnvelopeMaxPatchBump C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_bumpContradiction hlowerTrace hne
    hupperBddAbove hlowerBddBelow
    (B.perronLowerEnvelope_bumpContradiction_of_maxPatchBump hbump)


end ViscositySolns
