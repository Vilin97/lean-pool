/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.Bridges

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Perron bump global bridge interfaces

Global implications between Perron lower-envelope bump interfaces.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Source-shaped strict subsolution patch data at every failed subjet
inequality.
-/
def PerronLowerEnvelopeStrictSubsolutionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeStrictSubsolutionPatchAt C boundary F g B x

/--
Pointwise strict subsolution patch data at every failed subjet inequality.
-/
def PerronLowerEnvelopePointwiseStrictSubsolutionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopePointwiseStrictSubsolutionPatchAt C boundary F g B x

/--
Continuous strict subsolution patch data at every failed subjet inequality.
-/
def PerronLowerEnvelopeContinuousStrictSubsolutionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeContinuousStrictSubsolutionPatchAt C boundary F g B x

/--
Continuous Dirichlet bump data at every failed subjet inequality.
-/
def PerronLowerEnvelopeContinuousBump
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeContinuousBumpAt C boundary F g B x

/--
Continuous max-patch bump data at every failed subjet inequality.
-/
def PerronLowerEnvelopeContinuousMaxPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeContinuousMaxPatchAt C boundary F g B x

/--
Continuous local max-patch data at every failed subjet inequality.
-/
def PerronLowerEnvelopeContinuousLocalMaxPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeContinuousLocalMaxPatchAt C boundary F g B x

/--
Branch-local continuous max-patch data at every failed subjet inequality.
-/
def PerronLowerEnvelopeContinuousBranchMaxPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeContinuousBranchMaxPatchAt C boundary F g B x

/--
Active-branch continuous max-patch data at every failed subjet inequality.
-/
def PerronLowerEnvelopeContinuousActiveMaxPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeContinuousActiveMaxPatchAt C boundary F g B x

/--
Strict active-branch continuous max-patch data at every failed subjet
inequality.
-/
def PerronLowerEnvelopeContinuousStrictActiveMaxPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeContinuousStrictActiveMaxPatchAt C boundary F g B x

/--
Strict active-branch subsolution bump data at every failed subjet inequality.
-/
def PerronLowerEnvelopeContinuousStrictActiveSubsolutionBump
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeContinuousStrictActiveSubsolutionBumpAt
          C boundary F g B x

/--
Strict active-branch Dirichlet bump data at every failed subjet inequality.
-/
def PerronLowerEnvelopeContinuousStrictActiveDirichletBump
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeContinuousStrictActiveDirichletBumpAt
          C boundary F g B x

/--
A continuous Dirichlet bump at every failed contact gives continuous max-patch
data at every failed contact.
-/
theorem DirichletBarrierPair.continuousMaxPatch_of_continuousBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hbump : PerronLowerEnvelopeContinuousBump C boundary F g B) :
    PerronLowerEnvelopeContinuousMaxPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact B.continuousMaxPatchAt_of_continuousBumpAt (hbump x hx J hJ hneg)

/--
The local-germ max-patch formulation implies the continuous max-patch
formulation.
-/
theorem DirichletBarrierPair.continuousMaxPatch_of_continuousLocalMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hpatch : PerronLowerEnvelopeContinuousLocalMaxPatch C boundary F g B) :
    PerronLowerEnvelopeContinuousMaxPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact B.continuousMaxPatchAt_of_continuousLocalMaxPatchAt
    (hpatch x hx J hJ hneg)

/--
The continuous max-patch formulation implies localized improvement at every
failed contact.
-/
theorem DirichletBarrierPair.localizedImprovement_of_continuousMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hne : ∀ x : Point n, x ∈ C -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hpatch : PerronLowerEnvelopeContinuousMaxPatch C boundary F g B) :
    PerronLowerEnvelopeLocalizedImprovement C boundary F g B := by
  intro x hx J hJ hneg
  exact B.localizedImprovementAt_of_continuousMaxPatchAt
    (hne x hx) (hupperBddAbove x hx) (hpatch x hx J hJ hneg)

/--
The pointwise-lower-semicontinuous strict patch formulation implies localized
improvement at every failed contact.
-/
theorem DirichletBarrierPair.localizedImprovement_of_pointwiseStrictSubsolutionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hne : ∀ x : Point n, x ∈ C -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hpatch : PerronLowerEnvelopePointwiseStrictSubsolutionPatch C boundary F g B) :
    PerronLowerEnvelopeLocalizedImprovement C boundary F g B := by
  intro x hx J hJ hneg
  exact B.localizedImprovementAt_of_pointwiseStrictSubsolutionPatchAt
    (hne x hx) (hupperBddAbove x hx) (hpatch x hx J hJ hneg)

/--
The neighborhood-form improvement implies the frequent localized-improvement
form at every failed contact.
-/
theorem DirichletBarrierPair.localizedImprovement_of_neighborhoodImprovement
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (himprove : PerronLowerEnvelopeNeighborhoodImprovement C boundary F g B) :
    PerronLowerEnvelopeLocalizedImprovement C boundary F g B := by
  intro x hx J hJ hneg
  exact B.localizedImprovementAt_of_neighborhoodImprovementAt
    (himprove x hx J hJ hneg)

/--
The branch-local max-patch formulation implies the local-germ max-patch
formulation.
-/
theorem DirichletBarrierPair.continuousLocalMaxPatch_of_branchMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hpatch : PerronLowerEnvelopeContinuousBranchMaxPatch C boundary F g B) :
    PerronLowerEnvelopeContinuousLocalMaxPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact B.continuousLocalMaxPatchAt_of_branchMaxPatchAt
    (hpatch x hx J hJ hneg)

/--
The active-branch max-patch formulation implies the branch-local max-patch
formulation.
-/
theorem DirichletBarrierPair.branchMaxPatch_of_activeMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hpatch : PerronLowerEnvelopeContinuousActiveMaxPatch C boundary F g B) :
    PerronLowerEnvelopeContinuousBranchMaxPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact B.branchMaxPatchAt_of_activeMaxPatchAt (hpatch x hx J hJ hneg)

/--
The strict active-branch formulation implies the active-branch formulation.
-/
theorem DirichletBarrierPair.activeMaxPatch_of_strictActiveMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hpatch : PerronLowerEnvelopeContinuousStrictActiveMaxPatch C boundary F g B) :
    PerronLowerEnvelopeContinuousActiveMaxPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact B.activeMaxPatchAt_of_strictActiveMaxPatchAt (hpatch x hx J hJ hneg)

/--
The strict active subsolution-bump formulation implies the strict active
max-patch formulation.
-/
theorem DirichletBarrierPair.strictActiveMaxPatch_of_strictActiveSubsolutionBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hbump :
      PerronLowerEnvelopeContinuousStrictActiveSubsolutionBump C boundary F g B) :
    PerronLowerEnvelopeContinuousStrictActiveMaxPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact B.strictActiveMaxPatchAt_of_strictActiveSubsolutionBumpAt
    (hbump x hx J hJ hneg)

/--
The strict active Dirichlet-bump formulation implies the strict active
subsolution-bump formulation.
-/
theorem DirichletBarrierPair.strictActiveSubsolutionBump_of_strictActiveDirichletBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hbump :
      PerronLowerEnvelopeContinuousStrictActiveDirichletBump C boundary F g B) :
    PerronLowerEnvelopeContinuousStrictActiveSubsolutionBump C boundary F g B := by
  intro x hx J hJ hneg
  exact B.strictActiveSubsolutionBumpAt_of_strictActiveDirichletBumpAt
    (hbump x hx J hJ hneg)

/--
Interior quadratic bump data supplies the strict active Dirichlet-bump
interface used by the Perron lower-envelope argument.
-/
theorem DirichletBarrierPair.strictActiveDirichletBump_of_interiorQuadraticBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hFell : DegenerateElliptic F)
    (hinterior : ∀ z : Point n, z ∈ C -> z ∈ interior C)
    (hbump : PerronLowerEnvelopeInteriorQuadraticBump C boundary F g B) :
    PerronLowerEnvelopeContinuousStrictActiveDirichletBump C boundary F g B := by
  intro x hx J hJ hneg
  rcases hbump x hx J hJ hneg with
    ⟨x0, r, p, X, hHerm, hineq, hWlt, hboundary, hactive⟩
  exact B.strictActiveDirichletBumpAt_of_interior_quadraticModel
    hFell hinterior hHerm hineq hWlt hboundary hactive

/--
The strict active-branch formulation implies the branch-local max-patch
formulation.
-/
theorem DirichletBarrierPair.branchMaxPatch_of_strictActiveMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hpatch : PerronLowerEnvelopeContinuousStrictActiveMaxPatch C boundary F g B) :
    PerronLowerEnvelopeContinuousBranchMaxPatch C boundary F g B :=
  B.branchMaxPatch_of_activeMaxPatch
    (B.activeMaxPatch_of_strictActiveMaxPatch hpatch)

/--
The active-branch max-patch formulation implies the local-germ max-patch
formulation.
-/
theorem DirichletBarrierPair.continuousLocalMaxPatch_of_activeMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hpatch : PerronLowerEnvelopeContinuousActiveMaxPatch C boundary F g B) :
    PerronLowerEnvelopeContinuousLocalMaxPatch C boundary F g B :=
  B.continuousLocalMaxPatch_of_branchMaxPatch
    (B.branchMaxPatch_of_activeMaxPatch hpatch)

/--
The branch-local max-patch formulation implies the continuous max-patch
formulation.
-/
theorem DirichletBarrierPair.continuousMaxPatch_of_branchMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hpatch : PerronLowerEnvelopeContinuousBranchMaxPatch C boundary F g B) :
    PerronLowerEnvelopeContinuousMaxPatch C boundary F g B :=
  B.continuousMaxPatch_of_continuousLocalMaxPatch
    (B.continuousLocalMaxPatch_of_branchMaxPatch hpatch)

/--
The continuous max-patch formulation implies the strict subsolution patch
formulation.
-/
theorem DirichletBarrierPair.strictSubsolutionPatch_of_continuousMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hpatch : PerronLowerEnvelopeContinuousMaxPatch C boundary F g B) :
    PerronLowerEnvelopeStrictSubsolutionPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact B.strictSubsolutionPatchAt_of_continuousMaxPatchAt (hpatch x hx J hJ hneg)

/--
The continuous Dirichlet bump formulation implies the strict subsolution patch
formulation by maxing each bump with the lower barrier.
-/
theorem DirichletBarrierPair.strictSubsolutionPatch_of_continuousBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hbump : PerronLowerEnvelopeContinuousBump C boundary F g B) :
    PerronLowerEnvelopeStrictSubsolutionPatch C boundary F g B := by
  exact B.strictSubsolutionPatch_of_continuousMaxPatch
    (B.continuousMaxPatch_of_continuousBump hbump)

/--
The continuous pointwise patch formulation implies the
lower-semicontinuous pointwise patch formulation.
-/
theorem PerronLowerEnvelopeContinuousStrictSubsolutionPatch.pointwiseStrict
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeContinuousStrictSubsolutionPatch C boundary F g B) :
    PerronLowerEnvelopePointwiseStrictSubsolutionPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).pointwiseStrict

/--
The pointwise-lower-semicontinuous patch formulation implies the
neighborhood-strict subsolution patch formulation.
-/
theorem DirichletBarrierPair.strictSubsolutionPatch_of_pointwiseStrictSubsolutionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hpatch :
      PerronLowerEnvelopePointwiseStrictSubsolutionPatch C boundary F g B) :
    PerronLowerEnvelopeStrictSubsolutionPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact B.strictSubsolutionPatchAt_of_pointwiseStrictSubsolutionPatchAt
    (hpatch x hx J hJ hneg)


end ViscositySolns
