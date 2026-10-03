/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.Definitions

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Perron bump interface bridges

Implications between the local and global Perron lower-envelope
bump interfaces.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
A continuous strict bump is in particular a lower-semicontinuous strict bump.
-/
theorem PerronLowerEnvelopeContinuousStrictSubsolutionPatchAt.pointwiseStrict
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n}
    (hpatch :
      PerronLowerEnvelopeContinuousStrictSubsolutionPatchAt C boundary F g B x) :
    PerronLowerEnvelopePointwiseStrictSubsolutionPatchAt C boundary F g B x := by
  rcases hpatch with ⟨w, hwCont, hWltw, hwsub, hlower⟩
  exact ⟨w, hwCont.lowerSemicontinuousWithinAt, hWltw, hwsub, hlower⟩

/--
A continuous Dirichlet bump gives continuous max-patch data after maxing with
the lower barrier.
-/
theorem DirichletBarrierPair.continuousMaxPatchAt_of_continuousBumpAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hbump : PerronLowerEnvelopeContinuousBumpAt C boundary F g B x) :
    PerronLowerEnvelopeContinuousMaxPatchAt C boundary F g B x := by
  rcases hbump with ⟨w, hwCont, hWltw, hwsub⟩
  exact ⟨w, hwCont, hWltw, B.lower_dirichlet.max hwsub⟩

/--
The local-germ max-patch formulation assembles the global continuous max-patch
datum.
-/
theorem DirichletBarrierPair.continuousMaxPatchAt_of_continuousLocalMaxPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hpatch : PerronLowerEnvelopeContinuousLocalMaxPatchAt C boundary F g B x) :
    PerronLowerEnvelopeContinuousMaxPatchAt C boundary F g B x := by
  rcases hpatch with ⟨w, hwCont, hWltw, hboundary, husc, hlocal⟩
  refine ⟨w, hwCont, hWltw, ?_⟩
  exact DirichletSubsolutionOn.of_locally_eventuallyEq hlocal hboundary husc

/--
Continuous max-patch data gives localized-improvement data. The lower-envelope
selection supplies points near the contact where `W` lies below an intermediate
level, while continuity of the raw bump keeps the patched max above that level.
-/
theorem DirichletBarrierPair.localizedImprovementAt_of_continuousMaxPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hne : (nhdsWithin x C).NeBot)
    (hupperBddAbove : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hpatch : PerronLowerEnvelopeContinuousMaxPatchAt C boundary F g B x) :
    PerronLowerEnvelopeLocalizedImprovementAt C boundary F g B x := by
  rcases hpatch with ⟨w, hwCont, hWltw, hmaxSub⟩
  rcases exists_between hWltw with ⟨a, hWlta, hawx⟩
  let W : Point n -> Real := perronEnvelope C boundary F g B.lower B.upper
  let : (nhdsWithin x C).NeBot := hne
  have hWcobdd : (nhdsWithin x C).IsCoboundedUnder (· >= ·) W :=
    B.perronEnvelope_isCoboundedUnder_ge hupperBddAbove
  have hfreqW : ∃ᶠ y in nhdsWithin x C, W y < a :=
    frequently_lowerEnvelope_lt hWcobdd hWlta
  have hwAbove : {y : Point n | a < w y} ∈ nhdsWithin x C :=
    lowerSemicontinuousWithinAt_iff.mp
      hwCont.lowerSemicontinuousWithinAt a hawx
  have hfreq : ∃ᶠ y in nhdsWithin x C,
      W y < Max.max (B.lower y) (w y) := by
    exact (hfreqW.and_eventually hwAbove).mono (by
      intro y hy
      exact hy.1.trans_le (hy.2.le.trans (le_max_right (B.lower y) (w y))))
  exact ⟨fun y => Max.max (B.lower y) (w y), hmaxSub,
    (fun y _hy => le_max_left (B.lower y) (w y)), hfreq⟩

/--
Pointwise lower-semicontinuous strict subsolution patch data gives localized
improvement data.
-/
theorem DirichletBarrierPair.localizedImprovementAt_of_pointwiseStrictSubsolutionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hne : (nhdsWithin x C).NeBot)
    (hupperBddAbove : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hpatch :
      PerronLowerEnvelopePointwiseStrictSubsolutionPatchAt C boundary F g B x) :
    PerronLowerEnvelopeLocalizedImprovementAt C boundary F g B x := by
  rcases hpatch with ⟨w, hwLsc, hWltw, hwsub, hlower⟩
  rcases exists_between hWltw with ⟨a, hWlta, hawx⟩
  let W : Point n -> Real := perronEnvelope C boundary F g B.lower B.upper
  let : (nhdsWithin x C).NeBot := hne
  have hWcobdd : (nhdsWithin x C).IsCoboundedUnder (· >= ·) W :=
    B.perronEnvelope_isCoboundedUnder_ge hupperBddAbove
  have hfreqW : ∃ᶠ y in nhdsWithin x C, W y < a :=
    frequently_lowerEnvelope_lt hWcobdd hWlta
  have hwAbove : {y : Point n | a < w y} ∈ nhdsWithin x C :=
    lowerSemicontinuousWithinAt_iff.mp hwLsc a hawx
  have hfreq : ∃ᶠ y in nhdsWithin x C, W y < w y := by
    exact (hfreqW.and_eventually hwAbove).mono (by
      intro y hy
      exact hy.1.trans hy.2)
  exact ⟨w, hwsub, hlower, hfreq⟩

/--
The neighborhood-form improvement is exactly strong enough to give the
frequent localized-improvement formulation used by the formal contradiction.
-/
theorem DirichletBarrierPair.localizedImprovementAt_of_neighborhoodImprovementAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (himprove :
      PerronLowerEnvelopeNeighborhoodImprovementAt C boundary F g B x) :
    PerronLowerEnvelopeLocalizedImprovementAt C boundary F g B x := by
  rcases himprove with ⟨w, hwsub, hlower, hnear⟩
  refine ⟨w, hwsub, hlower, ?_⟩
  rw [Filter.frequently_iff]
  intro V hV
  exact hnear V hV

/--
Branch-local max-patch data supplies the local-germ max-patch formulation.
-/
theorem DirichletBarrierPair.continuousLocalMaxPatchAt_of_branchMaxPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hpatch : PerronLowerEnvelopeContinuousBranchMaxPatchAt C boundary F g B x) :
    PerronLowerEnvelopeContinuousLocalMaxPatchAt C boundary F g B x := by
  rcases hpatch with ⟨w, hwCont, hWltw, hboundary, husc, hbranch⟩
  refine ⟨w, hwCont, hWltw, hboundary, husc, ?_⟩
  intro z hz
  rcases hbranch z hz with hLower | hOther
  · rcases hLower with ⟨hzEq, hzGerm⟩
    exact ⟨B.lower, B.lower_dirichlet.viscosity, hzEq, hzGerm⟩
  · exact hOther

/--
Active-branch max-patch data supplies the branch-local max-patch formulation.
-/
theorem DirichletBarrierPair.branchMaxPatchAt_of_activeMaxPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hpatch : PerronLowerEnvelopeContinuousActiveMaxPatchAt C boundary F g B x) :
    PerronLowerEnvelopeContinuousBranchMaxPatchAt C boundary F g B x := by
  rcases hpatch with ⟨w, hwCont, hWltw, hboundary, husc, hactive⟩
  refine ⟨w, hwCont, hWltw, hboundary, husc, ?_⟩
  intro z hz
  rcases hactive z hz with hLower | hUpper
  · rcases hLower with ⟨hzLe, hle⟩
    left
    refine ⟨?_, ?_⟩
    · exact max_eq_left hzLe
    · filter_upwards [hle] with y hy
      exact max_eq_left hy
  · rcases hUpper with ⟨v, hv, hzLe, hzw, hle, hwv⟩
    right
    refine ⟨v, hv, ?_, ?_⟩
    · simpa [max_eq_right hzLe] using hzw
    · filter_upwards [hle, hwv] with y hy hwy
      simpa [max_eq_right hy] using hwy

/--
Strict active-branch data implies active-branch data by weakening the strict
branch inequalities.
-/
theorem DirichletBarrierPair.activeMaxPatchAt_of_strictActiveMaxPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hpatch :
      PerronLowerEnvelopeContinuousStrictActiveMaxPatchAt C boundary F g B x) :
    PerronLowerEnvelopeContinuousActiveMaxPatchAt C boundary F g B x := by
  rcases hpatch with ⟨w, hwCont, hWltw, hboundary, husc, hstrict⟩
  refine ⟨w, hwCont, hWltw, hboundary, husc, ?_⟩
  intro z hz
  rcases hstrict z hz with hLower | hUpper
  · rcases hLower with ⟨hzlt, hlt⟩
    left
    refine ⟨le_of_lt hzlt, ?_⟩
    filter_upwards [hlt] with y hy
    exact le_of_lt hy
  · rcases hUpper with ⟨v, hv, hzlt, hzw, hlt, hwv⟩
    right
    refine ⟨v, hv, le_of_lt hzlt, hzw, ?_, hwv⟩
    filter_upwards [hlt] with y hy
    exact le_of_lt hy

/--
If the strict active bump is already a viscosity subsolution, it supplies the
strict active max-patch data by taking the bump itself as the upper active
local branch.
-/
theorem DirichletBarrierPair.strictActiveMaxPatchAt_of_strictActiveSubsolutionBumpAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hbump :
      PerronLowerEnvelopeContinuousStrictActiveSubsolutionBumpAt
        C boundary F g B x) :
    PerronLowerEnvelopeContinuousStrictActiveMaxPatchAt C boundary F g B x := by
  rcases hbump with ⟨w, hwCont, hWltw, hboundary, husc, hwsub, hactive⟩
  refine ⟨w, hwCont, hWltw, hboundary, husc, ?_⟩
  intro z hz
  rcases hactive z hz with hLower | hUpper
  · exact Or.inl hLower
  · rcases hUpper with ⟨hzlt, hlt⟩
    exact Or.inr ⟨w, hwsub, hzlt, rfl, hlt, Filter.EventuallyEq.rfl⟩

/--
A strict active Dirichlet bump supplies the strict active subsolution-bump
formulation. The max-patch boundary inequality is just the boundary part of
the maximum of the lower barrier with the raw bump.
-/
theorem DirichletBarrierPair.strictActiveSubsolutionBumpAt_of_strictActiveDirichletBumpAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hbump :
      PerronLowerEnvelopeContinuousStrictActiveDirichletBumpAt C boundary F g B x) :
    PerronLowerEnvelopeContinuousStrictActiveSubsolutionBumpAt
      C boundary F g B x := by
  rcases hbump with ⟨w, hwCont, hWltw, hwdir, hactive⟩
  refine ⟨w, hwCont, hWltw, ?_, (B.lower_dirichlet.max hwdir).upperSemicontinuousOn,
    hwdir.viscosity, hactive⟩
  exact (B.lower_dirichlet.max hwdir).boundary

/--
Continuous max-patch bump data gives the source-shaped strict subsolution
patch data.
-/
theorem DirichletBarrierPair.strictSubsolutionPatchAt_of_continuousMaxPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hpatch : PerronLowerEnvelopeContinuousMaxPatchAt C boundary F g B x) :
    PerronLowerEnvelopeStrictSubsolutionPatchAt C boundary F g B x := by
  rcases hpatch with ⟨w, hwCont, hWltw, hmaxSub⟩
  rcases exists_between hWltw with ⟨a, hWlta, hawx⟩
  have hV : {y : Point n | a < w y} ∈ nhdsWithin x C :=
    lowerSemicontinuousWithinAt_iff.mp
      hwCont.lowerSemicontinuousWithinAt a hawx
  refine ⟨a, {y : Point n | a < w y}, fun y => Max.max (B.lower y) (w y),
    hV, ?_, hWlta, hmaxSub, ?_⟩
  · intro y hy
    exact hy.trans_le (le_max_right (B.lower y) (w y))
  · intro y _hy
    exact le_max_left (B.lower y) (w y)

/--
Maxing a continuous Dirichlet bump with the lower barrier gives the
source-shaped strict subsolution patch data.
-/
theorem DirichletBarrierPair.strictSubsolutionPatchAt_of_continuousBumpAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hbump : PerronLowerEnvelopeContinuousBumpAt C boundary F g B x) :
    PerronLowerEnvelopeStrictSubsolutionPatchAt C boundary F g B x := by
  exact B.strictSubsolutionPatchAt_of_continuousMaxPatchAt
    (B.continuousMaxPatchAt_of_continuousBumpAt hbump)

/--
Lower semicontinuity upgrades pointwise strictness at the failed contact into
the neighborhood-strict patch data used by the Perron contradiction.
-/
theorem DirichletBarrierPair.strictSubsolutionPatchAt_of_pointwiseStrictSubsolutionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hpatch :
      PerronLowerEnvelopePointwiseStrictSubsolutionPatchAt C boundary F g B x) :
    PerronLowerEnvelopeStrictSubsolutionPatchAt C boundary F g B x := by
  rcases hpatch with ⟨w, hwLsc, hWltw, hwsub, hlower⟩
  rcases exists_between hWltw with ⟨a, hWlta, hawx⟩
  have hV : {y : Point n | a < w y} ∈ nhdsWithin x C :=
    lowerSemicontinuousWithinAt_iff.mp hwLsc a hawx
  exact ⟨a, {y : Point n | a < w y}, w, hV, (fun y hy => hy), hWlta,
    hwsub, hlower⟩

/--
Comparison with the upper barrier turns source-shaped strict subsolution patch
data into Perron-class strict patch data.
-/
theorem DirichletBarrierPair.strictPatchAt_of_strictSubsolutionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g) {x : Point n}
    (hpatch : PerronLowerEnvelopeStrictSubsolutionPatchAt C boundary F g B x) :
    PerronLowerEnvelopeStrictPatchAt C boundary F g B x := by
  rcases hpatch with ⟨a, V, w, hV, hwAbove, hWlower, hwsub, hlower⟩
  refine ⟨a, V, w, hV, hwAbove, hWlower, hwsub, hlower, ?_⟩
  intro y hy
  exact hcomparison hwsub B.upper_dirichlet y hy

end ViscositySolns
