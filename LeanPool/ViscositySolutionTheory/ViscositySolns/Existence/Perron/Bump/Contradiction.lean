/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.GlobalBridges

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Perron bump contradiction

Conversion from bump interfaces to the lower-envelope contradiction, subjet
inequality, and supersolution conclusion.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Strict patch data implies the formal bump contradiction at the same failed
contact point.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_bumpContradictionAt_of_strictPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hne : (nhdsWithin x C).NeBot)
    (hupperBddAbove : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hpatch : PerronLowerEnvelopeStrictPatchAt C boundary F g B x) :
    ∃ y : Point n, y ∈ C ∪ boundary ∧ ∃ w : Point n -> Real,
      PerronClass C boundary F g B.lower B.upper w ∧
        perronEnvelope C boundary F g B.lower B.upper y < w y := by
  let W : Point n -> Real := perronEnvelope C boundary F g B.lower B.upper
  rcases hpatch with ⟨a, V, w, hV, hwAbove, hWlower, hw⟩
  let : (nhdsWithin x C).NeBot := hne
  have hWcobdd : (nhdsWithin x C).IsCoboundedUnder (· >= ·) W :=
    B.perronEnvelope_isCoboundedUnder_ge hupperBddAbove
  have hVC : V ∩ C ∈ nhdsWithin x C := Filter.inter_mem hV self_mem_nhdsWithin
  rcases exists_mem_nhdsWithin_lowerEnvelope_lt (u := W) hWcobdd hWlower hVC
    with ⟨y, hyVC, hWy⟩
  exact ⟨y, Or.inl hyVC.2, w, hw, hWy.trans (hwAbove y hyVC.1)⟩

/--
Strict patch data gives the neighborhood-form localized improvement at the
same failed contact point.

Given any relative neighborhood of the contact, intersect it with the patch
neighborhood and the domain. The lower-envelope selection lemma finds a point
there where `W` is below the strict level, while the patch is above that level.
-/
theorem DirichletBarrierPair.neighborhoodImprovementAt_of_strictPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hne : (nhdsWithin x C).NeBot)
    (hupperBddAbove : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hpatch : PerronLowerEnvelopeStrictPatchAt C boundary F g B x) :
    PerronLowerEnvelopeNeighborhoodImprovementAt C boundary F g B x := by
  let W : Point n -> Real := perronEnvelope C boundary F g B.lower B.upper
  rcases hpatch with ⟨a, V, w, hV, hwAbove, hWlower, hw⟩
  refine ⟨w, hw.dirichletSubsolution, ?_, ?_⟩
  · intro y hy
    exact hw.lower_le hy
  · intro U hU
    let : (nhdsWithin x C).NeBot := hne
    have hWcobdd : (nhdsWithin x C).IsCoboundedUnder (· >= ·) W :=
      B.perronEnvelope_isCoboundedUnder_ge hupperBddAbove
    have hUVC : (U ∩ V) ∩ C ∈ nhdsWithin x C :=
      Filter.inter_mem (Filter.inter_mem hU hV) self_mem_nhdsWithin
    rcases exists_mem_nhdsWithin_lowerEnvelope_lt (u := W) hWcobdd hWlower hUVC
      with ⟨y, hyUVC, hWy⟩
    exact ⟨y, hyUVC.1.1, hWy.trans (hwAbove y hyUVC.1.2)⟩

/--
Strict patch data at every failed subjet inequality.
-/
def PerronLowerEnvelopeStrictPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeStrictPatchAt C boundary F g B x

/--
Comparison turns source-shaped strict subsolution patch data into strict patch
data for Perron's contradiction.
-/
theorem DirichletBarrierPair.strictPatch_of_strictSubsolutionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hpatch : PerronLowerEnvelopeStrictSubsolutionPatch C boundary F g B) :
    PerronLowerEnvelopeStrictPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact B.strictPatchAt_of_strictSubsolutionPatchAt hcomparison
    (hpatch x hx J hJ hneg)

/--
The source-shaped strict patch formulation gives the formal bump
contradiction.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_bumpContradiction_of_strictPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hne : ∀ x : Point n, x ∈ C -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hpatch : PerronLowerEnvelopeStrictPatch C boundary F g B) :
    PerronLowerEnvelopeBumpContradiction C boundary F g B := by
  intro x hx J hJ hneg
  exact B.perronLowerEnvelope_bumpContradictionAt_of_strictPatchAt
    (hne x hx) (hupperBddAbove x hx) (hpatch x hx J hJ hneg)

/--
Strict patch data at every failed contact supplies the neighborhood-form
localized improvement.
-/
theorem DirichletBarrierPair.neighborhoodImprovement_of_strictPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hne : ∀ x : Point n, x ∈ C -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hpatch : PerronLowerEnvelopeStrictPatch C boundary F g B) :
    PerronLowerEnvelopeNeighborhoodImprovement C boundary F g B := by
  intro x hx J hJ hneg
  exact B.neighborhoodImprovementAt_of_strictPatchAt
    (hne x hx) (hupperBddAbove x hx) (hpatch x hx J hJ hneg)

/--
Strict patch data gives a direct localized improvement over `W^*` once
`W^* = W` on the domain.
-/
theorem DirichletBarrierPair.upperEnvelopeLocalizedImprovementAt_of_strictPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hne : (nhdsWithin x C).NeBot)
    (hupperBddAbove : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hEq : Set.EqOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
      (perronEnvelope C boundary F g B.lower B.upper) C)
    (hpatch : PerronLowerEnvelopeStrictPatchAt C boundary F g B x) :
    PerronUpperEnvelopeLocalizedImprovementAt C boundary F g B x := by
  let W : Point n -> Real := perronEnvelope C boundary F g B.lower B.upper
  rcases hpatch with ⟨a, V, w, hV, hwAbove, hWlower, hw⟩
  let : (nhdsWithin x C).NeBot := hne
  have hWcobdd : (nhdsWithin x C).IsCoboundedUnder (· >= ·) W :=
    B.perronEnvelope_isCoboundedUnder_ge hupperBddAbove
  refine ⟨w, hw.dirichletSubsolution, ?_, ?_⟩
  · intro y hy
    exact hw.lower_le hy
  · exact ((frequently_lowerEnvelope_lt hWcobdd hWlower).and_eventually
      (Filter.inter_mem hV self_mem_nhdsWithin)).mono (by
        intro y hy
        have hWy : W y < a := hy.1
        have hyV : y ∈ V := hy.2.1
        have hyC : y ∈ C := hy.2.2
        simpa [W, hEq hyC] using hWy.trans (hwAbove y hyV))

/--
Global strict patch data gives direct localized improvement over `W^*` once
`W^* = W` on the domain.
-/
theorem DirichletBarrierPair.upperEnvelopeLocalizedImprovement_of_strictPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hne : ∀ x : Point n, x ∈ C -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hEq : Set.EqOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
      (perronEnvelope C boundary F g B.lower B.upper) C)
    (hpatch : PerronLowerEnvelopeStrictPatch C boundary F g B) :
    PerronUpperEnvelopeLocalizedImprovement C boundary F g B := by
  intro x hx J hJ hneg
  exact B.upperEnvelopeLocalizedImprovementAt_of_strictPatchAt
    (hne x hx) (hupperBddAbove x hx) hEq (hpatch x hx J hJ hneg)

/--
Comparison turns source-shaped strict subsolution patch data into the
neighborhood-form localized improvement.
-/
theorem DirichletBarrierPair.neighborhoodImprovement_of_strictSubsolutionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hne : ∀ x : Point n, x ∈ C -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hpatch : PerronLowerEnvelopeStrictSubsolutionPatch C boundary F g B) :
    PerronLowerEnvelopeNeighborhoodImprovement C boundary F g B :=
  B.neighborhoodImprovement_of_strictPatch hne hupperBddAbove
    (B.strictPatch_of_strictSubsolutionPatch hcomparison hpatch)

/--
Localized-improvement data at a failed contact gives the formal bump
contradiction at that contact.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_bumpContradictionAt_of_localizedImprovementAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g) {x : Point n}
    (himprove : PerronLowerEnvelopeLocalizedImprovementAt C boundary F g B x) :
    ∃ y : Point n, y ∈ C ∪ boundary ∧ ∃ w : Point n -> Real,
      PerronClass C boundary F g B.lower B.upper w ∧
        perronEnvelope C boundary F g B.lower B.upper y < w y := by
  rcases himprove with ⟨w, hwsub, hlower, hfreq⟩
  rcases (hfreq.and_eventually self_mem_nhdsWithin).exists with ⟨y, hWy, hyC⟩
  have hupper : ∀ z : Point n, z ∈ C ∪ boundary -> w z <= B.upper z := by
    intro z hz
    exact hcomparison hwsub B.upper_dirichlet z hz
  have hw : PerronClass C boundary F g B.lower B.upper w :=
    ⟨hwsub, hlower, hupper⟩
  exact ⟨y, Or.inl hyC, w, hw, hWy⟩

/--
Localized-improvement data at every failed contact gives the formal bump
contradiction.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_bumpContradiction_of_localizedImprovement
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (himprove : PerronLowerEnvelopeLocalizedImprovement C boundary F g B) :
    PerronLowerEnvelopeBumpContradiction C boundary F g B := by
  intro x hx J hJ hneg
  exact B.perronLowerEnvelope_bumpContradictionAt_of_localizedImprovementAt
    hcomparison (himprove x hx J hJ hneg)

/--
An improvement over `W^*` gives the usual Perron localized improvement once
`W^* = W` on the domain.
-/
theorem PerronUpperEnvelopeLocalizedImprovementAt.lowerEnvelopeLocalizedImprovementAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n}
    (himprove : PerronUpperEnvelopeLocalizedImprovementAt C boundary F g B x)
    (hEq : Set.EqOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
      (perronEnvelope C boundary F g B.lower B.upper) C) :
    PerronLowerEnvelopeLocalizedImprovementAt C boundary F g B x := by
  rcases himprove with ⟨w, hwsub, hlower, hfreq⟩
  refine ⟨w, hwsub, hlower, ?_⟩
  exact (hfreq.and_eventually self_mem_nhdsWithin).mono (by
    intro y hy
    simpa [hEq hy.2] using hy.1)

/--
Global direct improvement over `W^*` gives the usual Perron localized
improvement once `W^* = W` on the domain.
-/
theorem PerronUpperEnvelopeLocalizedImprovement.lowerEnvelopeLocalizedImprovement
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (himprove : PerronUpperEnvelopeLocalizedImprovement C boundary F g B)
    (hEq : Set.EqOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
      (perronEnvelope C boundary F g B.lower B.upper) C) :
    PerronLowerEnvelopeLocalizedImprovement C boundary F g B := by
  intro x hx J hJ hneg
  exact (himprove x hx J hJ hneg).lowerEnvelopeLocalizedImprovementAt hEq

/--
A local strict-patch datum at a failed lower-envelope contact.

The analytic bump construction should eventually supply such data: a level
`a` strictly above `W_* x`, a relative neighborhood on which the bump is above
`a`, and an admissible max-patch Perron member. The lower-envelope selection
lemma then chooses a nearby point where `W < a`, hence where the patch exceeds
the Perron envelope.
-/
def PerronLowerEnvelopeStrictLocalPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ a : Real, ∃ V : Set (Point n), ∃ old bump : Point n -> Real,
    V ∈ nhdsWithin x C ∧
      (∀ y : Point n, y ∈ V -> a < bump y) ∧
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < a ∧
          PerronClass C boundary F g B.lower B.upper old ∧
            PerronClass C boundary F g B.lower B.upper
              (fun z => Max.max (old z) (bump z))

/--
The older max-patch strict-local formulation implies the source-shaped strict
patch formulation by taking the patched Perron-class member itself.
-/
theorem PerronLowerEnvelopeStrictLocalPatchAt.strictPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n}
    (hpatch : PerronLowerEnvelopeStrictLocalPatchAt C boundary F g B x) :
    PerronLowerEnvelopeStrictPatchAt C boundary F g B x := by
  rcases hpatch with ⟨a, V, old, bump, hV, hbumpAbove, hWlower, _hold, hmax⟩
  refine ⟨a, V, fun z => Max.max (old z) (bump z), hV, ?_, hWlower, hmax⟩
  intro y hy
  exact (hbumpAbove y hy).trans_le (le_max_right (old y) (bump y))

/--
The older strict-local max-patch formulation gives the neighborhood-form
localized improvement at the same failed contact.
-/
theorem DirichletBarrierPair.neighborhoodImprovementAt_of_strictLocalPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hne : (nhdsWithin x C).NeBot)
    (hupperBddAbove : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hpatch : PerronLowerEnvelopeStrictLocalPatchAt C boundary F g B x) :
    PerronLowerEnvelopeNeighborhoodImprovementAt C boundary F g B x :=
  B.neighborhoodImprovementAt_of_strictPatchAt hne hupperBddAbove hpatch.strictPatchAt

/--
The local strict-patch formulation implies the concrete max-patch output at
the same failed contact point.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_maxPatchBumpAt_of_strictLocalPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hne : (nhdsWithin x C).NeBot)
    (hupperBddAbove : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hpatch : PerronLowerEnvelopeStrictLocalPatchAt C boundary F g B x) :
    PerronLowerEnvelopeMaxPatchBumpAt C boundary F g B x := by
  let W : Point n -> Real := perronEnvelope C boundary F g B.lower B.upper
  rcases hpatch with ⟨a, V, old, bump, hV, hbumpAbove, hWlower, hold, hmax⟩
  let : (nhdsWithin x C).NeBot := hne
  have hWcobdd : (nhdsWithin x C).IsCoboundedUnder (· >= ·) W :=
    B.perronEnvelope_isCoboundedUnder_ge hupperBddAbove
  have hVC : V ∩ C ∈ nhdsWithin x C := Filter.inter_mem hV self_mem_nhdsWithin
  rcases exists_mem_nhdsWithin_lowerEnvelope_lt (u := W) hWcobdd hWlower hVC
    with ⟨y, hyVC, hWy⟩
  have hyC : y ∈ C := hyVC.2
  have hWltBump : W y < bump y :=
    hWy.trans (hbumpAbove y hyVC.1)
  have hWltMax : W y < Max.max (old y) (bump y) :=
    hWltBump.trans_le (le_max_right (old y) (bump y))
  exact ⟨y, Or.inl hyC, old, bump, hold, hmax, hWltMax⟩

/--
A strict local patch at every failed subjet inequality.
-/
def PerronLowerEnvelopeStrictLocalPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeStrictLocalPatchAt C boundary F g B x

/--
The older strict-local max-patch formulation supplies the neighborhood-form
localized improvement.
-/
theorem DirichletBarrierPair.neighborhoodImprovement_of_strictLocalPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hne : ∀ x : Point n, x ∈ C -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hpatch : PerronLowerEnvelopeStrictLocalPatch C boundary F g B) :
    PerronLowerEnvelopeNeighborhoodImprovement C boundary F g B := by
  intro x hx J hJ hneg
  exact B.neighborhoodImprovementAt_of_strictLocalPatchAt
    (hne x hx) (hupperBddAbove x hx) (hpatch x hx J hJ hneg)

/--
The strict local-patch formulation supplies the max-patch bump formulation,
provided the Perron envelope is locally bounded above by the upper barrier at
each interior contact point.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_maxPatchBump_of_strictLocalPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hne : ∀ x : Point n, x ∈ C -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hpatch : PerronLowerEnvelopeStrictLocalPatch C boundary F g B) :
    PerronLowerEnvelopeMaxPatchBump C boundary F g B := by
  intro x hx J hJ hneg
  exact B.perronLowerEnvelope_maxPatchBumpAt_of_strictLocalPatchAt
    (hne x hx) (hupperBddAbove x hx) (hpatch x hx J hJ hneg)

/--
A max-patch bump output gives the formal bump contradiction.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_bumpContradiction_of_maxPatchBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hbump : PerronLowerEnvelopeMaxPatchBump C boundary F g B) :
    PerronLowerEnvelopeBumpContradiction C boundary F g B := by
  intro x hx J hJ hneg
  rcases hbump x hx J hJ hneg with ⟨y, hy, old, bump, _hold, hpatch, hlt⟩
  exact ⟨y, hy, fun z => Max.max (old z) (bump z), hpatch, hlt⟩

end ViscositySolns
