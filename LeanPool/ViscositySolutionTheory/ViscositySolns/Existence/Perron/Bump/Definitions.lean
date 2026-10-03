/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.Quadratic
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Envelopes

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Perron bump definitions

Local and global formulations of the Perron lower-envelope bump input,
plus quadratic bump certification interfaces.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The subjet inequality for the lower Perron envelope.

This is the analytic conclusion supplied by the localized bump contradiction:
if the inequality failed at an interior subjet of `W_*`, one could construct a
larger admissible Perron-class member, contradicting the definition of the
envelope.
-/
def PerronLowerEnvelopeSubjetInequality
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      0 <= F x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
        J.gradient J.hessian

/--
The formal output expected from the localized bump construction.

If the lower-envelope subjet inequality fails at an interior point, the bump
argument should produce an admissible Perron-class member that is strictly
larger than the pointwise Perron envelope at that same point.
-/
def PerronLowerEnvelopeBumpContradiction
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        ∃ y : Point n, y ∈ C ∪ boundary ∧ ∃ w : Point n -> Real,
          PerronClass C boundary F g B.lower B.upper w ∧
            perronEnvelope C boundary F g B.lower B.upper y < w y

/--
Localized improvement output of the Perron bump construction at one failed
lower-envelope contact.

This is a direct Lean version of the payload of CIL Lemma 4.2: construct a
Dirichlet subsolution above the lower barrier that is strictly above the
Perron envelope at points arbitrarily close to the failed contact. Comparison
with the upper barrier turns this Dirichlet subsolution into a Perron-class
member, giving the formal contradiction.
-/
def PerronLowerEnvelopeLocalizedImprovementAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    DirichletSubsolutionOn C boundary F g w ∧
      (∀ y : Point n, y ∈ C ∪ boundary -> B.lower y <= w y) ∧
        ∃ᶠ y in nhdsWithin x C,
          perronEnvelope C boundary F g B.lower B.upper y < w y

/--
Neighborhood-form localized improvement at one failed contact.

This is the same payload as `PerronLowerEnvelopeLocalizedImprovementAt`, but
with the source-document phrasing made explicit: every relative neighborhood
of the failed contact contains a point where the improved subsolution beats the
Perron envelope.
-/
def PerronLowerEnvelopeNeighborhoodImprovementAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    DirichletSubsolutionOn C boundary F g w ∧
      (∀ y : Point n, y ∈ C ∪ boundary -> B.lower y <= w y) ∧
        ∀ V : Set (Point n), V ∈ nhdsWithin x C ->
          ∃ y : Point n, y ∈ V ∧
            perronEnvelope C boundary F g B.lower B.upper y < w y

/--
Concrete max-patch output of the localized bump construction at one failed
subjet inequality.

The analytic construction should produce an old admissible Perron member and a
local bump such that their pointwise maximum is still admissible and strictly
exceeds the Perron envelope at some Dirichlet-domain point.
-/
def PerronLowerEnvelopeMaxPatchBumpAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (_x : Point n) : Prop :=
  ∃ y : Point n, y ∈ C ∪ boundary ∧ ∃ old bump : Point n -> Real,
    PerronClass C boundary F g B.lower B.upper old ∧
      PerronClass C boundary F g B.lower B.upper
        (fun z => Max.max (old z) (bump z)) ∧
        perronEnvelope C boundary F g B.lower B.upper y <
          Max.max (old y) (bump y)

/--
The bump construction localized at every failed subjet inequality.
-/
def PerronLowerEnvelopeMaxPatchBump
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeMaxPatchBumpAt C boundary F g B x

/--
Localized improvement output at every failed lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeLocalizedImprovement
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalizedImprovementAt C boundary F g B x

/--
Direct localized improvement over the upper Perron envelope at one failed
lower-envelope contact.

This is the source-proof bump payload after the maximality step has identified
`W^*` with the pointwise Perron envelope on the domain. The analytic bump can
be constructed against the already-subsolution upper envelope; the method
layer later converts this into the ordinary Perron localized-improvement
interface using `W^* = W` on `C`.
-/
def PerronUpperEnvelopeLocalizedImprovementAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    DirichletSubsolutionOn C boundary F g w ∧
      (∀ y : Point n, y ∈ C ∪ boundary -> B.lower y <= w y) ∧
        ∃ᶠ y in nhdsWithin x C,
          upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) y < w y

/--
Direct localized improvement over `W^*` at every failed lower-envelope subjet
inequality.
-/
def PerronUpperEnvelopeLocalizedImprovement
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronUpperEnvelopeLocalizedImprovementAt C boundary F g B x

/--
Neighborhood-form localized improvement at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeNeighborhoodImprovement
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeNeighborhoodImprovementAt C boundary F g B x

/--
Source-shaped strict patch data at a failed lower-envelope contact.

This is the part of Lemma 4.2 that is actually needed for Perron's
contradiction: construct an admissible Perron-class member that lies above a
strict level on a relative neighborhood of the contact point, where that level
is above the lower envelope value `W_* x`.
-/
def PerronLowerEnvelopeStrictPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ a : Real, ∃ V : Set (Point n), ∃ w : Point n -> Real,
    V ∈ nhdsWithin x C ∧
      (∀ y : Point n, y ∈ V -> a < w y) ∧
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < a ∧
          PerronClass C boundary F g B.lower B.upper w

/--
Source-shaped strict bump data before applying comparison with the upper
barrier.

Lemma 4.2 constructs a Dirichlet subsolution patch. In Perron's method, the
upper-barrier bound needed for membership in the Perron class comes from the
abstract comparison principle.
-/
def PerronLowerEnvelopeStrictSubsolutionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ a : Real, ∃ V : Set (Point n), ∃ w : Point n -> Real,
    V ∈ nhdsWithin x C ∧
      (∀ y : Point n, y ∈ V -> a < w y) ∧
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < a ∧
          DirichletSubsolutionOn C boundary F g w ∧
            (∀ y : Point n, y ∈ C ∪ boundary -> B.lower y <= w y)

/--
Pointwise strict subsolution patch data at a failed lower-envelope contact.

This is closer to the analytic output of the bump construction: it is enough
to build a Dirichlet subsolution patch that is lower semicontinuous at the
contact point and whose value there is strictly above `W_* x`. Lower
semicontinuity turns the pointwise strict inequality into a strict relative
neighborhood, giving `PerronLowerEnvelopeStrictSubsolutionPatchAt`.
-/
def PerronLowerEnvelopePointwiseStrictSubsolutionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    LowerSemicontinuousWithinAt w C x ∧
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < w x ∧
        DirichletSubsolutionOn C boundary F g w ∧
          (∀ y : Point n, y ∈ C ∪ boundary -> B.lower y <= w y)

/--
Continuous pointwise strict subsolution patch data at a failed lower-envelope
contact.

This is the form naturally produced by a smooth local bump: continuity at the
contact point, pointwise strict improvement over `W_*`, the Dirichlet
subsolution property, and the lower-barrier bound.
-/
def PerronLowerEnvelopeContinuousStrictSubsolutionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    ContinuousWithinAt w C x ∧
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < w x ∧
        DirichletSubsolutionOn C boundary F g w ∧
          (∀ y : Point n, y ∈ C ∪ boundary -> B.lower y <= w y)

/--
Continuous Dirichlet bump data at a failed lower-envelope contact.

This removes one global burden from the analytic bump construction. The bump
only has to be a Dirichlet subsolution and be continuous and strictly above
`W_*` at the contact point; maxing with the lower barrier supplies the global
lower-barrier bound required by the Perron class.
-/
def PerronLowerEnvelopeContinuousBumpAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    ContinuousWithinAt w C x ∧
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < w x ∧
        DirichletSubsolutionOn C boundary F g w

/--
Continuous max-patch bump data at a failed lower-envelope contact.

Here the raw bump only has to be continuous and strictly above `W_*` at the
contact. The analytic gluing argument may prove directly that the patched
function `max lower bump` is a Dirichlet subsolution.
-/
def PerronLowerEnvelopeContinuousMaxPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    ContinuousWithinAt w C x ∧
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < w x ∧
        DirichletSubsolutionOn C boundary F g
          (fun y => Max.max (B.lower y) (w y))

/--
Continuous local max-patch bump data at a failed lower-envelope contact.

This is a gluing-oriented form of the bump step: the raw bump is continuous
and strictly above `W_*` at the contact, the boundary inequality is supplied
for the patched function, and the viscosity subsolution property of
`max lower w` is checked by local germ representatives.
-/
def PerronLowerEnvelopeContinuousLocalMaxPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    ContinuousWithinAt w C x ∧
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < w x ∧
        BoundarySubsolutionOn boundary g (fun y => Max.max (B.lower y) (w y)) ∧
          UpperSemicontinuousOn (fun y => Max.max (B.lower y) (w y)) (C ∪ boundary) ∧
          ∀ z : Point n, z ∈ C ->
            ∃ v : Point n -> Real,
              ViscositySubsolution C F v ∧
                Max.max (B.lower z) (w z) = v z ∧
                  (fun y => Max.max (B.lower y) (w y)) =ᶠ[nhdsWithin z C] v

/--
Branch-local continuous max-patch data at a failed lower-envelope contact.

This is the form closest to a local gluing proof: around each point of `C`,
the patched function either agrees with the lower barrier branch, or agrees
with a supplied viscosity subsolution branch.
-/
def PerronLowerEnvelopeContinuousBranchMaxPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    ContinuousWithinAt w C x ∧
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < w x ∧
        BoundarySubsolutionOn boundary g (fun y => Max.max (B.lower y) (w y)) ∧
          UpperSemicontinuousOn (fun y => Max.max (B.lower y) (w y)) (C ∪ boundary) ∧
          ∀ z : Point n, z ∈ C ->
            (Max.max (B.lower z) (w z) = B.lower z ∧
                (fun y => Max.max (B.lower y) (w y)) =ᶠ[nhdsWithin z C] B.lower) ∨
              ∃ v : Point n -> Real,
                ViscositySubsolution C F v ∧
                  Max.max (B.lower z) (w z) = v z ∧
                    (fun y => Max.max (B.lower y) (w y)) =ᶠ[nhdsWithin z C] v

/--
Active-branch continuous max-patch data at a failed lower-envelope contact.

This spells out the inequalities that make one branch of `max lower w`
locally active. Near each point of `C`, either the lower barrier dominates the
raw bump, or the raw bump dominates the lower barrier and agrees locally with
a viscosity subsolution representative.
-/
def PerronLowerEnvelopeContinuousActiveMaxPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    ContinuousWithinAt w C x ∧
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < w x ∧
        BoundarySubsolutionOn boundary g (fun y => Max.max (B.lower y) (w y)) ∧
          UpperSemicontinuousOn (fun y => Max.max (B.lower y) (w y)) (C ∪ boundary) ∧
          ∀ z : Point n, z ∈ C ->
            (w z <= B.lower z ∧
                ∀ᶠ y in nhdsWithin z C, w y <= B.lower y) ∨
              ∃ v : Point n -> Real,
                ViscositySubsolution C F v ∧
                  B.lower z <= w z ∧
                    w z = v z ∧
                      (∀ᶠ y in nhdsWithin z C, B.lower y <= w y) ∧
                        w =ᶠ[nhdsWithin z C] v

/--
Strict active-branch continuous max-patch data at a failed lower-envelope
contact.

This records the common gluing situation with strict local branch separation:
locally either the raw bump lies strictly below the lower barrier, or it lies
strictly above the lower barrier and agrees with a local subsolution branch.
-/
def PerronLowerEnvelopeContinuousStrictActiveMaxPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    ContinuousWithinAt w C x ∧
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < w x ∧
        BoundarySubsolutionOn boundary g (fun y => Max.max (B.lower y) (w y)) ∧
          UpperSemicontinuousOn (fun y => Max.max (B.lower y) (w y)) (C ∪ boundary) ∧
          ∀ z : Point n, z ∈ C ->
            (w z < B.lower z ∧
                ∀ᶠ y in nhdsWithin z C, w y < B.lower y) ∨
              ∃ v : Point n -> Real,
                ViscositySubsolution C F v ∧
                  B.lower z < w z ∧
                    w z = v z ∧
                      (∀ᶠ y in nhdsWithin z C, B.lower y < w y) ∧
                        w =ᶠ[nhdsWithin z C] v

/--
Strict active-branch bump data where the raw bump is itself a viscosity
subsolution.

This is the usual special case needed after a smooth local bump has already
been certified as a subsolution: the max patch is verified by strict branch
separation, and the upper active branch uses the bump itself as the local
subsolution representative.
-/
def PerronLowerEnvelopeContinuousStrictActiveSubsolutionBumpAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    ContinuousWithinAt w C x ∧
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < w x ∧
        BoundarySubsolutionOn boundary g (fun y => Max.max (B.lower y) (w y)) ∧
          UpperSemicontinuousOn (fun y => Max.max (B.lower y) (w y)) (C ∪ boundary) ∧
          ViscositySubsolution C F w ∧
            ∀ z : Point n, z ∈ C ->
              (w z < B.lower z ∧
                  ∀ᶠ y in nhdsWithin z C, w y < B.lower y) ∨
                (B.lower z < w z ∧
                  ∀ᶠ y in nhdsWithin z C, B.lower y < w y)

/--
Strict active-branch bump data where the raw bump is a Dirichlet
subsolution.

Compared with `PerronLowerEnvelopeContinuousStrictActiveSubsolutionBumpAt`,
this asks for the ordinary Dirichlet boundary inequality for the raw bump.
The boundary inequality for `max lower bump` then follows from the
Dirichlet max lemma.
-/
def PerronLowerEnvelopeContinuousStrictActiveDirichletBumpAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    ContinuousWithinAt w C x ∧
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < w x ∧
        DirichletSubsolutionOn C boundary F g w ∧
          ∀ z : Point n, z ∈ C ->
            (w z < B.lower z ∧
                ∀ᶠ y in nhdsWithin z C, w y < B.lower y) ∨
              (B.lower z < w z ∧
                ∀ᶠ y in nhdsWithin z C, B.lower y < w y)

/--
A certified quadratic bump supplies the strict active Dirichlet-bump interface.

This packages the analytic checks needed once a failed lower-envelope contact
has produced a concrete quadratic: superjet control plus degenerate ellipticity
certifies viscosity subsolution status, while the caller supplies the boundary
inequality and strict active-branch separation from the lower barrier.
-/
theorem DirichletBarrierPair.strictActiveDirichletBumpAt_of_quadraticModel
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x x0 : Point n}
    {r : Real} {p : Point n} {X : Hessian n}
    (hFell : DegenerateElliptic F)
    (hcontrol : ∀ z : Point n, z ∈ C -> ∀ J : Jet n,
      J ∈ Superjet C (fun y => quadraticModel x0 r p X y) z ->
        J.gradient = (quadraticModelJetAt x0 p X z).gradient ∧
          (quadraticModelJetAt x0 p X z).hessian <= J.hessian)
    (hineq : ∀ z : Point n, z ∈ C ->
      F z (quadraticModel x0 r p X z)
          (quadraticModelJetAt x0 p X z).gradient
          (quadraticModelJetAt x0 p X z).hessian <= 0)
    (hWlt :
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <
        quadraticModel x0 r p X x)
    (hboundary :
      BoundarySubsolutionOn boundary g (fun y => quadraticModel x0 r p X y))
    (hactive : ∀ z : Point n, z ∈ C ->
      (quadraticModel x0 r p X z < B.lower z ∧
          ∀ᶠ y in nhdsWithin z C, quadraticModel x0 r p X y < B.lower y) ∨
        (B.lower z < quadraticModel x0 r p X z ∧
          ∀ᶠ y in nhdsWithin z C, B.lower y < quadraticModel x0 r p X y)) :
    PerronLowerEnvelopeContinuousStrictActiveDirichletBumpAt C boundary F g B x := by
  let q : Point n -> Real := fun y => quadraticModel x0 r p X y
  have hqSub : ViscositySubsolution C F q :=
    ViscositySubsolution.quadraticModel_of_superjetControl
      (C := C) (F := F) (x0 := x0) (r := r) (p := p) (X := X)
      hFell hcontrol hineq
  have hqDir : DirichletSubsolutionOn C boundary F g q :=
    ⟨hqSub, hboundary, (continuous_quadraticModel x0 r p X).continuousOn.upperSemicontinuousOn⟩
  refine ⟨q, ?_, ?_, hqDir, ?_⟩
  · exact (continuous_quadraticModel x0 r p X).continuousWithinAt
  · exact hWlt
  · exact hactive

/--
An interior-domain certified quadratic bump supplies the strict active
Dirichlet-bump interface.

Compared with `strictActiveDirichletBumpAt_of_quadraticModel`, this discharges
the explicit superjet-control input using the shared local/full-neighborhood
quadratic superjet theorem.
-/
theorem DirichletBarrierPair.strictActiveDirichletBumpAt_of_interior_quadraticModel
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x x0 : Point n}
    {r : Real} {p : Point n} {X : Hessian n}
    (hFell : DegenerateElliptic F)
    (hinterior : ∀ z : Point n, z ∈ C -> z ∈ interior C)
    (hHerm : ∀ z : Point n, z ∈ C -> ∀ J : Jet n,
      J ∈ Superjet C (fun y => quadraticModel x0 r p X y) z ->
        (J.hessian - (quadraticModelJetAt x0 p X z).hessian).IsHermitian)
    (hineq : ∀ z : Point n, z ∈ C ->
      F z (quadraticModel x0 r p X z)
          (quadraticModelJetAt x0 p X z).gradient
          (quadraticModelJetAt x0 p X z).hessian <= 0)
    (hWlt :
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <
        quadraticModel x0 r p X x)
    (hboundary :
      BoundarySubsolutionOn boundary g (fun y => quadraticModel x0 r p X y))
    (hactive : ∀ z : Point n, z ∈ C ->
      (quadraticModel x0 r p X z < B.lower z ∧
          ∀ᶠ y in nhdsWithin z C, quadraticModel x0 r p X y < B.lower y) ∨
        (B.lower z < quadraticModel x0 r p X z ∧
          ∀ᶠ y in nhdsWithin z C, B.lower y < quadraticModel x0 r p X y)) :
    PerronLowerEnvelopeContinuousStrictActiveDirichletBumpAt C boundary F g B x := by
  let q : Point n -> Real := fun y => quadraticModel x0 r p X y
  have hqSub : ViscositySubsolution C F q :=
    ViscositySubsolution.quadraticModel_of_mem_interior_of_isHermitian_sub
      (C := C) (F := F) (x0 := x0) (r := r) (p := p) (X := X)
      hFell hinterior hHerm hineq
  have hqDir : DirichletSubsolutionOn C boundary F g q :=
    ⟨hqSub, hboundary, (continuous_quadraticModel x0 r p X).continuousOn.upperSemicontinuousOn⟩
  refine ⟨q, ?_, ?_, hqDir, ?_⟩
  · exact (continuous_quadraticModel x0 r p X).continuousWithinAt
  · exact hWlt
  · exact hactive

/--
Source-shaped interior quadratic bump data at every failed lower-envelope
subjet inequality.

This packages the analytic payload of the quadratic part of Lemma 4.2: from a
failed lower-envelope subjet inequality, produce a quadratic bump that is
strictly above the lower envelope at the contact, satisfies the differential
subsolution inequality throughout `C`, obeys the boundary condition, and has
strict local branch separation from the lower barrier.
-/
def PerronLowerEnvelopeInteriorQuadraticBump
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        ∃ x0 : Point n, ∃ r : Real, ∃ p : Point n, ∃ X : Hessian n,
          (∀ z : Point n, z ∈ C -> ∀ K : Jet n,
            K ∈ Superjet C (fun y => quadraticModel x0 r p X y) z ->
              (K.hessian - (quadraticModelJetAt x0 p X z).hessian).IsHermitian) ∧
            (∀ z : Point n, z ∈ C ->
              F z (quadraticModel x0 r p X z)
                  (quadraticModelJetAt x0 p X z).gradient
                  (quadraticModelJetAt x0 p X z).hessian <= 0) ∧
              lowerEnvelope C
                  (perronEnvelope C boundary F g B.lower B.upper) x <
                quadraticModel x0 r p X x ∧
                BoundarySubsolutionOn boundary g
                  (fun y => quadraticModel x0 r p X y) ∧
                  ∀ z : Point n, z ∈ C ->
                    (quadraticModel x0 r p X z < B.lower z ∧
                        ∀ᶠ y in nhdsWithin z C,
                          quadraticModel x0 r p X y < B.lower y) ∨
                      (B.lower z < quadraticModel x0 r p X z ∧
                        ∀ᶠ y in nhdsWithin z C,
                          B.lower y < quadraticModel x0 r p X y)

end ViscositySolns
