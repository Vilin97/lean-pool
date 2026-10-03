/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.Contradiction
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.QuadraticGluing.GluingSkeleton

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Quadratic gluing data for the Perron bump step (AnnulusSelectionPatches)

Part of the quadratic-gluing development connecting the lifted quadratic
supplied by operator continuity to the strict local max-patch formulation.
Split from `QuadraticGluing.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Source-radius compact-inactive data for the localized bent quadratic.

This is the finite-selection version of the source bump construction. The
patch ball carries the strict quadratic branch. On the compact inactive set,
including the Dirichlet boundary, local Perron-family branches dominate the
bent quadratic; finite selection then produces one old Perron branch for the
global max patch.
-/
def PerronLowerEnvelopeBentQuadraticSourceCompactInactivePatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V K : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                ContinuousWithinAt q C x ∧
                  (∀ z : Point n, z ∈ V -> z ∈ C ->
                    F z (q z)
                        (quadraticModelJetAt x J.gradient Xb z).gradient
                        (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                    IsCompact K ∧
                      (∀ z : Point n, z ∈ C -> z ∉ Metric.ball x r -> z ∈ K) ∧
                        (∀ z : Point n, z ∈ boundary -> z ∈ K) ∧
                          (∀ z : Point n, z ∈ K -> K ∈ nhdsWithin z C) ∧
                            ∀ z : Point n, z ∈ K ->
                              ∃ w : PerronFamily C boundary F g B.lower B.upper,
                                ∀ᶠ y in nhdsWithin z K, q y <= w.fun y

/--
Source-radius compact-inactive data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceCompactInactivePatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceCompactInactivePatchAt
          C boundary F g B x J

/--
Source-radius transition-annulus selection data.

The compact set `K` only has to control the transition region where the
piecewise patch crosses the sphere. For inactive points, the caller supplies
the local alternative `outside the patch ball or in K`; finite selection on
`K` then makes the patch agree locally with the selected old branch.
-/
def PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V K : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                ContinuousWithinAt q C x ∧
                  (∀ z : Point n, z ∈ V -> z ∈ C ->
                    F z (q z)
                        (quadraticModelJetAt x J.gradient Xb z).gradient
                        (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                    IsCompact K ∧
                      (∀ z : Point n, z ∈ K -> K ∈ nhdsWithin z K) ∧
                        (∀ z : Point n, z ∈ K ->
                          ∃ w : PerronFamily C boundary F g B.lower B.upper,
                            ∀ᶠ y in nhdsWithin z K, q y <= w.fun y) ∧
                          (∀ z : Point n, z ∈ C -> z ∉ Metric.ball x r ->
                            ∀ᶠ y in nhdsWithin z C,
                              y ∉ Metric.ball x r ∨ y ∈ K) ∧
                            ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Source-radius transition-annulus selection data at every failed
lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatchAt
          C boundary F g B x J

/--
Concrete closed-annulus source-radius transition data.

The transition compact set is the explicit closed annulus
`r / 2 <= dist z x <= r`. The bridge below proves the remaining local
alternative: any point of `C` outside the open patch ball is eventually either
outside that ball or inside this annulus.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                ContinuousWithinAt q C x ∧
                  (∀ z : Point n, z ∈ V -> z ∈ C ->
                    F z (q z)
                        (quadraticModelJetAt x J.gradient Xb z).gradient
                        (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                    (∀ z : Point n, z ∈ K ->
                      ∃ w : PerronFamily C boundary F g B.lower B.upper,
                        ∀ᶠ y in nhdsWithin z K, q y <= w.fun y) ∧
                      ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Concrete closed-annulus source-radius transition data at every failed
lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatchAt
          C boundary F g B x J

/--
Source-radius closed-annulus data with pointwise Perron-family branch
selection.

At each point of the explicit annulus, the caller only selects one
Perron-family branch that is strictly above the bent quadratic at that point
and lower semicontinuous relative to the annulus there. The bridge below turns
this into the local domination required by
`PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatchAt`.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                ContinuousWithinAt q C x ∧
                  (∀ z : Point n, z ∈ V -> z ∈ C ->
                    F z (q z)
                        (quadraticModelJetAt x J.gradient Xb z).gradient
                        (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                    (∀ z : Point n, z ∈ K ->
                      ∃ w : PerronFamily C boundary F g B.lower B.upper,
                        LowerSemicontinuousWithinAt w.fun K z ∧ q z < w.fun z) ∧
                      ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Closed-annulus lower-semicontinuous branch selection data at every failed
lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatchAt
          C boundary F g B x J

namespace PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatchAt

/--
Lower semicontinuity plus a pointwise strict gap gives local branch domination
on the explicit annulus.
-/
theorem closedAnnulusSelectionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatchAt
      C boundary F g B x J := by
  rcases hpatch with
    ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hWltq,
      hqCont, hneg, hpointwise, hboundaryAway⟩
  let δ : Real := γ * r ^ 2 / 8
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
  refine ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hWltq,
    hqCont, hneg, ?_, hboundaryAway⟩
  intro z hzK
  rcases hpointwise z hzK with ⟨w, hwLsc, hstrict⟩
  refine ⟨w, ?_⟩
  rcases exists_between hstrict with ⟨a, hqa, haw⟩
  have hqContK : ContinuousWithinAt q K z := by
    exact (continuous_quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb).continuousWithinAt
  have hqNear : ∀ᶠ y in nhdsWithin z K, q y < a :=
    hqContK (isOpen_Iio.mem_nhds hqa)
  have hwNear : ∀ᶠ y in nhdsWithin z K, a < w.fun y :=
    hwLsc a haw
  filter_upwards [hqNear, hwNear] with y hyq hyw
  exact le_of_lt (hyq.trans hyw)

end PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatch

/--
Global lower-semicontinuous closed-annulus branch selection data supplies the
closed-annulus local-domination interface.
-/
theorem closedAnnulusSelectionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).closedAnnulusSelectionPatchAt

end PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatch

/--
Source-radius closed-annulus data from strict Perron-envelope approximation.

The source annulus estimate naturally gives information against the Perron
supremum. This interface records the additional regularity needed to turn
strict Perron-envelope approximation into the lower-semicontinuous branch
selection used by the finite Perron patch: the Perron-family values are
bounded above at annulus points, the bent quadratic is strictly below the
Perron envelope there, and Perron-family branches are lower semicontinuous on
the annulus.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusEnvelopeLscSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                ContinuousWithinAt q C x ∧
                  (∀ z : Point n, z ∈ V -> z ∈ C ->
                    F z (q z)
                        (quadraticModelJetAt x J.gradient Xb z).gradient
                        (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                    (∀ z : Point n, z ∈ K ->
                      BddAbove {a : Real | ∃ w : Point n -> Real,
                        PerronClass C boundary F g B.lower B.upper w ∧ a = w z}) ∧
                      (∀ z : Point n, z ∈ K ->
                        q z < perronEnvelope C boundary F g B.lower B.upper z) ∧
                        (∀ w : PerronFamily C boundary F g B.lower B.upper,
                          LowerSemicontinuousOn w.fun K) ∧
                          ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Strict Perron-envelope closed-annulus approximation data at every failed
lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusEnvelopeLscSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusEnvelopeLscSelectionPatchAt
          C boundary F g B x J

namespace PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusEnvelopeLscSelectionPatchAt

/--
Strict approximation by the Perron envelope, plus lower semicontinuity of the
approximating Perron branches on the annulus, supplies the LSC branch-selection
interface.
-/
theorem lscSelectionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusEnvelopeLscSelectionPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatchAt
      C boundary F g B x J := by
  rcases hpatch with
    ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hWltq,
      hqCont, hneg, hbdd, henv, hfamilyLsc, hboundaryAway⟩
  let δ : Real := γ * r ^ 2 / 8
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
  refine ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hWltq,
    hqCont, hneg, ?_, hboundaryAway⟩
  intro z hzK
  rcases B.exists_perronFamily_gt_of_lt_perronEnvelope_of_bddAbove
      (hbdd z hzK) (henv z hzK) with ⟨w, hwgt⟩
  exact ⟨w, hfamilyLsc w z hzK, hwgt⟩

end PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusEnvelopeLscSelectionPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusEnvelopeLscSelectionPatch

/--
Global strict Perron-envelope closed-annulus approximation data supplies the
LSC branch-selection interface.
-/
theorem lscSelectionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusEnvelopeLscSelectionPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).lscSelectionPatchAt

end PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusEnvelopeLscSelectionPatch

/--
Source-radius closed-annulus data from strict Perron-envelope approximation,
with Perron-family boundedness discharged by an annulus-domain condition.

If every point of the explicit annulus lies in `C ∪ boundary`, the upper
barrier bounds every Perron-family member there, so the Perron envelope can be
approximated from below without asking the caller for a separate boundedness
proof.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusDomainEnvelopeLscSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                ContinuousWithinAt q C x ∧
                  (∀ z : Point n, z ∈ V -> z ∈ C ->
                    F z (q z)
                        (quadraticModelJetAt x J.gradient Xb z).gradient
                        (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                    (∀ z : Point n, z ∈ K -> z ∈ C ∪ boundary) ∧
                      (∀ z : Point n, z ∈ K ->
                        q z < perronEnvelope C boundary F g B.lower B.upper z) ∧
                        (∀ w : PerronFamily C boundary F g B.lower B.upper,
                          LowerSemicontinuousOn w.fun K) ∧
                          ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Domain-controlled strict Perron-envelope closed-annulus approximation data at
every failed lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusDomainEnvelopeLscSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusDomainEnvelopeLscSelectionPatchAt
          C boundary F g B x J

namespace PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusDomainEnvelopeLscSelectionPatchAt

/--
The annulus-domain condition lets the upper barrier provide the pointwise
boundedness needed for strict approximation by the Perron envelope.
-/
theorem envelopeLscSelectionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusDomainEnvelopeLscSelectionPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusEnvelopeLscSelectionPatchAt
      C boundary F g B x J := by
  rcases hpatch with
    ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hWltq,
      hqCont, hneg, hKdomain, henv, hfamilyLsc, hboundaryAway⟩
  let δ : Real := γ * r ^ 2 / 8
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
  refine ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hWltq,
    hqCont, hneg, ?_, henv, hfamilyLsc, hboundaryAway⟩
  intro z hzK
  refine ⟨B.upper z, ?_⟩
  intro a ha
  rcases ha with ⟨w, hw, rfl⟩
  exact hw.le_upper (hKdomain z hzK)

end PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusDomainEnvelopeLscSelectionPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusDomainEnvelopeLscSelectionPatch

/--
Global domain-controlled strict Perron-envelope data supplies the bounded
strict Perron-envelope approximation interface.
-/
theorem envelopeLscSelectionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusDomainEnvelopeLscSelectionPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusEnvelopeLscSelectionPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).envelopeLscSelectionPatchAt

end PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusDomainEnvelopeLscSelectionPatch

/--
Source-radius closed-annulus data with the source proof's geometric domain
condition.

The caller supplies the closed patch ball inside `C` and the Dirichlet
boundary outside `C`. These imply both that the explicit annulus lies in the
Dirichlet domain and that the open patch ball avoids the boundary.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedBallEnvelopeLscSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              (∀ z : Point n, z ∈ Metric.closedBall x r -> z ∈ C) ∧
                (∀ z : Point n, z ∈ boundary -> z ∉ C) ∧
                  lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                    ContinuousWithinAt q C x ∧
                      (∀ z : Point n, z ∈ V -> z ∈ C ->
                        F z (q z)
                            (quadraticModelJetAt x J.gradient Xb z).gradient
                            (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                        (∀ z : Point n, z ∈ K ->
                          q z < perronEnvelope C boundary F g B.lower B.upper z) ∧
                          ∀ w : PerronFamily C boundary F g B.lower B.upper,
                            LowerSemicontinuousOn w.fun K

/--
Closed-ball source-geometry strict Perron-envelope data at every failed
lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedBallEnvelopeLscSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceClosedBallEnvelopeLscSelectionPatchAt
          C boundary F g B x J

namespace PerronLowerEnvelopeBentQuadraticSourceClosedBallEnvelopeLscSelectionPatchAt

/--
Closed-ball source geometry supplies the domain-controlled closed-annulus
strict Perron-envelope interface.
-/
theorem domainEnvelopeLscSelectionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedBallEnvelopeLscSelectionPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusDomainEnvelopeLscSelectionPatchAt
      C boundary F g B x J := by
  rcases hpatch with
    ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hclosedBallC,
      hboundaryOutside, hWltq, hqCont, hneg, henv, hfamilyLsc⟩
  let δ : Real := γ * r ^ 2 / 8
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
  refine ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hWltq,
    hqCont, hneg, ?_, henv, hfamilyLsc, ?_⟩
  · intro z hzK
    exact Or.inl (hclosedBallC z (by
      simpa [Metric.mem_closedBall] using hzK.2))
  · intro z hzBoundary hzBall
    exact hboundaryOutside z hzBoundary
      (hclosedBallC z hzBall)

end PerronLowerEnvelopeBentQuadraticSourceClosedBallEnvelopeLscSelectionPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceClosedBallEnvelopeLscSelectionPatch

/--
Global closed-ball source-geometry data supplies the domain-controlled
closed-annulus strict Perron-envelope interface.
-/
theorem domainEnvelopeLscSelectionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedBallEnvelopeLscSelectionPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusDomainEnvelopeLscSelectionPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).domainEnvelopeLscSelectionPatchAt

end PerronLowerEnvelopeBentQuadraticSourceClosedBallEnvelopeLscSelectionPatch

/--
Source-radius closed-ball data with annulus strictness stated against the
lower relaxed Perron envelope.

The closed ball condition later converts the lower-envelope inequality to a
Perron-envelope inequality using local lower boundedness of the Perron envelope.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedBallLowerEnvelopeLscSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              (∀ z : Point n, z ∈ Metric.closedBall x r -> z ∈ C) ∧
                (∀ z : Point n, z ∈ boundary -> z ∉ C) ∧
                  lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                    ContinuousWithinAt q C x ∧
                      (∀ z : Point n, z ∈ V -> z ∈ C ->
                        F z (q z)
                            (quadraticModelJetAt x J.gradient Xb z).gradient
                            (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                        (∀ z : Point n, z ∈ K ->
                          q z < lowerEnvelope C
                            (perronEnvelope C boundary F g B.lower B.upper) z) ∧
                          ∀ w : PerronFamily C boundary F g B.lower B.upper,
                            LowerSemicontinuousOn w.fun K

/--
Closed-ball lower-envelope annulus data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedBallLowerEnvelopeLscSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceClosedBallLowerEnvelopeLscSelectionPatchAt
          C boundary F g B x J

namespace PerronLowerEnvelopeBentQuadraticSourceClosedBallLowerEnvelopeLscSelectionPatchAt

/--
Local lower boundedness turns strict annulus domination of the lower envelope
into strict annulus domination of the Perron envelope.
-/
theorem closedBallEnvelopeLscSelectionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedBallLowerEnvelopeLscSelectionPatchAt
        C boundary F g B x J)
    (hlowerBddBelow : ∀ z : Point n, z ∈ C ∪ boundary ->
      (nhdsWithin z C).IsBoundedUnder (· >= ·) B.lower) :
    PerronLowerEnvelopeBentQuadraticSourceClosedBallEnvelopeLscSelectionPatchAt
      C boundary F g B x J := by
  rcases hpatch with
    ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hclosedBallC,
      hboundaryOutside, hWltq, hqCont, hneg, hlowerAnnulus, hfamilyLsc⟩
  let δ : Real := γ * r ^ 2 / 8
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
  refine ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hclosedBallC,
    hboundaryOutside, hWltq, hqCont, hneg, ?_, hfamilyLsc⟩
  intro z hzK
  have hzClosed : z ∈ Metric.closedBall x r := by
    simpa [Metric.mem_closedBall] using hzK.2
  have hzC : z ∈ C := hclosedBallC z hzClosed
  have hle :
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) z <=
        perronEnvelope C boundary F g B.lower B.upper z :=
    lowerEnvelope_le hzC
      (B.perronEnvelope_isBoundedUnder_ge (hlowerBddBelow z (Or.inl hzC)))
  exact lt_of_lt_of_le (hlowerAnnulus z hzK) hle

end PerronLowerEnvelopeBentQuadraticSourceClosedBallLowerEnvelopeLscSelectionPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceClosedBallLowerEnvelopeLscSelectionPatch

/--
Global closed-ball lower-envelope annulus data supplies the closed-ball
Perron-envelope interface.
-/
theorem closedBallEnvelopeLscSelectionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedBallLowerEnvelopeLscSelectionPatch
        C boundary F g B)
    (hlowerBddBelow : ∀ z : Point n, z ∈ C ∪ boundary ->
      (nhdsWithin z C).IsBoundedUnder (· >= ·) B.lower) :
    PerronLowerEnvelopeBentQuadraticSourceClosedBallEnvelopeLscSelectionPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).closedBallEnvelopeLscSelectionPatchAt
    hlowerBddBelow

end PerronLowerEnvelopeBentQuadraticSourceClosedBallLowerEnvelopeLscSelectionPatch

/--
Source-radius closed-ball data with annulus strictness on the outer transition
annulus.

The transition region for the piecewise patch only needs to cover points near
the boundary of the patch ball. Using `3 * r / 4 <= dist z x <= r` leaves a
strict quadratic margin for the source subjet estimate while preserving the
metric transition argument.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    let K : Set (Point n) := {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              (∀ z : Point n, z ∈ Metric.closedBall x r -> z ∈ C) ∧
                (∀ z : Point n, z ∈ boundary -> z ∉ C) ∧
                  lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                    ContinuousWithinAt q C x ∧
                      (∀ z : Point n, z ∈ V -> z ∈ C ->
                        F z (q z)
                            (quadraticModelJetAt x J.gradient Xb z).gradient
                            (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                        ∀ z : Point n, z ∈ K ->
                          q z < lowerEnvelope C
                            (perronEnvelope C boundary F g B.lower B.upper) z

/--
Outer-transition closed-ball lower-envelope annulus data without Perron-family
branch lower-semicontinuity.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatchAt
          C boundary F g B x J

/--
Legacy source-radius closed-ball data with annulus strictness on the outer
transition annulus, plus the branch lower-semicontinuity field used by the older
selection route.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    let K : Set (Point n) := {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              (∀ z : Point n, z ∈ Metric.closedBall x r -> z ∈ C) ∧
                (∀ z : Point n, z ∈ boundary -> z ∉ C) ∧
                  lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                    ContinuousWithinAt q C x ∧
                      (∀ z : Point n, z ∈ V -> z ∈ C ->
                        F z (q z)
                            (quadraticModelJetAt x J.gradient Xb z).gradient
                            (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                        (∀ z : Point n, z ∈ K ->
                          q z < lowerEnvelope C
                            (perronEnvelope C boundary F g B.lower B.upper) z) ∧
                          ∀ w : PerronFamily C boundary F g B.lower B.upper,
                            LowerSemicontinuousOn w.fun K

/--
Outer-transition closed-ball lower-envelope annulus data at every failed
lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt
          C boundary F g B x J

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt

/--
Forget the branch lower-semicontinuity field from the legacy outer-annulus
package.
-/
theorem lowerEnvelopePatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatchAt
      C boundary F g B x J := by
  rcases hpatch with
    ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hclosedBallC,
      hboundaryOutside, hWltq, hqCont, hneg, hlowerAnnulus, _hfamilyLsc⟩
  exact ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hclosedBallC,
    hboundaryOutside, hWltq, hqCont, hneg, hlowerAnnulus⟩

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch

/--
Forget the branch lower-semicontinuity field from the legacy global
outer-annulus package.
-/
theorem lowerEnvelopePatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).lowerEnvelopePatchAt

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch

end ViscositySolns
