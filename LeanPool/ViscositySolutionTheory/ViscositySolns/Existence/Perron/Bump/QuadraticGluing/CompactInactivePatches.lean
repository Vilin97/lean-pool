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

# Quadratic gluing data for the Perron bump step (CompactInactivePatches)

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
Boundary-safe symmetrized compact-inactive data.

This is the same active/inactive geometric datum as
`PerronLowerEnvelopeLocalQuadraticCompactInactiveSymCertifiedPatchAt`, but the
boundary condition is stated only for the lifted quadratic `q`. Since every
old Perron branch already satisfies the boundary subsolution inequality,
`max old q` then satisfies the boundary inequality automatically.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveBoundaryPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ κ : Real, ∀ V : Set (Point n),
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
        J.gradient J.hessian z
    0 < κ ->
      V ∈ nhdsWithin x C ->
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
          ContinuousWithinAt q C x ->
            (∀ z : Point n, z ∈ V -> z ∈ C ->
              F z (q z)
                  (quadraticModelJetAt x J.gradient J.hessian z).gradient
                  (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0) ->
              ∃ K : Set (Point n),
                IsCompact K ∧
                  (∀ z : Point n, z ∈ C -> z ∉ V -> z ∈ K) ∧
                    (∀ z : Point n, z ∈ K -> K ∈ nhdsWithin z C) ∧
                      (∀ z : Point n, z ∈ K ->
                        ∃ w : PerronFamily C boundary F g B.lower B.upper,
                          ∀ᶠ y in nhdsWithin z K, q y <= w.fun y) ∧
                        (∀ z : Point n, z ∈ C -> z ∈ V ->
                          ∃ D : Set (Point n),
                            D ⊆ C ∧
                              D ∈ nhdsWithin z C ∧
                                (∀ y : Point n, y ∈ D -> D ∈ nhdsWithin y C) ∧
                                  (∀ y : Point n, y ∈ D -> y ∈ interior D) ∧
                                    (∀ y : Point n, y ∈ D -> y ∈ V)) ∧
                          BoundarySubsolutionOn boundary g q

/--
Boundary-safe symmetrized compact-inactive data at every failed lower-envelope
subjet inequality.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveBoundaryPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticCompactInactiveBoundaryPatchAt
          C boundary F g B x J

/--
Compact-inactive data whose inactive compact also covers the boundary.

After finite Perron selection, the selected old branch dominates the lifted
quadratic on the whole inactive compact. The extra boundary cover therefore
makes the max patch equal to the old Perron branch on the boundary, so the
boundary subsolution inequality needs no separate check for `q`.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveCoveredPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ κ : Real, ∀ V : Set (Point n),
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
        J.gradient J.hessian z
    0 < κ ->
      V ∈ nhdsWithin x C ->
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
          ContinuousWithinAt q C x ->
            (∀ z : Point n, z ∈ V -> z ∈ C ->
              F z (q z)
                  (quadraticModelJetAt x J.gradient J.hessian z).gradient
                  (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0) ->
              ∃ K : Set (Point n),
                IsCompact K ∧
                  (∀ z : Point n, z ∈ C -> z ∉ V -> z ∈ K) ∧
                    (∀ z : Point n, z ∈ boundary -> z ∈ K) ∧
                      (∀ z : Point n, z ∈ K -> K ∈ nhdsWithin z C) ∧
                        (∀ z : Point n, z ∈ K ->
                          ∃ w : PerronFamily C boundary F g B.lower B.upper,
                            ∀ᶠ y in nhdsWithin z K, q y <= w.fun y) ∧
                          ∀ z : Point n, z ∈ C -> z ∈ V ->
                            ∃ D : Set (Point n),
                              D ⊆ C ∧
                                D ∈ nhdsWithin z C ∧
                                  (∀ y : Point n, y ∈ D -> D ∈ nhdsWithin y C) ∧
                                    (∀ y : Point n, y ∈ D -> y ∈ interior D) ∧
                                      (∀ y : Point n, y ∈ D -> y ∈ V)

/--
Boundary-covered compact-inactive data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveCoveredPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticCompactInactiveCoveredPatchAt
          C boundary F g B x J

/--
Compact-inactive data whose inactive compact covers the exterior of the active
quadratic neighborhood in `C ∪ boundary`.

This is closer to the source proof: the active bump is chosen away from the
Dirichlet boundary, and the inactive compact covers every point of the domain
or boundary outside the active neighborhood. The boundary-covered interface is
then obtained by applying the boundary-away field.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveExteriorPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ κ : Real, ∀ V : Set (Point n),
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
        J.gradient J.hessian z
    0 < κ ->
      V ∈ nhdsWithin x C ->
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
          ContinuousWithinAt q C x ->
            (∀ z : Point n, z ∈ V -> z ∈ C ->
              F z (q z)
                  (quadraticModelJetAt x J.gradient J.hessian z).gradient
                  (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0) ->
              ∃ K : Set (Point n),
                IsCompact K ∧
                  (∀ z : Point n, z ∈ C ∪ boundary -> z ∉ V -> z ∈ K) ∧
                    (∀ z : Point n, z ∈ boundary -> z ∉ V) ∧
                      (∀ z : Point n, z ∈ K -> K ∈ nhdsWithin z C) ∧
                        (∀ z : Point n, z ∈ K ->
                          ∃ w : PerronFamily C boundary F g B.lower B.upper,
                            ∀ᶠ y in nhdsWithin z K, q y <= w.fun y) ∧
                          ∀ z : Point n, z ∈ C -> z ∈ V ->
                            ∃ D : Set (Point n),
                              D ⊆ C ∧
                                D ∈ nhdsWithin z C ∧
                                  (∀ y : Point n, y ∈ D -> D ∈ nhdsWithin y C) ∧
                                    (∀ y : Point n, y ∈ D -> y ∈ interior D) ∧
                                      (∀ y : Point n, y ∈ D -> y ∈ V)

/--
Exterior compact-inactive data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveExteriorPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticCompactInactiveExteriorPatchAt
          C boundary F g B x J

/--
Exterior compact-inactive data using the lower barrier as the inactive branch.

This is the source-style annulus input: outside the active quadratic
neighborhood, the lifted quadratic is locally below the lower barrier. Since
the lower barrier is itself a Perron-family member, this discharges the local
Perron-branch selection field required by
`PerronLowerEnvelopeLocalQuadraticCompactInactiveExteriorPatchAt`.
-/
def PerronLowerEnvelopeLocalQuadraticBarrierExteriorPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ κ : Real, ∀ V : Set (Point n),
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
        J.gradient J.hessian z
    0 < κ ->
      V ∈ nhdsWithin x C ->
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
          ContinuousWithinAt q C x ->
            (∀ z : Point n, z ∈ V -> z ∈ C ->
              F z (q z)
                  (quadraticModelJetAt x J.gradient J.hessian z).gradient
                  (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0) ->
              ∃ K : Set (Point n),
                IsCompact K ∧
                  (∀ z : Point n, z ∈ C ∪ boundary -> z ∉ V -> z ∈ K) ∧
                    (∀ z : Point n, z ∈ boundary -> z ∉ V) ∧
                      (∀ z : Point n, z ∈ K -> K ∈ nhdsWithin z C) ∧
                        (∀ z : Point n, z ∈ K ->
                          ∀ᶠ y in nhdsWithin z K, q y <= B.lower y) ∧
                          ∀ z : Point n, z ∈ C -> z ∈ V ->
                            ∃ D : Set (Point n),
                              D ⊆ C ∧
                                D ∈ nhdsWithin z C ∧
                                  (∀ y : Point n, y ∈ D -> D ∈ nhdsWithin y C) ∧
                                    (∀ y : Point n, y ∈ D -> y ∈ interior D) ∧
                                      (∀ y : Point n, y ∈ D -> y ∈ V)

/--
Lower-barrier exterior compact-inactive data at every failed lower-envelope
subjet inequality.
-/
def PerronLowerEnvelopeLocalQuadraticBarrierExteriorPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticBarrierExteriorPatchAt
          C boundary F g B x J

/--
Open-active lower-barrier exterior data.

This is the source-shaped annulus input for the bump produced directly by
operator continuity: it only has to handle open active neighborhoods `V`, and
therefore does not carry the local active-domain field. When `C` is open, the
active domain is supplied later by `C ∩ V`.
-/
def PerronLowerEnvelopeLocalQuadraticOpenBarrierExteriorPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ κ : Real, ∀ V : Set (Point n),
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
        J.gradient J.hessian z
    0 < κ ->
      IsOpen V ->
        V ∈ nhdsWithin x C ->
          lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
            ContinuousWithinAt q C x ->
              (∀ z : Point n, z ∈ V -> z ∈ C ->
                F z (q z)
                    (quadraticModelJetAt x J.gradient J.hessian z).gradient
                    (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0) ->
                ∃ K : Set (Point n),
                  IsCompact K ∧
                    (∀ z : Point n, z ∈ C ∪ boundary -> z ∉ V -> z ∈ K) ∧
                      (∀ z : Point n, z ∈ boundary -> z ∉ V) ∧
                        (∀ z : Point n, z ∈ K -> K ∈ nhdsWithin z C) ∧
                          ∀ z : Point n, z ∈ K ->
                            ∀ᶠ y in nhdsWithin z K, q y <= B.lower y

/--
Open-active lower-barrier exterior data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeLocalQuadraticOpenBarrierExteriorPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticOpenBarrierExteriorPatchAt
          C boundary F g B x J

/--
Open-active exterior data for the bent source quadratic.

Compared with `PerronLowerEnvelopeLocalQuadraticOpenBarrierExteriorPatchAt`,
the active branch is the lifted and downward-bent quadratic
`J.hessian - γ • I`. This matches the quadratic used in the source annulus
argument.
-/
def PerronLowerEnvelopeBentQuadraticOpenBarrierExteriorPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ δ γ : Real, ∀ V : Set (Point n),
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < δ ->
      0 < γ ->
        IsOpen V ->
          V ∈ nhdsWithin x C ->
            lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
              ContinuousWithinAt q C x ->
                (∀ z : Point n, z ∈ V -> z ∈ C ->
                  F z (q z)
                      (quadraticModelJetAt x J.gradient Xb z).gradient
                      (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ->
                  ∃ K : Set (Point n),
                    IsCompact K ∧
                      (∀ z : Point n, z ∈ C ∪ boundary -> z ∉ V -> z ∈ K) ∧
                        (∀ z : Point n, z ∈ boundary -> z ∉ V) ∧
                          (∀ z : Point n, z ∈ K -> K ∈ nhdsWithin z C) ∧
                            ∀ z : Point n, z ∈ K ->
                              ∀ᶠ y in nhdsWithin z K, q y <= B.lower y

/--
Bent open-active exterior data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeBentQuadraticOpenBarrierExteriorPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticOpenBarrierExteriorPatchAt
          C boundary F g B x J

/--
Bent quadratic max-patch data at a failed lower-envelope contact.

This endpoint is intentionally independent of
`PerronLowerEnvelopeLocalQuadraticMaxPatchAt`, whose public payload records
the unbent Hessian `J.hessian`. The bent patch still feeds the generic Perron
contradiction through `PerronLowerEnvelopeStrictLocalPatchAt`.
-/
def PerronLowerEnvelopeBentQuadraticMaxPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ δ : Real, ∃ γ : Real, ∃ V : Set (Point n), ∃ old : Point n -> Real,
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < δ ∧
      0 < γ ∧
        V ∈ nhdsWithin x C ∧
          lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
            ContinuousWithinAt q C x ∧
              PerronClass C boundary F g B.lower B.upper old ∧
                PerronClass C boundary F g B.lower B.upper
                  (fun z => Max.max (old z) (q z))

/--
Bent quadratic max-patch data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeBentQuadraticMaxPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticMaxPatchAt C boundary F g B x J

/--
Localized lower-barrier piecewise patch data for the bent source quadratic.

The outside branch is the lower barrier itself. The caller supplies a patched
function which is locally `max lower q` on the active neighborhood and locally
the lower barrier off that neighborhood. This is the Lean-facing form of the
source piecewise definition.
-/
def PerronLowerEnvelopeBentQuadraticLocalizedLowerPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ δ γ : Real, ∀ V : Set (Point n),
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < δ ->
      0 < γ ->
        IsOpen V ->
          V ∈ nhdsWithin x C ->
            lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
              ContinuousWithinAt q C x ->
                (∀ z : Point n, z ∈ V -> z ∈ C ->
                  F z (q z)
                      (quadraticModelJetAt x J.gradient Xb z).gradient
                      (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ->
                  ∃ patched : Point n -> Real,
                    (∀ z : Point n, z ∈ C -> z ∈ V ->
                      patched =ᶠ[nhdsWithin z C]
                        (fun y => Max.max (B.lower y) (q y))) ∧
                      (∀ z : Point n, z ∈ C -> z ∉ V ->
                        patched =ᶠ[nhdsWithin z C] B.lower) ∧
                        (∀ z : Point n, z ∈ boundary ->
                          patched z = B.lower z) ∧
                                (∀ z ∈ boundary, UpperSemicontinuousWithinAt patched
                                  (C ∪ boundary) z) ∧
                          ∀ z : Point n, z ∈ C ∪ boundary ->
                            B.lower z <= patched z

/--
Localized lower-barrier piecewise patch data at every failed lower-envelope
subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticLocalizedLowerPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticLocalizedLowerPatchAt
          C boundary F g B x J

/--
Open patch-set data for the localized bent source quadratic.

The caller supplies an open patch region `P` containing the active
strict-negativity neighborhood `V`. Openness makes `P` a relative
neighborhood of every active point, so only the inactive and boundary
lower-barrier domination estimates remain.
-/
def PerronLowerEnvelopeBentQuadraticOpenPiecewisePatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ δ γ : Real, ∀ V : Set (Point n),
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < δ ->
      0 < γ ->
        IsOpen V ->
          V ∈ nhdsWithin x C ->
            lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
              ContinuousWithinAt q C x ->
                (∀ z : Point n, z ∈ V -> z ∈ C ->
                  F z (q z)
                      (quadraticModelJetAt x J.gradient Xb z).gradient
                      (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ->
                  ∃ P : Set (Point n),
                    IsOpen P ∧
                      (∀ z : Point n, z ∈ V -> z ∈ P) ∧
                        (∀ z : Point n, z ∈ C -> z ∉ V ->
                          ∀ᶠ y in nhdsWithin z C, y ∉ P ∨ q y <= B.lower y) ∧
                          ∀ z : Point n, z ∈ boundary ->
                            z ∉ closure P ∨ q z <= B.lower z

/--
Open patch-set data at every failed lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticOpenPiecewisePatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticOpenPiecewisePatchAt
          C boundary F g B x J

/--
Boundary-away open patch-set data for the localized bent source quadratic.

This is the direct source shape when the patch region is chosen strictly inside
the domain: the open patch set contains the active neighborhood, is disjoint
from the Dirichlet boundary, and satisfies lower-barrier domination wherever
points of `C` lie outside the active neighborhood.
-/
def PerronLowerEnvelopeBentQuadraticBoundaryAwayOpenPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ δ γ : Real, ∀ V : Set (Point n),
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < δ ->
      0 < γ ->
        IsOpen V ->
          V ∈ nhdsWithin x C ->
            lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
              ContinuousWithinAt q C x ->
                (∀ z : Point n, z ∈ V -> z ∈ C ->
                  F z (q z)
                      (quadraticModelJetAt x J.gradient Xb z).gradient
                      (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ->
                  ∃ P : Set (Point n),
                    IsOpen P ∧
                      (∀ z : Point n, z ∈ V -> z ∈ P) ∧
                        (∀ z : Point n, z ∈ C -> z ∉ V ->
                          ∀ᶠ y in nhdsWithin z C, y ∉ P ∨ q y <= B.lower y) ∧
                          ∀ z : Point n, z ∈ boundary -> z ∉ closure P

/--
Boundary-away open patch-set data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeBentQuadraticBoundaryAwayOpenPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticBoundaryAwayOpenPatchAt
          C boundary F g B x J

/--
Ball patch data for the localized bent source quadratic.

This is the ball-shaped source patch: the patch region is the open metric ball
`Metric.ball x r`, it contains the active strict-negativity neighborhood `V`,
it is disjoint from the Dirichlet boundary, and the bent quadratic is locally
below the lower barrier whenever a point of `C` lies outside `V`.
-/
def PerronLowerEnvelopeBentQuadraticBallPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ δ γ : Real, ∀ V : Set (Point n),
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < δ ->
      0 < γ ->
        IsOpen V ->
          V ∈ nhdsWithin x C ->
            lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
              ContinuousWithinAt q C x ->
                (∀ z : Point n, z ∈ V -> z ∈ C ->
                  F z (q z)
                      (quadraticModelJetAt x J.gradient Xb z).gradient
                      (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ->
                  ∃ r : Real,
                    0 < r ∧
                      (∀ z : Point n, z ∈ V -> z ∈ Metric.ball x r) ∧
                        (∀ z : Point n, z ∈ C -> z ∉ V ->
                          ∀ᶠ y in nhdsWithin z C,
                            y ∉ Metric.ball x r ∨ q y <= B.lower y) ∧
                          ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Ball patch data at every failed lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticBallPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticBallPatchAt C boundary F g B x J

/--
Closed-ball annulus data for the localized bent source quadratic.

The patch region is still the open ball `Metric.ball x r`, but the inactive
estimate only needs to be supplied on the closed ball. Points outside the
closed ball are automatically eventually outside the open patch ball.
-/
def PerronLowerEnvelopeBentQuadraticClosedBallAnnulusPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ δ γ : Real, ∀ V : Set (Point n),
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < δ ->
      0 < γ ->
        IsOpen V ->
          V ∈ nhdsWithin x C ->
            lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
              ContinuousWithinAt q C x ->
                (∀ z : Point n, z ∈ V -> z ∈ C ->
                  F z (q z)
                      (quadraticModelJetAt x J.gradient Xb z).gradient
                      (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ->
                  ∃ r : Real,
                    0 < r ∧
                      (∀ z : Point n, z ∈ V -> z ∈ Metric.ball x r) ∧
                        (∀ z : Point n, z ∈ C -> z ∉ V ->
                          z ∈ Metric.closedBall x r ->
                            ∀ᶠ y in nhdsWithin z C, q y <= B.lower y) ∧
                          ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Closed-ball annulus data at every failed lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticClosedBallAnnulusPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticClosedBallAnnulusPatchAt
          C boundary F g B x J

/--
Shrinkable localized lower-barrier piecewise patch data for the bent source
quadratic.

The strict-negativity neighborhood `V` comes from operator continuity. The
actual patch region `P` may be a smaller open relative neighborhood of the
contact point contained in `V`; this matches the source proof, which shrinks
to a ball before patching.
-/
def PerronLowerEnvelopeBentQuadraticShrinkingLocalizedLowerPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ δ γ : Real, ∀ V : Set (Point n),
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < δ ->
      0 < γ ->
        IsOpen V ->
          V ∈ nhdsWithin x C ->
            lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
              ContinuousWithinAt q C x ->
                (∀ z : Point n, z ∈ V -> z ∈ C ->
                  F z (q z)
                      (quadraticModelJetAt x J.gradient Xb z).gradient
                      (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ->
                  ∃ P : Set (Point n), ∃ patched : Point n -> Real,
                    IsOpen P ∧
                      P ∈ nhdsWithin x C ∧
                        (∀ z : Point n, z ∈ P -> z ∈ V) ∧
                          (∀ z : Point n, z ∈ C -> z ∈ P ->
                            patched =ᶠ[nhdsWithin z C]
                              (fun y => Max.max (B.lower y) (q y))) ∧
                            (∀ z : Point n, z ∈ C -> z ∉ P ->
                              patched =ᶠ[nhdsWithin z C] B.lower) ∧
                              (∀ z : Point n, z ∈ boundary ->
                                patched z = B.lower z) ∧
                                (∀ z ∈ boundary, UpperSemicontinuousWithinAt patched
                                  (C ∪ boundary) z) ∧
                                ∀ z : Point n, z ∈ C ∪ boundary ->
                                  B.lower z <= patched z

/--
Shrinkable localized lower-barrier patch data at every failed lower-envelope
subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticShrinkingLocalizedLowerPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticShrinkingLocalizedLowerPatchAt
          C boundary F g B x J

/--
Shrinking closed-ball annulus data for the localized bent source quadratic.

The chosen ball is contained in the operator-continuity neighborhood `V`.
Lower-barrier domination is required only on the closed-ball annulus outside
the open patch ball; outside the closed ball, metric separation makes the
patch locally inactive.
-/
def PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ δ γ : Real, ∀ V : Set (Point n),
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < δ ->
      0 < γ ->
        IsOpen V ->
          V ∈ nhdsWithin x C ->
            lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
              ContinuousWithinAt q C x ->
                (∀ z : Point n, z ∈ V -> z ∈ C ->
                  F z (q z)
                      (quadraticModelJetAt x J.gradient Xb z).gradient
                      (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ->
                  ∃ r : Real,
                    0 < r ∧
                      (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
                        (∀ z : Point n, z ∈ C -> z ∉ Metric.ball x r ->
                          z ∈ Metric.closedBall x r ->
                            ∀ᶠ y in nhdsWithin z C, q y <= B.lower y) ∧
                          ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Shrinking closed-ball annulus data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatchAt
          C boundary F g B x J

/--
Small-radius closed-ball annulus data for the localized bent source quadratic.

The analytic estimates are required only below some positive radius bound.
The bridge to the shrinkable annulus package intersects this bound with the
radius forced by the open strict-negativity neighborhood supplied by operator
continuity.
-/
def PerronLowerEnvelopeBentQuadraticSmallRadiusClosedBallAnnulusPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ δ γ : Real, ∀ V : Set (Point n),
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < δ ->
      0 < γ ->
        IsOpen V ->
          V ∈ nhdsWithin x C ->
            lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
              ContinuousWithinAt q C x ->
                (∀ z : Point n, z ∈ V -> z ∈ C ->
                  F z (q z)
                      (quadraticModelJetAt x J.gradient Xb z).gradient
                      (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ->
                  ∃ ρ : Real,
                    0 < ρ ∧
                      ∀ r : Real, 0 < r -> r <= ρ ->
                        (∀ z : Point n, z ∈ C -> z ∉ Metric.ball x r ->
                          z ∈ Metric.closedBall x r ->
                            ∀ᶠ y in nhdsWithin z C, q y <= B.lower y) ∧
                          ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Small-radius closed-ball annulus data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeBentQuadraticSmallRadiusClosedBallAnnulusPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSmallRadiusClosedBallAnnulusPatchAt
          C boundary F g B x J

/--
Chosen localized lower-barrier patch data for one bent lifted quadratic.

Unlike the compatibility interfaces above, this is existential in the lift,
bend, active neighborhood, and patch set. It is the right target for the
source proof, where the lift is chosen together with the patch radius.
-/
def PerronLowerEnvelopeBentQuadraticChosenLocalizedLowerPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ δ : Real, ∃ γ : Real, ∃ V : Set (Point n),
    ∃ P : Set (Point n), ∃ patched : Point n -> Real,
      let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
      let q : Point n -> Real := fun z =>
        quadraticModel x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
          J.gradient Xb z
      0 < δ ∧
        0 < γ ∧
          IsOpen V ∧
            V ∈ nhdsWithin x C ∧
              lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                ContinuousWithinAt q C x ∧
                  (∀ z : Point n, z ∈ V -> z ∈ C ->
                    F z (q z)
                        (quadraticModelJetAt x J.gradient Xb z).gradient
                        (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                    IsOpen P ∧
                      P ∈ nhdsWithin x C ∧
                        (∀ z : Point n, z ∈ P -> z ∈ V) ∧
                          (∀ z : Point n, z ∈ C -> z ∈ P ->
                            patched =ᶠ[nhdsWithin z C]
                              (fun y => Max.max (B.lower y) (q y))) ∧
                            (∀ z : Point n, z ∈ C -> z ∉ P ->
                              patched =ᶠ[nhdsWithin z C] B.lower) ∧
                              (∀ z : Point n, z ∈ boundary ->
                                patched z = B.lower z) ∧
                                (∀ z ∈ boundary, UpperSemicontinuousWithinAt patched
                                  (C ∪ boundary) z) ∧
                                ∀ z : Point n, z ∈ C ∪ boundary ->
                                  B.lower z <= patched z

/--
Chosen localized lower-barrier patch data at every failed lower-envelope
subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticChosenLocalizedLowerPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticChosenLocalizedLowerPatchAt
          C boundary F g B x J

/--
Source-radius closed-ball annulus data for the localized bent quadratic.

This matches the expanded source proof: the vertical lift is tied to the patch
radius by `δ = γ * r ^ 2 / 8`, and lower-barrier domination is only needed on
the closed-ball sphere where the open patch ball becomes inactive.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedBallAnnulusPatchAt
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
                    (∀ z : Point n, z ∈ C -> z ∉ Metric.ball x r ->
                      z ∈ Metric.closedBall x r ->
                        ∀ᶠ y in nhdsWithin z C, q y <= B.lower y) ∧
                      ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Source-radius closed-ball annulus data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedBallAnnulusPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceClosedBallAnnulusPatchAt
          C boundary F g B x J

/--
Outside a closed metric ball, one is eventually outside the corresponding
open ball, even relative to an arbitrary set `C`.
-/
theorem eventually_not_mem_ball_of_not_mem_closedBall
    {C : Set (Point n)} {x z : Point n} {r : Real}
    (hz : z ∉ Metric.closedBall x r) :
    ∀ᶠ y in nhdsWithin z C, y ∉ Metric.ball x r := by
  have hdist : r < dist z x := by
    simpa [Metric.mem_closedBall, not_le] using hz
  let ε : Real := (dist z x - r) / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hball : Metric.ball z ε ∈ nhdsWithin z C :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hεpos)
  filter_upwards [hball] with y hyz hyx
  have hyz' : dist z y < ε := by
    simpa [Metric.mem_ball, dist_comm] using hyz
  have hyx' : dist y x < r := by
    simpa [Metric.mem_ball] using hyx
  have htri : dist z x <= dist z y + dist y x := dist_triangle z y x
  have hlt : dist z x < ε + r :=
    lt_of_le_of_lt htri (add_lt_add hyz' hyx')
  have hcontra : ε + r < dist z x := by
    dsimp [ε]
    linarith
  linarith

/--
Exterior compact-inactive data supplies the boundary-covered compact-inactive
datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticCompactInactiveExteriorPatchAt.coveredPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveExteriorPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticCompactInactiveCoveredPatchAt
      C boundary F g B x J := by
  intro κ V q hκpos hV hWltq hqCont hneg
  rcases hpatch κ V hκpos hV hWltq hqCont hneg with
    ⟨K, hKcompact, hcover, hboundaryAway, hKnhds, hlocalOld, hactive⟩
  refine ⟨K, hKcompact, ?_, ?_, hKnhds, hlocalOld, hactive⟩
  · intro z hz hzV
    exact hcover z (Or.inl hz) hzV
  · intro z hz
    exact hcover z (Or.inr hz) (hboundaryAway z hz)

/--
Global exterior compact-inactive data supplies global boundary-covered
compact-inactive data.
-/
theorem PerronLowerEnvelopeLocalQuadraticCompactInactiveExteriorPatch.coveredPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveExteriorPatch C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticCompactInactiveCoveredPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).coveredPatchAt

/-- Near a point outside an open ball, points inside the ball lie in its outer annulus. -/
theorem eventually_not_mem_ball_or_mem_outerAnnulus
    {C : Set (Point n)} {x z : Point n} {r : Real}
    (hr : 0 < r) (hzNotBall : z ∉ Metric.ball x r) :
    ∀ᶠ y in nhdsWithin z C, y ∉ Metric.ball x r ∨
      (3 * r / 4 ≤ dist y x ∧ dist y x ≤ r) := by
  by_cases hzClosed : z ∈ Metric.closedBall x r
  · have hzle : dist z x <= r := by
      simpa [Metric.mem_closedBall] using hzClosed
    have hrle : r <= dist z x := by
      simpa [Metric.mem_ball, not_lt] using hzNotBall
    have hdist_eq : dist z x = r := le_antisymm hzle hrle
    let ε : Real := r / 4
    have hεpos : 0 < ε := by
      dsimp [ε]
      linarith
    have hball : Metric.ball z ε ∈ nhdsWithin z C :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hεpos)
    filter_upwards [hball] with y hyz
    by_cases hyOutside : y ∉ Metric.ball x r
    · exact Or.inl hyOutside
    · have hyBall : y ∈ Metric.ball x r := not_not.mp hyOutside
      have hyUpperLt : dist y x < r := by
        simpa [Metric.mem_ball] using hyBall
      have hyUpper : dist y x <= r := le_of_lt hyUpperLt
      have hyz' : dist z y < ε := by
        simpa [Metric.mem_ball, dist_comm] using hyz
      have htri : dist z x <= dist z y + dist y x := dist_triangle z y x
      have hlt : r < ε + dist y x := by
        have hltAdd : dist z y + dist y x < ε + dist y x := by
          linarith
        have hlt' : dist z x < ε + dist y x :=
          lt_of_le_of_lt htri hltAdd
        simpa [hdist_eq] using hlt'
      have hyLower : 3 * r / 4 <= dist y x := by
        dsimp [ε] at hlt
        linarith
      exact Or.inr (And.intro hyLower hyUpper)
  · filter_upwards
      [eventually_not_mem_ball_of_not_mem_closedBall
        (C := C) (x := x) (z := z) (r := r) hzClosed] with y hy
    have hyP : y ∉ Metric.ball x r := by
      exact hy
    exact Or.inl hyP

end ViscositySolns
