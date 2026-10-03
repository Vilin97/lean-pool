/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.LiftedQuadratic
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.SupStability

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Quadratic gluing data for the Perron bump step (GluingSkeleton)

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
Finite pointwise maximum, with a base branch used for the empty list.

The compact part of the Perron bump argument selects finitely many old Perron
members and then replaces them by their pointwise maximum. Keeping the base
branch explicit avoids a nonempty-list side condition in later selection
lemmas.
-/
def pointwiseMaxList (base : Point n -> Real) :
    List (Point n -> Real) -> Point n -> Real
  | [] => base
  | u :: us => fun x => Max.max (u x) (pointwiseMaxList base us x)

/--
Local quadratic active-branch gluing data at a failed lower-envelope contact.

This is the point at which the source proof's branch separation is visible:
the patched function `max old q` is locally equal either to the old Perron
member or to the lifted quadratic branch, and the lifted quadratic branch has
already been certified as a viscosity subsolution.
-/
def PerronLowerEnvelopeLocalQuadraticActiveGluingAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ κ : Real, ∃ V : Set (Point n), ∃ old : Point n -> Real,
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
        J.gradient J.hessian z
    0 < κ ∧
      V ∈ nhdsWithin x C ∧
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
          ContinuousWithinAt q C x ∧
            (∀ z : Point n, z ∈ V -> z ∈ C ->
              F z (q z)
                  (quadraticModelJetAt x J.gradient J.hessian z).gradient
                  (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0) ∧
              PerronClass C boundary F g B.lower B.upper old ∧
                ViscositySubsolution C F q ∧
                  (∀ z : Point n, z ∈ C ->
                    (q z <= old z ∧
                        ∀ᶠ y in nhdsWithin z C, q y <= old y) ∨
                      (old z <= q z ∧
                        ∀ᶠ y in nhdsWithin z C, old y <= q y)) ∧
                    BoundarySubsolutionOn boundary g
                      (fun y => Max.max (old y) (q y)) ∧
                      (∀ z : Point n, z ∈ C ∪ boundary ->
                        Max.max (old z) (q z) <= B.upper z)

/--
Local quadratic active-branch gluing data at every failed lower-envelope
subjet inequality.
-/
def PerronLowerEnvelopeLocalQuadraticActiveGluing
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticActiveGluingAt C boundary F g B x J

/--
Local quadratic gluing data stated in terms of local viscosity-subsolution
germs for the patched function.

This is the branch-separation form of the source bump construction: after the
lifted quadratic has been chosen, an old Perron-class branch is selected so
that `max old q` has local subsolution representatives, satisfies the boundary
condition, and stays below the upper barrier.
-/
def PerronLowerEnvelopeLocalQuadraticGluingAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ κ : Real, ∃ V : Set (Point n), ∃ old : Point n -> Real,
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
        J.gradient J.hessian z
    0 < κ ∧
      V ∈ nhdsWithin x C ∧
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
          ContinuousWithinAt q C x ∧
            (∀ z : Point n, z ∈ V -> z ∈ C ->
              F z (q z)
                  (quadraticModelJetAt x J.gradient J.hessian z).gradient
                  (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0) ∧
              PerronClass C boundary F g B.lower B.upper old ∧
                (∀ z : Point n, z ∈ C ->
                  ∃ v : Point n -> Real,
                    ViscositySubsolution C F v ∧
                      Max.max (old z) (q z) = v z ∧
                        (fun y => Max.max (old y) (q y)) =ᶠ[nhdsWithin z C] v) ∧
                  BoundarySubsolutionOn boundary g
                    (fun y => Max.max (old y) (q y)) ∧
                    (∀ z : Point n, z ∈ C ∪ boundary ->
                      Max.max (old z) (q z) <= B.upper z)

/--
Local quadratic gluing data at every failed lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeLocalQuadraticGluing
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticGluingAt C boundary F g B x J

/--
Local quadratic branch-gluing data at a failed lower-envelope contact.

Unlike `PerronLowerEnvelopeLocalQuadraticActiveGluingAt`, this does not ask
the lifted quadratic to be a global subsolution. It only asks for local
subsolution representatives on the region where the quadratic branch is
allowed to be active.
-/
def PerronLowerEnvelopeLocalQuadraticBranchGluingAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ κ : Real, ∃ V : Set (Point n), ∃ old : Point n -> Real,
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
        J.gradient J.hessian z
    0 < κ ∧
      V ∈ nhdsWithin x C ∧
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
          ContinuousWithinAt q C x ∧
            (∀ z : Point n, z ∈ V -> z ∈ C ->
              F z (q z)
                  (quadraticModelJetAt x J.gradient J.hessian z).gradient
                  (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0) ∧
              PerronClass C boundary F g B.lower B.upper old ∧
                (∀ z : Point n, z ∈ C -> z ∈ V ->
                  ∃ v : Point n -> Real,
                    ViscositySubsolution C F v ∧
                      q z = v z ∧
                        q =ᶠ[nhdsWithin z C] v) ∧
                  (∀ z : Point n, z ∈ C ->
                    (q z <= old z ∧
                        ∀ᶠ y in nhdsWithin z C, q y <= old y) ∨
                      (z ∈ V ∧ old z <= q z ∧
                        ∀ᶠ y in nhdsWithin z C, old y <= q y)) ∧
                    BoundarySubsolutionOn boundary g
                      (fun y => Max.max (old y) (q y)) ∧
                      (∀ z : Point n, z ∈ C ∪ boundary ->
                        Max.max (old z) (q z) <= B.upper z)

/--
Local quadratic branch-gluing data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeLocalQuadraticBranchGluing
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticBranchGluingAt C boundary F g B x J

/--
Selection data for the source patch step once the lifted quadratic has been
chosen by continuity.

For every certified local lifted quadratic, this asks for the old Perron
branch and the local branch/boundary/upper-barrier facts needed to glue the
quadratic into the Perron family.
-/
def PerronLowerEnvelopeLocalQuadraticPatchSelectionAt
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
              ∃ old : Point n -> Real,
                PerronClass C boundary F g B.lower B.upper old ∧
                  (∀ z : Point n, z ∈ C -> z ∈ V ->
                    ∃ v : Point n -> Real,
                      ViscositySubsolution C F v ∧
                        q z = v z ∧
                          q =ᶠ[nhdsWithin z C] v) ∧
                    (∀ z : Point n, z ∈ C ->
                      (q z <= old z ∧
                          ∀ᶠ y in nhdsWithin z C, q y <= old y) ∨
                        (z ∈ V ∧ old z <= q z ∧
                          ∀ᶠ y in nhdsWithin z C, old y <= q y)) ∧
                      BoundarySubsolutionOn boundary g
                        (fun y => Max.max (old y) (q y)) ∧
                        (∀ z : Point n, z ∈ C ∪ boundary ->
                          Max.max (old z) (q z) <= B.upper z)

/--
Selection data for every failed lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeLocalQuadraticPatchSelection
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticPatchSelectionAt C boundary F g B x J

/--
Compact-inactive selection data for the source bump construction.

This is a weaker and more source-shaped old-branch obligation than
`PerronLowerEnvelopeLocalQuadraticPatchSelectionAt`. The caller chooses a
compact inactive set `K` containing the points of `C` outside the active
quadratic neighborhood `V`; finite Perron selection builds one old branch
dominating the lifted quadratic near every point of `K`. Inside `V`, the max
patch is certified by taking the maximum of the old branch and the local
quadratic subsolution representative, so no branch ordering is required there.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveSelectionAt
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
                          ∃ v : Point n -> Real,
                            ViscositySubsolution C F v ∧
                              q z = v z ∧ q =ᶠ[nhdsWithin z C] v) ∧
                          ∀ old : Point n -> Real,
                            PerronClass C boundary F g B.lower B.upper old ->
                              (∀ z : Point n, z ∈ K ->
                                q z <= old z ∧
                                  ∀ᶠ y in nhdsWithin z C, q y <= old y) ->
                                BoundarySubsolutionOn boundary g
                                    (fun y => Max.max (old y) (q y)) ∧
                                  ∀ z : Point n, z ∈ C ∪ boundary ->
                                    Max.max (old z) (q z) <= B.upper z

/--
Compact-inactive selection data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveSelection
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticCompactInactiveSelectionAt
          C boundary F g B x J

/--
Compact-inactive max-patch data with genuinely local active representatives.

After the old Perron branch is selected from the compact inactive set, the
caller supplies local-domain subsolution representatives for the patched
function `max old q` on the active quadratic neighborhood. Outside the active
neighborhood, finite selection makes `max old q` locally equal to `old`.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactivePatchAt
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
                        ∀ old : Point n -> Real,
                          PerronClass C boundary F g B.lower B.upper old ->
                            (∀ z : Point n, z ∈ K ->
                              q z <= old z ∧
                                ∀ᶠ y in nhdsWithin z C, q y <= old y) ->
                              (∀ z : Point n, z ∈ C -> z ∈ V ->
                                ∃ D : Set (Point n), ∃ v : Point n -> Real,
                                  D ⊆ C ∧
                                    D ∈ nhdsWithin z C ∧
                                      ViscositySubsolution D F v ∧
                                        Max.max (old z) (q z) = v z ∧
                                          (fun y => Max.max (old y) (q y)) =ᶠ[
                                            nhdsWithin z C] v) ∧
                                BoundarySubsolutionOn boundary g
                                    (fun y => Max.max (old y) (q y)) ∧
                                  ∀ z : Point n, z ∈ C ∪ boundary ->
                                    Max.max (old z) (q z) <= B.upper z

/--
Compact-inactive local max-patch data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactivePatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticCompactInactivePatchAt
          C boundary F g B x J

/--
Compact-inactive patch data before comparison with the upper barrier.

This is the source-shaped variant of
`PerronLowerEnvelopeLocalQuadraticCompactInactivePatchAt`: after finite
selection of the old branch, the caller only has to certify that the patched
function is locally a viscosity subsolution and satisfies the boundary
subsolution inequality. The upper-barrier bound is later supplied by the
abstract Dirichlet comparison principle.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveSubsolutionPatchAt
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
                        ∀ old : Point n -> Real,
                          PerronClass C boundary F g B.lower B.upper old ->
                            (∀ z : Point n, z ∈ K ->
                              q z <= old z ∧
                                ∀ᶠ y in nhdsWithin z C, q y <= old y) ->
                              (∀ z : Point n, z ∈ C -> z ∈ V ->
                                ∃ D : Set (Point n), ∃ v : Point n -> Real,
                                  D ⊆ C ∧
                                    D ∈ nhdsWithin z C ∧
                                      ViscositySubsolution D F v ∧
                                        Max.max (old z) (q z) = v z ∧
                                          (fun y => Max.max (old y) (q y)) =ᶠ[
                                            nhdsWithin z C] v) ∧
                                BoundarySubsolutionOn boundary g
                                  (fun y => Max.max (old y) (q y))

/--
Compact-inactive local subsolution-patch data at every failed lower-envelope
subjet inequality.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveSubsolutionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticCompactInactiveSubsolutionPatchAt
          C boundary F g B x J

/--
Compact-inactive data where the active branch is the lifted quadratic itself.

Compared with `PerronLowerEnvelopeLocalQuadraticCompactInactiveSubsolutionPatchAt`,
the active input is no longer a local representative for `max old q`. Instead
it supplies a relative-open local domain on which the lifted quadratic `q`
is a viscosity subsolution; max-stability with the old Perron branch then
builds the patched local representative.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatchAt
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
                                  (∀ y : Point n, y ∈ D -> y ∈ V) ∧
                                    ViscositySubsolution D F q) ∧
                          ∀ old : Point n -> Real,
                            PerronClass C boundary F g B.lower B.upper old ->
                              BoundarySubsolutionOn boundary g
                                (fun y => Max.max (old y) (q y))

/--
Compact-inactive quadratic-active patch data at every failed lower-envelope
subjet inequality.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatchAt
          C boundary F g B x J

/--
Compact-inactive data with certified active domains for the lifted quadratic.

This is one step closer to the analytic bump construction than
`PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatchAt`: on the
active side, the caller supplies only relative-open interior domains contained
in the strict negativity region. Degenerate ellipticity and symmetric
Hessian-invariance certify the lifted quadratic as a viscosity subsolution on
those domains.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveCertifiedPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  J.hessian.IsHermitian ∧
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
                            ∀ old : Point n -> Real,
                              PerronClass C boundary F g B.lower B.upper old ->
                                BoundarySubsolutionOn boundary g
                                  (fun y => Max.max (old y) (q y))

/--
Compact-inactive certified active-domain data at every failed lower-envelope
subjet inequality.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveCertifiedPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticCompactInactiveCertifiedPatchAt
          C boundary F g B x J

/--
Compact-inactive certified active-domain data without assuming the failed jet
Hessian is already symmetric.

The active domains are the same geometric data as in
`PerronLowerEnvelopeLocalQuadraticCompactInactiveCertifiedPatchAt`, but the
quadratic subsolution certification is later applied to `symHessian J.hessian`
and transported back using `quadraticModel_symHessian`.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveSymCertifiedPatchAt
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
                          ∀ old : Point n -> Real,
                            PerronClass C boundary F g B.lower B.upper old ->
                              BoundarySubsolutionOn boundary g
                                (fun y => Max.max (old y) (q y))

/--
Compact-inactive symmetrized certified active-domain data at every failed
lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeLocalQuadraticCompactInactiveSymCertifiedPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticCompactInactiveSymCertifiedPatchAt
          C boundary F g B x J

/--
Perron-class membership can be proved from local viscosity-subsolution germs
plus the global Dirichlet and order bounds.

This is the gluing skeleton used by the localized Perron bump construction:
the analytic branch proof supplies the local representatives, while the
boundary and barrier inequalities are checked separately.
-/
theorem PerronClass.of_locally_eventuallyEq
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper u : Point n -> Real}
    (hlocal : ∀ x : Point n, x ∈ C ->
      ∃ v : Point n -> Real,
        ViscositySubsolution C F v ∧
          u x = v x ∧
            u =ᶠ[nhdsWithin x C] v)
    (hboundary : BoundarySubsolutionOn boundary g u)
    (husc : UpperSemicontinuousOn u (C ∪ boundary))
    (hlower : ∀ x : Point n, x ∈ C ∪ boundary -> lower x <= u x)
    (hupper : ∀ x : Point n, x ∈ C ∪ boundary -> u x <= upper x) :
    PerronClass C boundary F g lower upper u :=
  ⟨DirichletSubsolutionOn.of_locally_eventuallyEq hlocal hboundary husc,
    hlower, hupper⟩

/--
Perron-class membership can be proved from local-domain
viscosity-subsolution germs plus the global Dirichlet and order bounds.

Compared with `PerronClass.of_locally_eventuallyEq`, each local representative
only has to be a subsolution on a relative neighborhood of the point.
-/
theorem PerronClass.of_locally_eventuallyEqOn
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper u : Point n -> Real}
    (hlocal : ∀ x : Point n, x ∈ C ->
      ∃ D : Set (Point n), ∃ v : Point n -> Real,
        D ⊆ C ∧
          D ∈ nhdsWithin x C ∧
            ViscositySubsolution D F v ∧
              u x = v x ∧
                u =ᶠ[nhdsWithin x C] v)
    (hboundary : BoundarySubsolutionOn boundary g u)
    (husc : UpperSemicontinuousOn u (C ∪ boundary))
    (hlower : ∀ x : Point n, x ∈ C ∪ boundary -> lower x <= u x)
    (hupper : ∀ x : Point n, x ∈ C ∪ boundary -> u x <= upper x) :
    PerronClass C boundary F g lower upper u :=
  ⟨DirichletSubsolutionOn.of_locally_eventuallyEqOn hlocal hboundary husc,
    hlower, hupper⟩

/--
Local viscosity-subsolution germs for a max patch are enough to certify the
patched function as Perron-admissible, provided the upper and boundary bounds
are supplied. The lower bound follows from the old Perron-class branch.
-/
theorem PerronClass.max_patch_of_locally_eventuallyEq
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper old bump : Point n -> Real}
    (hold : PerronClass C boundary F g lower upper old)
    (hlocal : ∀ x : Point n, x ∈ C ->
      ∃ v : Point n -> Real,
        ViscositySubsolution C F v ∧
          Max.max (old x) (bump x) = v x ∧
            (fun y => Max.max (old y) (bump y)) =ᶠ[nhdsWithin x C] v)
    (hboundary :
      BoundarySubsolutionOn boundary g (fun y => Max.max (old y) (bump y)))
    (husc : UpperSemicontinuousOn (fun y => Max.max (old y) (bump y))
      (C ∪ boundary))
    (hupper : ∀ x : Point n, x ∈ C ∪ boundary ->
      Max.max (old x) (bump x) <= upper x) :
    PerronClass C boundary F g lower upper
      (fun y => Max.max (old y) (bump y)) := by
  refine PerronClass.of_locally_eventuallyEq hlocal hboundary husc ?_ hupper
  intro x hx
  exact (hold.lower_le hx).trans (le_max_left (old x) (bump x))

/--
Local-domain viscosity-subsolution germs for a max patch are enough to certify
the patched function as Perron-admissible.

This is the patching form closest to the source bump argument: in the active
ball the representative may be a subsolution only on that local ball, while
outside the ball it can be the old Perron branch.
-/
theorem PerronClass.max_patch_of_locally_eventuallyEqOn
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper old bump : Point n -> Real}
    (hold : PerronClass C boundary F g lower upper old)
    (hlocal : ∀ x : Point n, x ∈ C ->
      ∃ D : Set (Point n), ∃ v : Point n -> Real,
        D ⊆ C ∧
          D ∈ nhdsWithin x C ∧
            ViscositySubsolution D F v ∧
              Max.max (old x) (bump x) = v x ∧
                (fun y => Max.max (old y) (bump y)) =ᶠ[nhdsWithin x C] v)
    (hboundary :
      BoundarySubsolutionOn boundary g (fun y => Max.max (old y) (bump y)))
    (husc : UpperSemicontinuousOn (fun y => Max.max (old y) (bump y))
      (C ∪ boundary))
    (hupper : ∀ x : Point n, x ∈ C ∪ boundary ->
      Max.max (old x) (bump x) <= upper x) :
    PerronClass C boundary F g lower upper
      (fun y => Max.max (old y) (bump y)) := by
  refine PerronClass.of_locally_eventuallyEqOn hlocal hboundary husc ?_ hupper
  intro x hx
  exact (hold.lower_le hx).trans (le_max_left (old x) (bump x))

/--
Active-branch separation gives the local viscosity-subsolution germs needed to
certify a max patch as Perron-admissible.
-/
theorem PerronClass.max_patch_of_active_branches
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper old bump : Point n -> Real}
    (hold : PerronClass C boundary F g lower upper old)
    (hbumpSub : ViscositySubsolution C F bump)
    (hactive : ∀ x : Point n, x ∈ C ->
      (bump x <= old x ∧
          ∀ᶠ y in nhdsWithin x C, bump y <= old y) ∨
        (old x <= bump x ∧
          ∀ᶠ y in nhdsWithin x C, old y <= bump y))
    (hboundary :
      BoundarySubsolutionOn boundary g (fun y => Max.max (old y) (bump y)))
    (husc : UpperSemicontinuousOn (fun y => Max.max (old y) (bump y))
      (C ∪ boundary))
    (hupper : ∀ x : Point n, x ∈ C ∪ boundary ->
      Max.max (old x) (bump x) <= upper x) :
    PerronClass C boundary F g lower upper
      (fun y => Max.max (old y) (bump y)) := by
  refine PerronClass.max_patch_of_locally_eventuallyEq hold ?_ hboundary husc hupper
  intro x hx
  rcases hactive x hx with hOld | hBump
  · rcases hOld with ⟨hxle, hnear⟩
    refine ⟨old, hold.dirichletSubsolution.viscosity, max_eq_left hxle, ?_⟩
    filter_upwards [hnear] with y hyle
    exact max_eq_left hyle
  · rcases hBump with ⟨hxle, hnear⟩
    refine ⟨bump, hbumpSub, max_eq_right hxle, ?_⟩
    filter_upwards [hnear] with y hyle
    exact max_eq_right hyle

/-- The base branch lies below the finite pointwise maximum. -/
theorem le_pointwiseMaxList_base
    {base : Point n -> Real} {us : List (Point n -> Real)} {x : Point n} :
    base x <= pointwiseMaxList base us x := by
  induction us with
  | nil =>
      simp [pointwiseMaxList]
  | cons u us ih =>
      exact le_max_of_le_right ih

/-- Every listed branch lies below the finite pointwise maximum. -/
theorem le_pointwiseMaxList_of_mem
    {base u : Point n -> Real} {us : List (Point n -> Real)} {x : Point n}
    (hu : u ∈ us) :
    u x <= pointwiseMaxList base us x := by
  induction us with
  | nil =>
      cases hu
  | cons v us ih =>
      simp only [List.mem_cons] at hu
      rcases hu with huv | hu
      · subst huv
        simp [pointwiseMaxList]
      · exact le_max_of_le_right (ih hu)

/-- A finite pointwise maximum is bounded above if every branch is. -/
theorem pointwiseMaxList_le
    {base : Point n -> Real} {us : List (Point n -> Real)}
    {x : Point n} {a : Real}
    (hbase : base x <= a)
    (hus : ∀ u : Point n -> Real, u ∈ us -> u x <= a) :
    pointwiseMaxList base us x <= a := by
  induction us with
  | nil =>
      simpa [pointwiseMaxList] using hbase
  | cons u us ih =>
      refine max_le ?_ ?_
      · exact hus u List.mem_cons_self
      · exact ih (fun v hv => hus v (List.mem_cons_of_mem u hv))

/-- Finite pointwise maxima of Perron-class members remain Perron-admissible. -/
theorem PerronClass.pointwiseMaxList
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper base : Point n -> Real} {us : List (Point n -> Real)}
    (hbase : PerronClass C boundary F g lower upper base)
    (hus : ∀ u : Point n -> Real, u ∈ us ->
      PerronClass C boundary F g lower upper u) :
    PerronClass C boundary F g lower upper
      (ViscositySolns.pointwiseMaxList base us) := by
  induction us with
  | nil =>
      exact hbase
  | cons u us ih =>
      have hu : PerronClass C boundary F g lower upper u := by
        exact hus u List.mem_cons_self
      have hrest : PerronClass C boundary F g lower upper
          (ViscositySolns.pointwiseMaxList base us) := by
        refine ih ?_
        intro v hv
        exact hus v (List.mem_cons_of_mem u hv)
      exact hu.max hrest

/--
Finite maxima of Perron-family witnesses remain Perron-admissible.

This is the form used after compact selection has produced a finite list of
Perron-family members.
-/
theorem PerronFamily.pointwiseMaxList_mem
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper : Point n -> Real}
    (base : PerronFamily C boundary F g lower upper)
    (ws : List (PerronFamily C boundary F g lower upper)) :
    PerronClass C boundary F g lower upper
      (ViscositySolns.pointwiseMaxList base.fun (ws.map PerronFamily.fun)) := by
  refine PerronClass.pointwiseMaxList base.mem ?_
  intro u hu
  rcases List.mem_map.mp hu with ⟨w, hw, rfl⟩
  exact w.mem

/-- A listed Perron-family branch lies below the finite maximum of the list. -/
theorem PerronFamily.fun_le_pointwiseMaxList_of_mem
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper : Point n -> Real}
    {base w : PerronFamily C boundary F g lower upper}
    {ws : List (PerronFamily C boundary F g lower upper)} {x : Point n}
    (hw : w ∈ ws) :
    w.fun x <=
      ViscositySolns.pointwiseMaxList base.fun (ws.map PerronFamily.fun) x :=
  le_pointwiseMaxList_of_mem (List.mem_map.mpr ⟨w, hw, rfl⟩)

/--
Compact finite-selection step for old Perron branches.

If every point of a compact set has a local Perron-family branch dominating a
candidate `q`, then finitely many of those branches can be replaced by one old
Perron-class function dominating `q` on the whole compact set. This is the
finite-subcover core of the source Perron patch argument.
-/
theorem DirichletBarrierPair.exists_perronClass_dominate_on_isCompact
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    {K : Set (Point n)} {q : Point n -> Real}
    (hKcompact : IsCompact K)
    (hlocal : ∀ z : Point n, z ∈ K ->
      ∃ w : PerronFamily C boundary F g B.lower B.upper,
        ∀ᶠ y in nhdsWithin z K, q y <= w.fun y) :
    ∃ old : Point n -> Real,
      PerronClass C boundary F g B.lower B.upper old ∧
        ∀ y : Point n, y ∈ K -> q y <= old y := by
  classical
  choose w hw using hlocal
  let V : ∀ z : Point n, z ∈ K -> Set (Point n) :=
    fun z hz => {y : Point n | q y <= (w z hz).fun y}
  have hV : ∀ z (hz : z ∈ K), V z hz ∈ nhdsWithin z K := by
    intro z hz
    exact hw z hz
  rcases hKcompact.elim_nhdsWithin_subcover' V hV with ⟨t, hcover⟩
  let base : PerronFamily C boundary F g B.lower B.upper :=
    ⟨B.lower, B.lower_mem_perronClass⟩
  let ws : List (PerronFamily C boundary F g B.lower B.upper) :=
    t.toList.map fun z : K => w z z.2
  refine ⟨ViscositySolns.pointwiseMaxList base.fun (ws.map PerronFamily.fun),
    PerronFamily.pointwiseMaxList_mem base ws, ?_⟩
  intro y hyK
  rcases Set.mem_iUnion₂.1 (hcover hyK) with ⟨z, hzt, hyV⟩
  have hq : q y <= (w z z.2).fun y := hyV
  have hmem : w z z.2 ∈ ws := by
    exact List.mem_map.mpr ⟨z, Finset.mem_toList.mpr hzt, rfl⟩
  exact hq.trans
    (PerronFamily.fun_le_pointwiseMaxList_of_mem
      (base := base) (ws := ws) (x := y) hmem)

/--
Compact finite-selection step with eventual domination in the ambient domain.

This is the version needed by the inactive annulus in the Perron bump
construction. If every point of a compact set has a local Perron-family
branch dominating the candidate bump on that compact set, and the compact set
is itself a relative neighborhood of each point under consideration, then the
finite maximum branch dominates the bump eventually in `nhdsWithin z C`.
-/
theorem DirichletBarrierPair.exists_perronClass_eventually_dominate_on_isCompact
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    {K : Set (Point n)} {q : Point n -> Real}
    (hKcompact : IsCompact K)
    (hKnhds : ∀ z : Point n, z ∈ K -> K ∈ nhdsWithin z C)
    (hlocal : ∀ z : Point n, z ∈ K ->
      ∃ w : PerronFamily C boundary F g B.lower B.upper,
        ∀ᶠ y in nhdsWithin z K, q y <= w.fun y) :
    ∃ old : Point n -> Real,
      PerronClass C boundary F g B.lower B.upper old ∧
        ∀ z : Point n, z ∈ K ->
          q z <= old z ∧ ∀ᶠ y in nhdsWithin z C, q y <= old y := by
  rcases B.exists_perronClass_dominate_on_isCompact hKcompact hlocal with
    ⟨old, hold, hdom⟩
  refine ⟨old, hold, ?_⟩
  intro z hz
  refine ⟨hdom z hz, ?_⟩
  filter_upwards [hKnhds z hz] with y hyK
  exact hdom y hyK

/--
Approximate the Perron envelope from below at a point where the Perron-family
values are bounded above.

Unlike `DirichletBarrierPair.exists_perronClass_gt_of_lt_perronEnvelope`, this
version does not require the point to lie in `C ∪ boundary`; the needed
boundedness is supplied directly.
-/
theorem DirichletBarrierPair.exists_perronFamily_gt_of_lt_perronEnvelope_of_bddAbove
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n} {a : Real}
    (hbdd : BddAbove {r : Real | ∃ w : Point n -> Real,
      PerronClass C boundary F g B.lower B.upper w ∧ r = w x})
    (ha : a < perronEnvelope C boundary F g B.lower B.upper x) :
    ∃ w : PerronFamily C boundary F g B.lower B.upper, a < w.fun x := by
  let S : Set Real := {r : Real | ∃ w : Point n -> Real,
    PerronClass C boundary F g B.lower B.upper w ∧ r = w x}
  have hne : S.Nonempty :=
    ⟨B.lower x, B.lower, B.lower_mem_perronClass, rfl⟩
  have haS : a < sSup S := by
    simpa [perronEnvelope, S] using ha
  rcases (lt_csSup_iff hbdd hne).1 haS with ⟨r, hrS, har⟩
  rcases hrS with ⟨w, hw, rfl⟩
  exact ⟨⟨w, hw⟩, by simpa [PerronFamily.fun] using har⟩

end ViscositySolns
