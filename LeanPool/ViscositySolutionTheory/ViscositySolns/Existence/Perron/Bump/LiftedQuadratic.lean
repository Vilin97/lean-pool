/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.Definitions

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Lifted quadratic data for the Perron bump step

Continuity packages for the lifted quadratic produced at a failed lower
Perron-envelope subjet inequality.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
At a failed lower-envelope subjet inequality, operator continuity supplies a
positive vertical lift of the touching quadratic whose operator value remains
strictly negative near the contact.

This is the Perron-shaped version of the local quadratic continuity step in
Lemma 4.2. The remaining bump work is to localize/glue this lifted quadratic
against the Perron family.
-/
theorem OperatorContinuous.exists_pos_eventually_lowerEnvelope_quadratic_lift_lt_of_neg
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F)
    {x : Point n} {J : Jet n}
    (hneg :
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0) :
    ∃ κ : Real, 0 < κ ∧
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <
        quadraticModel x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
          J.gradient J.hessian x ∧
        ∀ᶠ z in nhdsWithin x C,
          F z
              (quadraticModel x
                (lowerEnvelope C
                  (perronEnvelope C boundary F g B.lower B.upper) x + κ)
                J.gradient J.hessian z)
              (quadraticModelJetAt x J.gradient J.hessian z).gradient
              (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0 := by
  let W : Point n -> Real :=
    lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)
  have hbase :
      F x (quadraticModel x (W x) J.gradient J.hessian x)
          (quadraticModelJetAt x J.gradient J.hessian x).gradient
          (quadraticModelJetAt x J.gradient J.hessian x).hessian < 0 := by
    simpa [W, quadraticModel] using hneg
  rcases hF.exists_pos_eventually_quadraticModelJetAt_lift_lt_of_lt
      (x0 := x) (r := W x) (p := J.gradient) (X := J.hessian) hbase with
    ⟨κ, hκpos, hnear⟩
  refine ⟨κ, hκpos, ?_, ?_⟩
  · simpa [W, quadraticModel] using lt_add_of_pos_right (W x) hκpos
  · exact hnear.filter_mono nhdsWithin_le_nhds

/--
At a failed lower-envelope subjet inequality, operator continuity also allows
a small downward identity-Hessian bend of the lifted quadratic.

This is the analytic continuity choice behind the source bump
`Q + δ - γ |· - x|²`: after choosing a positive vertical lift, one can choose a
positive bend parameter and still keep the operator value strictly negative in
a relative neighborhood of the contact.
-/
theorem OperatorContinuous.exists_pos_pos_eventually_lowerEnvelope_bentQuadratic_lift_lt_of_neg
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F)
    {x : Point n} (hx : x ∈ C) {J : Jet n}
    (hneg :
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0) :
    ∃ δ : Real, ∃ γ : Real, 0 < δ ∧ 0 < γ ∧
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <
        quadraticModel x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
          J.gradient (J.hessian - γ • (1 : Hessian n)) x ∧
        ∀ᶠ z in nhdsWithin x C,
          F z
              (quadraticModel x
                (lowerEnvelope C
                  (perronEnvelope C boundary F g B.lower B.upper) x + δ)
                J.gradient (J.hessian - γ • (1 : Hessian n)) z)
              (quadraticModelJetAt x J.gradient
                (J.hessian - γ • (1 : Hessian n)) z).gradient
              (quadraticModelJetAt x J.gradient
                (J.hessian - γ • (1 : Hessian n)) z).hessian < 0 := by
  let W : Point n -> Real :=
    lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)
  rcases hF.exists_pos_eventually_lowerEnvelope_quadratic_lift_lt_of_neg
      (C := C) (boundary := boundary) (g := g) (B := B) (x := x) (J := J)
      hneg with
    ⟨δ, hδpos, _hWlt, hnearδ⟩
  have hbaseδ :
      F x
          (quadraticModel x (W x + δ) J.gradient J.hessian x)
          (quadraticModelJetAt x J.gradient J.hessian x).gradient
          (quadraticModelJetAt x J.gradient J.hessian x).hessian < 0 :=
    hnearδ.self_of_nhdsWithin hx
  let A : Jet n := quadraticModelJetAt x J.gradient J.hessian x
  have hzero :
      F x (quadraticModel x (W x + δ) J.gradient
            (J.hessian - (0 : Real) • (1 : Hessian n)) x)
          (quadraticModelJetAt x J.gradient
            (J.hessian - (0 : Real) • (1 : Hessian n)) x).gradient
          (quadraticModelJetAt x J.gradient
            (J.hessian - (0 : Real) • (1 : Hessian n)) x).hessian < 0 := by
    simpa [W, A] using hbaseδ
  have hpathγ : Continuous fun γ : Real =>
      ((x,
          quadraticModel x (W x + δ) J.gradient
            (J.hessian - γ • (1 : Hessian n)) x),
        quadraticModelJetAt x J.gradient
          (J.hessian - γ • (1 : Hessian n)) x) := by
    have hH : Continuous fun γ : Real =>
        J.hessian - γ • (1 : Hessian n) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    have hJetγ : Continuous fun γ : Real =>
        ({ gradient := J.gradient, hessian := J.hessian - γ • (1 : Hessian n) } :
          Jet n) := by
      apply continuous_induced_rng.mpr
      change Continuous fun γ : Real =>
        (({ gradient := J.gradient, hessian := J.hessian - γ • (1 : Hessian n) } :
            Jet n).gradient,
          ({ gradient := J.gradient, hessian := J.hessian - γ • (1 : Hessian n) } :
            Jet n).hessian)
      simpa using Continuous.prodMk continuous_const hH
    have hval : Continuous fun γ : Real =>
        quadraticModel x (W x + δ) J.gradient
          (J.hessian - γ • (1 : Hessian n)) x := by
      exact (continuous_quadraticModel_jet x (W x + δ) x).comp hJetγ
    have hjet : Continuous fun γ : Real =>
        quadraticModelJetAt x J.gradient
          (J.hessian - γ • (1 : Hessian n)) x := by
      apply continuous_induced_rng.mpr
      change Continuous fun γ : Real =>
        ((quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).gradient,
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).hessian)
      simpa [quadraticModelJetAt] using Continuous.prodMk continuous_const hH
    exact Continuous.prodMk (Continuous.prodMk continuous_const hval) hjet
  have hcontγ : Continuous fun γ : Real =>
      F x
          (quadraticModel x (W x + δ) J.gradient
            (J.hessian - γ • (1 : Hessian n)) x)
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).gradient
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).hessian := by
    exact hF.continuous.comp hpathγ
  have hnearγ : ∀ᶠ γ in nhds (0 : Real),
      F x
          (quadraticModel x (W x + δ) J.gradient
            (J.hessian - γ • (1 : Hessian n)) x)
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).gradient
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).hessian < 0 := by
    exact hcontγ.continuousAt (isOpen_Iio.mem_nhds hzero)
  have : NeBot (nhdsWithin (0 : Real) (Set.Ioi 0)) := by infer_instance
  have hnearγWithin : ∀ᶠ γ in nhdsWithin (0 : Real) (Set.Ioi 0),
      F x
          (quadraticModel x (W x + δ) J.gradient
            (J.hessian - γ • (1 : Hessian n)) x)
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).gradient
          (quadraticModelJetAt x J.gradient
            (J.hessian - γ • (1 : Hessian n)) x).hessian < 0 :=
    hnearγ.filter_mono nhdsWithin_le_nhds
  have hposWithin : ∀ᶠ γ in nhdsWithin (0 : Real) (Set.Ioi 0),
      γ ∈ Set.Ioi (0 : Real) :=
    self_mem_nhdsWithin
  rcases (hnearγWithin.and hposWithin).exists with
    ⟨γ, hbaseBent, hγpos⟩
  refine ⟨δ, γ, hδpos, hγpos, ?_, ?_⟩
  · simpa [W, quadraticModel] using lt_add_of_pos_right (W x) hδpos
  · exact (hF.eventually_quadraticModelJetAt_lt_of_lt
      (x0 := x) (r := W x + δ) (p := J.gradient)
      (X := J.hessian - γ • (1 : Hessian n)) hbaseBent).filter_mono
        nhdsWithin_le_nhds

/--
Local lifted-quadratic data at a failed lower-envelope subjet inequality.

The data records the first analytic move in the source proof of Lemma 4.2:
after the lower-envelope viscosity inequality fails, one can lift the touching
quadratic by a positive height so that it is strictly above `W_*` at the
contact and still has strictly negative operator value in a relative
neighborhood of the contact.
-/
def PerronLowerEnvelopeLiftedQuadraticNegativeAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ κ : Real, 0 < κ ∧
    lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
        J.gradient J.hessian x ∧
      ∀ᶠ z in nhdsWithin x C,
        F z
            (quadraticModel x
              (lowerEnvelope C
                (perronEnvelope C boundary F g B.lower B.upper) x + κ)
              J.gradient J.hessian z)
            (quadraticModelJetAt x J.gradient J.hessian z).gradient
            (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0

/--
Lifted-quadratic negativity at every failed lower-envelope subjet inequality.

This is the continuity-only input to the later gluing/localization step of
Lemma 4.2.
-/
def PerronLowerEnvelopeLiftedQuadraticNegative
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLiftedQuadraticNegativeAt C boundary F g B x J

/--
Operator continuity supplies the local lifted-quadratic negativity datum at
every failed lower-envelope subjet inequality.
-/
theorem OperatorContinuous.perronLowerEnvelope_liftedQuadraticNegative
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F) :
    PerronLowerEnvelopeLiftedQuadraticNegative C boundary F g B := by
  intro _x _hx _J _hJ hneg
  exact hF.exists_pos_eventually_lowerEnvelope_quadratic_lift_lt_of_neg hneg

/--
Neighborhood-form local quadratic bump data at a failed lower-envelope
contact.

This is the same continuity output as
`PerronLowerEnvelopeLiftedQuadraticNegativeAt`, but with the relative
neighborhood made explicit. Later gluing arguments can use `V` as the region
where the lifted quadratic branch is certified to satisfy the strict
differential inequality.
-/
def PerronLowerEnvelopeLocalQuadraticBumpAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ κ : Real, ∃ V : Set (Point n),
    0 < κ ∧
      V ∈ nhdsWithin x C ∧
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <
          quadraticModel x
            (lowerEnvelope C
              (perronEnvelope C boundary F g B.lower B.upper) x + κ)
            J.gradient J.hessian x ∧
          ContinuousWithinAt
            (fun z => quadraticModel x
              (lowerEnvelope C
                (perronEnvelope C boundary F g B.lower B.upper) x + κ)
              J.gradient J.hessian z)
            C x ∧
            ∀ z : Point n, z ∈ V -> z ∈ C ->
              F z
                  (quadraticModel x
                    (lowerEnvelope C
                      (perronEnvelope C boundary F g B.lower B.upper) x + κ)
                    J.gradient J.hessian z)
                  (quadraticModelJetAt x J.gradient J.hessian z).gradient
                  (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0

/--
Neighborhood-form local quadratic bump data at every failed lower-envelope
subjet inequality.
-/
def PerronLowerEnvelopeLocalQuadraticBump
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticBumpAt C boundary F g B x J

/--
Open-neighborhood local quadratic bump data at a failed lower-envelope
contact.

This strengthens `PerronLowerEnvelopeLocalQuadraticBumpAt` by recording that
the strict-negativity neighborhood can be taken open in the ambient topology.
That openness lets later patching arguments use `C ∩ V` as the active local
domain.
-/
def PerronLowerEnvelopeLocalQuadraticOpenBumpAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ κ : Real, ∃ V : Set (Point n),
    0 < κ ∧
      IsOpen V ∧
        V ∈ nhdsWithin x C ∧
          lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <
            quadraticModel x
              (lowerEnvelope C
                (perronEnvelope C boundary F g B.lower B.upper) x + κ)
              J.gradient J.hessian x ∧
            ContinuousWithinAt
              (fun z => quadraticModel x
                (lowerEnvelope C
                  (perronEnvelope C boundary F g B.lower B.upper) x + κ)
                J.gradient J.hessian z)
              C x ∧
              ∀ z : Point n, z ∈ V -> z ∈ C ->
                F z
                    (quadraticModel x
                      (lowerEnvelope C
                        (perronEnvelope C boundary F g B.lower B.upper) x + κ)
                      J.gradient J.hessian z)
                    (quadraticModelJetAt x J.gradient J.hessian z).gradient
                    (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0

/--
Open-neighborhood local quadratic bump data at every failed lower-envelope
subjet inequality.
-/
def PerronLowerEnvelopeLocalQuadraticOpenBump
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticOpenBumpAt C boundary F g B x J

/--
Open-neighborhood bent quadratic bump data at a failed lower-envelope contact.

This is closer to the source bump than the pure lifted quadratic: the
quadratic is lifted by a positive height `δ` and bent downward by a positive
identity-Hessian amount `γ`.
-/
def PerronLowerEnvelopeBentQuadraticOpenBumpAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ δ : Real, ∃ γ : Real, ∃ V : Set (Point n),
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
                ∀ z : Point n, z ∈ V -> z ∈ C ->
                  F z (q z)
                      (quadraticModelJetAt x J.gradient Xb z).gradient
                      (quadraticModelJetAt x J.gradient Xb z).hessian < 0

/--
Open-neighborhood bent quadratic bump data at every failed lower-envelope
subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticOpenBump
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticOpenBumpAt C boundary F g B x J

/-- Open-neighborhood bump data forgets to ordinary neighborhood-form data. -/
theorem PerronLowerEnvelopeLocalQuadraticOpenBumpAt.localQuadraticBumpAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hquad : PerronLowerEnvelopeLocalQuadraticOpenBumpAt C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticBumpAt C boundary F g B x J := by
  rcases hquad with ⟨κ, V, hκpos, _hVopen, hV, hWlt, hqCont, hneg⟩
  exact ⟨κ, V, hκpos, hV, hWlt, hqCont, hneg⟩

/--
Global open-neighborhood bump data forgets to ordinary neighborhood-form
local quadratic bump data.
-/
theorem PerronLowerEnvelopeLocalQuadraticOpenBump.localQuadraticBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hquad : PerronLowerEnvelopeLocalQuadraticOpenBump C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticBump C boundary F g B := by
  intro x hx J hJ hneg
  exact (hquad x hx J hJ hneg).localQuadraticBumpAt

/--
The filter-form lifted quadratic datum supplies the explicit neighborhood-form
local quadratic bump datum.
-/
theorem PerronLowerEnvelopeLiftedQuadraticNegativeAt.localQuadraticBumpAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hquad : PerronLowerEnvelopeLiftedQuadraticNegativeAt C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticBumpAt C boundary F g B x J := by
  rcases hquad with ⟨κ, hκpos, hWlt, hnear⟩
  refine ⟨κ, {z : Point n |
    F z
        (quadraticModel x
          (lowerEnvelope C
            (perronEnvelope C boundary F g B.lower B.upper) x + κ)
          J.gradient J.hessian z)
        (quadraticModelJetAt x J.gradient J.hessian z).gradient
        (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0},
    hκpos, hnear, hWlt, ?_, ?_⟩
  · exact (continuous_quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
      J.gradient J.hessian).continuousWithinAt
  · intro z hz _hzC
    exact hz

/--
The global lifted-quadratic datum supplies the global neighborhood-form local
quadratic bump datum.
-/
theorem PerronLowerEnvelopeLiftedQuadraticNegative.localQuadraticBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hquad : PerronLowerEnvelopeLiftedQuadraticNegative C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticBump C boundary F g B := by
  intro x hx J hJ hneg
  exact (hquad x hx J hJ hneg).localQuadraticBumpAt

/--
Operator continuity supplies the explicit neighborhood-form local quadratic
bump datum at every failed lower-envelope subjet inequality.
-/
theorem OperatorContinuous.perronLowerEnvelope_localQuadraticBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F) :
    PerronLowerEnvelopeLocalQuadraticBump C boundary F g B :=
  hF.perronLowerEnvelope_liftedQuadraticNegative.localQuadraticBump

/--
Operator continuity supplies the open-neighborhood local quadratic bump datum
at every failed lower-envelope subjet inequality.
-/
theorem OperatorContinuous.perronLowerEnvelope_localQuadraticOpenBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F) :
    PerronLowerEnvelopeLocalQuadraticOpenBump C boundary F g B := by
  intro x _hx J _hJ hneg
  rcases hF.exists_pos_eventually_lowerEnvelope_quadratic_lift_lt_of_neg
      (C := C) (boundary := boundary) (g := g) (B := B) (x := x) (J := J)
      hneg with
    ⟨κ, hκpos, hWlt, hnear⟩
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
      J.gradient J.hessian z
  let negSet : Set (Point n) := {z : Point n |
    F z (q z)
        (quadraticModelJetAt x J.gradient J.hessian z).gradient
        (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0}
  have hpath : Continuous fun z : Point n =>
      ((z, q z), quadraticModelJetAt x J.gradient J.hessian z) := by
    exact Continuous.prodMk
      (Continuous.prodMk continuous_id
        (continuous_quadraticModel x
          (lowerEnvelope C
            (perronEnvelope C boundary F g B.lower B.upper) x + κ)
          J.gradient J.hessian))
      (continuous_quadraticModelJetAt x J.gradient J.hessian)
  have hcont : Continuous fun z : Point n =>
      F z (q z)
          (quadraticModelJetAt x J.gradient J.hessian z).gradient
          (quadraticModelJetAt x J.gradient J.hessian z).hessian := by
    exact hF.continuous.comp hpath
  have hnegSetOpen : IsOpen negSet := by
    exact isOpen_Iio.preimage hcont
  have hnegSetNhds : negSet ∈ nhdsWithin x C := by
    exact hnear
  refine ⟨κ, negSet, hκpos, hnegSetOpen, hnegSetNhds, ?_, ?_, ?_⟩
  · simpa [q] using hWlt
  · simpa [q] using
      (continuous_quadraticModel x
        (lowerEnvelope C
          (perronEnvelope C boundary F g B.lower B.upper) x + κ)
        J.gradient J.hessian).continuousWithinAt
  · intro z hz _hzC
    simpa [q, negSet] using hz

/--
Operator continuity supplies the open-neighborhood bent quadratic bump datum at
every failed lower-envelope subjet inequality.
-/
theorem OperatorContinuous.perronLowerEnvelope_bentQuadraticOpenBump
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F) :
    PerronLowerEnvelopeBentQuadraticOpenBump C boundary F g B := by
  intro x hx J _hJ hneg
  rcases hF.exists_pos_pos_eventually_lowerEnvelope_bentQuadratic_lift_lt_of_neg
      (C := C) (boundary := boundary) (g := g) (B := B) (x := x) hx
      (J := J) hneg with
    ⟨δ, γ, hδpos, hγpos, hWlt, hnear⟩
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let negSet : Set (Point n) := {z : Point n |
    F z (q z)
        (quadraticModelJetAt x J.gradient Xb z).gradient
        (quadraticModelJetAt x J.gradient Xb z).hessian < 0}
  have hpath : Continuous fun z : Point n =>
      ((z, q z), quadraticModelJetAt x J.gradient Xb z) := by
    exact Continuous.prodMk
      (Continuous.prodMk continuous_id
        (continuous_quadraticModel x
          (lowerEnvelope C
            (perronEnvelope C boundary F g B.lower B.upper) x + δ)
          J.gradient Xb))
      (continuous_quadraticModelJetAt x J.gradient Xb)
  have hcont : Continuous fun z : Point n =>
      F z (q z)
          (quadraticModelJetAt x J.gradient Xb z).gradient
          (quadraticModelJetAt x J.gradient Xb z).hessian := by
    exact hF.continuous.comp hpath
  have hnegSetOpen : IsOpen negSet := by
    exact isOpen_Iio.preimage hcont
  have hnegSetNhds : negSet ∈ nhdsWithin x C := by
    exact hnear
  refine ⟨δ, γ, negSet, hδpos, hγpos, hnegSetOpen, hnegSetNhds, ?_, ?_, ?_⟩
  · simpa [q, Xb] using hWlt
  · simpa [q, Xb] using
      (continuous_quadraticModel x
        (lowerEnvelope C
          (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb).continuousWithinAt
  · intro z hz _hzC
    simpa [q, Xb, negSet] using hz

end ViscositySolns
