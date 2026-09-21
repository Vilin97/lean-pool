/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurck
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeTransport
/-!
# First gauge-reduction wrappers for Ricci flow

This internal file specializes the generic transport primitives from
`GaugeTransport.lean` to the intrinsic DeTurck vector field. It packages
DeTurck-specific gauge-flow objects, the corresponding initial-time pullback
lemmas, and the first Levi-Civita/Ricci transport consequences needed by the
Ricci-flow gauge-reduction bridge.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace ChosenIntrinsicDeTurckLocalExistenceUniqueness

/-- Fixed `C³` pullback transports the chosen-background Ricci-DeTurck theorem package by
converting through the intrinsic Ricci-flow package. -/
noncomputable def pullbackByDiffeomorph3
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M)) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ) :=
  (IntrinsicLocalExistenceUniqueness.pullbackByDiffeomorph3
    (I := I) (M := M) (pkg.toIntrinsic) φ).toChosenIntrinsicDeTurck

/-- Metric uniqueness in a chosen-background Ricci-DeTurck theorem package transports to arbitrary
local solutions of the pulled-back initial data. -/
theorem pullbackByDiffeomorph3_unique_metric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ))
    {t : ℝ}
    (ht : t ∈ Set.Icc (ivp.pullbackByDiffeomorph3 φ).initialTime
      (min sol₁.1.terminalTime sol₂.1.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v :=
  (pkg.pullbackByDiffeomorph3 φ).unique_metric sol₁ sol₂ t ht x u v

/-- Connection uniqueness in a chosen-background Ricci-DeTurck theorem package transports to
arbitrary local solutions of the pulled-back initial data. -/
theorem pullbackByDiffeomorph3_unique_connection
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (φ : SmoothSelfDiffeomorph3 (I := I) (M := M))
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M)
      (ivp.pullbackByDiffeomorph3 φ))
    {t : ℝ}
    (ht : t ∈ Set.Icc (ivp.pullbackByDiffeomorph3 φ).initialTime
      (min sol₁.1.terminalTime sol₂.1.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.1.canonicalConnection
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
      sol₂.1.canonicalConnection
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2) t σ x :=
  chosenIntrinsicDeTurckLocalExistenceUniqueness_connection_eq_on_common_interval
    (I := I) (M := M) (pkg.pullbackByDiffeomorph3 φ) sol₁ sol₂ ht hσ

end ChosenIntrinsicDeTurckLocalExistenceUniqueness

/-- The time-dependent vector field driving the intrinsic DeTurck pullback gauge.

This is the reverse DeTurck vector field: differentiating a pullback by this
flow subtracts the DeTurck Lie-derivative correction from the source
Ricci-DeTurck velocity. -/
abbrev intrinsicDeTurckGaugeField
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M)) :
    CovariantDerivative.TimeDependentVectorField (I := I) (M := M) :=
  fun t x ↦ -intrinsicDeTurckVectorField (I := I) (M := M) g background t x

/-- Pointwise differentiability of the intrinsic DeTurck vector field transfers
to the reverse gauge field. -/
theorem intrinsicDeTurckGaugeField_mdiffAt_of_intrinsicDeTurckVectorField_mdiffAt
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M}
    (hW : MDiffAt (T%
      (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) x) :
    MDiffAt (T%
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background t)) x := by
  simpa [intrinsicDeTurckGaugeField] using mdifferentiableAt_neg_section hW

/-- Global version of
`intrinsicDeTurckGaugeField_mdiffAt_of_intrinsicDeTurckVectorField_mdiffAt`. -/
theorem intrinsicDeTurckGaugeField_mdiff_of_intrinsicDeTurckVectorField_mdiff
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    {t : ℝ}
    (hW : MDiff (T%
      (intrinsicDeTurckVectorField (I := I) (M := M) g background t))) :
    MDiff (T%
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background t)) := by
  intro x
  exact intrinsicDeTurckGaugeField_mdiffAt_of_intrinsicDeTurckVectorField_mdiffAt
    (I := I) (M := M) g background (hW x)

/-- Smooth-background specialization of
`intrinsicDeTurckGaugeField_mdiffAt_of_intrinsicDeTurckVectorField_mdiffAt`. -/
theorem intrinsicDeTurckGaugeField_mdiffAt_of_contMDiffCovariantDerivative_background
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x : M) :
    MDiffAt (T%
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background t)) x := by
  exact intrinsicDeTurckGaugeField_mdiffAt_of_intrinsicDeTurckVectorField_mdiffAt
    (I := I) (M := M) g background
    (intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivative_background
      (I := I) (M := M) g background t hbackground x)

/-- Global smooth-background specialization of
`intrinsicDeTurckGaugeField_mdiff_of_intrinsicDeTurckVectorField_mdiff`. -/
theorem intrinsicDeTurckGaugeField_mdiff_of_contMDiffCovariantDerivative_background
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    MDiff (T%
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background t)) := by
  intro x
  exact intrinsicDeTurckGaugeField_mdiffAt_of_contMDiffCovariantDerivative_background
    (I := I) (M := M) g background t hbackground x

/-- With a Levi-Civita background, the reverse intrinsic DeTurck gauge field
vanishes. -/
theorem intrinsicDeTurckGaugeField_eq_zero_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    intrinsicDeTurckGaugeField (I := I) (M := M) g background = 0 := by
  funext t x
  have hW :
      intrinsicDeTurckVectorField (I := I) (M := M) g background = 0 :=
    intrinsicDeTurckVectorField_eq_zero_of_isLeviCivita
      (I := I) (M := M) g background hbackground
  simpa [intrinsicDeTurckGaugeField] using congrFun (congrFun hW t) x

/-- With a Levi-Civita background, the reverse intrinsic DeTurck gauge field
has the pointwise differentiability required by gauge-flow arguments. -/
theorem intrinsicDeTurckGaugeField_mdiffAt_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background)
    (t : ℝ) (x : M) :
    MDiffAt (T%
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background t)) x := by
  have hX :
      intrinsicDeTurckGaugeField (I := I) (M := M) g background t = 0 := by
    exact congrArg (fun X => X t)
      (intrinsicDeTurckGaugeField_eq_zero_of_isLeviCivita
        (I := I) (M := M) g background hbackground)
  rw [hX]
  change MDiffAt (Bundle.zeroSection (B := M) E TM) x
  exact mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := E) (E := TM) (x := x)

/-- Global version of
`intrinsicDeTurckGaugeField_mdiffAt_of_isLeviCivita`. -/
theorem intrinsicDeTurckGaugeField_mdiff_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background)
    (t : ℝ) :
    MDiff (T%
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background t)) := by
  intro x
  exact intrinsicDeTurckGaugeField_mdiffAt_of_isLeviCivita
    (I := I) (M := M) g background hbackground t x

/-- The reverse DeTurck gauge field contributes the negative of the intrinsic
DeTurck correction once the Lie-derivative slots are written with the
Levi-Civita derivative of the gauge field.

The differentiability hypothesis is only used to apply the covariant-derivative
constant-scalar rule to the section
`intrinsicDeTurckVectorField g background t`. -/
theorem intrinsicDeTurckGaugeField_lieCorrection_eq_neg_intrinsicDeTurckCorrection
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x)
    (hW : MDiffAt (T%
      (intrinsicDeTurckVectorField (I := I) (M := M) g background t)) x) :
    (g t).inner x
        (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
          (intrinsicDeTurckGaugeField (I := I) (M := M) g background t) x u) v +
      (g t).inner x u
        (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
          (intrinsicDeTurckGaugeField (I := I) (M := M) g background t) x v) =
      -intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v := by
  let cov := (chosenLeviCivitaFamily (I := I) (M := M) g) t
  let W : Π y : M, TM y :=
    intrinsicDeTurckVectorField (I := I) (M := M) g background t
  have hcov_neg :
      cov (intrinsicDeTurckGaugeField (I := I) (M := M) g background t) x =
        (-1 : ℝ) • cov W x := by
    change cov (-W) x = (-1 : ℝ) • cov W x
    simpa [cov, W] using
      (IsCovariantDerivativeOn.smul_const
        (F := E) (V := TM)
        (hcov := cov.isCovariantDerivativeOnUniv)
        (a := (-1 : ℝ)) (σ := W) (x := x) (hσ := by simpa [W] using hW))
  have hcov_neg_u :
      cov (intrinsicDeTurckGaugeField (I := I) (M := M) g background t) x u =
        -cov W x u := by
    simpa using congrArg (fun A : TM x →L[ℝ] TM x ↦ A u) hcov_neg
  have hcov_neg_v :
      cov (intrinsicDeTurckGaugeField (I := I) (M := M) g background t) x v =
        -cov W x v := by
    simpa using congrArg (fun A : TM x →L[ℝ] TM x ↦ A v) hcov_neg
  rw [hcov_neg_u, hcov_neg_v]
  change
    ((g t).inner x (-(cov W x u))) v + ((g t).inner x u) (-(cov W x v)) =
      -(((g t).inner x (cov W x u)) v + ((g t).inner x u) (cov W x v))
  have hneg_left :
      ((g t).inner x (-(cov W x u))) v =
        -((g t).inner x (cov W x u)) v := by
    have hneg_left_map :
        (g t).inner x (-(cov W x u)) =
          -((g t).inner x (cov W x u)) := by
      exact map_neg ((g t).inner x) (cov W x u)
    calc
      ((g t).inner x (-(cov W x u))) v =
          (-((g t).inner x (cov W x u))) v := by rw [hneg_left_map]
      _ = -((g t).inner x (cov W x u)) v := rfl
  have hneg_right :
      ((g t).inner x u) (-(cov W x v)) =
        -((g t).inner x u) (cov W x v) := by
    exact map_neg ((g t).inner x u) (cov W x v)
  rw [hneg_left, hneg_right]
  abel

/-- Levi-Civita-background specialization of
`intrinsicDeTurckGaugeField_lieCorrection_eq_neg_intrinsicDeTurckCorrection`,
with the DeTurck vector-field differentiability input discharged by the zero
section bridge. -/
theorem intrinsicDeTurckGaugeField_lieCorrection_eq_neg_intrinsicDeTurckCorrection_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background)
    (t : ℝ) (x : M) (u v : TM x) :
    (g t).inner x
        (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
          (intrinsicDeTurckGaugeField (I := I) (M := M) g background t) x u) v +
      (g t).inner x u
        (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
          (intrinsicDeTurckGaugeField (I := I) (M := M) g background t) x v) =
      -intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v := by
  exact
    intrinsicDeTurckGaugeField_lieCorrection_eq_neg_intrinsicDeTurckCorrection
      (I := I) (M := M) g background t x u v
      (intrinsicDeTurckVectorField_mdiffAt_of_isLeviCivita
        (I := I) (M := M) g background hbackground t x)

@[simp] theorem intrinsicDeTurckTraceEndomorphism_eq_connectionDifferenceTraceEndomorphism
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (w : TM x) :
    intrinsicDeTurckTraceEndomorphism (I := I) (M := M) g background t x w =
      connectionDifferenceTraceEndomorphism (I := I) (M := M)
        (chosenLeviCivitaFamily (I := I) (M := M) g) background t x w := by
  ext u
  rfl

@[simp] theorem intrinsicDeTurckOneForm_eq_connectionDifferenceTraceOneForm
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) :
    intrinsicDeTurckOneForm (I := I) (M := M) g background t x =
      connectionDifferenceTraceOneForm (I := I) (M := M)
        (chosenLeviCivitaFamily (I := I) (M := M) g) background t x := by
  ext w
  rw [intrinsicDeTurckOneForm_apply, connectionDifferenceTraceOneForm_apply]
  rfl

theorem SmoothSelfDiffeomorph2Family.trace_pullbackChosenLeviCivita_background_eq_intrinsicDeTurckOneForm
    (Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} (w : TM x) :
    LinearMap.trace ℝ (TM x)
        (connectionDifferenceTraceEndomorphism (I := I) (M := M)
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            Φ (chosenLeviCivitaFamily (I := I) (M := M) g))
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            Φ background) t x w).toLinearMap =
      intrinsicDeTurckOneForm (I := I) (M := M) g background t
        ((Φ t) x) ((Φ t).pushforwardTangent x w) := by
  calc
    LinearMap.trace ℝ (TM x)
        (connectionDifferenceTraceEndomorphism (I := I) (M := M)
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            Φ (chosenLeviCivitaFamily (I := I) (M := M) g))
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            Φ background) t x w).toLinearMap =
      LinearMap.trace ℝ (TM ((Φ t) x))
        (connectionDifferenceTraceEndomorphism (I := I) (M := M)
          (chosenLeviCivitaFamily (I := I) (M := M) g) background t
          ((Φ t) x) ((Φ t).pushforwardTangent x w)).toLinearMap := by
          exact Φ.trace_connectionDifferenceTraceEndomorphism_pullbackConnectionFamily
            (chosenLeviCivitaFamily (I := I) (M := M) g) background w
    _ = intrinsicDeTurckOneForm (I := I) (M := M) g background t
        ((Φ t) x) ((Φ t).pushforwardTangent x w) := by
          rw [intrinsicDeTurckOneForm_apply]
          rfl

@[simp] theorem SmoothSelfDiffeomorph2Family.traceOneForm_pullbackChosenLeviCivita_background_apply
    (Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} (w : TM x) :
    connectionDifferenceTraceOneForm (I := I) (M := M)
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          Φ (chosenLeviCivitaFamily (I := I) (M := M) g))
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          Φ background) t x w =
      intrinsicDeTurckOneForm (I := I) (M := M) g background t
        ((Φ t) x) ((Φ t).pushforwardTangent x w) := by
  calc
    connectionDifferenceTraceOneForm (I := I) (M := M)
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          Φ (chosenLeviCivitaFamily (I := I) (M := M) g))
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          Φ background) t x w =
      connectionDifferenceTraceOneForm (I := I) (M := M)
        (chosenLeviCivitaFamily (I := I) (M := M) g) background t
        ((Φ t) x) ((Φ t).pushforwardTangent x w) := by
          exact Φ.connectionDifferenceTraceOneForm_pullbackConnectionFamily_apply
            (chosenLeviCivitaFamily (I := I) (M := M) g) background w
    _ = intrinsicDeTurckOneForm (I := I) (M := M) g background t
        ((Φ t) x) ((Φ t).pushforwardTangent x w) := by
          rw [intrinsicDeTurckOneForm_eq_connectionDifferenceTraceOneForm]

theorem SmoothSelfDiffeomorph2Family.traceOneForm_pullbackChosenLeviCivita_background
    (Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} :
    connectionDifferenceTraceOneForm (I := I) (M := M)
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          Φ (chosenLeviCivitaFamily (I := I) (M := M) g))
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          Φ background) t x =
      (intrinsicDeTurckOneForm (I := I) (M := M) g background t
        ((Φ t) x)).comp ((Φ t).pushforwardTangent x) := by
  ext w
  exact SmoothSelfDiffeomorph2Family.traceOneForm_pullbackChosenLeviCivita_background_apply
    (I := I) (M := M) Φ g background w

/-- `C³` version of the DeTurck trace-one-form transport identity. The stronger
regularity keeps the pulled-back metric family at the `MetricFamily` regularity level. -/
@[simp] theorem SmoothSelfDiffeomorph3Family.traceOneForm_pullbackChosenLeviCivita_background_apply
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} (w : TM x) :
    connectionDifferenceTraceOneForm (I := I) (M := M)
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          Φ (chosenLeviCivitaFamily (I := I) (M := M) g))
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          Φ background) t x w =
      intrinsicDeTurckOneForm (I := I) (M := M) g background t
        ((Φ t) x) ((Φ t).pushforwardTangent x w) := by
  calc
    connectionDifferenceTraceOneForm (I := I) (M := M)
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          Φ (chosenLeviCivitaFamily (I := I) (M := M) g))
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          Φ background) t x w =
      connectionDifferenceTraceOneForm (I := I) (M := M)
        (chosenLeviCivitaFamily (I := I) (M := M) g) background t
        ((Φ t) x) ((Φ t).pushforwardTangent x w) := by
          exact Φ.connectionDifferenceTraceOneForm_pullbackConnectionFamily_apply
            (chosenLeviCivitaFamily (I := I) (M := M) g) background w
    _ = intrinsicDeTurckOneForm (I := I) (M := M) g background t
        ((Φ t) x) ((Φ t).pushforwardTangent x w) := by
          rw [intrinsicDeTurckOneForm_eq_connectionDifferenceTraceOneForm]

theorem SmoothSelfDiffeomorph3Family.traceOneForm_pullbackChosenLeviCivita_background
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} :
    connectionDifferenceTraceOneForm (I := I) (M := M)
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          Φ (chosenLeviCivitaFamily (I := I) (M := M) g))
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          Φ background) t x =
      (intrinsicDeTurckOneForm (I := I) (M := M) g background t
        ((Φ t) x)).comp ((Φ t).pushforwardTangent x) := by
  ext w
  exact SmoothSelfDiffeomorph3Family.traceOneForm_pullbackChosenLeviCivita_background_apply
    (I := I) (M := M) Φ g background w

theorem SmoothSelfDiffeomorph3Family.trace_pullbackChosenLeviCivita_background_eq_intrinsicDeTurckOneForm
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    {t : ℝ} {x : M} (w : TM x) :
    LinearMap.trace ℝ (TM x)
        (connectionDifferenceTraceEndomorphism (I := I) (M := M)
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            Φ (chosenLeviCivitaFamily (I := I) (M := M) g))
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            Φ background) t x w).toLinearMap =
      intrinsicDeTurckOneForm (I := I) (M := M) g background t
        ((Φ t) x) ((Φ t).pushforwardTangent x w) := by
  simpa [connectionDifferenceTraceOneForm_apply] using
    SmoothSelfDiffeomorph3Family.traceOneForm_pullbackChosenLeviCivita_background_apply
      (I := I) (M := M) Φ g background w

/-- A smooth self-map family follows the reverse intrinsic DeTurck gauge field on `s`. -/
def FollowsIntrinsicDeTurckOn
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  SatisfiesGaugeFlowOn (I := I) (M := M) Φ
    (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s

/-- Local version of `FollowsIntrinsicDeTurckOn`. -/
def FollowsIntrinsicDeTurckAt
    (Φ : SmoothSelfMapFamily (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t₀ : ℝ) : Prop :=
  SatisfiesGaugeFlowAt (I := I) (M := M) Φ
    (intrinsicDeTurckGaugeField (I := I) (M := M) g background) t₀

lemma FollowsIntrinsicDeTurckOn.mono
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (hΦ : FollowsIntrinsicDeTurckOn (I := I) (M := M) Φ g background t)
    (hst : s ⊆ t) :
    FollowsIntrinsicDeTurckOn (I := I) (M := M) Φ g background s := by
  exact SatisfiesGaugeFlowOn.mono (I := I) (M := M) hΦ hst

lemma FollowsIntrinsicDeTurckOn.satisfiesAt
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (hΦ : FollowsIntrinsicDeTurckOn (I := I) (M := M) Φ g background s)
    (hs : s ∈ 𝓝 t₀) :
    FollowsIntrinsicDeTurckAt (I := I) (M := M) Φ g background t₀ := by
  exact SatisfiesGaugeFlowOn.satisfiesAt (I := I) (M := M) hΦ hs

/-- Reinterpret an intrinsic DeTurck-following family for an equivalent gauge field along its image. -/
lemma FollowsIntrinsicDeTurckOn.congr_gaugeField
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {g g' : MetricFamily (I := I) (M := M)}
    {background background' : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hΦ : FollowsIntrinsicDeTurckOn (I := I) (M := M) Φ g background s)
    (hfield : ∀ t ∈ s, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M) g background t (Φ t x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g' background' t (Φ t x)) :
    FollowsIntrinsicDeTurckOn (I := I) (M := M) Φ g' background' s := by
  exact SatisfiesGaugeFlowOn.congr_vectorField (I := I) (M := M) hΦ hfield

/-- Pointwise derivative form of the DeTurck gauge-flow equation. -/
lemma FollowsIntrinsicDeTurckOn.hasMFDerivAt
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hΦ : FollowsIntrinsicDeTurckOn (I := I) (M := M) Φ g background s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasMFDerivAt[s] (fun τ : ℝ ↦ Φ τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t (Φ t x))) := by
  exact hΦ x t ht

/-- An anchored DeTurck gauge family on `s` consists of a smooth self-map family that agrees with
the identity at the base time and follows the reverse intrinsic DeTurck vector field on `s`. -/
structure AnchoredIntrinsicDeTurckGaugeOn
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) where
  maps : SmoothSelfMapFamily (I := I) (M := M)
  anchored : AnchoredAt (I := I) (M := M) maps t₀
  follows : FollowsIntrinsicDeTurckOn (I := I) (M := M) maps g background s

def AnchoredIntrinsicDeTurckGaugeOn.congr_gaugeField
    {g g' : MetricFamily (I := I) (M := M)}
    {background background' : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckGaugeOn
      (I := I) (M := M) g background s t₀)
    (hfield : ∀ t ∈ s, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M) g background t (gauge.maps t x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g' background' t (gauge.maps t x)) :
    AnchoredIntrinsicDeTurckGaugeOn (I := I) (M := M) g' background' s t₀ where
  maps := gauge.maps
  anchored := gauge.anchored
  follows := gauge.follows.congr_gaugeField hfield

/-- Restrict an anchored intrinsic DeTurck map gauge to a smaller time set. -/
def AnchoredIntrinsicDeTurckGaugeOn.restrictTimeSet
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckGaugeOn (I := I) (M := M) g background t t₀)
    (hst : s ⊆ t) :
    AnchoredIntrinsicDeTurckGaugeOn (I := I) (M := M) g background s t₀ where
  maps := gauge.maps
  anchored := gauge.anchored
  follows := gauge.follows.mono hst

@[simp] theorem AnchoredIntrinsicDeTurckGaugeOn.restrictTimeSet_maps
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckGaugeOn (I := I) (M := M) g background t t₀)
    (hst : s ⊆ t) :
    (gauge.restrictTimeSet hst).maps = gauge.maps :=
  rfl

/-- A `C²` diffeomorphism-valued anchored DeTurck gauge family. This is the natural strengthening
of `AnchoredIntrinsicDeTurckGaugeOn` needed for later connection transport. -/
structure AnchoredIntrinsicDeTurckDiffeomorphGaugeOn
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) where
  maps : SmoothSelfDiffeomorph2Family (I := I) (M := M)
  anchored :
    SmoothSelfDiffeomorph2Family.AnchoredAt (I := I) (M := M) maps t₀
  follows : FollowsIntrinsicDeTurckOn (I := I) (M := M)
    maps.toSmoothSelfMapFamily g background s

def AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.of_hasMFDerivWithinAt
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps : SmoothSelfDiffeomorph2Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph2Family.AnchoredAt (I := I) (M := M) maps t₀)
    (hflow : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ (maps τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((maps t) x)))) :
    AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M) g background s t₀ where
  maps := maps
  anchored := anchored
  follows :=
    SatisfiesGaugeFlowOn.of_hasMFDerivWithinAt
      (I := I) (M := M)
      (Φ := maps.toSmoothSelfMapFamily)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (s := s)
      (fun t ht x ↦ by
        change HasMFDerivAt[s] (fun τ : ℝ ↦ (maps τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((maps t) x)))
        exact hflow t ht x)

def AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.congr_gaugeField
    {g g' : MetricFamily (I := I) (M := M)}
    {background background' : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn
      (I := I) (M := M) g background s t₀)
    (hfield : ∀ t ∈ s, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M) g background t
          (gauge.maps.toSmoothSelfMapFamily t x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g' background' t
          (gauge.maps.toSmoothSelfMapFamily t x)) :
    AnchoredIntrinsicDeTurckDiffeomorphGaugeOn
      (I := I) (M := M) g' background' s t₀ where
  maps := gauge.maps
  anchored := gauge.anchored
  follows := gauge.follows.congr_gaugeField hfield

/-- Restrict an anchored `C²` intrinsic DeTurck diffeomorphism gauge to a smaller time set. -/
def AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.restrictTimeSet
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn
      (I := I) (M := M) g background t t₀)
    (hst : s ⊆ t) :
    AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M) g background s t₀ where
  maps := gauge.maps
  anchored := gauge.anchored
  follows := gauge.follows.mono hst

@[simp] theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.restrictTimeSet_maps
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn
      (I := I) (M := M) g background t t₀)
    (hst : s ⊆ t) :
    (gauge.restrictTimeSet hst).maps = gauge.maps :=
  rfl

def AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.toMapGauge
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn
      (I := I) (M := M) g background s t₀) :
    AnchoredIntrinsicDeTurckGaugeOn (I := I) (M := M) g background s t₀ where
  maps := gauge.maps.toSmoothSelfMapFamily
  anchored := gauge.anchored.toMapAnchoredAt
  follows := gauge.follows

@[simp] theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.toMapGauge_restrictTimeSet
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn
      (I := I) (M := M) g background t t₀)
    (hst : s ⊆ t) :
    (gauge.restrictTimeSet hst).toMapGauge =
      gauge.toMapGauge.restrictTimeSet hst :=
  rfl

/-- A `C³` diffeomorphism-valued anchored DeTurck gauge family. This stronger regularity is
exactly what lets the gauge pullback of a `C²` metric remain a genuine `MetricFamily`. -/
structure AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) where
  maps : SmoothSelfDiffeomorph3Family (I := I) (M := M)
  anchored :
    SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M) maps t₀
  follows : FollowsIntrinsicDeTurckOn (I := I) (M := M)
    maps.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily g background s

def AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M) maps t₀)
    (hflow : SatisfiesGaugeFlowOn (I := I) (M := M)
      maps.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M) g background s t₀ where
  maps := maps
  anchored := anchored
  follows := hflow

def AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (maps : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M) maps t₀)
    (hflow : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ (maps τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((maps t) x)))) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M) g background s t₀ :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
    (I := I) (M := M) (g := g) (background := background) (s := s) (t₀ := t₀)
    maps anchored
    (SatisfiesGaugeFlowOn.of_hasMFDerivWithinAt
      (I := I) (M := M)
      (Φ := maps.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (s := s)
      (fun t ht x ↦ by
        change HasMFDerivAt[s] (fun τ : ℝ ↦ (maps τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((maps t) x)))
        exact hflow t ht x))

def AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.identity_of_intrinsicDeTurckGaugeField_eq_zero
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (hzero : ∀ t ∈ s, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M) g background t x = 0) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M) g background s t₀ :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
    (I := I) (M := M) (g := g) (background := background) (s := s) (t₀ := t₀)
    (SmoothSelfDiffeomorph3Family.id (I := I) (M := M))
    (SmoothSelfDiffeomorph3Family.id_anchoredAt (I := I) (M := M) t₀)
    (SmoothSelfDiffeomorph3Family.id_satisfiesGaugeFlowOn_of_eq_zero
      (I := I) (M := M) (s := s) hzero)

def AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.identity_of_intrinsicDeTurckGaugeField_eq_zero_via_hasMFDerivWithinAt
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (hzero : ∀ t ∈ s, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M) g background t x = 0) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M) g background s t₀ :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
    (I := I) (M := M) (g := g) (background := background) (s := s) (t₀ := t₀)
    (SmoothSelfDiffeomorph3Family.id (I := I) (M := M))
    (SmoothSelfDiffeomorph3Family.id_anchoredAt (I := I) (M := M) t₀)
    (by
      intro t ht x
      simpa using
        SmoothSelfDiffeomorph3Family.id_hasMFDerivWithinAt_of_eq_zero
          (I := I) (M := M) (s := s) hzero t ht x)

def AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.congr_gaugeField
    {g g' : MetricFamily (I := I) (M := M)}
    {background background' : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) g background s t₀)
    (hfield : ∀ t ∈ s, ∀ x : M,
      intrinsicDeTurckGaugeField (I := I) (M := M) g background t
          (gauge.maps.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily t x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g' background' t
          (gauge.maps.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily t x)) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) g' background' s t₀ where
  maps := gauge.maps
  anchored := gauge.anchored
  follows := gauge.follows.congr_gaugeField hfield

/-- Restrict an anchored `C³` intrinsic DeTurck diffeomorphism gauge to a smaller time set. -/
def AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.restrictTimeSet
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) g background t t₀)
    (hst : s ⊆ t) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M) g background s t₀ where
  maps := gauge.maps
  anchored := gauge.anchored
  follows := gauge.follows.mono hst

@[simp] theorem AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.restrictTimeSet_maps
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) g background t t₀)
    (hst : s ⊆ t) :
    (gauge.restrictTimeSet hst).maps = gauge.maps :=
  rfl

def AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toDiffeomorph2Gauge
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) g background s t₀) :
    AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M) g background s t₀ where
  maps := gauge.maps.toSmoothSelfDiffeomorph2Family
  anchored := gauge.anchored.toSmoothSelfDiffeomorph2AnchoredAt
  follows := gauge.follows

@[simp] theorem AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toDiffeomorph2Gauge_restrictTimeSet
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) g background t t₀)
    (hst : s ⊆ t) :
    (gauge.restrictTimeSet hst).toDiffeomorph2Gauge =
      gauge.toDiffeomorph2Gauge.restrictTimeSet hst :=
  rfl

def AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toMapGauge
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) g background s t₀) :
    AnchoredIntrinsicDeTurckGaugeOn (I := I) (M := M) g background s t₀ :=
  gauge.toDiffeomorph2Gauge.toMapGauge

@[simp] theorem AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toMapGauge_restrictTimeSet
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) g background t t₀)
    (hst : s ⊆ t) :
    (gauge.restrictTimeSet hst).toMapGauge =
      gauge.toMapGauge.restrictTimeSet hst :=
  rfl

theorem AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.hasMFDerivAt
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) g background s t₀)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasMFDerivAt[s]
      (fun τ : ℝ ↦ gauge.maps.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t
          (gauge.maps t x))) := by
  exact gauge.follows.hasMFDerivAt ht x

/-- The `C³` gauge-flow ODE for the actual diffeomorphism-valued maps, rather than for their
forgotten `C¹` map family. -/
theorem AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.hasMFDerivAt_apply
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) g background s t₀)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasMFDerivAt[s]
      (fun τ : ℝ ↦ (gauge.maps τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t
          (gauge.maps t x))) := by
  change HasMFDerivAt[s] (fun τ : ℝ ↦ (gauge.maps τ) x) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background t
        ((gauge.maps t) x)))
  exact gauge.hasMFDerivAt ht x

theorem AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.pullbackMetricFamily_eq_initial
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) g background s t₀) :
    gauge.maps.pullbackMetricFamily g t₀ = g t₀ := by
  exact gauge.maps.pullbackMetricFamily_eq_at_anchored_time g gauge.anchored

theorem AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.pullbackBackgroundConnection_isLeviCivita_pullbackMetricFamily
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) g background s t₀)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      (gauge.maps.pullbackMetricFamily g)
      (gauge.maps.pullbackConnectionFamily background) := by
  exact gauge.maps.isLeviCivita_pullbackConnectionFamily_pullbackMetricFamily
    g background hbackground

theorem AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.pullbackBackgroundConnection_contMDiff
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn
      (I := I) (M := M) g background s t₀)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge.maps background t) 1 := by
  have hpullLevi :
      CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
        (I := I) (M := M) (gauge.maps.pullbackMetricFamily g)
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge.maps background) :=
    gauge.pullbackBackgroundConnection_isLeviCivita_pullbackMetricFamily hbackground
  exact
    CovariantDerivative.TimeDependentRiemannianMetric.contMDiffCovariantDerivative_of_isLeviCivita
      (I := I) (M := M) (g := gauge.maps.pullbackMetricFamily g) hpullLevi

theorem IntrinsicDeTurckLocalSolution.background_contMDiff_of_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background) :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (source.toIntrinsicDeTurckSolution.background t) 1 :=
  CovariantDerivative.TimeDependentRiemannianMetric.contMDiffCovariantDerivative_of_isLeviCivita
    (I := I) (M := M) (g := source.toIntrinsicDeTurckSolution.metric) hbackground

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.hasMFDerivAt
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn
      (I := I) (M := M) g background s t₀)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasMFDerivAt[s] (fun τ : ℝ ↦ gauge.maps.toSmoothSelfMapFamily τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t
          (gauge.maps t x))) := by
  exact gauge.follows.hasMFDerivAt ht x

noncomputable def identityDiffeomorphGaugeOn_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M) g background s t₀ where
  maps := SmoothSelfDiffeomorph2Family.id (I := I) (M := M)
  anchored := SmoothSelfDiffeomorph2Family.id_anchoredAt (I := I) (M := M) t₀
  follows := by
    rw [SmoothSelfDiffeomorph2Family.id_toSmoothSelfMapFamily]
    exact SmoothSelfMapFamily.id_satisfiesGaugeFlowOn_of_eq_zero
      (I := I) (M := M) (s := s)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (fun t _ht x ↦ by
        have hzero :
            intrinsicDeTurckVectorField (I := I) (M := M) g background = 0 :=
          intrinsicDeTurckVectorField_eq_zero_of_isLeviCivita
            (I := I) (M := M) g background hbackground
        simpa [intrinsicDeTurckGaugeField] using congrFun (congrFun hzero t) x)

noncomputable def identityDiffeomorph3GaugeOn_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M) g background s t₀ :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.identity_of_intrinsicDeTurckGaugeField_eq_zero
    (I := I) (M := M) (g := g) (background := background) (s := s) (t₀ := t₀)
    (fun t _ht x ↦ by
      have hzero :
          intrinsicDeTurckVectorField (I := I) (M := M) g background = 0 :=
        intrinsicDeTurckVectorField_eq_zero_of_isLeviCivita
          (I := I) (M := M) g background hbackground
      simpa [intrinsicDeTurckGaugeField] using congrFun (congrFun hzero t) x)

/-- On zero-dimensional tangent fibers, the identity diffeomorphism family follows the intrinsic
DeTurck gauge field for any background connection family. -/
noncomputable def identityDiffeomorphGaugeOn_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M) g background s t₀ where
  maps := SmoothSelfDiffeomorph2Family.id (I := I) (M := M)
  anchored := SmoothSelfDiffeomorph2Family.id_anchoredAt (I := I) (M := M) t₀
  follows := by
    rw [SmoothSelfDiffeomorph2Family.id_toSmoothSelfMapFamily]
    exact SmoothSelfMapFamily.id_satisfiesGaugeFlowOn_of_eq_zero
      (I := I) (M := M) (s := s)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (fun t _ht x ↦ by
        have hzero :
            intrinsicDeTurckVectorField (I := I) (M := M) g background = 0 :=
          intrinsicDeTurckVectorField_eq_zero_of_subsingleton_tangent
            (I := I) (M := M) g background
        simpa [intrinsicDeTurckGaugeField] using congrFun (congrFun hzero t) x)

/-- `C³` version of the zero-dimensional identity DeTurck gauge. -/
noncomputable def identityDiffeomorph3GaugeOn_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) (t₀ : ℝ) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M) g background s t₀ :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.identity_of_intrinsicDeTurckGaugeField_eq_zero
    (I := I) (M := M) (g := g) (background := background) (s := s) (t₀ := t₀)
    (fun t _ht x ↦ by
      have hzero :
          intrinsicDeTurckVectorField (I := I) (M := M) g background = 0 :=
        intrinsicDeTurckVectorField_eq_zero_of_subsingleton_tangent
          (I := I) (M := M) g background
      simpa [intrinsicDeTurckGaugeField] using congrFun (congrFun hzero t) x)

noncomputable def IntrinsicDeTurckLocalSolution.identityDiffeomorphGaugeOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  identityDiffeomorphGaugeOn_of_isLeviCivita
    (I := I) (M := M)
    sol.toIntrinsicDeTurckSolution.metric
    sol.toIntrinsicDeTurckSolution.background
    sol.toIntrinsicDeTurckSolution.timeSet
    ivp.initialTime
    hbackground

noncomputable def IntrinsicDeTurckLocalSolution.identityDiffeomorphGaugeOn_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  RicciFlow.identityDiffeomorphGaugeOn_of_subsingleton_tangent
    (I := I) (M := M)
    sol.toIntrinsicDeTurckSolution.metric
    sol.toIntrinsicDeTurckSolution.background
    sol.toIntrinsicDeTurckSolution.timeSet
    ivp.initialTime

noncomputable def IntrinsicDeTurckLocalSolution.identityDiffeomorph3GaugeOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  identityDiffeomorph3GaugeOn_of_isLeviCivita
    (I := I) (M := M)
    sol.toIntrinsicDeTurckSolution.metric
    sol.toIntrinsicDeTurckSolution.background
    sol.toIntrinsicDeTurckSolution.timeSet
    ivp.initialTime
    hbackground

noncomputable def IntrinsicDeTurckLocalSolution.identityDiffeomorph3GaugeOn_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  RicciFlow.identityDiffeomorph3GaugeOn_of_subsingleton_tangent
    (I := I) (M := M)
    sol.toIntrinsicDeTurckSolution.metric
    sol.toIntrinsicDeTurckSolution.background
    sol.toIntrinsicDeTurckSolution.timeSet
    ivp.initialTime

theorem IntrinsicDeTurckLocalSolution.pullbackMetricTensor_eq_initial_of_anchored
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfMapFamily (I := I) (M := M)}
    (hΦ : AnchoredAt (I := I) (M := M) Φ ivp.initialTime)
    (x : M) (u v : TM x) :
    pullbackMetricTensor (I := I) (M := M) Φ
        sol.toIntrinsicDeTurckSolution.metric ivp.initialTime x u v =
      ivp.initialMetric.inner x u v := by
  calc
    pullbackMetricTensor (I := I) (M := M) Φ
        sol.toIntrinsicDeTurckSolution.metric ivp.initialTime x u v
      = metricTensor (I := I) (M := M)
          sol.toIntrinsicDeTurckSolution.metric ivp.initialTime x u v := by
          exact congrArg (fun T => T x u v)
            (pullbackMetricTensor_eq_metricTensor_at_anchored_time
              (I := I) (M := M) Φ sol.toIntrinsicDeTurckSolution.metric ivp.initialTime hΦ)
    _ = ivp.initialMetric.inner x u v :=
      intrinsicDeTurckLocalSolution_metric_eq_initial
        (E := E) (H := H) (I := I) (M := M) sol x u v

theorem AnchoredIntrinsicDeTurckGaugeOn.pullbackMetricTensor_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (x : M) (u v : TM x) :
    pullbackMetricTensor (I := I) (M := M) gauge.maps
        sol.toIntrinsicDeTurckSolution.metric ivp.initialTime x u v =
      ivp.initialMetric.inner x u v :=
  sol.pullbackMetricTensor_eq_initial_of_anchored gauge.anchored x u v

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.pullbackMetricTensor_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (x : M) (u v : TM x) :
    pullbackMetricTensor (I := I) (M := M) gauge.maps.toSmoothSelfMapFamily
        sol.toIntrinsicDeTurckSolution.metric ivp.initialTime x u v =
      ivp.initialMetric.inner x u v :=
  (gauge.toMapGauge).pullbackMetricTensor_eq_initial sol x u v

theorem IntrinsicDeTurckLocalSolution.pullbackRiemannianMetric_eq_initial_of_anchored
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    (hΦ : Φ.AnchoredAt ivp.initialTime) :
    (Φ ivp.initialTime).pullbackRiemannianMetric
        (sol.toIntrinsicDeTurckSolution.metric ivp.initialTime) =
      ({ ivp.initialMetric with contMDiff := ivp.initialMetric.contMDiff.of_le (by norm_num) } :
        Bundle.ContMDiffRiemannianMetric I 1 E TM) := by
  have hpull :
      (Φ ivp.initialTime).pullbackRiemannianMetric
          (sol.toIntrinsicDeTurckSolution.metric ivp.initialTime) =
        ({ sol.toIntrinsicDeTurckSolution.metric ivp.initialTime with
            contMDiff :=
              (sol.toIntrinsicDeTurckSolution.metric ivp.initialTime).contMDiff.of_le
                (by norm_num) } :
          Bundle.ContMDiffRiemannianMetric I 1 E TM) := by
    simpa using
      (SmoothSelfDiffeomorph2Family.pullbackRiemannianMetric_eq_at_anchored_time
        (I := I) (M := M) (Φ := Φ) sol.toIntrinsicDeTurckSolution.metric hΦ)
  have hinit :
      ({ sol.toIntrinsicDeTurckSolution.metric ivp.initialTime with
          contMDiff :=
            (sol.toIntrinsicDeTurckSolution.metric ivp.initialTime).contMDiff.of_le
              (by norm_num) } :
        Bundle.ContMDiffRiemannianMetric I 1 E TM) =
      ({ ivp.initialMetric with contMDiff := ivp.initialMetric.contMDiff.of_le (by norm_num) } :
        Bundle.ContMDiffRiemannianMetric I 1 E TM) := by
    ext x u v
    exact intrinsicDeTurckLocalSolution_metric_eq_initial
      (E := E) (H := H) (I := I) (M := M) sol x u v
  exact hpull.trans hinit

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.pullbackRiemannianMetric_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime) :
    (gauge.maps ivp.initialTime).pullbackRiemannianMetric
        (sol.toIntrinsicDeTurckSolution.metric ivp.initialTime) =
      ({ ivp.initialMetric with contMDiff := ivp.initialMetric.contMDiff.of_le (by norm_num) } :
        Bundle.ContMDiffRiemannianMetric I 1 E TM) :=
  sol.pullbackRiemannianMetric_eq_initial_of_anchored gauge.anchored

theorem IntrinsicDeTurckLocalSolution.transformedMetric_eq_initial_of_anchored_of_inner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    (hΦ : Φ.AnchoredAt ivp.initialTime)
    {g' : MetricFamily (I := I) (M := M)}
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (sol.toIntrinsicDeTurckSolution.metric t).inner ((Φ t) x)
          (((Φ t).pushforwardTangent x) u)
          (((Φ t).pushforwardTangent x) v)) :
    g' ivp.initialTime = ivp.initialMetric := by
  ext x u v
  calc
    (g' ivp.initialTime).inner x u v
      = (sol.toIntrinsicDeTurckSolution.metric ivp.initialTime).inner ((Φ ivp.initialTime) x)
          (((Φ ivp.initialTime).pushforwardTangent x) u)
          (((Φ ivp.initialTime).pushforwardTangent x) v) := hinner ivp.initialTime x u v
    _ = (sol.toIntrinsicDeTurckSolution.metric ivp.initialTime).inner x u v := by
          rw [
            SmoothSelfDiffeomorph2Family.AnchoredAt.pushforwardTangent (Φ := Φ) hΦ x u,
            SmoothSelfDiffeomorph2Family.AnchoredAt.pushforwardTangent (Φ := Φ) hΦ x v,
            SmoothSelfDiffeomorph2Family.AnchoredAt.apply (Φ := Φ) hΦ x]
    _ = ivp.initialMetric.inner x u v :=
          intrinsicDeTurckLocalSolution_metric_eq_initial
            (E := E) (H := H) (I := I) (M := M) sol x u v

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.transformedMetric_eq_initial_of_inner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {g' : MetricFamily (I := I) (M := M)}
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (sol.toIntrinsicDeTurckSolution.metric t).inner ((gauge.maps t) x)
          (((gauge.maps t).pushforwardTangent x) u)
          (((gauge.maps t).pushforwardTangent x) v)) :
    g' ivp.initialTime = ivp.initialMetric :=
  sol.transformedMetric_eq_initial_of_anchored_of_inner gauge.anchored hinner

theorem IntrinsicDeTurckLocalSolution.pullbackBackgroundConnection_eq_initial_of_anchored
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    (hΦ : Φ.AnchoredAt ivp.initialTime) :
    SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
        sol.toIntrinsicDeTurckSolution.background ivp.initialTime =
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime := by
  simpa using
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_eq_at_anchored_time
      (I := I) (M := M) (Φ := Φ) sol.toIntrinsicDeTurckSolution.background hΦ)

theorem IntrinsicDeTurckLocalSolution.pullbackBackgroundConnection_isLeviCivita_initial_of_anchored
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    (hΦ : Φ.AnchoredAt ivp.initialTime)
    (hLevi :
      letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      (sol.toIntrinsicDeTurckSolution.background ivp.initialTime).IsLeviCivita) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨((Φ ivp.initialTime).pullbackRiemannianMetric
        (sol.toIntrinsicDeTurckSolution.metric ivp.initialTime)).toRiemannianMetric⟩;
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime).IsLeviCivita := by
  let gPull : Bundle.ContMDiffRiemannianMetric I 1 E TM :=
    (Φ ivp.initialTime).pullbackRiemannianMetric
      (sol.toIntrinsicDeTurckSolution.metric ivp.initialTime)
  let g0 : Bundle.ContMDiffRiemannianMetric I 1 E TM :=
    { ivp.initialMetric with contMDiff := ivp.initialMetric.contMDiff.of_le (by norm_num) }
  have hg : gPull = g0 := by
    simpa [gPull, g0] using
      sol.pullbackRiemannianMetric_eq_initial_of_anchored (Φ := Φ) hΦ
  rw [sol.pullbackBackgroundConnection_eq_initial_of_anchored (Φ := Φ) hΦ]
  change
    letI : Bundle.RiemannianBundle TM := ⟨gPull.toRiemannianMetric⟩;
    (sol.toIntrinsicDeTurckSolution.background ivp.initialTime).IsLeviCivita
  rw [hg]
  convert hLevi using 1 <;> rfl

theorem IntrinsicDeTurckLocalSolution.pullbackBackgroundConnection_isLeviCivita_of_inner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    {g' : MetricFamily (I := I) (M := M)}
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (sol.toIntrinsicDeTurckSolution.metric t).inner ((Φ t) x)
          (((Φ t).pushforwardTangent x) u)
          (((Φ t).pushforwardTangent x) v))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g'
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
        sol.toIntrinsicDeTurckSolution.background) := by
  exact SmoothSelfDiffeomorph2Family.isLeviCivita_pullbackConnectionFamily
    (I := I) (M := M) (Φ := Φ)
    (g := sol.toIntrinsicDeTurckSolution.metric) (g' := g')
    (cov := sol.toIntrinsicDeTurckSolution.background)
    (hinner := hinner) (hcov := hbackground)

theorem IntrinsicDeTurckLocalSolution.pullbackBackgroundConnection_isLeviCivita_pullbackRiemannianMetric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    ∀ t : ℝ,
      letI : Bundle.RiemannianBundle TM :=
        ⟨((Φ t).pullbackRiemannianMetric
          (sol.toIntrinsicDeTurckSolution.metric t)).toRiemannianMetric⟩
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
        sol.toIntrinsicDeTurckSolution.background t).IsLeviCivita := by
  exact SmoothSelfDiffeomorph2Family.isLeviCivita_pullbackConnectionFamily_pullbackRiemannianMetric
    (I := I) (M := M) (Φ := Φ)
    (g := sol.toIntrinsicDeTurckSolution.metric)
    (cov := sol.toIntrinsicDeTurckSolution.background)
    (hcov := hbackground)

theorem IntrinsicDeTurckLocalSolution.intrinsicRicciTensor_eq_pullbackBackgroundRicciTensor_of_inner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    {g' : MetricFamily (I := I) (M := M)}
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (sol.toIntrinsicDeTurckSolution.metric t).inner ((Φ t) x)
          (((Φ t).pushforwardTangent x) u)
          (((Φ t).pushforwardTangent x) v))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
          sol.toIntrinsicDeTurckSolution.background t) 1) :
    intrinsicRicciTensor (I := I) (M := M) g' =
      ricciTensor (I := I) (M := M) g'
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
          sol.toIntrinsicDeTurckSolution.background) hpull := by
  exact intrinsicRicciTensor_eq_ricciTensor_of_isLeviCivita
    (I := I) (M := M) g' hpull
    (sol.pullbackBackgroundConnection_isLeviCivita_of_inner
      (Φ := Φ) (g' := g') hinner hbackground)

theorem IntrinsicDeTurckLocalSolution.intrinsicRicciFlowRHS_eq_pullbackBackgroundRicciFlowRHS_of_inner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    {g' : MetricFamily (I := I) (M := M)}
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (sol.toIntrinsicDeTurckSolution.metric t).inner ((Φ t) x)
          (((Φ t).pushforwardTangent x) u)
          (((Φ t).pushforwardTangent x) v))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
          sol.toIntrinsicDeTurckSolution.background t) 1) :
    intrinsicRicciFlowRHS (I := I) (M := M) g' =
      ricciFlowRHS (I := I) (M := M) g'
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
          sol.toIntrinsicDeTurckSolution.background) hpull := by
  exact intrinsicRicciFlowRHS_eq_ricciFlowRHS_of_isLeviCivita
    (I := I) (M := M) g' hpull
    (sol.pullbackBackgroundConnection_isLeviCivita_of_inner
      (Φ := Φ) (g' := g') hinner hbackground)

theorem IntrinsicDeTurckLocalSolution.isIntrinsicRicciFlowOn_of_pullbackBackgroundEquation_of_inner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    {g' : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (sol.toIntrinsicDeTurckSolution.metric t).inner ((Φ t) x)
          (((Φ t).pushforwardTangent x) u)
          (((Φ t).pushforwardTangent x) v))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
          sol.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M) g' gdot s)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ s →
      SatisfiesEquationAt (I := I) (M := M) g'
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
          sol.toIntrinsicDeTurckSolution.background) hpull gdot t) :
    IsIntrinsicRicciFlowOn (I := I) (M := M) g' gdot s := by
  have hLevi :
      CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
        (I := I) (M := M) g'
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
          sol.toIntrinsicDeTurckSolution.background) :=
    sol.pullbackBackgroundConnection_isLeviCivita_of_inner
      (Φ := Φ) (g' := g') hinner hbackground
  exact
    (isIntrinsicRicciFlowOn_iff_of_isLeviCivita
      (I := I) (M := M) g' hpull gdot s hLevi).2
      ⟨hLevi, hderiv, heq⟩

theorem IntrinsicDeTurckLocalSolution.pullbackBackgroundConnection_eq_initial_of_anchored_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    (hΦ : Φ.AnchoredAt ivp.initialTime)
    (X : Π x : M, TM x) (x : M) (u : TM x) :
    SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
        sol.toIntrinsicDeTurckSolution.background ivp.initialTime X x u =
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime X x u := by
  simpa using
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_eq_at_anchored_time_apply
      (I := I) (M := M) (Φ := Φ) sol.toIntrinsicDeTurckSolution.background hΦ X x u)

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.pullbackBackgroundConnection_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime) :
    SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
        sol.toIntrinsicDeTurckSolution.background ivp.initialTime =
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime :=
  sol.pullbackBackgroundConnection_eq_initial_of_anchored gauge.anchored

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.pullbackBackgroundConnection_eq_initial_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (X : Π x : M, TM x) (x : M) (u : TM x) :
    SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
        sol.toIntrinsicDeTurckSolution.background ivp.initialTime X x u =
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime X x u :=
  sol.pullbackBackgroundConnection_eq_initial_of_anchored_apply gauge.anchored X x u

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.pullbackBackgroundConnection_isLeviCivita_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hLevi :
      letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      (sol.toIntrinsicDeTurckSolution.background ivp.initialTime).IsLeviCivita) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge.maps ivp.initialTime).pullbackRiemannianMetric
        (sol.toIntrinsicDeTurckSolution.metric ivp.initialTime)).toRiemannianMetric⟩;
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime).IsLeviCivita :=
  sol.pullbackBackgroundConnection_isLeviCivita_initial_of_anchored gauge.anchored hLevi

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.pullbackBackgroundConnection_isLeviCivita_of_inner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {g' : MetricFamily (I := I) (M := M)}
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (sol.toIntrinsicDeTurckSolution.metric t).inner ((gauge.maps t) x)
          (((gauge.maps t).pushforwardTangent x) u)
          (((gauge.maps t).pushforwardTangent x) v))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g'
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
        sol.toIntrinsicDeTurckSolution.background) := by
  exact sol.pullbackBackgroundConnection_isLeviCivita_of_inner
    (Φ := gauge.maps) (g' := g') hinner hbackground

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.pullbackBackgroundConnection_isLeviCivita_pullbackRiemannianMetric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    ∀ t : ℝ,
      letI : Bundle.RiemannianBundle TM :=
        ⟨((gauge.maps t).pullbackRiemannianMetric
          (sol.toIntrinsicDeTurckSolution.metric t)).toRiemannianMetric⟩
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
        sol.toIntrinsicDeTurckSolution.background t).IsLeviCivita := by
  exact sol.pullbackBackgroundConnection_isLeviCivita_pullbackRiemannianMetric
    (Φ := gauge.maps) hbackground

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.intrinsicRicciTensor_eq_pullbackBackgroundRicciTensor_of_inner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {g' : MetricFamily (I := I) (M := M)}
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (sol.toIntrinsicDeTurckSolution.metric t).inner ((gauge.maps t) x)
          (((gauge.maps t).pushforwardTangent x) u)
          (((gauge.maps t).pushforwardTangent x) v))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.toIntrinsicDeTurckSolution.background t) 1) :
    intrinsicRicciTensor (I := I) (M := M) g' =
      ricciTensor (I := I) (M := M) g'
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.toIntrinsicDeTurckSolution.background) hpull := by
  exact sol.intrinsicRicciTensor_eq_pullbackBackgroundRicciTensor_of_inner
    (Φ := gauge.maps) (g' := g') hinner hbackground hpull

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.intrinsicRicciFlowRHS_eq_pullbackBackgroundRicciFlowRHS_of_inner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {g' : MetricFamily (I := I) (M := M)}
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (sol.toIntrinsicDeTurckSolution.metric t).inner ((gauge.maps t) x)
          (((gauge.maps t).pushforwardTangent x) u)
          (((gauge.maps t).pushforwardTangent x) v))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.toIntrinsicDeTurckSolution.background t) 1) :
    intrinsicRicciFlowRHS (I := I) (M := M) g' =
      ricciFlowRHS (I := I) (M := M) g'
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.toIntrinsicDeTurckSolution.background) hpull := by
  exact sol.intrinsicRicciFlowRHS_eq_pullbackBackgroundRicciFlowRHS_of_inner
    (Φ := gauge.maps) (g' := g') hinner hbackground hpull

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.isIntrinsicRicciFlowOn_of_pullbackBackgroundEquation
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {g' : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (sol.toIntrinsicDeTurckSolution.metric t).inner ((gauge.maps t) x)
          (((gauge.maps t).pushforwardTangent x) u)
          (((gauge.maps t).pushforwardTangent x) v))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M) g' gdot s)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ s →
      SatisfiesEquationAt (I := I) (M := M) g'
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.toIntrinsicDeTurckSolution.background) hpull gdot t) :
    IsIntrinsicRicciFlowOn (I := I) (M := M) g' gdot s := by
  exact sol.isIntrinsicRicciFlowOn_of_pullbackBackgroundEquation_of_inner
    (Φ := gauge.maps) (g' := g') (gdot := gdot) (s := s)
    hinner hbackground hpull hderiv heq

noncomputable def AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.toIntrinsicLocalSolution_of_pullbackBackgroundEquation
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {g' : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (sol.toIntrinsicDeTurckSolution.metric t).inner ((gauge.maps t) x)
          (((gauge.maps t).pushforwardTangent x) u)
          (((gauge.maps t).pushforwardTangent x) v))
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M) g' gdot
      sol.toIntrinsicDeTurckSolution.timeSet)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ sol.toIntrinsicDeTurckSolution.timeSet →
      SatisfiesEquationAt (I := I) (M := M) g'
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.toIntrinsicDeTurckSolution.background) hpull gdot t) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := sol.terminalTime
  initial_lt_terminal := sol.initial_lt_terminal
  toIntrinsicSolution :=
    { timeSet := sol.toIntrinsicDeTurckSolution.timeSet
      metric := g'
      metricVelocity := gdot
      isRicciFlow :=
        gauge.isIntrinsicRicciFlowOn_of_pullbackBackgroundEquation sol
          hinner hbackground hpull hderiv heq }
  interval_subset := sol.interval_subset
  matchesInitialMetric := by
    intro x u v
    change (g' ivp.initialTime).inner x u v = ivp.initialMetric.inner x u v
    rw [gauge.transformedMetric_eq_initial_of_inner sol hinner]

/-- A fully checked gauge-reduced Ricci-DeTurck local solution: a DeTurck local solution, an
anchored diffeomorphism gauge, the transformed metric/velocity, and the hypotheses proving that the
transformed metric satisfies intrinsic Ricci flow. The fields are exactly the non-identity gauge
reduction obligations left after constructing a DeTurck solution and its gauge. -/
structure GaugeReducedIntrinsicDeTurckLocalSolution
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  /-- The source intrinsic Ricci-DeTurck local solution. -/
  source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp
  /-- The anchored diffeomorphism gauge used to transform the source solution. -/
  gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
    source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
    source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime
  /-- The transformed metric. -/
  transformedMetric : MetricFamily (I := I) (M := M)
  /-- The transformed metric velocity. -/
  transformedVelocity : MetricTensorFamily (I := I) (M := M)
  /-- The transformed metric is the gauge pullback of the source metric. -/
  transformed_inner :
    ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (transformedMetric t).inner x u v =
        (source.toIntrinsicDeTurckSolution.metric t).inner ((gauge.maps t) x)
          (((gauge.maps t).pushforwardTangent x) u)
          (((gauge.maps t).pushforwardTangent x) v)
  /-- The source background is Levi-Civita for the source metric. -/
  background_isLeviCivita :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric
      source.toIntrinsicDeTurckSolution.background
  /-- The pulled-back background is slicewise `C¹`. -/
  pullbackBackground_contMDiff :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          gauge.maps source.toIntrinsicDeTurckSolution.background t) 1
  /-- The transformed metric has the prescribed transformed velocity on the source time set. -/
  transformed_hasTimeDerivative :
    HasTimeDerivativeOn (I := I) (M := M)
      transformedMetric transformedVelocity source.toIntrinsicDeTurckSolution.timeSet
  /-- The transformed velocity satisfies the connection-parametrized Ricci-flow equation for the
  pulled-back background. -/
  transformed_equation :
    ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      SatisfiesEquationAt (I := I) (M := M)
        transformedMetric
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          gauge.maps source.toIntrinsicDeTurckSolution.background)
        pullbackBackground_contMDiff transformedVelocity t

/-- The source DeTurck one-form transported by an actual `C³` gauge. This is the one-form whose
metric dual gives the gauge-correction term in the velocity of the pulled-back metric. -/
noncomputable def IntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (t : ℝ) (x : M) : TM x →L[ℝ] ℝ :=
  connectionDifferenceTraceOneForm (I := I) (M := M)
    (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      gauge3.maps
      (chosenLeviCivitaFamily (I := I) (M := M)
        source.toIntrinsicDeTurckSolution.metric))
    (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      gauge3.maps source.toIntrinsicDeTurckSolution.background)
    t x

@[simp] theorem IntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (t : ℝ) (x : M) (w : TM x) :
    source.pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge gauge3 t x w =
      connectionDifferenceTraceOneForm (I := I) (M := M)
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps
          (chosenLeviCivitaFamily (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric))
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background)
        t x w := rfl

noncomputable def IntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime) :
    CovariantDerivative.TimeDependentVectorField (I := I) (M := M) :=
  fun t x ↦ by
    let pulledMetric :=
      gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric
    letI : Bundle.RiemannianBundle TM := ⟨(pulledMetric t).toRiemannianMetric⟩
    exact CovariantDerivative.rieszMap (I := I) x
      (source.pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge gauge3 t x)

@[simp] theorem IntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (t : ℝ) (x : M) :
    source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t x =
      (let pulledMetric :=
        gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric
       letI : Bundle.RiemannianBundle TM := ⟨(pulledMetric t).toRiemannianMetric⟩
       CovariantDerivative.rieszMap (I := I) x
        (source.pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge gauge3 t x)) := rfl

/-- The concrete velocity predicted by differentiating the actual `C³` gauge pullback of the
source DeTurck metric: source velocity transported to the gauge image, minus the pulled-back
DeTurck Lie-derivative correction. -/
noncomputable def IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime) :
    MetricTensorFamily (I := I) (M := M) :=
  fun t x u v ↦
    source.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x)
        ((gauge3.maps t).pushforwardTangent x u)
        ((gauge3.maps t).pushforwardTangent x v) -
      (((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric) t).inner x
          ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                source.toIntrinsicDeTurckSolution.metric) t)
            (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v +
        ((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric) t).inner x u
          ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                source.toIntrinsicDeTurckSolution.metric) t)
            (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v))

@[simp] theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (t : ℝ) (x : M) (u v : TM x) :
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
      source.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)
          ((gauge3.maps t).pushforwardTangent x v) -
        (((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric) t).inner x
            ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
                gauge3.maps
                (chosenLeviCivitaFamily (I := I) (M := M)
                  source.toIntrinsicDeTurckSolution.metric) t)
              (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v +
          ((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric) t).inner x u
            ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
                gauge3.maps
                (chosenLeviCivitaFamily (I := I) (M := M)
                source.toIntrinsicDeTurckSolution.metric) t)
              (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v)) := rfl

theorem IntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge_eq_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (t : ℝ) (x : M) (w : TM x) :
    source.pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge gauge3 t x w =
      intrinsicDeTurckOneForm (I := I) (M := M)
        source.toIntrinsicDeTurckSolution.metric
        source.toIntrinsicDeTurckSolution.background t
        ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x w) :=
  SmoothSelfDiffeomorph3Family.traceOneForm_pullbackChosenLeviCivita_background_apply
    (I := I) (M := M) gauge3.maps
    source.toIntrinsicDeTurckSolution.metric
    source.toIntrinsicDeTurckSolution.background w

theorem IntrinsicDeTurckLocalSolution.pushforward_riesz_pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (t : ℝ) (x : M) :
    (gauge3.maps t).pushforwardTangent x
        (letI : Bundle.RiemannianBundle TM :=
          ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
            t).toRiemannianMetric⟩
         CovariantDerivative.rieszMap (I := I) x
          (source.pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge gauge3 t x)) =
      intrinsicDeTurckVectorField (I := I) (M := M)
        source.toIntrinsicDeTurckSolution.metric
        source.toIntrinsicDeTurckSolution.background t ((gauge3.maps t) x) := by
  have hpush2 :
      ((gauge3.maps t).toSmoothSelfDiffeomorph2).pushforwardTangent x
          (letI : Bundle.RiemannianBundle TM :=
            ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
              t).toRiemannianMetric⟩
           CovariantDerivative.rieszMap (I := I) x
            (source.pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge gauge3 t x)) =
        (letI : Bundle.RiemannianBundle TM :=
          ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩
         CovariantDerivative.rieszMap (I := I) ((gauge3.maps t) x)
          (intrinsicDeTurckOneForm (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric
            source.toIntrinsicDeTurckSolution.background t ((gauge3.maps t) x))) := by
    exact SmoothSelfDiffeomorph2.pushforwardTangent_rieszMap_of_pullback_inner
      (I := I) (M := M) (φ := (gauge3.maps t).toSmoothSelfDiffeomorph2)
      (g := source.toIntrinsicDeTurckSolution.metric t)
      (g' := (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric) t)
      (fun y u v => rfl)
      (source.pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge gauge3 t x)
      (intrinsicDeTurckOneForm (I := I) (M := M)
        source.toIntrinsicDeTurckSolution.metric
        source.toIntrinsicDeTurckSolution.background t ((gauge3.maps t) x))
      (fun u =>
        source.pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge_eq_source gauge3 t x u)
  have hpush :
      (gauge3.maps t).pushforwardTangent x
          (letI : Bundle.RiemannianBundle TM :=
            ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
              t).toRiemannianMetric⟩
           CovariantDerivative.rieszMap (I := I) x
            (source.pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge gauge3 t x)) =
        (letI : Bundle.RiemannianBundle TM :=
          ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩
         CovariantDerivative.rieszMap (I := I) ((gauge3.maps t) x)
          (intrinsicDeTurckOneForm (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric
            source.toIntrinsicDeTurckSolution.background t ((gauge3.maps t) x))) := by
    rw [← SmoothSelfDiffeomorph3.toSmoothSelfDiffeomorph2_pushforwardTangent]
    exact hpush2
  simpa [intrinsicDeTurckVectorField,
    SmoothSelfDiffeomorph3.pushforwardTangent_apply] using hpush

theorem IntrinsicDeTurckLocalSolution.pushforward_pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (t : ℝ) (x : M) :
    (gauge3.maps t).pushforwardTangent x
        (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t x) =
      intrinsicDeTurckVectorField (I := I) (M := M)
        source.toIntrinsicDeTurckSolution.metric
        source.toIntrinsicDeTurckSolution.background t ((gauge3.maps t) x) := by
  simpa [IntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge]
    using
      source.pushforward_riesz_pulledBackSourceDeTurckOneFormOfDiffeomorph3Gauge gauge3 t x

theorem IntrinsicDeTurckLocalSolution.diffeomorph3Gauge_hasMFDerivAt_pulledBackSourceDeTurckVectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) :
    HasMFDerivAt[source.toIntrinsicDeTurckSolution.timeSet]
      (fun τ : ℝ ↦ gauge3.maps.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (-((gauge3.maps t).pushforwardTangent x
          (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t x)))) := by
  have hvec :=
    source.pushforward_pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t x
  rw [hvec]
  simpa [intrinsicDeTurckGaugeField] using gauge3.hasMFDerivAt ht x

/-- The concrete pulled-back source DeTurck vector field for a `C³` gauge is the ordinary
pullback of the source DeTurck vector field by the time-slice diffeomorphism. -/
theorem IntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_eq_pullbackVectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (t : ℝ) :
    source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t =
      ((gauge3.maps t).toSmoothSelfDiffeomorph2).pullbackVectorField
        (intrinsicDeTurckVectorField (I := I) (M := M)
          source.toIntrinsicDeTurckSolution.metric
          source.toIntrinsicDeTurckSolution.background t) := by
  funext x
  calc
    source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t x =
        (gauge3.maps t).pullbackTangent x
          ((gauge3.maps t).pushforwardTangent x
            (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t x)) := by
          exact ((gauge3.maps t).pullbackTangent_pushforwardTangent x
            (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t x)).symm
    _ = (gauge3.maps t).pullbackTangent x
        (intrinsicDeTurckVectorField (I := I) (M := M)
          source.toIntrinsicDeTurckSolution.metric
          source.toIntrinsicDeTurckSolution.background t ((gauge3.maps t) x)) := by
          rw [source.pushforward_pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge
            gauge3 t x]
    _ = ((gauge3.maps t).toSmoothSelfDiffeomorph2).pullbackVectorField
        (intrinsicDeTurckVectorField (I := I) (M := M)
          source.toIntrinsicDeTurckSolution.metric
          source.toIntrinsicDeTurckSolution.background t) x := rfl

theorem IntrinsicDeTurckLocalSolution.pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (t : ℝ) (x : M) (u : TM x) :
    (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps
        (chosenLeviCivitaFamily (I := I) (M := M)
          source.toIntrinsicDeTurckSolution.metric) t)
      (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u =
      (gauge3.maps t).pullbackTangent x
        (((chosenLeviCivitaFamily (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric) t)
          (intrinsicDeTurckVectorField (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric
            source.toIntrinsicDeTurckSolution.background t)
          ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)) := by
  rw [source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_eq_pullbackVectorField
    gauge3 t]
  simp only [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily_apply,
    SmoothSelfDiffeomorph2.pullbackCovariantDerivative_apply,
    SmoothSelfDiffeomorph2.pushforwardVectorField_pullbackVectorField,
    SmoothSelfDiffeomorph3.toSmoothSelfDiffeomorph2_apply,
    SmoothSelfDiffeomorph3.toSmoothSelfDiffeomorph2_pushforwardTangent,
    SmoothSelfDiffeomorph3.toSmoothSelfDiffeomorph2_pullbackTangent]
  rfl

theorem IntrinsicDeTurckLocalSolution.pushforwardTangent_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (t : ℝ) (x : M) (u : TM x) :
    (gauge3.maps t).pushforwardTangent x
      ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps
          (chosenLeviCivitaFamily (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric) t)
        (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) =
      ((chosenLeviCivitaFamily (I := I) (M := M)
          source.toIntrinsicDeTurckSolution.metric) t)
        (intrinsicDeTurckVectorField (I := I) (M := M)
          source.toIntrinsicDeTurckSolution.metric
          source.toIntrinsicDeTurckSolution.background t)
        ((gauge3.maps t) x)
        ((gauge3.maps t).pushforwardTangent x u) := by
  rw [source.pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_apply
    gauge3 t x u]
  exact (gauge3.maps t).pushforwardTangent_pullbackTangent x _

theorem IntrinsicDeTurckLocalSolution.pullbackMetric_inner_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_left
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (t : ℝ) (x : M) (u v : TM x) :
    ((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric) t).inner x
      ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps
          (chosenLeviCivitaFamily (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric) t)
        (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v =
      (source.toIntrinsicDeTurckSolution.metric t).inner ((gauge3.maps t) x)
        (((chosenLeviCivitaFamily (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric) t)
          (intrinsicDeTurckVectorField (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric
            source.toIntrinsicDeTurckSolution.background t)
          ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u))
        ((gauge3.maps t).pushforwardTangent x v) := by
  let A : TM x :=
    (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps
        (chosenLeviCivitaFamily (I := I) (M := M)
          source.toIntrinsicDeTurckSolution.metric) t)
      (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u
  calc
    ((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric) t).inner x A v =
        (source.toIntrinsicDeTurckSolution.metric t).inner ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x A)
          ((gauge3.maps t).pushforwardTangent x v) := rfl
    _ = (source.toIntrinsicDeTurckSolution.metric t).inner ((gauge3.maps t) x)
        (((chosenLeviCivitaFamily (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric) t)
          (intrinsicDeTurckVectorField (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric
            source.toIntrinsicDeTurckSolution.background t)
          ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u))
        ((gauge3.maps t).pushforwardTangent x v) := by
          rw [show (gauge3.maps t).pushforwardTangent x A =
              ((chosenLeviCivitaFamily (I := I) (M := M)
                  source.toIntrinsicDeTurckSolution.metric) t)
                (intrinsicDeTurckVectorField (I := I) (M := M)
                  source.toIntrinsicDeTurckSolution.metric
                  source.toIntrinsicDeTurckSolution.background t)
                ((gauge3.maps t) x)
                ((gauge3.maps t).pushforwardTangent x u) by
            simpa [A] using
              source.pushforwardTangent_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_apply
                gauge3 t x u]

theorem IntrinsicDeTurckLocalSolution.pullbackMetric_inner_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_right
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (t : ℝ) (x : M) (u v : TM x) :
    ((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric) t).inner x u
      ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps
          (chosenLeviCivitaFamily (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric) t)
        (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v) =
      (source.toIntrinsicDeTurckSolution.metric t).inner ((gauge3.maps t) x)
        ((gauge3.maps t).pushforwardTangent x u)
        (((chosenLeviCivitaFamily (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric) t)
          (intrinsicDeTurckVectorField (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric
            source.toIntrinsicDeTurckSolution.background t)
          ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x v)) := by
  let A : TM x :=
    (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps
        (chosenLeviCivitaFamily (I := I) (M := M)
          source.toIntrinsicDeTurckSolution.metric) t)
      (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v
  calc
    ((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric) t).inner x u A =
        (source.toIntrinsicDeTurckSolution.metric t).inner ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)
          ((gauge3.maps t).pushforwardTangent x A) := rfl
    _ = (source.toIntrinsicDeTurckSolution.metric t).inner ((gauge3.maps t) x)
        ((gauge3.maps t).pushforwardTangent x u)
        (((chosenLeviCivitaFamily (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric) t)
          (intrinsicDeTurckVectorField (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric
            source.toIntrinsicDeTurckSolution.background t)
          ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x v)) := by
          rw [show (gauge3.maps t).pushforwardTangent x A =
              ((chosenLeviCivitaFamily (I := I) (M := M)
                  source.toIntrinsicDeTurckSolution.metric) t)
                (intrinsicDeTurckVectorField (I := I) (M := M)
                  source.toIntrinsicDeTurckSolution.metric
                  source.toIntrinsicDeTurckSolution.background t)
                ((gauge3.maps t) x)
                ((gauge3.maps t).pushforwardTangent x v) by
            simpa [A] using
              source.pushforwardTangent_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_apply
                gauge3 t x v]

theorem IntrinsicDeTurckLocalSolution.pullbackSourceDeTurckCorrectionOfDiffeomorph3Gauge_eq_sourceDeTurckCorrection
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (t : ℝ) (x : M) (u v : TM x) :
    ((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric) t).inner x
        ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps
            (chosenLeviCivitaFamily (I := I) (M := M)
              source.toIntrinsicDeTurckSolution.metric) t)
          (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v +
      ((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric) t).inner x u
        ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps
            (chosenLeviCivitaFamily (I := I) (M := M)
              source.toIntrinsicDeTurckSolution.metric) t)
          (source.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v) =
      intrinsicDeTurckCorrection (I := I) (M := M)
        source.toIntrinsicDeTurckSolution.metric
        source.toIntrinsicDeTurckSolution.background t
        ((gauge3.maps t) x)
        ((gauge3.maps t).pushforwardTangent x u)
        ((gauge3.maps t).pushforwardTangent x v) := by
  rw [
    source.pullbackMetric_inner_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_left
      gauge3 t x u v,
    source.pullbackMetric_inner_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_right
      gauge3 t x u v]
  rfl

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_neg_two_backgroundRicciCurvature
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
      (-2 : ℝ) *
        (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)
          ((gauge3.maps t).pushforwardTangent x v) := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (source.toIntrinsicDeTurckSolution.background t) 1 :=
    hsourceBackground t
  have hvelocity :
      source.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)
          ((gauge3.maps t).pushforwardTangent x v) =
        (-2 : ℝ) *
          (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
            ((gauge3.maps t) x)
            ((gauge3.maps t).pushforwardTangent x u)
            ((gauge3.maps t).pushforwardTangent x v) +
        intrinsicDeTurckCorrection (I := I) (M := M)
          source.toIntrinsicDeTurckSolution.metric
          source.toIntrinsicDeTurckSolution.background t
          ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)
          ((gauge3.maps t).pushforwardTangent x v) := by
    calc
      source.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)
          ((gauge3.maps t).pushforwardTangent x v) =
          intrinsicRicciFlowRHS (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric t
            ((gauge3.maps t) x)
            ((gauge3.maps t).pushforwardTangent x u)
            ((gauge3.maps t).pushforwardTangent x v) +
          intrinsicDeTurckCorrection (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric
            source.toIntrinsicDeTurckSolution.background t
            ((gauge3.maps t) x)
            ((gauge3.maps t).pushforwardTangent x u)
            ((gauge3.maps t).pushforwardTangent x v) := by
        calc
          source.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x)
              ((gauge3.maps t).pushforwardTangent x u)
              ((gauge3.maps t).pushforwardTangent x v) =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                source.toIntrinsicDeTurckSolution.metric
                source.toIntrinsicDeTurckSolution.background t
                ((gauge3.maps t) x)
                ((gauge3.maps t).pushforwardTangent x u)
                ((gauge3.maps t).pushforwardTangent x v) :=
            intrinsicDeTurckSolution_equation
              (I := I) (M := M) source.toIntrinsicDeTurckSolution ht
              ((gauge3.maps t) x)
              ((gauge3.maps t).pushforwardTangent x u)
              ((gauge3.maps t).pushforwardTangent x v)
          _ = intrinsicRicciFlowRHS (I := I) (M := M)
              source.toIntrinsicDeTurckSolution.metric t
              ((gauge3.maps t) x)
              ((gauge3.maps t).pushforwardTangent x u)
              ((gauge3.maps t).pushforwardTangent x v) +
            intrinsicDeTurckCorrection (I := I) (M := M)
              source.toIntrinsicDeTurckSolution.metric
              source.toIntrinsicDeTurckSolution.background t
              ((gauge3.maps t) x)
              ((gauge3.maps t).pushforwardTangent x u)
              ((gauge3.maps t).pushforwardTangent x v) := rfl
      _ = ricciFlowRHS (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric
            source.toIntrinsicDeTurckSolution.background
            hsourceBackground t
            ((gauge3.maps t) x)
            ((gauge3.maps t).pushforwardTangent x u)
            ((gauge3.maps t).pushforwardTangent x v) +
          intrinsicDeTurckCorrection (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric
            source.toIntrinsicDeTurckSolution.background t
            ((gauge3.maps t) x)
            ((gauge3.maps t).pushforwardTangent x u)
            ((gauge3.maps t).pushforwardTangent x v) := by
        rw [intrinsicRicciFlowRHS_eq_ricciFlowRHS_of_isLeviCivita
          (I := I) (M := M)
          source.toIntrinsicDeTurckSolution.metric hsourceBackground hbackground]
      _ = (-2 : ℝ) *
          (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
            ((gauge3.maps t) x)
            ((gauge3.maps t).pushforwardTangent x u)
            ((gauge3.maps t).pushforwardTangent x v) +
          intrinsicDeTurckCorrection (I := I) (M := M)
            source.toIntrinsicDeTurckSolution.metric
            source.toIntrinsicDeTurckSolution.background t
            ((gauge3.maps t) x)
            ((gauge3.maps t).pushforwardTangent x u)
            ((gauge3.maps t).pushforwardTangent x v) := rfl
  rw [IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_apply,
    source.pullbackSourceDeTurckCorrectionOfDiffeomorph3Gauge_eq_sourceDeTurckCorrection
      gauge3 t x u v]
  rw [hvelocity]
  ring

theorem IntrinsicDeTurckLocalSolution.sourceRicciTransport_initial_of_diffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (x : M) (u v : TM x) :
    (letI : Bundle.RiemannianBundle TM :=
      ⟨(source.toIntrinsicDeTurckSolution.metric ivp.initialTime).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background ivp.initialTime) 1 :=
      hsourceBackground ivp.initialTime;
     (source.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature
      ((gauge3.maps ivp.initialTime) x)
      ((gauge3.maps ivp.initialTime).pushforwardTangent x u)
      ((gauge3.maps ivp.initialTime).pushforwardTangent x v)) =
    (letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        ivp.initialTime).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background ivp.initialTime) 1 :=
      hpull ivp.initialTime;
     (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u v) := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      ivp.initialTime).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (source.toIntrinsicDeTurckSolution.background ivp.initialTime) 1 :=
    hsourceBackground ivp.initialTime
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background ivp.initialTime) 1 :=
    hpull ivp.initialTime
  symm
  simpa using
    SmoothSelfDiffeomorph3Family.ricciCurvature_pullbackConnectionFamily_eq_at_anchored_time
      (I := I) (M := M) (Φ := gauge3.maps)
      (cov := source.toIntrinsicDeTurckSolution.background)
      hsourceBackground hpull gauge3.anchored (x := x) u v

theorem IntrinsicDeTurckLocalSolution.sourceRicciTransport_of_right_slot_curvature
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hRight : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x, ∀ z : TM ((gauge3.maps t) x),
        (source.toIntrinsicDeTurckSolution.background t).curvatureAux
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) z)
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x u))
          ((gauge3.maps t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v))
          ((gauge3.maps t) x) =
        (source.toIntrinsicDeTurckSolution.background t).curvatureAux
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) z)
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x u))
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x v))
          ((gauge3.maps t) x))
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    (letI : Bundle.RiemannianBundle TM :=
      ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
     (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
      ((gauge3.maps t) x)
      ((gauge3.maps t).pushforwardTangent x u)
      ((gauge3.maps t).pushforwardTangent x v)) =
    (letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
      hpull t;
     (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v) := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (source.toIntrinsicDeTurckSolution.background t) 1 :=
    hsourceBackground t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
    hpull t
  symm
  simpa using
    SmoothSelfDiffeomorph3Family.ricciCurvature_pullbackConnectionFamily_eq_of_right_slot
      (I := I) (M := M) (Φ := gauge3.maps)
      (cov := source.toIntrinsicDeTurckSolution.background)
      hsourceBackground hpull (t := t) (x := x) u v (hRight ht x u v)

theorem IntrinsicDeTurckLocalSolution.sourceRicciTransport_of_right_slot_section_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hRightEq : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ w : TM x,
        (gauge3.maps t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) =
          CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x w))
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    (letI : Bundle.RiemannianBundle TM :=
      ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
     (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
      ((gauge3.maps t) x)
      ((gauge3.maps t).pushforwardTangent x u)
      ((gauge3.maps t).pushforwardTangent x v)) =
    (letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
      hpull t;
     (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v) := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (source.toIntrinsicDeTurckSolution.background t) 1 :=
    hsourceBackground t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
    hpull t
  symm
  simpa using
    SmoothSelfDiffeomorph3Family.ricciCurvature_pullbackConnectionFamily_eq_of_right_slot_section_eq
      (I := I) (M := M) (Φ := gauge3.maps)
      (cov := source.toIntrinsicDeTurckSolution.background)
      hsourceBackground hpull (t := t) (x := x) u v (hRightEq ht x v)

theorem IntrinsicDeTurckLocalSolution.sourceRicciTransport_of_eventuallyEq_right_slot
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hRightEq : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ w : TM x,
        (gauge3.maps t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) =ᶠ[nhds ((gauge3.maps t) x)]
          CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x w))
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    (letI : Bundle.RiemannianBundle TM :=
      ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
     (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
      ((gauge3.maps t) x)
      ((gauge3.maps t).pushforwardTangent x u)
      ((gauge3.maps t).pushforwardTangent x v)) =
    (letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
      hpull t;
     (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v) := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (source.toIntrinsicDeTurckSolution.background t) 1 :=
    hsourceBackground t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
    hpull t
  symm
  simpa using
    SmoothSelfDiffeomorph3Family.ricciCurvature_pullbackConnectionFamily_eq_of_eventuallyEq_right_slot
      (I := I) (M := M) (Φ := gauge3.maps)
      (cov := source.toIntrinsicDeTurckSolution.background)
      hsourceBackground hpull (t := t) (x := x) u v (hRightEq ht x v)

theorem IntrinsicDeTurckLocalSolution.sourceRicciTransport_of_right_slot_localFrameCoeff
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E)
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hZpushCoeff : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ w : TM x, ∀ i : ι,
        ContMDiff I 𝓘(ℝ) 2
          (fun y' ↦
            (trivializationAt E TM ((gauge3.maps t) x)).localFrameCoeff I b i y'
              (((gauge3.maps t).pushforwardVectorField
                (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w)) y')))
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    (letI : Bundle.RiemannianBundle TM :=
      ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
     (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
      ((gauge3.maps t) x)
      ((gauge3.maps t).pushforwardTangent x u)
      ((gauge3.maps t).pushforwardTangent x v)) =
    (letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
      hpull t;
     (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v) := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (source.toIntrinsicDeTurckSolution.background t) 1 :=
    hsourceBackground t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
    hpull t
  symm
  simpa using
    SmoothSelfDiffeomorph3Family.ricciCurvature_pullbackConnectionFamily_eq_of_right_slot_localFrameCoeff
      (I := I) (M := M) (Φ := gauge3.maps)
      (b := b) (cov := source.toIntrinsicDeTurckSolution.background)
      hsourceBackground hpull (t := t) (x := x) u v
      (hZpushCoeff ht x v)

theorem IntrinsicDeTurckLocalSolution.sourceRicciTransport_of_right_slot_tsupport_subset
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E)
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hZsupport : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ ⦃z : M⦄,
        z ∈ tsupport (CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x) →
          (gauge3.maps t) z ∈ (trivializationAt E TM ((gauge3.maps t) x)).baseSet)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    (letI : Bundle.RiemannianBundle TM :=
      ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
     (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
      ((gauge3.maps t) x)
      ((gauge3.maps t).pushforwardTangent x u)
      ((gauge3.maps t).pushforwardTangent x v)) =
    (letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
      hpull t;
     (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v) := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (source.toIntrinsicDeTurckSolution.background t) 1 :=
    hsourceBackground t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
    hpull t
  symm
  simpa using
    SmoothSelfDiffeomorph3Family.ricciCurvature_pullbackConnectionFamily_eq_of_right_slot_tsupport_subset
      (I := I) (M := M) (Φ := gauge3.maps)
      (b := b) (cov := source.toIntrinsicDeTurckSolution.background)
      hsourceBackground hpull (t := t) (x := x) u v
      (hZsupport ht x)

theorem IntrinsicDeTurckLocalSolution.sourceRicciTransport_of_right_slot_tsupport_subset_finBasis
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hZsupport : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ ⦃z : M⦄,
        z ∈ tsupport (CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x) →
          (gauge3.maps t) z ∈ (trivializationAt E TM ((gauge3.maps t) x)).baseSet)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    (letI : Bundle.RiemannianBundle TM :=
      ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
     (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
      ((gauge3.maps t) x)
      ((gauge3.maps t).pushforwardTangent x u)
      ((gauge3.maps t).pushforwardTangent x v)) =
    (letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
      hpull t;
     (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v) := by
  classical
  exact source.sourceRicciTransport_of_right_slot_tsupport_subset
    (Module.finBasis ℝ E) gauge3 hpull hsourceBackground hZsupport ht x u v

theorem IntrinsicDeTurckLocalSolution.sourceRicciTransport
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (_ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    (letI : Bundle.RiemannianBundle TM :=
      ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
     (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
      ((gauge3.maps t) x)
      ((gauge3.maps t).pushforwardTangent x u)
      ((gauge3.maps t).pushforwardTangent x v)) =
    (letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
      hpull t;
     (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v) := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (source.toIntrinsicDeTurckSolution.background t) 1 :=
    hsourceBackground t
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
    hpull t
  symm
  simpa using
    SmoothSelfDiffeomorph3Family.ricciCurvature_pullbackConnectionFamily
      (I := I) (M := M) (Φ := gauge3.maps)
      (cov := source.toIntrinsicDeTurckSolution.background)
      hsourceBackground hpull (t := t) (x := x) u v

theorem IntrinsicDeTurckLocalSolution.sourceRicciTransport_of_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    (letI : Bundle.RiemannianBundle TM :=
      ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1 :=
      source.background_contMDiff_of_isLeviCivita hbackground t;
     (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
      ((gauge3.maps t) x)
      ((gauge3.maps t).pushforwardTangent x u)
      ((gauge3.maps t).pushforwardTangent x v)) =
    (letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        t).toRiemannianMetric⟩;
     letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
      gauge3.pullbackBackgroundConnection_contMDiff hbackground t;
     (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v) := by
  exact source.sourceRicciTransport gauge3
    (gauge3.pullbackBackgroundConnection_contMDiff hbackground)
    (source.background_contMDiff_of_isLeviCivita hbackground) ht x u v

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_neg_two_pullbackBackgroundRicciCurvature_of_sourceRicciTransportAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (hRicciTransportAt :
      ∀ x : M, ∀ u v : TM x,
        (letI : Bundle.RiemannianBundle TM :=
          ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
         letI :
            CovariantDerivative.ContMDiffCovariantDerivative
              (source.toIntrinsicDeTurckSolution.background t) 1 :=
          hsourceBackground t;
         (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)
          ((gauge3.maps t).pushforwardTangent x v)) =
        (letI : Bundle.RiemannianBundle TM :=
          ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
            t).toRiemannianMetric⟩;
         letI :
            CovariantDerivative.ContMDiffCovariantDerivative
              (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
                gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
          hpull t;
         (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v))
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
      hpull t;
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
      (-2 : ℝ) *
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
    hpull t
  calc
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
        (-2 : ℝ) *
          (letI : Bundle.RiemannianBundle TM :=
            ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
           letI :
              CovariantDerivative.ContMDiffCovariantDerivative
                (source.toIntrinsicDeTurckSolution.background t) 1 :=
            hsourceBackground t;
           (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
            ((gauge3.maps t) x)
            ((gauge3.maps t).pushforwardTangent x u)
            ((gauge3.maps t).pushforwardTangent x v)) := by
      simpa using
        source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_neg_two_backgroundRicciCurvature
          gauge3 hbackground hsourceBackground ht x u v
    _ = (-2 : ℝ) *
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v := by
      exact congrArg (fun r : ℝ => (-2 : ℝ) * r) (hRicciTransportAt x u v)

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_neg_two_pullbackBackgroundRicciCurvature_of_sourceRicciTransport
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hRicciTransport : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x,
        (letI : Bundle.RiemannianBundle TM :=
          ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
         letI :
            CovariantDerivative.ContMDiffCovariantDerivative
              (source.toIntrinsicDeTurckSolution.background t) 1 :=
          hsourceBackground t;
         (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)
          ((gauge3.maps t).pushforwardTangent x v)) =
        (letI : Bundle.RiemannianBundle TM :=
          ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
            t).toRiemannianMetric⟩;
         letI :
            CovariantDerivative.ContMDiffCovariantDerivative
              (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
                gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
          hpull t;
         (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v))
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
      hpull t;
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
      (-2 : ℝ) *
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v := by
  exact
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_neg_two_pullbackBackgroundRicciCurvature_of_sourceRicciTransportAt
      gauge3 hbackground hpull hsourceBackground ht (hRicciTransport ht) x u v

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_neg_two_pullbackBackgroundRicciCurvature
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
      hpull t;
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
      (-2 : ℝ) *
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v := by
  exact
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_neg_two_pullbackBackgroundRicciCurvature_of_sourceRicciTransportAt
      gauge3 hbackground hpull hsourceBackground ht
      (by
        intro y a b
        exact source.sourceRicciTransport gauge3 hpull hsourceBackground ht y a b)
      x u v

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_neg_two_pullbackBackgroundRicciCurvature_of_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
      gauge3.pullbackBackgroundConnection_contMDiff hbackground t;
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
      (-2 : ℝ) *
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v := by
  exact
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_neg_two_pullbackBackgroundRicciCurvature
      gauge3 hbackground
      (gauge3.pullbackBackgroundConnection_contMDiff hbackground)
      (source.background_contMDiff_of_isLeviCivita hbackground) ht x u v

/-- If the pulled-back background Ricci curvature vanishes at a slot, then the
geometric gauge-corrected velocity of the `C³` pullback vanishes at that slot. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_zero_of_pullbackBackgroundRicciCurvature_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x)
    (hRicciZero :
      (letI : Bundle.RiemannianBundle TM :=
        ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
          t).toRiemannianMetric⟩;
       letI :
          CovariantDerivative.ContMDiffCovariantDerivative
            (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
        gauge3.pullbackBackgroundConnection_contMDiff hbackground t;
       (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
         gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v) = 0) :
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v = 0 := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
    gauge3.pullbackBackgroundConnection_contMDiff hbackground t
  rw [
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_neg_two_pullbackBackgroundRicciCurvature_of_isLeviCivita
      gauge3 hbackground ht x u v,
    hRicciZero]
  ring

/-- Initial-time specialization of
`gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_zero_of_pullbackBackgroundRicciCurvature_eq_zero`. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_zero_initial_of_pullbackBackgroundRicciCurvature_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (x : M) (u v : TM x)
    (hRicciZero :
      (letI : Bundle.RiemannianBundle TM :=
        ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
          ivp.initialTime).toRiemannianMetric⟩;
       letI :
          CovariantDerivative.ContMDiffCovariantDerivative
            (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps source.toIntrinsicDeTurckSolution.background ivp.initialTime) 1 :=
        gauge3.pullbackBackgroundConnection_contMDiff hbackground ivp.initialTime;
       (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
         gauge3.maps source.toIntrinsicDeTurckSolution.background
         ivp.initialTime).ricciCurvature x u v) = 0) :
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 ivp.initialTime x u v = 0 :=
  source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_zero_of_pullbackBackgroundRicciCurvature_eq_zero
    gauge3 hbackground (intrinsicDeTurckLocalSolution_initialTime_mem source) x u v hRicciZero

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_sourceRicciTransportAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (hRicciTransportAt :
      ∀ x : M, ∀ u v : TM x,
        (letI : Bundle.RiemannianBundle TM :=
          ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
         letI :
            CovariantDerivative.ContMDiffCovariantDerivative
              (source.toIntrinsicDeTurckSolution.background t) 1 :=
          hsourceBackground t;
         (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)
          ((gauge3.maps t).pushforwardTangent x v)) =
        (letI : Bundle.RiemannianBundle TM :=
          ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
            t).toRiemannianMetric⟩;
         letI :
            CovariantDerivative.ContMDiffCovariantDerivative
              (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
                gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
          hpull t;
         (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v)) :
    SatisfiesEquationAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background)
      hpull
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3) t := by
  intro x u v
  letI : Bundle.RiemannianBundle TM :=
    ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
    hpull t
  simpa [ricciFlowRHS, ricciTensor] using
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_neg_two_pullbackBackgroundRicciCurvature_of_sourceRicciTransportAt
      gauge3 hbackground hpull hsourceBackground ht hRicciTransportAt x u v

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_sourceRicciTransport
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hRicciTransport : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x,
        (letI : Bundle.RiemannianBundle TM :=
          ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
         letI :
            CovariantDerivative.ContMDiffCovariantDerivative
              (source.toIntrinsicDeTurckSolution.background t) 1 :=
          hsourceBackground t;
         (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)
          ((gauge3.maps t).pushforwardTangent x v)) =
        (letI : Bundle.RiemannianBundle TM :=
          ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
            t).toRiemannianMetric⟩;
         letI :
            CovariantDerivative.ContMDiffCovariantDerivative
              (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
                gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
          hpull t;
         (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
            gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v))
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet) :
    SatisfiesEquationAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background)
      hpull
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3) t := by
  exact
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_sourceRicciTransportAt
      gauge3 hbackground hpull hsourceBackground ht (hRicciTransport ht)

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet) :
    SatisfiesEquationAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background)
      (gauge3.pullbackBackgroundConnection_contMDiff hbackground)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3) t := by
  exact
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_sourceRicciTransport
      gauge3 hbackground
      (gauge3.pullbackBackgroundConnection_contMDiff hbackground)
      (source.background_contMDiff_of_isLeviCivita hbackground)
      (fun {τ} hτ y a b =>
        source.sourceRicciTransport_of_isLeviCivita gauge3 hbackground (t := τ) hτ y a b)
      ht

/-- The remaining non-identity gauge time-regularity obligation, stated as the exact scalar
time-derivative formula for the pulled-back metric inner product. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackMetric_hasTimeDerivativeOn_of_inner_hasDerivAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x,
        HasDerivAt
          (fun τ ↦
            (source.toIntrinsicDeTurckSolution.metric τ).inner ((gauge3.maps τ) x)
              ((gauge3.maps τ).pushforwardTangent x u)
              ((gauge3.maps τ).pushforwardTangent x v))
          (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v) t) :
    HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet := by
  exact
    SmoothSelfDiffeomorph3Family.pullbackMetricFamily_hasTimeDerivativeOn_of_inner_hasDerivAt
      (I := I) (M := M) (Φ := gauge3.maps) hderiv

/-- Extract the exact scalar inner-product derivative obligation from a proved time derivative for
the `C³` gauge-pulled metric with the concrete gauge-corrected velocity. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackMetric_inner_hasDerivAt_of_hasTimeDerivativeOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    HasDerivAt
      (fun τ ↦
        (source.toIntrinsicDeTurckSolution.metric τ).inner ((gauge3.maps τ) x)
          ((gauge3.maps τ).pushforwardTangent x u)
          ((gauge3.maps τ).pushforwardTangent x v))
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v) t := by
  exact
    SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner_hasDerivAt_of_hasTimeDerivativeOn
      (I := I) (M := M) (Φ := gauge3.maps) hderiv ht x u v

/-- Single-time endpoint version of
`gaugeCorrectedPullbackMetric_hasTimeDerivativeOn_of_inner_hasDerivAt`. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackMetric_hasTimeDerivativeAt_of_inner_hasDerivAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {t : ℝ}
    (hderiv : ∀ x : M, ∀ u v : TM x,
      HasDerivAt
        (fun τ ↦
          (source.toIntrinsicDeTurckSolution.metric τ).inner ((gauge3.maps τ) x)
            ((gauge3.maps τ).pushforwardTangent x u)
            ((gauge3.maps τ).pushforwardTangent x v))
        (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v) t) :
    HasTimeDerivativeAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3) t := by
  exact
    SmoothSelfDiffeomorph3Family.pullbackMetricFamily_hasTimeDerivativeAt_of_inner_hasDerivAt
      (I := I) (M := M) (Φ := gauge3.maps) hderiv

/-- Extract the single-time scalar inner-product derivative obligation from a
proved endpoint time derivative for the concrete gauge-corrected velocity. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackMetric_inner_hasDerivAt_of_hasTimeDerivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {t : ℝ}
    (hderiv : HasTimeDerivativeAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3) t)
    (x : M) (u v : TM x) :
    HasDerivAt
      (fun τ ↦
        (source.toIntrinsicDeTurckSolution.metric τ).inner ((gauge3.maps τ) x)
          ((gauge3.maps τ).pushforwardTangent x u)
          ((gauge3.maps τ).pushforwardTangent x v))
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v) t := by
  exact
    SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner_hasDerivAt_of_hasTimeDerivativeAt
      (I := I) (M := M) (Φ := gauge3.maps) hderiv x u v

/-- DeTurck-specific closed-interval gluing from interior tensor time
regularity and endpoint tensor derivatives. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackMetric_hasTimeDerivativeOn_of_timeSet_eq_Icc_of_Ioo_endpoints
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {tmin tmax : ℝ}
    (htimeSet : source.toIntrinsicDeTurckSolution.timeSet = Set.Icc tmin tmax)
    (hIoo : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      (Set.Ioo tmin tmax))
    (hleft : HasTimeDerivativeAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      tmin)
    (hright : HasTimeDerivativeAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      tmax) :
    HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet := by
  intro t ht
  exact (HasTimeDerivativeOn.of_Ioo_endpoints hIoo hleft hright) (by
    simpa [htimeSet] using ht)

/-- DeTurck-specific closed-interval gluing from interior tensor time
regularity and scalar endpoint inner-product derivatives. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackMetric_hasTimeDerivativeOn_of_timeSet_eq_Icc_of_Ioo_endpointInner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {tmin tmax : ℝ}
    (htimeSet : source.toIntrinsicDeTurckSolution.timeSet = Set.Icc tmin tmax)
    (hIoo : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      (Set.Ioo tmin tmax))
    (hleft : ∀ x : M, ∀ u v : TM x,
      HasDerivAt
        (fun τ ↦
          (source.toIntrinsicDeTurckSolution.metric τ).inner ((gauge3.maps τ) x)
            ((gauge3.maps τ).pushforwardTangent x u)
            ((gauge3.maps τ).pushforwardTangent x v))
        (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3
          tmin x u v) tmin)
    (hright : ∀ x : M, ∀ u v : TM x,
      HasDerivAt
        (fun τ ↦
          (source.toIntrinsicDeTurckSolution.metric τ).inner ((gauge3.maps τ) x)
            ((gauge3.maps τ).pushforwardTangent x u)
            ((gauge3.maps τ).pushforwardTangent x v))
        (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3
          tmax x u v) tmax) :
    HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet :=
  source.gaugeCorrectedPullbackMetric_hasTimeDerivativeOn_of_timeSet_eq_Icc_of_Ioo_endpoints
    gauge3 htimeSet hIoo
    (source.gaugeCorrectedPullbackMetric_hasTimeDerivativeAt_of_inner_hasDerivAt
      gauge3 hleft)
    (source.gaugeCorrectedPullbackMetric_hasTimeDerivativeAt_of_inner_hasDerivAt
      gauge3 hright)

/-- DeTurck-specific closed-interval gluing from interior tensor time
regularity and tensor derivative data at the non-interior boundary points. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackMetric_hasTimeDerivativeOn_of_timeSet_eq_Icc_of_Ioo_boundary
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {tmin tmax : ℝ}
    (htimeSet : source.toIntrinsicDeTurckSolution.timeSet = Set.Icc tmin tmax)
    (hIoo : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      (Set.Ioo tmin tmax))
    (hboundary : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc tmin tmax → t ∉ Set.Ioo tmin tmax →
      HasTimeDerivativeAt (I := I) (M := M)
        (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
        t) :
    HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet := by
  intro t ht
  have htIcc : t ∈ Set.Icc tmin tmax := by
    simpa [htimeSet] using ht
  by_cases htInterior : t ∈ Set.Ioo tmin tmax
  · exact hIoo htInterior
  · exact hboundary htIcc htInterior

/-- DeTurck-specific closed-interval gluing from interior tensor time
regularity and scalar inner-product derivative data at the non-interior
boundary points. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackMetric_hasTimeDerivativeOn_of_timeSet_eq_Icc_of_Ioo_boundaryInner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {tmin tmax : ℝ}
    (htimeSet : source.toIntrinsicDeTurckSolution.timeSet = Set.Icc tmin tmax)
    (hIoo : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      (Set.Ioo tmin tmax))
    (hboundary : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc tmin tmax → t ∉ Set.Ioo tmin tmax →
      ∀ x : M, ∀ u v : TM x,
        HasDerivAt
          (fun τ ↦
            (source.toIntrinsicDeTurckSolution.metric τ).inner ((gauge3.maps τ) x)
              ((gauge3.maps τ).pushforwardTangent x u)
              ((gauge3.maps τ).pushforwardTangent x v))
          (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3
            t x u v) t) :
    HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet :=
  source.gaugeCorrectedPullbackMetric_hasTimeDerivativeOn_of_timeSet_eq_Icc_of_Ioo_boundary
    gauge3 htimeSet hIoo
    (fun {t} ht hnot ↦
      source.gaugeCorrectedPullbackMetric_hasTimeDerivativeAt_of_inner_hasDerivAt
        gauge3 (hboundary (t := t) ht hnot))

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_right_slot_curvature
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hRight : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x, ∀ z : TM ((gauge3.maps t) x),
        (source.toIntrinsicDeTurckSolution.background t).curvatureAux
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) z)
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x u))
          ((gauge3.maps t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v))
          ((gauge3.maps t) x) =
        (source.toIntrinsicDeTurckSolution.background t).curvatureAux
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) z)
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x u))
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x v))
          ((gauge3.maps t) x))
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet) :
    SatisfiesEquationAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background)
      hpull
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3) t := by
  exact
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_sourceRicciTransportAt
      gauge3 hbackground hpull hsourceBackground ht
      (by
        intro x u v
        exact source.sourceRicciTransport_of_right_slot_curvature
          gauge3 hpull hsourceBackground hRight ht x u v)

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_eventuallyEq_right_slot
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hRightEq : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ w : TM x,
        (gauge3.maps t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) =ᶠ[nhds ((gauge3.maps t) x)]
          CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x w))
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet) :
    SatisfiesEquationAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background)
      hpull
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3) t := by
  exact
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_sourceRicciTransportAt
      gauge3 hbackground hpull hsourceBackground ht
      (by
        intro x u v
        exact source.sourceRicciTransport_of_eventuallyEq_right_slot
          gauge3 hpull hsourceBackground hRightEq ht x u v)

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_right_slot_section_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hRightEq : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ w : TM x,
        (gauge3.maps t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) =
          CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x w))
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet) :
    SatisfiesEquationAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background)
      hpull
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3) t := by
  exact
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_sourceRicciTransportAt
      gauge3 hbackground hpull hsourceBackground ht
      (by
        intro x u v
        exact source.sourceRicciTransport_of_right_slot_section_eq
          gauge3 hpull hsourceBackground hRightEq ht x u v)

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_right_slot_localFrameCoeff
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E)
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hZpushCoeff : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ w : TM x, ∀ i : ι,
        ContMDiff I 𝓘(ℝ) 2
          (fun y' ↦
            (trivializationAt E TM ((gauge3.maps t) x)).localFrameCoeff I b i y'
              (((gauge3.maps t).pushforwardVectorField
                (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w)) y')))
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet) :
    SatisfiesEquationAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background)
      hpull
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3) t := by
  exact
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_sourceRicciTransportAt
      gauge3 hbackground hpull hsourceBackground ht
      (by
        intro x u v
        exact source.sourceRicciTransport_of_right_slot_localFrameCoeff
          b gauge3 hpull hsourceBackground hZpushCoeff ht x u v)

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_right_slot_tsupport_subset
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E)
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hZsupport : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ ⦃z : M⦄,
        z ∈ tsupport (CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x) →
          (gauge3.maps t) z ∈ (trivializationAt E TM ((gauge3.maps t) x)).baseSet)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet) :
    SatisfiesEquationAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background)
      hpull
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3) t := by
  exact
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_sourceRicciTransportAt
      gauge3 hbackground hpull hsourceBackground ht
      (by
        intro x u v
        exact source.sourceRicciTransport_of_right_slot_tsupport_subset
          b gauge3 hpull hsourceBackground hZsupport ht x u v)

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_right_slot_tsupport_subset_finBasis
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hZsupport : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ ⦃z : M⦄,
        z ∈ tsupport (CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x) →
          (gauge3.maps t) z ∈ (trivializationAt E TM ((gauge3.maps t) x)).baseSet)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet) :
    SatisfiesEquationAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background)
      hpull
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3) t := by
  classical
  exact
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_right_slot_tsupport_subset
      (Module.finBasis ℝ E) gauge3 hbackground hpull hsourceBackground hZsupport ht

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet) :
    SatisfiesEquationAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background)
      hpull
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3) t := by
  exact
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_sourceRicciTransportAt
      gauge3 hbackground hpull hsourceBackground ht
      (by
        intro x u v
        exact source.sourceRicciTransport gauge3 hpull hsourceBackground ht x u v)

theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_initial_of_diffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1) :
    SatisfiesEquationAt (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps source.toIntrinsicDeTurckSolution.background)
      hpull
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3) ivp.initialTime := by
  exact
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_sourceRicciTransportAt
      gauge3 hbackground hpull hsourceBackground
      (source.interval_subset ⟨le_rfl, le_of_lt source.initial_lt_terminal⟩)
      (by
        intro x u v
        exact source.sourceRicciTransport_initial_of_diffeomorph3Gauge
          gauge3 hpull hsourceBackground x u v)

/-- Build the gauge-reduced local solution package from a `C³` gauge by taking the transformed
metric to be the actual `C²` gauge pullback of the source metric. The remaining hypotheses are the
genuine time-derivative and Ricci-flow equation obligations. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (transformedVelocity : MetricTensorFamily (I := I) (M := M))
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      transformedVelocity source.toIntrinsicDeTurckSolution.timeSet)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      SatisfiesEquationAt (I := I) (M := M)
        (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background)
        hpull transformedVelocity t) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  source := source
  gauge := gauge3.toDiffeomorph2Gauge
  transformedMetric := gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric
  transformedVelocity := transformedVelocity
  transformed_inner := by
    intro t x u v
    rfl
  background_isLeviCivita := hbackground
  pullbackBackground_contMDiff := by
    intro t
    simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toDiffeomorph2Gauge] using hpull t
  transformed_hasTimeDerivative := hderiv
  transformed_equation := by
    intro t ht
    simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toDiffeomorph2Gauge] using heq ht

/-- C³ gauge reduction with the transformed velocity fixed to the concrete gauge-corrected source
velocity. This repackages the remaining equation obligation as the precise Ricci-transport identity
for that velocity, rather than as an arbitrary transformed-velocity equation. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet)
    (hRicci : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x,
        letI : Bundle.RiemannianBundle TM :=
          ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
            t).toRiemannianMetric⟩;
        source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
          (-2 : ℝ) *
            (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3Gauge
    source gauge3 hbackground
    (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
    hpull hderiv
    (by
      intro t ht x u v
      letI : Bundle.RiemannianBundle TM :=
        ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
          t).toRiemannianMetric⟩
      simpa [ricciFlowRHS, ricciTensor] using hRicci ht x u v)

/-- C³ gauge reduction with the concrete corrected velocity, reducing the Ricci-flow equation
obligation to the geometric transport of source Ricci curvature through the gauge. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfSourceRicciTransport
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hRicciTransport : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x,
        (letI : Bundle.RiemannianBundle TM :=
          ⟨(source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
         letI :
            CovariantDerivative.ContMDiffCovariantDerivative
              (source.toIntrinsicDeTurckSolution.background t) 1 :=
          hsourceBackground t;
         (source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)
          ((gauge3.maps t).pushforwardTangent x v)) =
        (letI : Bundle.RiemannianBundle TM :=
          ⟨((gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
            t).toRiemannianMetric⟩;
         letI :
            CovariantDerivative.ContMDiffCovariantDerivative
              (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
                gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1 :=
          hpull t;
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
           gauge3.maps source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v)) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3Gauge
    source gauge3 hbackground
    (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
    hpull hderiv
    (by
      intro t ht
      exact
        source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt_of_sourceRicciTransport
          gauge3 hbackground hpull hsourceBackground hRicciTransport ht)

/-- C³ gauge reduction with concrete corrected velocity, reducing the final Ricci-transport
obligation to the pointwise right-slot curvature replacement in the pushed frame. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfRightSlotCurvature
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hRight : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x, ∀ z : TM ((gauge3.maps t) x),
        (source.toIntrinsicDeTurckSolution.background t).curvatureAux
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) z)
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x u))
          ((gauge3.maps t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x v))
          ((gauge3.maps t) x) =
        (source.toIntrinsicDeTurckSolution.background t).curvatureAux
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) z)
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x u))
          (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x v))
          ((gauge3.maps t) x)) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfSourceRicciTransport
    source gauge3 hbackground hpull hderiv hsourceBackground
    (by
      intro t ht x u v
      exact source.sourceRicciTransport_of_right_slot_curvature
        gauge3 hpull hsourceBackground hRight ht x u v)

/-- C³ gauge reduction with concrete corrected velocity, reducing the final Ricci-transport
obligation to equality of the pushed right-slot smooth extension with the canonical right-slot
extension at the gauge image. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfRightSlotSectionEq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hRightEq : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ w : TM x,
        (gauge3.maps t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) =
          CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x w)) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfSourceRicciTransport
    source gauge3 hbackground hpull hderiv hsourceBackground
    (by
      intro t ht x u v
      exact source.sourceRicciTransport_of_right_slot_section_eq
        gauge3 hpull hsourceBackground hRightEq ht x u v)

/-- C³ gauge reduction with concrete corrected velocity, reducing the final Ricci-transport
obligation to local equality near the gauge image between the pushed right-slot smooth extension and
the canonical right-slot extension. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfEventuallyEqRightSlot
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hRightEq : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ w : TM x,
        (gauge3.maps t).pushforwardVectorField
            (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w) =ᶠ[nhds ((gauge3.maps t) x)]
          CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM)
            ((gauge3.maps t) x) ((gauge3.maps t).pushforwardTangent x w)) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfSourceRicciTransport
    source gauge3 hbackground hpull hderiv hsourceBackground
    (by
      intro t ht x u v
      exact source.sourceRicciTransport_of_eventuallyEq_right_slot
        gauge3 hpull hsourceBackground hRightEq ht x u v)

/-- C³ gauge reduction with concrete corrected velocity, reducing the final Ricci-transport
obligation to `C²` regularity of the pushed right-slot local-frame coefficients.  The matching
canonical coefficient regularity is discharged by the curvature tensor layer. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfRightSlotLocalFrameCoeff
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E)
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hZpushCoeff : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ w : TM x, ∀ i : ι,
        ContMDiff I 𝓘(ℝ) 2
          (fun y' ↦
            (trivializationAt E TM ((gauge3.maps t) x)).localFrameCoeff I b i y'
              (((gauge3.maps t).pushforwardVectorField
                (CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x w)) y'))) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfSourceRicciTransport
    source gauge3 hbackground hpull hderiv hsourceBackground
    (by
      intro t ht x u v
      exact source.sourceRicciTransport_of_right_slot_localFrameCoeff
        b gauge3 hpull hsourceBackground hZpushCoeff ht x u v)

/-- C³ gauge reduction with concrete corrected velocity, reducing pushed right-slot local-frame
coefficient regularity to a support-containment condition for the source smooth-extension bump. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfRightSlotSupport
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E)
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn
      (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hZsupport : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ ⦃z : M⦄,
        z ∈ tsupport (CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x) →
          (gauge3.maps t) z ∈ (trivializationAt E TM ((gauge3.maps t) x)).baseSet) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfSourceRicciTransport
    source gauge3 hbackground hpull hderiv hsourceBackground
    (by
      intro t ht x u v
      exact source.sourceRicciTransport_of_right_slot_tsupport_subset
        b gauge3 hpull hsourceBackground hZsupport ht x u v)

/-- Basis-free version of
`ofDiffeomorph3GaugeCorrectedVelocityOfRightSlotSupport`, using a finite-dimensional basis
chosen by `Module.finBasis`. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfRightSlotSupportFinBasis
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn
      (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hZsupport : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ ⦃z : M⦄,
        z ∈ tsupport (CovariantDerivative.smoothExtendBump (I := I) (F := E) (V := TM) x) →
          (gauge3.maps t) z ∈ (trivializationAt E TM ((gauge3.maps t) x)).baseSet) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfRightSlotSupport
    (Module.finBasis ℝ E) source gauge3 hbackground hpull hderiv hsourceBackground hZsupport

/-- C³ gauge reduction with an externally supplied transformed velocity that is pointwise equal to
the concrete gauge-corrected velocity.  This lets later time-derivative proofs use their natural
velocity expression and identify it with the geometric corrected velocity only at the equation step. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeVelocityEqCorrectedOfGeometricRicciTransport
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (transformedVelocity : MetricTensorFamily (I := I) (M := M))
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn
      (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      transformedVelocity source.toIntrinsicDeTurckSolution.timeSet)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1)
    (hvelocity : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x,
        transformedVelocity t x u v =
          source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3Gauge
    source gauge3 hbackground transformedVelocity hpull hderiv
    (by
      intro t ht
      exact
        (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt
          gauge3 hbackground hpull hsourceBackground ht).congr_velocity
          (fun x u v ↦ (hvelocity ht x u v).symm))

/-- C³ gauge reduction with the concrete corrected velocity and no right-slot hypotheses.  The
right-slot curvature/Ricci transport is discharged by shrinking the auxiliary bump in
`GaugeTransport.lean`. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfGeometricRicciTransport
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps source.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn
      (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (source.toIntrinsicDeTurckSolution.background t) 1) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3Gauge
    source gauge3 hbackground
    (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
    hpull hderiv
    (by
      intro t ht
      exact
        source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_satisfiesEquationAt
          gauge3 hbackground hpull hsourceBackground ht)

/-- C³ gauge reduction with concrete corrected velocity where both the source-background and
pulled-back-background `C¹` regularity obligations are derived from the Levi-Civita hypotheses.
The remaining nontrivial analytic input is the time derivative of the gauge-pulled metric. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hderiv : HasTimeDerivativeOn
      (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfGeometricRicciTransport
    source gauge3 hbackground
    (gauge3.pullbackBackgroundConnection_contMDiff hbackground)
    hderiv
    (source.background_contMDiff_of_isLeviCivita hbackground)

/-- Final `C³` gauge-reduction constructor whose analytic input is the exact scalar
time-derivative formula for the gauge-pulled metric inner product. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfLeviCivitaInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (hderiv : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x,
        HasDerivAt
          (fun τ ↦
            (source.toIntrinsicDeTurckSolution.metric τ).inner ((gauge3.maps τ) x)
              ((gauge3.maps τ).pushforwardTangent x u)
              ((gauge3.maps τ).pushforwardTangent x v))
          (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v) t) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfLeviCivita
    source gauge3 hbackground
    (source.gaugeCorrectedPullbackMetric_hasTimeDerivativeOn_of_inner_hasDerivAt gauge3 hderiv)

/-- Variant of `ofDiffeomorph3GaugeCorrectedVelocityOfLeviCivita` for a naturally supplied
transformed velocity that is pointwise equal to the concrete gauge-corrected velocity. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeVelocityEqCorrectedOfLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background)
    (transformedVelocity : MetricTensorFamily (I := I) (M := M))
    (hderiv : HasTimeDerivativeOn
      (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      transformedVelocity source.toIntrinsicDeTurckSolution.timeSet)
    (hvelocity : ∀ ⦃t : ℝ⦄, t ∈ source.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x,
        transformedVelocity t x u v =
          source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeVelocityEqCorrectedOfGeometricRicciTransport
    source gauge3 hbackground transformedVelocity
    (gauge3.pullbackBackgroundConnection_contMDiff hbackground)
    hderiv
    (source.background_contMDiff_of_isLeviCivita hbackground)
    hvelocity

noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.gauge.toIntrinsicLocalSolution_of_pullbackBackgroundEquation
    sol.source
    sol.transformed_inner
    sol.background_isLeviCivita
    sol.pullbackBackground_contMDiff
    sol.transformed_hasTimeDerivative
    sol.transformed_equation

noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.toLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.toIntrinsicLocalSolution.toLocalSolution

theorem GaugeReducedIntrinsicDeTurckLocalSolution.initialTime_mem
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ivp.initialTime ∈ sol.source.toIntrinsicDeTurckSolution.timeSet :=
  sol.source.interval_subset ⟨le_rfl, le_of_lt sol.source.initial_lt_terminal⟩

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gauge_anchored
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    SmoothSelfDiffeomorph2Family.AnchoredAt (I := I) (M := M)
      sol.gauge.maps ivp.initialTime :=
  sol.gauge.anchored

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gauge_apply_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (x : M) :
    sol.gauge.maps ivp.initialTime x = x :=
  SmoothSelfDiffeomorph2Family.AnchoredAt.apply (Φ := sol.gauge.maps)
    sol.gauge_anchored x

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gauge_pushforwardTangent_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (x : M) (u : TM x) :
    (sol.gauge.maps ivp.initialTime).pushforwardTangent x u = u :=
  SmoothSelfDiffeomorph2Family.AnchoredAt.pushforwardTangent
    (Φ := sol.gauge.maps) sol.gauge_anchored x u

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gauge_follows
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    FollowsIntrinsicDeTurckOn (I := I) (M := M)
      sol.gauge.maps.toSmoothSelfMapFamily
      sol.source.toIntrinsicDeTurckSolution.metric
      sol.source.toIntrinsicDeTurckSolution.background
      sol.source.toIntrinsicDeTurckSolution.timeSet :=
  sol.gauge.follows

theorem GaugeReducedIntrinsicDeTurckLocalSolution.localInterval_subset_timeSet
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Set.Icc ivp.initialTime sol.source.terminalTime ⊆
      sol.source.toIntrinsicDeTurckSolution.timeSet :=
  sol.source.interval_subset

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gauge_follows_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    FollowsIntrinsicDeTurckOn (I := I) (M := M)
      sol.gauge.maps.toSmoothSelfMapFamily
      sol.source.toIntrinsicDeTurckSolution.metric
      sol.source.toIntrinsicDeTurckSolution.background
      (Set.Icc ivp.initialTime sol.source.terminalTime) :=
  sol.gauge.follows.mono sol.localInterval_subset_timeSet

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gaugeIntegralCurveOn_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (x : M) :
    IsTimeDependentIntegralCurveOn (I := I) (M := M)
      (fun t : ℝ ↦ sol.gauge.maps.toSmoothSelfMapFamily t x)
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background)
      (Set.Icc ivp.initialTime sol.source.terminalTime) :=
  sol.gauge_follows_on_localInterval x

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gauge_hasMFDerivAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) :
    HasMFDerivAt[sol.source.toIntrinsicDeTurckSolution.timeSet]
      (fun τ : ℝ ↦ sol.gauge.maps.toSmoothSelfMapFamily τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
          sol.source.toIntrinsicDeTurckSolution.background t
          (sol.gauge.maps t x))) :=
  sol.gauge.hasMFDerivAt ht x

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gauge_hasMFDerivAt_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) :
    HasMFDerivAt[Set.Icc ivp.initialTime sol.source.terminalTime]
      (fun τ : ℝ ↦ sol.gauge.maps.toSmoothSelfMapFamily τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
            sol.source.toIntrinsicDeTurckSolution.background t
            (sol.gauge.maps t x))) :=
  sol.gauge_follows_on_localInterval.hasMFDerivAt ht x

noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckOneForm
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) : TM x →L[ℝ] ℝ :=
  connectionDifferenceTraceOneForm (I := I) (M := M)
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
      sol.gauge.maps
      (chosenLeviCivitaFamily (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric))
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
      sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
    t x

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckOneForm_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (w : TM x) :
    sol.pulledBackSourceDeTurckOneForm t x w =
      connectionDifferenceTraceOneForm (I := I) (M := M)
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps
          (chosenLeviCivitaFamily (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric))
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
        t x w := rfl

noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckVectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    CovariantDerivative.TimeDependentVectorField (I := I) (M := M) :=
  fun t x ↦ by
    letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩
    exact CovariantDerivative.rieszMap (I := I) x (sol.pulledBackSourceDeTurckOneForm t x)

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckVectorField_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) :
    sol.pulledBackSourceDeTurckVectorField t x =
      (letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩
       CovariantDerivative.rieszMap (I := I) x (sol.pulledBackSourceDeTurckOneForm t x)) := rfl

theorem GaugeReducedIntrinsicDeTurckLocalSolution.trace_pullbackSourceChosenLeviCivita_sourceBackground_eq_sourceDeTurckOneForm
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (w : TM x) :
    LinearMap.trace ℝ (TM x)
        (connectionDifferenceTraceEndomorphism (I := I) (M := M)
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps
            (chosenLeviCivitaFamily (I := I) (M := M)
              sol.source.toIntrinsicDeTurckSolution.metric))
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
          t x w).toLinearMap =
      intrinsicDeTurckOneForm (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t
        ((sol.gauge.maps t) x) ((sol.gauge.maps t).pushforwardTangent x w) := by
  exact SmoothSelfDiffeomorph2Family.trace_pullbackChosenLeviCivita_background_eq_intrinsicDeTurckOneForm
    (I := I) (M := M) sol.gauge.maps
    sol.source.toIntrinsicDeTurckSolution.metric
    sol.source.toIntrinsicDeTurckSolution.background w

theorem GaugeReducedIntrinsicDeTurckLocalSolution.traceOneForm_pullbackSourceChosenLeviCivita_sourceBackground_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (w : TM x) :
    connectionDifferenceTraceOneForm (I := I) (M := M)
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps
          (chosenLeviCivitaFamily (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric))
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
        t x w =
      intrinsicDeTurckOneForm (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t
        ((sol.gauge.maps t) x) ((sol.gauge.maps t).pushforwardTangent x w) := by
  exact SmoothSelfDiffeomorph2Family.traceOneForm_pullbackChosenLeviCivita_background_apply
    (I := I) (M := M) sol.gauge.maps
    sol.source.toIntrinsicDeTurckSolution.metric
    sol.source.toIntrinsicDeTurckSolution.background w

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pushforward_riesz_pullbackSourceDeTurckOneForm
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) :
    (sol.gauge.maps t).pushforwardTangent x
        (letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩
         CovariantDerivative.rieszMap (I := I) x
          (connectionDifferenceTraceOneForm (I := I) (M := M)
            (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.source.toIntrinsicDeTurckSolution.metric))
            (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
            t x)) =
      intrinsicDeTurckVectorField (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t ((sol.gauge.maps t) x) := by
  have hpush :
      (sol.gauge.maps t).pushforwardTangent x
          (letI : Bundle.RiemannianBundle TM :=
            ⟨(sol.transformedMetric t).toRiemannianMetric⟩
           CovariantDerivative.rieszMap (I := I) x
            (connectionDifferenceTraceOneForm (I := I) (M := M)
              (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
                sol.gauge.maps
                (chosenLeviCivitaFamily (I := I) (M := M)
                  sol.source.toIntrinsicDeTurckSolution.metric))
              (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
                sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
              t x)) =
        (letI : Bundle.RiemannianBundle TM :=
          ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩
         CovariantDerivative.rieszMap (I := I) ((sol.gauge.maps t) x)
          (intrinsicDeTurckOneForm (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric
            sol.source.toIntrinsicDeTurckSolution.background t ((sol.gauge.maps t) x))) := by
    exact SmoothSelfDiffeomorph2.pushforwardTangent_rieszMap_of_pullback_inner
      (I := I) (M := M) (φ := sol.gauge.maps t)
      (g := sol.source.toIntrinsicDeTurckSolution.metric t)
      (g' := sol.transformedMetric t)
      (fun y u v => sol.transformed_inner t y u v)
      (connectionDifferenceTraceOneForm (I := I) (M := M)
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps
          (chosenLeviCivitaFamily (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric))
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
        t x)
      (intrinsicDeTurckOneForm (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t ((sol.gauge.maps t) x))
      (fun u => sol.traceOneForm_pullbackSourceChosenLeviCivita_sourceBackground_apply t x u)
  simpa [intrinsicDeTurckVectorField] using hpush

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pushforward_pulledBackSourceDeTurckVectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) :
    (sol.gauge.maps t).pushforwardTangent x
        (sol.pulledBackSourceDeTurckVectorField t x) =
      intrinsicDeTurckVectorField (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t ((sol.gauge.maps t) x) := by
  simpa [GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckVectorField,
    GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckOneForm] using
    sol.pushforward_riesz_pullbackSourceDeTurckOneForm t x

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckVectorField_eq_pullbackVectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) :
    sol.pulledBackSourceDeTurckVectorField t =
      (sol.gauge.maps t).pullbackVectorField
        (intrinsicDeTurckVectorField (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
          sol.source.toIntrinsicDeTurckSolution.background t) := by
  funext x
  calc
    sol.pulledBackSourceDeTurckVectorField t x =
        (sol.gauge.maps t).pullbackTangent x
          ((sol.gauge.maps t).pushforwardTangent x
            (sol.pulledBackSourceDeTurckVectorField t x)) := by
          exact ((sol.gauge.maps t).pullbackTangent_pushforwardTangent x
            (sol.pulledBackSourceDeTurckVectorField t x)).symm
    _ = (sol.gauge.maps t).pullbackTangent x
        (intrinsicDeTurckVectorField (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
          sol.source.toIntrinsicDeTurckSolution.background t ((sol.gauge.maps t) x)) := by
          rw [sol.pushforward_pulledBackSourceDeTurckVectorField t x]

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorField_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (u : TM x) :
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps
        (chosenLeviCivitaFamily (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric) t)
      (sol.pulledBackSourceDeTurckVectorField t) x u =
      (sol.gauge.maps t).pullbackTangent x
        (((chosenLeviCivitaFamily (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric) t)
          (intrinsicDeTurckVectorField (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric
            sol.source.toIntrinsicDeTurckSolution.background t)
          ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x u)) := by
  rw [sol.pulledBackSourceDeTurckVectorField_eq_pullbackVectorField t]
  simp [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply]

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pushforwardTangent_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorField_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (u : TM x) :
    (sol.gauge.maps t).pushforwardTangent x
      ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps
          (chosenLeviCivitaFamily (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric) t)
        (sol.pulledBackSourceDeTurckVectorField t) x u) =
      ((chosenLeviCivitaFamily (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric) t)
        (intrinsicDeTurckVectorField (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
          sol.source.toIntrinsicDeTurckSolution.background t)
        ((sol.gauge.maps t) x)
        ((sol.gauge.maps t).pushforwardTangent x u) := by
  rw [sol.pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorField_apply t x u]
  exact (sol.gauge.maps t).pushforwardTangent_pullbackTangent x _

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_inner_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorField_left
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (u v : TM x) :
    (sol.transformedMetric t).inner x
      ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps
          (chosenLeviCivitaFamily (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric) t)
        (sol.pulledBackSourceDeTurckVectorField t) x u) v =
      (sol.source.toIntrinsicDeTurckSolution.metric t).inner ((sol.gauge.maps t) x)
        (((chosenLeviCivitaFamily (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric) t)
          (intrinsicDeTurckVectorField (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric
            sol.source.toIntrinsicDeTurckSolution.background t)
          ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x u))
        ((sol.gauge.maps t).pushforwardTangent x v) := by
  let A : TM x :=
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps
        (chosenLeviCivitaFamily (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric) t)
      (sol.pulledBackSourceDeTurckVectorField t) x u
  calc
    (sol.transformedMetric t).inner x A v =
        (sol.source.toIntrinsicDeTurckSolution.metric t).inner ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x A)
          ((sol.gauge.maps t).pushforwardTangent x v) := sol.transformed_inner t x A v
    _ = (sol.source.toIntrinsicDeTurckSolution.metric t).inner ((sol.gauge.maps t) x)
        (((chosenLeviCivitaFamily (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric) t)
          (intrinsicDeTurckVectorField (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric
            sol.source.toIntrinsicDeTurckSolution.background t)
          ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x u))
        ((sol.gauge.maps t).pushforwardTangent x v) := by
          rw [show (sol.gauge.maps t).pushforwardTangent x A =
              ((chosenLeviCivitaFamily (I := I) (M := M)
                  sol.source.toIntrinsicDeTurckSolution.metric) t)
                (intrinsicDeTurckVectorField (I := I) (M := M)
                  sol.source.toIntrinsicDeTurckSolution.metric
                  sol.source.toIntrinsicDeTurckSolution.background t)
                ((sol.gauge.maps t) x)
                ((sol.gauge.maps t).pushforwardTangent x u) by
            simpa [A] using
              sol.pushforwardTangent_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorField_apply
                t x u]

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_inner_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorField_right
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (u v : TM x) :
    (sol.transformedMetric t).inner x u
      ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps
          (chosenLeviCivitaFamily (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric) t)
        (sol.pulledBackSourceDeTurckVectorField t) x v) =
      (sol.source.toIntrinsicDeTurckSolution.metric t).inner ((sol.gauge.maps t) x)
        ((sol.gauge.maps t).pushforwardTangent x u)
        (((chosenLeviCivitaFamily (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric) t)
          (intrinsicDeTurckVectorField (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric
            sol.source.toIntrinsicDeTurckSolution.background t)
          ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x v)) := by
  let A : TM x :=
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps
        (chosenLeviCivitaFamily (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric) t)
      (sol.pulledBackSourceDeTurckVectorField t) x v
  calc
    (sol.transformedMetric t).inner x u A =
        (sol.source.toIntrinsicDeTurckSolution.metric t).inner ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x u)
          ((sol.gauge.maps t).pushforwardTangent x A) := sol.transformed_inner t x u A
    _ = (sol.source.toIntrinsicDeTurckSolution.metric t).inner ((sol.gauge.maps t) x)
        ((sol.gauge.maps t).pushforwardTangent x u)
        (((chosenLeviCivitaFamily (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric) t)
          (intrinsicDeTurckVectorField (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric
            sol.source.toIntrinsicDeTurckSolution.background t)
          ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x v)) := by
          rw [show (sol.gauge.maps t).pushforwardTangent x A =
              ((chosenLeviCivitaFamily (I := I) (M := M)
                  sol.source.toIntrinsicDeTurckSolution.metric) t)
                (intrinsicDeTurckVectorField (I := I) (M := M)
                  sol.source.toIntrinsicDeTurckSolution.metric
                  sol.source.toIntrinsicDeTurckSolution.background t)
                ((sol.gauge.maps t) x)
                ((sol.gauge.maps t).pushforwardTangent x v) by
            simpa [A] using
              sol.pushforwardTangent_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorField_apply
                t x v]

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_pullbackSourceDeTurckCorrection_eq_sourceDeTurckCorrection
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (u v : TM x) :
    (sol.transformedMetric t).inner x
        ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps
            (chosenLeviCivitaFamily (I := I) (M := M)
              sol.source.toIntrinsicDeTurckSolution.metric) t)
          (sol.pulledBackSourceDeTurckVectorField t) x u) v +
      (sol.transformedMetric t).inner x u
        ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps
            (chosenLeviCivitaFamily (I := I) (M := M)
              sol.source.toIntrinsicDeTurckSolution.metric) t)
          (sol.pulledBackSourceDeTurckVectorField t) x v) =
      intrinsicDeTurckCorrection (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t
        ((sol.gauge.maps t) x)
        ((sol.gauge.maps t).pushforwardTangent x u)
        ((sol.gauge.maps t).pushforwardTangent x v) := by
  rw [
    sol.transformed_inner_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorField_left
      t x u v,
    sol.transformed_inner_pullbackSourceChosenLeviCivita_pulledBackSourceDeTurckVectorField_right
      t x u v]
  rfl

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gauge_hasMFDerivAt_pullbackSourceDeTurckOneForm
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) :
    HasMFDerivAt[sol.source.toIntrinsicDeTurckSolution.timeSet]
      (fun τ : ℝ ↦ sol.gauge.maps.toSmoothSelfMapFamily τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (-((sol.gauge.maps t).pushforwardTangent x
          (letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩
           CovariantDerivative.rieszMap (I := I) x
            (sol.pulledBackSourceDeTurckOneForm t x))))) := by
  have hvec := sol.pushforward_riesz_pullbackSourceDeTurckOneForm t x
  simpa [intrinsicDeTurckGaugeField,
    GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckOneForm, hvec] using
    sol.gauge_hasMFDerivAt ht x

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gauge_hasMFDerivAt_pullbackSourceDeTurckOneForm_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) :
    HasMFDerivAt[Set.Icc ivp.initialTime sol.source.terminalTime]
      (fun τ : ℝ ↦ sol.gauge.maps.toSmoothSelfMapFamily τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (-((sol.gauge.maps t).pushforwardTangent x
          (letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩
           CovariantDerivative.rieszMap (I := I) x
            (sol.pulledBackSourceDeTurckOneForm t x))))) := by
  have hvec := sol.pushforward_riesz_pullbackSourceDeTurckOneForm t x
  simpa [intrinsicDeTurckGaugeField,
    GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckOneForm, hvec] using
    sol.gauge_hasMFDerivAt_localInterval ht x

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gauge_hasMFDerivAt_pulledBackSourceDeTurckVectorField
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) :
    HasMFDerivAt[sol.source.toIntrinsicDeTurckSolution.timeSet]
      (fun τ : ℝ ↦ sol.gauge.maps.toSmoothSelfMapFamily τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (-((sol.gauge.maps t).pushforwardTangent x
          (sol.pulledBackSourceDeTurckVectorField t x)))) := by
  simpa [GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckVectorField] using
    sol.gauge_hasMFDerivAt_pullbackSourceDeTurckOneForm ht x

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gauge_hasMFDerivAt_pulledBackSourceDeTurckVectorField_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) :
    HasMFDerivAt[Set.Icc ivp.initialTime sol.source.terminalTime]
      (fun τ : ℝ ↦ sol.gauge.maps.toSmoothSelfMapFamily τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (-((sol.gauge.maps t).pushforwardTangent x
          (sol.pulledBackSourceDeTurckVectorField t x)))) := by
  simpa [GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackSourceDeTurckVectorField] using
    sol.gauge_hasMFDerivAt_pullbackSourceDeTurckOneForm_localInterval ht x

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_satisfiesDeTurckEquationAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime) :
    SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M)
      sol.source.toIntrinsicDeTurckSolution.metric
      sol.source.toIntrinsicDeTurckSolution.metricVelocity
      sol.source.toIntrinsicDeTurckSolution.background t :=
  intrinsicDeTurckSolution_equation
    (I := I) (M := M) sol.source.toIntrinsicDeTurckSolution
    (sol.localInterval_subset_timeSet ht)

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_eq_zero_of_intrinsicRicciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    {x : M} {u v : TM x}
    (hRicciZero : intrinsicRicciTensor (I := I) (M := M)
      sol.source.toIntrinsicDeTurckSolution.metric t x u v = 0) :
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0 :=
  intrinsicDeTurckLocalSolution_metricVelocity_eq_zero_of_isLeviCivita_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) sol.source sol.background_isLeviCivita ht hRicciZero

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_eq_zero_iff_intrinsicRicciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0 ↔
      intrinsicRicciTensor (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric t x u v = 0 :=
  intrinsicDeTurckLocalSolution_metricVelocity_eq_zero_iff_intrinsicRicciTensor_eq_zero_of_isLeviCivita
    (I := I) (M := M) sol.source sol.background_isLeviCivita ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_zero_velocity_iff_intrinsicRicciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0) ↔
      (∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
        ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M)
            sol.source.toIntrinsicDeTurckSolution.metric t x u v = 0) :=
  intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
    (I := I) (M := M) sol.source sol.background_isLeviCivita

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_metric_eq_initial_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      sol.source.toIntrinsicDeTurckSolution.metric t x u v =
        ivp.initialMetric.inner x u v :=
  intrinsicDeTurckLocalSolution_metric_eq_initial_of_zero_velocity
    (I := I) (M := M) sol.source sol.background_isLeviCivita hzero ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_metric_eq_initial_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      sol.source.toIntrinsicDeTurckSolution.metric t x u v =
        ivp.initialMetric.inner x u v :=
  intrinsicDeTurckLocalSolution_metric_eq_initial_of_ricciTensor_zero
    (I := I) (M := M) sol.source sol.background_isLeviCivita hRicciZero ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_canonicalConnection_eq_initial_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.source.canonicalConnection sol.background_isLeviCivita t σ x =
      sol.source.canonicalConnection sol.background_isLeviCivita ivp.initialTime σ x :=
  intrinsicDeTurckLocalSolution_connection_eq_initial_of_zero_velocity
    (I := I) (M := M) sol.source sol.background_isLeviCivita hzero ht hσ

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_canonicalConnection_eq_initial_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.source.canonicalConnection sol.background_isLeviCivita t σ x =
      sol.source.canonicalConnection sol.background_isLeviCivita ivp.initialTime σ x :=
  intrinsicDeTurckLocalSolution_connection_eq_initial_of_ricciTensor_zero
    (I := I) (M := M) sol.source sol.background_isLeviCivita hRicciZero ht hσ

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_eq_intrinsicRicciDeTurckRHS
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v =
      intrinsicRicciDeTurckRHS (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t x u v :=
  intrinsicDeTurckSolution_equation
    (I := I) (M := M) sol.source.toIntrinsicDeTurckSolution ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_eq_intrinsicRicciDeTurckRHS_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v =
      intrinsicRicciDeTurckRHS (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t x u v :=
  sol.source_velocity_eq_intrinsicRicciDeTurckRHS
    (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_eq_intrinsicRicciFlowRHS_add_deTurckCorrection
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v =
      intrinsicRicciFlowRHS (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric t x u v +
      intrinsicDeTurckCorrection (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t x u v := by
  calc
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v =
        intrinsicRicciDeTurckRHS (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
          sol.source.toIntrinsicDeTurckSolution.background t x u v :=
      sol.source_velocity_eq_intrinsicRicciDeTurckRHS ht x u v
    _ = intrinsicRicciFlowRHS (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric t x u v +
        intrinsicDeTurckCorrection (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
          sol.source.toIntrinsicDeTurckSolution.background t x u v := rfl

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_eq_intrinsicRicciFlowRHS_add_deTurckCorrection_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v =
      intrinsicRicciFlowRHS (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric t x u v +
      intrinsicDeTurckCorrection (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t x u v :=
  sol.source_velocity_eq_intrinsicRicciFlowRHS_add_deTurckCorrection
    (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_intrinsicRicciFlowRHS_eq_backgroundRicciFlowRHS
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1) :
    intrinsicRicciFlowRHS (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric =
      ricciFlowRHS (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background
        hsourceBackground :=
  intrinsicRicciFlowRHS_eq_ricciFlowRHS_of_isLeviCivita
    (I := I) (M := M)
    sol.source.toIntrinsicDeTurckSolution.metric
    hsourceBackground sol.background_isLeviCivita

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_eq_neg_two_backgroundRicciCurvature_add_deTurckCorrection
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v +
      intrinsicDeTurckCorrection (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t x u v := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
    hsourceBackground t
  calc
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v =
        intrinsicRicciFlowRHS (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric t x u v +
        intrinsicDeTurckCorrection (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
          sol.source.toIntrinsicDeTurckSolution.background t x u v :=
      sol.source_velocity_eq_intrinsicRicciFlowRHS_add_deTurckCorrection ht x u v
    _ = ricciFlowRHS (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
          sol.source.toIntrinsicDeTurckSolution.background
          hsourceBackground t x u v +
        intrinsicDeTurckCorrection (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
          sol.source.toIntrinsicDeTurckSolution.background t x u v := by
          rw [sol.source_intrinsicRicciFlowRHS_eq_backgroundRicciFlowRHS hsourceBackground]
    _ = (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v +
      intrinsicDeTurckCorrection (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t x u v := rfl

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_eq_neg_two_backgroundRicciCurvature_add_deTurckCorrection_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v +
      intrinsicDeTurckCorrection (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t x u v :=
  sol.source_velocity_eq_neg_two_backgroundRicciCurvature_add_deTurckCorrection
    hsourceBackground (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_sub_deTurckCorrection_eq_neg_two_backgroundRicciCurvature
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v -
        intrinsicDeTurckCorrection (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
          sol.source.toIntrinsicDeTurckSolution.background t x u v =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
    hsourceBackground t
  rw [sol.source_velocity_eq_neg_two_backgroundRicciCurvature_add_deTurckCorrection
    hsourceBackground ht x u v]
  ring

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_sub_deTurckCorrection_eq_neg_two_backgroundRicciCurvature_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v -
        intrinsicDeTurckCorrection (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
          sol.source.toIntrinsicDeTurckSolution.background t x u v =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v :=
  sol.source_velocity_sub_deTurckCorrection_eq_neg_two_backgroundRicciCurvature
    hsourceBackground (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_at_gauge_sub_transformed_pullbackSourceDeTurckCorrection_eq_neg_two_backgroundRicciCurvature
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t ((sol.gauge.maps t) x)
        ((sol.gauge.maps t).pushforwardTangent x u)
        ((sol.gauge.maps t).pushforwardTangent x v) -
      ((sol.transformedMetric t).inner x
          ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.source.toIntrinsicDeTurckSolution.metric) t)
            (sol.pulledBackSourceDeTurckVectorField t) x u) v +
        (sol.transformedMetric t).inner x u
          ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.source.toIntrinsicDeTurckSolution.metric) t)
            (sol.pulledBackSourceDeTurckVectorField t) x v)) =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x u)
          ((sol.gauge.maps t).pushforwardTangent x v) := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
    hsourceBackground t
  rw [sol.transformed_pullbackSourceDeTurckCorrection_eq_sourceDeTurckCorrection t x u v]
  exact sol.source_velocity_sub_deTurckCorrection_eq_neg_two_backgroundRicciCurvature
    hsourceBackground ht ((sol.gauge.maps t) x)
    ((sol.gauge.maps t).pushforwardTangent x u)
    ((sol.gauge.maps t).pushforwardTangent x v)

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_at_gauge_sub_transformed_pullbackSourceDeTurckCorrection_eq_neg_two_backgroundRicciCurvature_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t ((sol.gauge.maps t) x)
        ((sol.gauge.maps t).pushforwardTangent x u)
        ((sol.gauge.maps t).pushforwardTangent x v) -
      ((sol.transformedMetric t).inner x
          ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.source.toIntrinsicDeTurckSolution.metric) t)
            (sol.pulledBackSourceDeTurckVectorField t) x u) v +
        (sol.transformedMetric t).inner x u
          ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.source.toIntrinsicDeTurckSolution.metric) t)
            (sol.pulledBackSourceDeTurckVectorField t) x v)) =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x u)
          ((sol.gauge.maps t).pushforwardTangent x v) := by
  exact
    sol.source_velocity_at_gauge_sub_transformed_pullbackSourceDeTurckCorrection_eq_neg_two_backgroundRicciCurvature
      hsourceBackground (sol.localInterval_subset_timeSet ht) x u v

/-- The pointwise velocity predicted by differentiating the gauge-pulled source metric:
the source metric velocity at the gauge image, corrected by the DeTurck gauge term transported
back to the transformed metric. -/
noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.gaugeCorrectedSourceVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    MetricTensorFamily (I := I) (M := M) :=
  fun t x u v ↦
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t ((sol.gauge.maps t) x)
        ((sol.gauge.maps t).pushforwardTangent x u)
        ((sol.gauge.maps t).pushforwardTangent x v) -
      ((sol.transformedMetric t).inner x
          ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.source.toIntrinsicDeTurckSolution.metric) t)
            (sol.pulledBackSourceDeTurckVectorField t) x u) v +
        (sol.transformedMetric t).inner x u
          ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.source.toIntrinsicDeTurckSolution.metric) t)
            (sol.pulledBackSourceDeTurckVectorField t) x v))

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.gaugeCorrectedSourceVelocity_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (u v : TM x) :
    sol.gaugeCorrectedSourceVelocity t x u v =
      sol.source.toIntrinsicDeTurckSolution.metricVelocity t ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x u)
          ((sol.gauge.maps t).pushforwardTangent x v) -
        ((sol.transformedMetric t).inner x
            ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
                sol.gauge.maps
                (chosenLeviCivitaFamily (I := I) (M := M)
                  sol.source.toIntrinsicDeTurckSolution.metric) t)
              (sol.pulledBackSourceDeTurckVectorField t) x u) v +
          (sol.transformedMetric t).inner x u
            ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
                sol.gauge.maps
                (chosenLeviCivitaFamily (I := I) (M := M)
                  sol.source.toIntrinsicDeTurckSolution.metric) t)
              (sol.pulledBackSourceDeTurckVectorField t) x v)) := rfl

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gaugeCorrectedSourceVelocity_eq_neg_two_backgroundRicciCurvature
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
    sol.gaugeCorrectedSourceVelocity t x u v =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x u)
          ((sol.gauge.maps t).pushforwardTangent x v) := by
  simpa [GaugeReducedIntrinsicDeTurckLocalSolution.gaugeCorrectedSourceVelocity] using
    sol.source_velocity_at_gauge_sub_transformed_pullbackSourceDeTurckCorrection_eq_neg_two_backgroundRicciCurvature
      hsourceBackground ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gaugeCorrectedSourceVelocity_eq_neg_two_backgroundRicciCurvature_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      hsourceBackground t;
    sol.gaugeCorrectedSourceVelocity t x u v =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x u)
          ((sol.gauge.maps t).pushforwardTangent x v) :=
  sol.gaugeCorrectedSourceVelocity_eq_neg_two_backgroundRicciCurvature
    hsourceBackground (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_hasTimeDerivativeOn_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      sol.transformedMetric sol.transformedVelocity
      (Set.Icc ivp.initialTime sol.source.terminalTime) :=
  sol.transformed_hasTimeDerivative.mono sol.localInterval_subset_timeSet

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pullbackBackground_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) sol.transformedMetric
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background) := by
  exact sol.source.pullbackBackgroundConnection_isLeviCivita_of_inner
    (Φ := sol.gauge.maps) (g' := sol.transformedMetric)
    sol.transformed_inner sol.background_isLeviCivita

theorem GaugeReducedIntrinsicDeTurckLocalSolution.intrinsicRicciTensor_eq_pullbackBackgroundRicciTensor
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric =
      ricciTensor (I := I) (M := M) sol.transformedMetric
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
        sol.pullbackBackground_contMDiff := by
  exact sol.source.intrinsicRicciTensor_eq_pullbackBackgroundRicciTensor_of_inner
    (Φ := sol.gauge.maps) (g' := sol.transformedMetric)
    sol.transformed_inner sol.background_isLeviCivita sol.pullbackBackground_contMDiff

theorem GaugeReducedIntrinsicDeTurckLocalSolution.intrinsicRicciFlowRHS_eq_pullbackBackgroundRicciFlowRHS
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    intrinsicRicciFlowRHS (I := I) (M := M) sol.transformedMetric =
      ricciFlowRHS (I := I) (M := M) sol.transformedMetric
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
        sol.pullbackBackground_contMDiff := by
  exact sol.source.intrinsicRicciFlowRHS_eq_pullbackBackgroundRicciFlowRHS_of_inner
    (Φ := sol.gauge.maps) (g' := sol.transformedMetric)
    sol.transformed_inner sol.background_isLeviCivita sol.pullbackBackground_contMDiff

theorem GaugeReducedIntrinsicDeTurckLocalSolution.isIntrinsicRicciFlowOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IsIntrinsicRicciFlowOn (I := I) (M := M)
      sol.transformedMetric sol.transformedVelocity sol.source.toIntrinsicDeTurckSolution.timeSet := by
  exact sol.source.isIntrinsicRicciFlowOn_of_pullbackBackgroundEquation_of_inner
    (Φ := sol.gauge.maps) (g' := sol.transformedMetric) (gdot := sol.transformedVelocity)
    (s := sol.source.toIntrinsicDeTurckSolution.timeSet)
    sol.transformed_inner sol.background_isLeviCivita sol.pullbackBackground_contMDiff
    sol.transformed_hasTimeDerivative sol.transformed_equation

theorem GaugeReducedIntrinsicDeTurckLocalSolution.satisfiesEquationAt_pullbackBackground
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet) :
    SatisfiesEquationAt (I := I) (M := M)
      sol.transformedMetric
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
      sol.pullbackBackground_contMDiff sol.transformedVelocity t :=
  sol.transformed_equation ht

theorem GaugeReducedIntrinsicDeTurckLocalSolution.satisfiesEquationAt_pullbackBackground_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime) :
    SatisfiesEquationAt (I := I) (M := M)
      sol.transformedMetric
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
      sol.pullbackBackground_contMDiff sol.transformedVelocity t :=
  sol.satisfiesEquationAt_pullbackBackground (sol.localInterval_subset_timeSet ht)

theorem GaugeReducedIntrinsicDeTurckLocalSolution.satisfiesIntrinsicEquationAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet) :
    SatisfiesIntrinsicEquationAt (I := I) (M := M)
      sol.transformedMetric sol.transformedVelocity t :=
  sol.isIntrinsicRicciFlowOn.2 ht

theorem GaugeReducedIntrinsicDeTurckLocalSolution.satisfiesIntrinsicEquationAt_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime) :
    SatisfiesIntrinsicEquationAt (I := I) (M := M)
      sol.transformedMetric sol.transformedVelocity t :=
  sol.satisfiesIntrinsicEquationAt (sol.localInterval_subset_timeSet ht)

theorem GaugeReducedIntrinsicDeTurckLocalSolution.isIntrinsicRicciFlowOn_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IsIntrinsicRicciFlowOn (I := I) (M := M)
      sol.transformedMetric sol.transformedVelocity
      (Set.Icc ivp.initialTime sol.source.terminalTime) :=
  ⟨sol.transformed_hasTimeDerivativeOn_localInterval,
    fun {t} ht ↦ sol.satisfiesIntrinsicEquationAt_on_localInterval (t := t) ht⟩

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_intrinsicRicciFlowRHS
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    sol.transformedVelocity t x u v =
      intrinsicRicciFlowRHS (I := I) (M := M) sol.transformedMetric t x u v :=
  sol.satisfiesIntrinsicEquationAt ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_intrinsicRicciFlowRHS_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    sol.transformedVelocity t x u v =
      intrinsicRicciFlowRHS (I := I) (M := M) sol.transformedMetric t x u v :=
  sol.transformed_velocity_eq_intrinsicRicciFlowRHS
    (sol.localInterval_subset_timeSet ht) x u v

/-- The transformed velocity is the genuine intrinsic Ricci-flow velocity of
the transformed metric, written directly as `-2 Ric`. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_neg_two_intrinsicRicciTensor
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    sol.transformedVelocity t x u v =
      (-2 : ℝ) *
        intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric t x u v := by
  calc
    sol.transformedVelocity t x u v =
        intrinsicRicciFlowRHS (I := I) (M := M) sol.transformedMetric t x u v :=
      sol.transformed_velocity_eq_intrinsicRicciFlowRHS ht x u v
    _ = (-2 : ℝ) *
        intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric t x u v := by
      rfl

/-- Local-interval form of
`GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_neg_two_intrinsicRicciTensor`. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_neg_two_intrinsicRicciTensor_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    sol.transformedVelocity t x u v =
      (-2 : ℝ) *
        intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric t x u v :=
  sol.transformed_velocity_eq_neg_two_intrinsicRicciTensor
    (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_pullbackBackgroundRicciFlowRHS
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    sol.transformedVelocity t x u v =
      ricciFlowRHS (I := I) (M := M) sol.transformedMetric
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
        sol.pullbackBackground_contMDiff t x u v :=
  sol.satisfiesEquationAt_pullbackBackground ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_pullbackBackgroundRicciFlowRHS_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    sol.transformedVelocity t x u v =
      ricciFlowRHS (I := I) (M := M) sol.transformedMetric
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
        sol.pullbackBackground_contMDiff t x u v :=
  sol.transformed_velocity_eq_pullbackBackgroundRicciFlowRHS
    (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_neg_two_pullbackBackgroundRicciCurvature
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      sol.pullbackBackground_contMDiff t;
    sol.transformedVelocity t x u v =
      (-2 : ℝ) *
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v := by
  letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
    sol.pullbackBackground_contMDiff t
  calc
    sol.transformedVelocity t x u v =
        ricciFlowRHS (I := I) (M := M) sol.transformedMetric
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
          sol.pullbackBackground_contMDiff t x u v :=
      sol.transformed_velocity_eq_pullbackBackgroundRicciFlowRHS ht x u v
    _ = (-2 : ℝ) *
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v := rfl

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_neg_two_pullbackBackgroundRicciCurvature_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      sol.pullbackBackground_contMDiff t;
    sol.transformedVelocity t x u v =
      (-2 : ℝ) *
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v :=
  sol.transformed_velocity_eq_neg_two_pullbackBackgroundRicciCurvature
    (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pullbackBackgroundRicciCurvature_eq_trace_conj
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1)
    (t : ℝ) (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      sol.pullbackBackground_contMDiff t;
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
      sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v =
      LinearMap.trace ℝ (TM ((sol.gauge.maps t) x))
        ((((sol.gauge.maps t).tangentMap x).toLinearEquiv).conj
          ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciEndomorphism x u v)) := by
  letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
    sol.pullbackBackground_contMDiff t
  exact SmoothSelfDiffeomorph2Family.ricciCurvature_pullbackConnectionFamily_eq_trace_tangentMap_conj_ricciEndomorphism
    (I := I) (M := M) (Φ := sol.gauge.maps)
    sol.source.toIntrinsicDeTurckSolution.background
    hsourceBackground sol.pullbackBackground_contMDiff (t := t) (x := x) u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_neg_two_trace_conj_pullbackBackgroundRicciEndomorphism
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      sol.pullbackBackground_contMDiff t;
    sol.transformedVelocity t x u v =
      (-2 : ℝ) *
        LinearMap.trace ℝ (TM ((sol.gauge.maps t) x))
          ((((sol.gauge.maps t).tangentMap x).toLinearEquiv).conj
            ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciEndomorphism x u v)) := by
  letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
    sol.pullbackBackground_contMDiff t
  calc
    sol.transformedVelocity t x u v =
        (-2 : ℝ) *
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v :=
      sol.transformed_velocity_eq_neg_two_pullbackBackgroundRicciCurvature ht x u v
    _ = (-2 : ℝ) *
        LinearMap.trace ℝ (TM ((sol.gauge.maps t) x))
          ((((sol.gauge.maps t).tangentMap x).toLinearEquiv).conj
            ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciEndomorphism x u v)) := by
          exact congrArg (fun z : ℝ ↦ (-2 : ℝ) * z)
            (sol.pullbackBackgroundRicciCurvature_eq_trace_conj hsourceBackground t x u v)

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_neg_two_trace_conj_pullbackBackgroundRicciEndomorphism_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      sol.pullbackBackground_contMDiff t;
    sol.transformedVelocity t x u v =
      (-2 : ℝ) *
        LinearMap.trace ℝ (TM ((sol.gauge.maps t) x))
          ((((sol.gauge.maps t).tangentMap x).toLinearEquiv).conj
            ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciEndomorphism x u v)) :=
  sol.transformed_velocity_eq_neg_two_trace_conj_pullbackBackgroundRicciEndomorphism
    hsourceBackground (sol.localInterval_subset_timeSet ht) x u v

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.toLocalSolution_metric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toLocalSolution.toSolution.metric = sol.transformedMetric := by
  rfl

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.toLocalSolution_timeSet
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toLocalSolution.toSolution.timeSet =
      sol.source.toIntrinsicDeTurckSolution.timeSet := by
  rfl

/-- On zero-dimensional tangent fibers, the source DeTurck velocity of a gauge-reduced solution
vanishes on its local interval. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0 :=
  intrinsicDeTurckLocalSolution_metricVelocity_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) sol.source ht x u v

/-- On zero-dimensional tangent fibers, the source DeTurck metric has vanishing intrinsic Ricci
tensor on the local interval. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_intrinsicRicciTensor_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M)
      sol.source.toIntrinsicDeTurckSolution.metric t x u v = 0 :=
  intrinsicDeTurckLocalSolution_intrinsicRicciTensor_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) sol.source ht x u v

/-- On zero-dimensional tangent fibers, the intrinsic Ricci-flow right-hand side of the source
DeTurck metric vanishes on the local interval. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_intrinsicRicciFlowRHS_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M)
      sol.source.toIntrinsicDeTurckSolution.metric t x u v = 0 :=
  intrinsicDeTurckLocalSolution_intrinsicRicciFlowRHS_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) sol.source ht x u v

/-- On zero-dimensional tangent fibers, the source DeTurck right-hand side vanishes on the local
interval for the stored background. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_intrinsicRicciDeTurckRHS_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M)
      sol.source.toIntrinsicDeTurckSolution.metric
      sol.source.toIntrinsicDeTurckSolution.background t x u v = 0 :=
  intrinsicDeTurckLocalSolution_intrinsicRicciDeTurckRHS_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) sol.source ht x u v

/-- On zero-dimensional tangent fibers, the source DeTurck metric of a gauge-reduced solution is
stationary in metric tensor components, independently of the stored background. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_metric_eq_initial_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric t x u v =
      ivp.initialMetric.inner x u v :=
  intrinsicDeTurckLocalSolution_metric_eq_initial_of_subsingleton_tangent_any_background
    (I := I) (M := M) sol.source ht x u v

/-- On zero-dimensional tangent fibers, any two gauge-reduced solutions have the same source
DeTurck metric tensor on every common time. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.unique_source_metric_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.source.terminalTime sol₂.source.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
        sol₁.source.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M)
        sol₂.source.toIntrinsicDeTurckSolution.metric t x u v :=
  intrinsicDeTurckLocalSolution_unique_metric_of_subsingleton_tangent
    (I := I) (M := M) sol₁.source sol₂.source ht x u v

/-- On zero-dimensional tangent fibers, the source background of a gauge-reduced solution is
automatically Levi-Civita for the source DeTurck metric family. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_background_isLeviCivita_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.source.toIntrinsicDeTurckSolution.metric
      sol.source.toIntrinsicDeTurckSolution.background :=
  sol.source.background_isLeviCivita_of_subsingleton_tangent

/-- On zero-dimensional tangent fibers, the canonical source connection of a gauge-reduced solution
is stationary on the local interval. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_connection_eq_initial_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    {x : M} {σ : Π y : M, TM y} :
    sol.source.canonicalConnection sol.source_background_isLeviCivita_of_subsingleton_tangent t σ x =
      sol.source.canonicalConnection sol.source_background_isLeviCivita_of_subsingleton_tangent
        ivp.initialTime σ x :=
  intrinsicDeTurckLocalSolution_connection_eq_initial_of_subsingleton_tangent
    (I := I) (M := M) sol.source
    sol.source_background_isLeviCivita_of_subsingleton_tangent ht

/-- On zero-dimensional tangent fibers, any two gauge-reduced solutions have the same canonical
source connection values on every common time. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.unique_source_connection_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.source.terminalTime sol₂.source.terminalTime))
    {x : M} {σ : Π y : M, TM y} :
    sol₁.source.canonicalConnection sol₁.source_background_isLeviCivita_of_subsingleton_tangent
        t σ x =
      sol₂.source.canonicalConnection sol₂.source_background_isLeviCivita_of_subsingleton_tangent
        t σ x :=
  intrinsicDeTurckLocalSolution_unique_connection_of_subsingleton_tangent
    (I := I) (M := M) sol₁.source sol₂.source
    sol₁.source_background_isLeviCivita_of_subsingleton_tangent
    sol₂.source_background_isLeviCivita_of_subsingleton_tangent ht

/-- On zero-dimensional tangent fibers, the stored source DeTurck background of a gauge-reduced
solution is stationary in connection values. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_background_connection_eq_initial_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    {x : M} {σ : Π y : M, TM y} :
    sol.source.toIntrinsicDeTurckSolution.background t σ x =
      sol.source.toIntrinsicDeTurckSolution.background ivp.initialTime σ x :=
  intrinsicDeTurckLocalSolution_background_connection_eq_initial_of_subsingleton_tangent
    (I := I) (M := M) sol.source ht

/-- On zero-dimensional tangent fibers, any two gauge-reduced solutions have the same stored source
DeTurck background connection values on every common time. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.unique_source_background_connection_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.source.terminalTime sol₂.source.terminalTime))
    {x : M} {σ : Π y : M, TM y} :
    sol₁.source.toIntrinsicDeTurckSolution.background t σ x =
      sol₂.source.toIntrinsicDeTurckSolution.background t σ x :=
  intrinsicDeTurckLocalSolution_unique_background_connection_of_subsingleton_tangent
    (I := I) (M := M) sol₁.source sol₂.source ht

/-- On zero-dimensional tangent fibers, the transformed velocity of a gauge-reduced local solution
vanishes on the source time set. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    sol.transformedVelocity t x u v = 0 :=
  SatisfiesIntrinsicEquationAt.metricVelocity_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) (sol.satisfiesIntrinsicEquationAt ht) x u v

/-- On zero-dimensional tangent fibers, the transformed velocity of a gauge-reduced local solution
vanishes on its local interval. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_zero_of_subsingleton_tangent_on_localInterval
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    sol.transformedVelocity t x u v = 0 :=
  sol.transformed_velocity_eq_zero_of_subsingleton_tangent
    (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_zero_of_intrinsicRicciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    {x : M} {u v : TM x}
    (hRicciZero : intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric t x u v = 0) :
    sol.transformedVelocity t x u v = 0 :=
  SatisfiesIntrinsicEquationAt.metricVelocity_eq_zero_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) (sol.satisfiesIntrinsicEquationAt ht) hRicciZero

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_zero_iff_intrinsicRicciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    sol.transformedVelocity t x u v = 0 ↔
      intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric t x u v = 0 := by
  constructor
  · intro hzero
    have heq :
        sol.transformedVelocity t x u v =
          (-2 : ℝ) * intrinsicRicciTensor (I := I) (M := M)
            sol.transformedMetric t x u v := by
      simpa [intrinsicRicciFlowRHS, ricciFlowRHS, intrinsicRicciTensor] using
        sol.satisfiesIntrinsicEquationAt ht x u v
    linarith
  · intro hRicciZero
    exact sol.transformed_velocity_eq_zero_of_intrinsicRicciTensor_eq_zero ht hRicciZero

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_zero_of_intrinsicRicciTensor_eq_zero_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    {x : M} {u v : TM x}
    (hRicciZero : intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric t x u v = 0) :
    sol.transformedVelocity t x u v = 0 :=
  sol.transformed_velocity_eq_zero_of_intrinsicRicciTensor_eq_zero
    (sol.localInterval_subset_timeSet ht) hRicciZero

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_zero_iff_intrinsicRicciTensor_eq_zero_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    sol.transformedVelocity t x u v = 0 ↔
      intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric t x u v = 0 :=
  sol.transformed_velocity_eq_zero_iff_intrinsicRicciTensor_eq_zero
    (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_zero_velocity_iff_intrinsicRicciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x, sol.transformedVelocity t x u v = 0) ↔
      (∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
        ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric t x u v = 0) := by
  change
    (∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicLocalSolution.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        sol.toIntrinsicLocalSolution.toIntrinsicSolution.metricVelocity t x u v = 0) ↔
      (∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M)
            sol.toIntrinsicLocalSolution.toIntrinsicSolution.metric t x u v = 0)
  exact intrinsicLocalSolution_zero_velocity_iff_ricciTensor_zero
    (I := I) (M := M) sol.toIntrinsicLocalSolution

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_metric_eq_initial_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x, sol.transformedVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.transformedMetric t x u v =
      ivp.initialMetric.inner x u v := by
  change
    metricTensor (I := I) (M := M)
      sol.toIntrinsicLocalSolution.toIntrinsicSolution.metric t x u v =
      ivp.initialMetric.inner x u v
  change ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicLocalSolution.terminalTime,
    ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicLocalSolution.toIntrinsicSolution.metricVelocity t x u v = 0 at hzero
  exact intrinsicLocalSolution_metric_eq_initial_of_zero_velocity
    (I := I) (M := M) sol.toIntrinsicLocalSolution hzero ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_metric_eq_initial_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.transformedMetric t x u v =
      ivp.initialMetric.inner x u v := by
  change
    metricTensor (I := I) (M := M)
      sol.toIntrinsicLocalSolution.toIntrinsicSolution.metric t x u v =
      ivp.initialMetric.inner x u v
  change ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicLocalSolution.terminalTime,
    ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M)
        sol.toIntrinsicLocalSolution.toIntrinsicSolution.metric t x u v = 0 at hRicciZero
  exact intrinsicLocalSolution_metric_eq_initial_of_ricciTensor_zero
    (I := I) (M := M) sol.toIntrinsicLocalSolution hRicciZero ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_connection_eq_initial_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x, sol.transformedVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toLocalSolution.toSolution.connection t σ x =
      sol.toLocalSolution.toSolution.connection ivp.initialTime σ x := by
  change
    sol.toIntrinsicLocalSolution.toIntrinsicSolution.toSolution.connection t σ x =
      sol.toIntrinsicLocalSolution.toIntrinsicSolution.toSolution.connection ivp.initialTime σ x
  change ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicLocalSolution.terminalTime,
    ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicLocalSolution.toIntrinsicSolution.metricVelocity t x u v = 0 at hzero
  exact intrinsicLocalSolution_connection_eq_initial_of_zero_velocity
    (I := I) (M := M) sol.toIntrinsicLocalSolution hzero ht hσ

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_connection_eq_initial_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toLocalSolution.toSolution.connection t σ x =
      sol.toLocalSolution.toSolution.connection ivp.initialTime σ x := by
  change
    sol.toIntrinsicLocalSolution.toIntrinsicSolution.toSolution.connection t σ x =
      sol.toIntrinsicLocalSolution.toIntrinsicSolution.toSolution.connection ivp.initialTime σ x
  change ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicLocalSolution.terminalTime,
    ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M)
        sol.toIntrinsicLocalSolution.toIntrinsicSolution.metric t x u v = 0 at hRicciZero
  exact intrinsicLocalSolution_connection_eq_initial_of_ricciTensor_zero
    (I := I) (M := M) sol.toIntrinsicLocalSolution hRicciZero ht hσ

/-- On zero-dimensional tangent fibers, the transformed metric has vanishing intrinsic Ricci tensor
on the local interval. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_intrinsicRicciTensor_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric t x u v = 0 :=
  _root_.RicciFlow.intrinsicRicciTensor_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) sol.transformedMetric t x u v

/-- On zero-dimensional tangent fibers, the transformed Ricci-flow right-hand side vanishes on the
local interval. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_intrinsicRicciFlowRHS_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M) sol.transformedMetric t x u v = 0 :=
  _root_.RicciFlow.intrinsicRicciFlowRHS_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) sol.transformedMetric t x u v

/-- On zero-dimensional tangent fibers, every gauge-reduced local solution is stationary in
transformed metric tensor components on its local interval. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_metric_eq_initial_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.transformedMetric t x u v =
      ivp.initialMetric.inner x u v := by
  simpa [GaugeReducedIntrinsicDeTurckLocalSolution.toLocalSolution_metric] using
    localSolution_metric_eq_initial_of_subsingleton_tangent
      (I := I) (M := M) sol.toLocalSolution ht x u v

/-- On zero-dimensional tangent fibers, any two gauge-reduced local solutions have the same
transformed metric tensor on every common time. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.unique_transformed_metric_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime (min sol₁.source.terminalTime sol₂.source.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.transformedMetric t x u v =
      metricTensor (I := I) (M := M) sol₂.transformedMetric t x u v := by
  rw [metricTensor_eq_zero_of_subsingleton_tangent
      (I := I) (M := M) sol₁.transformedMetric t x u v,
    metricTensor_eq_zero_of_subsingleton_tangent
      (I := I) (M := M) sol₂.transformedMetric t x u v]

/-- On zero-dimensional tangent fibers, the transformed local-solution connection is stationary on
the local interval. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_connection_eq_initial_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    {x : M} {σ : Π y : M, TM y} :
    sol.toLocalSolution.toSolution.connection t σ x =
      sol.toLocalSolution.toSolution.connection ivp.initialTime σ x :=
  localSolution_connection_eq_initial_of_subsingleton_tangent
    (I := I) (M := M) sol.toLocalSolution ht

/-- On zero-dimensional tangent fibers, any two gauge-reduced local solutions have the same
transformed local-solution connection values on every common time. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.unique_transformed_connection_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.source.terminalTime sol₂.source.terminalTime))
    {x : M} {σ : Π y : M, TM y} :
    sol₁.toLocalSolution.toSolution.connection t σ x =
      sol₂.toLocalSolution.toSolution.connection t σ x :=
  localSolution_unique_connection_of_subsingleton_tangent
    (I := I) (M := M) sol₁.toLocalSolution sol₂.toLocalSolution ht

theorem GaugeReducedIntrinsicDeTurckLocalSolution.intrinsicDeTurckVectorField_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    intrinsicDeTurckVectorField (I := I) (M := M) sol.transformedMetric
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background) = 0 := by
  exact intrinsicDeTurckVectorField_eq_zero_of_isLeviCivita
    (I := I) (M := M) sol.transformedMetric
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
      sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
    sol.pullbackBackground_isLeviCivita

theorem GaugeReducedIntrinsicDeTurckLocalSolution.intrinsicDeTurckCorrection_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    intrinsicDeTurckCorrection (I := I) (M := M) sol.transformedMetric
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background) = 0 := by
  exact intrinsicDeTurckCorrection_eq_zero_of_isLeviCivita
    (I := I) (M := M) sol.transformedMetric
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
      sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
    sol.pullbackBackground_isLeviCivita

theorem GaugeReducedIntrinsicDeTurckLocalSolution.intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    intrinsicRicciDeTurckRHS (I := I) (M := M) sol.transformedMetric
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background) =
      intrinsicRicciFlowRHS (I := I) (M := M) sol.transformedMetric := by
  exact intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita
    (I := I) (M := M) sol.transformedMetric
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
      sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
    sol.pullbackBackground_isLeviCivita

theorem GaugeReducedIntrinsicDeTurckLocalSolution.isIntrinsicRicciDeTurckOn_pullbackBackground
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IsIntrinsicRicciDeTurckOn (I := I) (M := M)
      sol.transformedMetric sol.transformedVelocity
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
      sol.source.toIntrinsicDeTurckSolution.timeSet := by
  exact
    (isIntrinsicRicciDeTurckOn_iff_of_isLeviCivita
      (I := I) (M := M) sol.transformedMetric sol.transformedVelocity
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
      sol.source.toIntrinsicDeTurckSolution.timeSet
      sol.pullbackBackground_isLeviCivita).2
      sol.isIntrinsicRicciFlowOn

theorem GaugeReducedIntrinsicDeTurckLocalSolution.satisfiesIntrinsicDeTurckEquationAt_pullbackBackground
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet) :
    SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M)
      sol.transformedMetric sol.transformedVelocity
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background) t :=
  sol.isIntrinsicRicciDeTurckOn_pullbackBackground.2 ht

theorem GaugeReducedIntrinsicDeTurckLocalSolution.satisfiesIntrinsicDeTurckEquationAt_pullbackBackground_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime) :
    SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M)
      sol.transformedMetric sol.transformedVelocity
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background) t :=
  sol.satisfiesIntrinsicDeTurckEquationAt_pullbackBackground
    (sol.localInterval_subset_timeSet ht)

theorem GaugeReducedIntrinsicDeTurckLocalSolution.isIntrinsicRicciDeTurckOn_pullbackBackground_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IsIntrinsicRicciDeTurckOn (I := I) (M := M)
      sol.transformedMetric sol.transformedVelocity
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background)
      (Set.Icc ivp.initialTime sol.source.terminalTime) :=
  ⟨sol.transformed_hasTimeDerivativeOn_localInterval,
    fun {t} ht ↦
      sol.satisfiesIntrinsicDeTurckEquationAt_pullbackBackground_on_localInterval (t := t) ht⟩

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pullbackBackgroundConnection_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background ivp.initialTime =
      sol.source.toIntrinsicDeTurckSolution.background ivp.initialTime :=
  sol.source.pullbackBackgroundConnection_eq_initial_of_anchored sol.gauge.anchored

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pullbackBackgroundConnection_eq_initial_apply
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (X : Π x : M, TM x) (x : M) (u : TM x) :
    SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background
        ivp.initialTime X x u =
      sol.source.toIntrinsicDeTurckSolution.background ivp.initialTime X x u :=
  sol.source.pullbackBackgroundConnection_eq_initial_of_anchored_apply
    sol.gauge.anchored X x u

theorem GaugeReducedIntrinsicDeTurckLocalSolution.sourceBackground_isLeviCivita_initialMetric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
    (sol.source.toIntrinsicDeTurckSolution.background ivp.initialTime).IsLeviCivita :=
by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  exact
    (CovariantDerivative.isLeviCivita_iff_of_inner_eq
      (I := I) (E := E) (M := M)
      (cov := sol.source.toIntrinsicDeTurckSolution.background ivp.initialTime)
      (g := sol.source.toIntrinsicDeTurckSolution.metric ivp.initialTime)
      (g' := ivp.initialMetric)
      (fun y u v ↦ intrinsicDeTurckLocalSolution_metric_eq_initial
        (E := E) (H := H) (I := I) (M := M) sol.source y u v)).mp
      (sol.background_isLeviCivita ivp.initialTime)

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pullbackBackground_isLeviCivita_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨((sol.gauge.maps ivp.initialTime).pullbackRiemannianMetric
        (sol.source.toIntrinsicDeTurckSolution.metric ivp.initialTime)).toRiemannianMetric⟩;
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
      sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background
      ivp.initialTime).IsLeviCivita :=
  sol.gauge.pullbackBackgroundConnection_isLeviCivita_initial
    sol.source sol.sourceBackground_isLeviCivita_initialMetric

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformedMetric_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.transformedMetric ivp.initialTime = ivp.initialMetric := by
  exact sol.gauge.transformedMetric_eq_initial_of_inner sol.source sol.transformed_inner

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformedMetric_initial_inner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (x : M) (u v : TM x) :
    (sol.transformedMetric ivp.initialTime).inner x u v = ivp.initialMetric.inner x u v := by
  rw [sol.transformedMetric_eq_initial]

noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.toPulledBackIntrinsicDeTurckLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := sol.source.terminalTime
  initial_lt_terminal := sol.source.initial_lt_terminal
  toIntrinsicDeTurckSolution := {
    timeSet := sol.source.toIntrinsicDeTurckSolution.timeSet
    metric := sol.transformedMetric
    metricVelocity := sol.transformedVelocity
    background :=
      SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background
    isRicciDeTurck := sol.isIntrinsicRicciDeTurckOn_pullbackBackground }
  interval_subset := sol.source.interval_subset
  matchesInitialMetric := by
    intro x u v
    exact sol.transformedMetric_initial_inner x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackDeTurck_background_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
      sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background := by
  simpa [GaugeReducedIntrinsicDeTurckLocalSolution.toPulledBackIntrinsicDeTurckLocalSolution]
    using sol.pullbackBackground_isLeviCivita

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_metric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toIntrinsicLocalSolution.toIntrinsicSolution.metric = sol.transformedMetric := by
  rfl

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_metricVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toIntrinsicLocalSolution.toIntrinsicSolution.metricVelocity =
      sol.transformedVelocity := by
  rfl

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_timeSet
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toIntrinsicLocalSolution.toIntrinsicSolution.timeSet =
      sol.source.toIntrinsicDeTurckSolution.timeSet := by
  rfl

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackDeTurck_terminalTime
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toPulledBackIntrinsicDeTurckLocalSolution.terminalTime = sol.source.terminalTime := by
  rfl

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackDeTurck_metric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric =
      sol.transformedMetric := by
  rfl

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackDeTurck_metricVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity =
      sol.transformedVelocity := by
  rfl

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackDeTurck_timeSet
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.timeSet =
      sol.source.toIntrinsicDeTurckSolution.timeSet := by
  rfl

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackDeTurck_background
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background =
      SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background := by
  rfl

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackDeTurck_hasTimeDerivativeOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
      sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity
      sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.timeSet := by
  simpa [GaugeReducedIntrinsicDeTurckLocalSolution.toPulledBackIntrinsicDeTurckLocalSolution]
    using sol.transformed_hasTimeDerivative

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackDeTurck_equation
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ}
    (ht : t ∈ sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.timeSet) :
    SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M)
      sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
      sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity
      sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t := by
  simpa [GaugeReducedIntrinsicDeTurckLocalSolution.toPulledBackIntrinsicDeTurckLocalSolution]
    using sol.satisfiesIntrinsicDeTurckEquationAt_pullbackBackground ht

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackDeTurck_toIntrinsicLocalSolution_metric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution
      sol.pulledBackDeTurck_background_isLeviCivita).toIntrinsicSolution.metric =
      sol.transformedMetric := by
  rfl

theorem GaugeReducedIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_metric_eq_pulledBack
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toIntrinsicLocalSolution.toIntrinsicSolution.metric =
      (sol.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution
        sol.pulledBackDeTurck_background_isLeviCivita).toIntrinsicSolution.metric := by
  rw [sol.toIntrinsicLocalSolution_metric, sol.pulledBackDeTurck_toIntrinsicLocalSolution_metric]

/-- Compact-theorem package after the analytic DeTurck solution and non-identity gauge-reduction
obligations have been discharged. -/
structure GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  /-- Existence of a gauge-reduced DeTurck local solution. -/
  exists_solution :
    Nonempty (GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
  /-- Uniqueness of intrinsic Ricci-flow metrics on overlaps, supplied by the analytic uniqueness
  argument after gauge reduction. -/
  unique_metric :
    ∀ sol₁ sol₂ :
        IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime),
        ∀ x : M, ∀ u v : TM x,
          metricTensor (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v =
            metricTensor (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v

theorem gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_nonempty_localSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  pkg.exists_solution

theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.nonempty_pulledBackDeTurckLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) := by
  rcases pkg.exists_solution with ⟨sol⟩
  exact ⟨sol.toPulledBackIntrinsicDeTurckLocalSolution⟩

theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.transformedMetric_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.source.terminalTime sol₂.source.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.transformedMetric t x u v =
      metricTensor (I := I) (M := M) sol₂.transformedMetric t x u v := by
  exact pkg.unique_metric sol₁.toIntrinsicLocalSolution sol₂.toIntrinsicLocalSolution t ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.pulledBackDeTurckMetric_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.source.terminalTime sol₂.source.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
        sol₁.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
        t x u v =
      metricTensor (I := I) (M := M)
        sol₂.toPulledBackIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
        t x u v := by
  simpa [GaugeReducedIntrinsicDeTurckLocalSolution.toPulledBackIntrinsicDeTurckLocalSolution] using
    pkg.transformedMetric_eq_on_common_interval sol₁ sol₂ ht x u v

noncomputable def GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := by
    rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toIntrinsicLocalSolution⟩
  unique_metric := by
    intro sol₁ sol₂ t ht x u v
    exact pkg.unique_metric sol₁ sol₂ t ht x u v

noncomputable def GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toIntrinsic.toOrdinary

theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.nonempty_intrinsicLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  pkg.toIntrinsic.exists_solution

theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.nonempty_localSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  pkg.toOrdinary.exists_solution

theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.connection_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    [CompactSpace M]
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.source.terminalTime sol₂.source.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toIntrinsicLocalSolution.toIntrinsicSolution.toSolution.connection t σ x =
      sol₂.toIntrinsicLocalSolution.toIntrinsicSolution.toSolution.connection t σ x := by
  exact intrinsicLocalExistenceUniqueness_connection_eq_on_common_interval
    (I := I) (M := M) (pkg := pkg.toIntrinsic)
    sol₁.toIntrinsicLocalSolution sol₂.toIntrinsicLocalSolution ht hσ

/-- In the zero-dimensional tangent-fiber case, a gauge-reduced package also controls the source
DeTurck metrics on common intervals. -/
theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.sourceMetric_eq_on_common_interval_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (_pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.source.terminalTime sol₂.source.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
        sol₁.source.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M)
        sol₂.source.toIntrinsicDeTurckSolution.metric t x u v :=
  sol₁.unique_source_metric_of_subsingleton_tangent sol₂ ht x u v

/-- In the zero-dimensional tangent-fiber case, a gauge-reduced package also controls the canonical
source DeTurck connections on common intervals. -/
theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.sourceConnection_eq_on_common_interval_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (_pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.source.terminalTime sol₂.source.terminalTime))
    {x : M} {σ : Π y : M, TM y} :
    sol₁.source.canonicalConnection sol₁.source_background_isLeviCivita_of_subsingleton_tangent
        t σ x =
      sol₂.source.canonicalConnection sol₂.source_background_isLeviCivita_of_subsingleton_tangent
        t σ x :=
  sol₁.unique_source_connection_of_subsingleton_tangent sol₂ ht

/-- In the zero-dimensional tangent-fiber case, a gauge-reduced package also controls the stored
source DeTurck background connection values on common intervals. -/
theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.sourceBackgroundConnection_eq_on_common_interval_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (_pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.source.terminalTime sol₂.source.terminalTime))
    {x : M} {σ : Π y : M, TM y} :
    sol₁.source.toIntrinsicDeTurckSolution.background t σ x =
      sol₂.source.toIntrinsicDeTurckSolution.background t σ x :=
  sol₁.unique_source_background_connection_of_subsingleton_tangent sol₂ ht

/-- A theorem-family version of the conditional gauge-reduced compact theorem package. Providing
this data for every initial-value problem is enough to derive the point-4 theorem family. -/
structure GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily where
  package :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
        (E := E) (H := H) (I := I) (M := M) ivp

noncomputable def GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsic
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  fun ivp ↦ (pkg.package ivp).toIntrinsic

noncomputable def GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinary
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  fun ivp ↦ (pkg.package ivp).toOrdinary

noncomputable def GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := pkg.toIntrinsic

noncomputable def GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  pkg.toIntrinsicFamily.toOrdinary

theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily.nonempty_localSolution
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  ((pkg.toOrdinary ivp).exists_solution)

theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily.connection_eq_on_common_interval
    [CompactSpace M]
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol₁ sol₂ : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.source.terminalTime sol₂.source.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toIntrinsicLocalSolution.toIntrinsicSolution.toSolution.connection t σ x =
      sol₂.toIntrinsicLocalSolution.toIntrinsicSolution.toSolution.connection t σ x :=
  (pkg.package ivp).connection_eq_on_common_interval sol₁ sol₂ ht hσ

theorem IntrinsicDeTurckLocalSolution.identityDiffeomorphGaugeOn_inner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (t : ℝ) (x : M) (u v : TM x) :
    (sol.toIntrinsicDeTurckSolution.metric t).inner x u v =
      (sol.toIntrinsicDeTurckSolution.metric t).inner
        (((sol.identityDiffeomorphGaugeOn hbackground).maps t) x)
        ((((sol.identityDiffeomorphGaugeOn hbackground).maps t).pushforwardTangent x) u)
        ((((sol.identityDiffeomorphGaugeOn hbackground).maps t).pushforwardTangent x) v) := by
  have hΦ : (SmoothSelfDiffeomorph2Family.id (I := I) (M := M)).AnchoredAt t :=
    SmoothSelfDiffeomorph2Family.id_anchoredAt (I := I) (M := M) t
  change (sol.toIntrinsicDeTurckSolution.metric t).inner x u v =
      (sol.toIntrinsicDeTurckSolution.metric t).inner
        (((SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) t) x)
        ((((SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) t).pushforwardTangent x) u)
        ((((SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) t).pushforwardTangent x) v)
  rw [
    SmoothSelfDiffeomorph2Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) hΦ x u,
    SmoothSelfDiffeomorph2Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) hΦ x v,
    SmoothSelfDiffeomorph2Family.AnchoredAt.apply
      (Φ := SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) hΦ x]

theorem IntrinsicDeTurckLocalSolution.identityDiffeomorphGaugeOn_pullbackBackground_contMDiff
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hconn : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background t) 1) :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          (sol.identityDiffeomorphGaugeOn hbackground).maps
          sol.toIntrinsicDeTurckSolution.background t) 1 := by
  intro t
  have hconn_eq :
      SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        (sol.identityDiffeomorphGaugeOn hbackground).maps
        sol.toIntrinsicDeTurckSolution.background t =
      sol.toIntrinsicDeTurckSolution.background t := by
    change SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        (SmoothSelfDiffeomorph2Family.id (I := I) (M := M))
        sol.toIntrinsicDeTurckSolution.background t =
      sol.toIntrinsicDeTurckSolution.background t
    exact SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_eq_at_anchored_time
      (I := I) (M := M) (Φ := SmoothSelfDiffeomorph2Family.id (I := I) (M := M))
      sol.toIntrinsicDeTurckSolution.background
      (SmoothSelfDiffeomorph2Family.id_anchoredAt (I := I) (M := M) t)
  rw [hconn_eq]
  exact hconn t

theorem IntrinsicDeTurckLocalSolution.identityDiffeomorph3GaugeOn_pullbackBackground_contMDiff
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hconn : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background t) 1) :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          (sol.identityDiffeomorph3GaugeOn hbackground).maps
          sol.toIntrinsicDeTurckSolution.background t) 1 := by
  intro t
  have hconn_eq :
      SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        (sol.identityDiffeomorph3GaugeOn hbackground).maps
        sol.toIntrinsicDeTurckSolution.background t =
      sol.toIntrinsicDeTurckSolution.background t := by
    change SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        (SmoothSelfDiffeomorph3Family.id (I := I) (M := M))
        sol.toIntrinsicDeTurckSolution.background t =
      sol.toIntrinsicDeTurckSolution.background t
    exact congrFun
      (SmoothSelfDiffeomorph3Family.id_pullbackConnectionFamily
        (I := I) (M := M) sol.toIntrinsicDeTurckSolution.background) t
  rw [hconn_eq]
  exact hconn t

noncomputable def IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  (sol.identityDiffeomorphGaugeOn hbackground).toIntrinsicLocalSolution_of_pullbackBackgroundEquation
    sol
    (sol.identityDiffeomorphGaugeOn_inner hbackground)
    hbackground
    (sol.identityDiffeomorphGaugeOn_pullbackBackground_contMDiff hbackground
      (sol.background_contMDiff_of_isLeviCivita hbackground))
    (intrinsicDeTurckSolution_hasTimeDerivativeOn
      (I := I) (M := M) sol.toIntrinsicDeTurckSolution)
    (by
      intro t ht
      have hIntrinsicDeTurck :
          SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M)
            sol.toIntrinsicDeTurckSolution.metric
            sol.toIntrinsicDeTurckSolution.metricVelocity
            sol.toIntrinsicDeTurckSolution.background t :=
        intrinsicDeTurckSolution_equation
          (I := I) (M := M) sol.toIntrinsicDeTurckSolution ht
      have hIntrinsic :
          SatisfiesIntrinsicEquationAt (I := I) (M := M)
            sol.toIntrinsicDeTurckSolution.metric
            sol.toIntrinsicDeTurckSolution.metricVelocity t :=
        (satisfiesIntrinsicDeTurckEquationAt_iff_of_isLeviCivita
          (I := I) (M := M)
          sol.toIntrinsicDeTurckSolution.metric
          sol.toIntrinsicDeTurckSolution.metricVelocity
          sol.toIntrinsicDeTurckSolution.background t hbackground).1 hIntrinsicDeTurck
      have hBackgroundEquation :
          SatisfiesEquationAt (I := I) (M := M)
            sol.toIntrinsicDeTurckSolution.metric
            sol.toIntrinsicDeTurckSolution.background
            (sol.background_contMDiff_of_isLeviCivita hbackground)
            sol.toIntrinsicDeTurckSolution.metricVelocity t :=
        (satisfiesIntrinsicEquationAt_iff_of_isLeviCivita
          (I := I) (M := M)
          sol.toIntrinsicDeTurckSolution.metric
          (sol.background_contMDiff_of_isLeviCivita hbackground)
          sol.toIntrinsicDeTurckSolution.metricVelocity t hbackground).1 hIntrinsic
      have hconn_eq :
          SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            (sol.identityDiffeomorphGaugeOn hbackground).maps
            sol.toIntrinsicDeTurckSolution.background t =
          sol.toIntrinsicDeTurckSolution.background t := by
        change SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            (SmoothSelfDiffeomorph2Family.id (I := I) (M := M))
            sol.toIntrinsicDeTurckSolution.background t =
          sol.toIntrinsicDeTurckSolution.background t
        exact SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_eq_at_anchored_time
          (I := I) (M := M) (Φ := SmoothSelfDiffeomorph2Family.id (I := I) (M := M))
          sol.toIntrinsicDeTurckSolution.background
          (SmoothSelfDiffeomorph2Family.id_anchoredAt (I := I) (M := M) t)
      have hconn_eq' :
          (((sol.identityDiffeomorphGaugeOn hbackground).maps t).pullbackCovariantDerivative
            (sol.toIntrinsicDeTurckSolution.background t)) =
          sol.toIntrinsicDeTurckSolution.background t := by
        simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using hconn_eq
      intro x u v
      simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply, hconn_eq'] using
        hBackgroundEquation x u v)

@[simp] theorem IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge_terminalTime
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    (sol.toIntrinsicLocalSolution_viaIdentityGauge hbackground).terminalTime =
      sol.terminalTime := by
  rfl

@[simp] theorem IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge_timeSet
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    (sol.toIntrinsicLocalSolution_viaIdentityGauge hbackground).toIntrinsicSolution.timeSet =
      sol.toIntrinsicDeTurckSolution.timeSet := by
  rfl

@[simp] theorem IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge_metric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    (sol.toIntrinsicLocalSolution_viaIdentityGauge hbackground).toIntrinsicSolution.metric =
      sol.toIntrinsicDeTurckSolution.metric := by
  rfl

@[simp] theorem IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge_metricVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    (sol.toIntrinsicLocalSolution_viaIdentityGauge hbackground).toIntrinsicSolution.metricVelocity =
      sol.toIntrinsicDeTurckSolution.metricVelocity := by
  rfl

/-- In the zero-dimensional tangent-fiber case, the identity gauge turns any intrinsic
Ricci-DeTurck local solution into an intrinsic Ricci-flow local solution, because every DeTurck
background is automatically Levi-Civita. -/
noncomputable def IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.toIntrinsicLocalSolution_viaIdentityGauge
    sol.background_isLeviCivita_of_subsingleton_tangent

@[simp] theorem IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge_of_subsingleton_tangent_metric
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    (sol.toIntrinsicLocalSolution_viaIdentityGauge_of_subsingleton_tangent).toIntrinsicSolution.metric =
      sol.toIntrinsicDeTurckSolution.metric := by
  rfl

noncomputable def IntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3Gauge
    sol
    (sol.identityDiffeomorph3GaugeOn hbackground)
    hbackground
    sol.toIntrinsicDeTurckSolution.metricVelocity
    (sol.identityDiffeomorph3GaugeOn_pullbackBackground_contMDiff hbackground
      (sol.background_contMDiff_of_isLeviCivita hbackground))
    (by
      change HasTimeDerivativeOn (I := I) (M := M)
        ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
          sol.toIntrinsicDeTurckSolution.metric)
        sol.toIntrinsicDeTurckSolution.metricVelocity sol.toIntrinsicDeTurckSolution.timeSet
      simpa using
        intrinsicDeTurckSolution_hasTimeDerivativeOn
          (I := I) (M := M) sol.toIntrinsicDeTurckSolution)
    (by
      intro t ht
      have hIntrinsicDeTurck :
          SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M)
            sol.toIntrinsicDeTurckSolution.metric
            sol.toIntrinsicDeTurckSolution.metricVelocity
            sol.toIntrinsicDeTurckSolution.background t :=
        intrinsicDeTurckSolution_equation
          (I := I) (M := M) sol.toIntrinsicDeTurckSolution ht
      have hIntrinsic :
          SatisfiesIntrinsicEquationAt (I := I) (M := M)
            sol.toIntrinsicDeTurckSolution.metric
            sol.toIntrinsicDeTurckSolution.metricVelocity t :=
        (satisfiesIntrinsicDeTurckEquationAt_iff_of_isLeviCivita
          (I := I) (M := M)
          sol.toIntrinsicDeTurckSolution.metric
          sol.toIntrinsicDeTurckSolution.metricVelocity
          sol.toIntrinsicDeTurckSolution.background t hbackground).1 hIntrinsicDeTurck
      have hpullLC :
          CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
            (I := I) (M := M)
            ((sol.identityDiffeomorph3GaugeOn hbackground).maps.pullbackMetricFamily
              sol.toIntrinsicDeTurckSolution.metric)
            (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              (sol.identityDiffeomorph3GaugeOn hbackground).maps
              sol.toIntrinsicDeTurckSolution.background) :=
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.pullbackBackgroundConnection_isLeviCivita_pullbackMetricFamily
          (I := I) (M := M) (sol.identityDiffeomorph3GaugeOn hbackground) hbackground
      have hIntrinsicPull :
          SatisfiesIntrinsicEquationAt (I := I) (M := M)
            ((sol.identityDiffeomorph3GaugeOn hbackground).maps.pullbackMetricFamily
              sol.toIntrinsicDeTurckSolution.metric)
            sol.toIntrinsicDeTurckSolution.metricVelocity t := by
        change SatisfiesIntrinsicEquationAt (I := I) (M := M)
          ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
            sol.toIntrinsicDeTurckSolution.metric)
          sol.toIntrinsicDeTurckSolution.metricVelocity t
        simpa using hIntrinsic
      exact
        (satisfiesIntrinsicEquationAt_iff_of_isLeviCivita
          (I := I) (M := M)
           ((sol.identityDiffeomorph3GaugeOn hbackground).maps.pullbackMetricFamily
             sol.toIntrinsicDeTurckSolution.metric)
           (sol.identityDiffeomorph3GaugeOn_pullbackBackground_contMDiff hbackground
             (sol.background_contMDiff_of_isLeviCivita hbackground))
           sol.toIntrinsicDeTurckSolution.metricVelocity t hpullLC).1 hIntrinsicPull)

@[simp] theorem IntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    (sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge hbackground).source = sol := by
  rfl

@[simp] theorem IntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge_transformedMetric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    (sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge hbackground).transformedMetric =
      (sol.identityDiffeomorph3GaugeOn hbackground).maps.pullbackMetricFamily
        sol.toIntrinsicDeTurckSolution.metric := by
  rfl

@[simp] theorem IntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge_transformedMetric_eq_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    (sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge hbackground).transformedMetric =
      sol.toIntrinsicDeTurckSolution.metric := by
  change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
      sol.toIntrinsicDeTurckSolution.metric =
    sol.toIntrinsicDeTurckSolution.metric
  simp

@[simp] theorem IntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge_transformedVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    (sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge hbackground).transformedVelocity =
      sol.toIntrinsicDeTurckSolution.metricVelocity := by
  rfl

/-- In the zero-dimensional tangent-fiber case, any intrinsic Ricci-DeTurck local solution is already
gauge-reduced by the identity `C³` gauge. -/
noncomputable def IntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityGauge_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge
    sol.background_isLeviCivita_of_subsingleton_tangent

@[simp] theorem IntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityGauge_of_subsingleton_tangent_source
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    (sol.toGaugeReduced_viaIdentityGauge_of_subsingleton_tangent).source = sol := by
  rfl

@[simp] theorem IntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityGauge_of_subsingleton_tangent_transformedVelocity
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    (sol.toGaugeReduced_viaIdentityGauge_of_subsingleton_tangent).transformedVelocity =
      sol.toIntrinsicDeTurckSolution.metricVelocity := by
  rfl

@[simp] theorem IntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityGauge_of_subsingleton_tangent_transformedMetric
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    (sol.toGaugeReduced_viaIdentityGauge_of_subsingleton_tangent).transformedMetric =
      sol.toIntrinsicDeTurckSolution.metric := by
  change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
      sol.toIntrinsicDeTurckSolution.metric =
      sol.toIntrinsicDeTurckSolution.metric
  simp

/-- For an identity `C³` gauge whose source background is already Levi-Civita, the concrete
gauge-corrected pullback velocity is just the source DeTurck velocity. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocity_identityDiffeomorph3Gauge_eq_metricVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    sol.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (sol.identityDiffeomorph3GaugeOn hbackground) =
      sol.toIntrinsicDeTurckSolution.metricVelocity := by
  funext t x u v
  let gauge3 := sol.identityDiffeomorph3GaugeOn hbackground
  change sol.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v =
    sol.toIntrinsicDeTurckSolution.metricVelocity t x u v
  have hΦ : (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).AnchoredAt t :=
    SmoothSelfDiffeomorph3Family.id_anchoredAt (I := I) (M := M) t
  have hx : (gauge3.maps t) x = x := by
    change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t) x = x
    exact SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x
  have hu : (gauge3.maps t).pushforwardTangent x u = u := by
    change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t).pushforwardTangent x u = u
    exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x u
  have hv : (gauge3.maps t).pushforwardTangent x v = v := by
    change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t).pushforwardTangent x v = v
    exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x v
  have hvec :
      sol.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t = 0 := by
    rw [sol.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge_eq_pullbackVectorField]
    have hsource :
        intrinsicDeTurckVectorField (I := I) (M := M)
          sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background t = 0 := by
      exact congrFun
        (intrinsicDeTurckVectorField_eq_zero_of_isLeviCivita
          (I := I) (M := M)
          sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
          hbackground) t
    rw [hsource]
    funext y
    rw [SmoothSelfDiffeomorph2.pullbackVectorField_apply]
    exact ContinuousLinearMap.map_zero ((gauge3.maps t).pullbackTangent y)
  let pulledConnection :=
    SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      gauge3.maps
      (chosenLeviCivitaFamily (I := I) (M := M) sol.toIntrinsicDeTurckSolution.metric) t
  have hcov :
      pulledConnection (sol.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) = 0 := by
    rw [hvec]
    exact CovariantDerivative.zero (cov := pulledConnection)
  have hcovu :
      pulledConnection (sol.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u = 0 := by
    exact congrArg (fun A => A u) (congrFun hcov x)
  have hcovv :
      pulledConnection (sol.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v = 0 := by
    exact congrArg (fun A => A v) (congrFun hcov x)
  have hleft :
      ((gauge3.maps.pullbackMetricFamily sol.toIntrinsicDeTurckSolution.metric) t).inner x
          (pulledConnection
            (sol.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v = 0 := by
    rw [hcovu]
    exact congrArg (fun L : TM x →L[ℝ] ℝ => L v)
      (ContinuousLinearMap.map_zero
        (((gauge3.maps.pullbackMetricFamily sol.toIntrinsicDeTurckSolution.metric) t).inner x))
  have hright :
      ((gauge3.maps.pullbackMetricFamily sol.toIntrinsicDeTurckSolution.metric) t).inner x u
          (pulledConnection
            (sol.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v) = 0 := by
    rw [hcovv]
    exact ContinuousLinearMap.map_zero
      (((gauge3.maps.pullbackMetricFamily sol.toIntrinsicDeTurckSolution.metric) t).inner x u)
  have hpoint :
      sol.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x) u v =
        sol.toIntrinsicDeTurckSolution.metricVelocity t x u v := by
    change sol.toIntrinsicDeTurckSolution.metricVelocity t
        ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M) t) x) u v =
      sol.toIntrinsicDeTurckSolution.metricVelocity t x u v
    rw [SmoothSelfDiffeomorph3Family.AnchoredAt.apply
      (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x]
  have hleftExact :
      ((gauge3.maps.pullbackMetricFamily sol.toIntrinsicDeTurckSolution.metric) t).inner x
          ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.toIntrinsicDeTurckSolution.metric) t)
            (sol.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x u) v = 0 := by
    simpa [pulledConnection] using hleft
  have hrightExact :
      ((gauge3.maps.pullbackMetricFamily sol.toIntrinsicDeTurckSolution.metric) t).inner x u
          ((SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
              gauge3.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.toIntrinsicDeTurckSolution.metric) t)
            (sol.pulledBackSourceDeTurckVectorFieldOfDiffeomorph3Gauge gauge3 t) x v) = 0 := by
    simpa [pulledConnection] using hright
  rw [IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_apply]
  rw [hu, hv, hleftExact, hrightExact, zero_add, sub_zero]
  exact hpoint

/-- The identity `C³` gauge has the scalar derivative expected by the explicit
inner-derivative gauge-reducibility interface. -/
theorem IntrinsicDeTurckLocalSolution.identityDiffeomorph3Gauge_inner_hasDerivAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    ∀ ⦃t : ℝ⦄, t ∈ sol.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x,
        HasDerivAt
          (fun τ ↦
            (sol.toIntrinsicDeTurckSolution.metric τ).inner
              (((sol.identityDiffeomorph3GaugeOn hbackground).maps τ) x)
              (((sol.identityDiffeomorph3GaugeOn hbackground).maps τ).pushforwardTangent x u)
              (((sol.identityDiffeomorph3GaugeOn hbackground).maps τ).pushforwardTangent x v))
          (sol.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (sol.identityDiffeomorph3GaugeOn hbackground) t x u v) t := by
  intro t ht x u v
  have hsource :
      HasDerivAt
        (fun τ ↦ metricTensor (I := I) (M := M)
          sol.toIntrinsicDeTurckSolution.metric τ x u v)
        (sol.toIntrinsicDeTurckSolution.metricVelocity t x u v) t :=
    intrinsicDeTurckSolution_hasTimeDerivativeOn
      (I := I) (M := M) sol.toIntrinsicDeTurckSolution ht x u v
  have hfun :
      (fun τ ↦
        (sol.toIntrinsicDeTurckSolution.metric τ).inner
          (((sol.identityDiffeomorph3GaugeOn hbackground).maps τ) x)
          (((sol.identityDiffeomorph3GaugeOn hbackground).maps τ).pushforwardTangent x u)
          (((sol.identityDiffeomorph3GaugeOn hbackground).maps τ).pushforwardTangent x v)) =
        (fun τ ↦ metricTensor (I := I) (M := M)
          sol.toIntrinsicDeTurckSolution.metric τ x u v) := by
    funext τ
    let hΦ : (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).AnchoredAt τ :=
      SmoothSelfDiffeomorph3Family.id_anchoredAt (I := I) (M := M) τ
    have hx :
        ((sol.identityDiffeomorph3GaugeOn hbackground).maps τ) x = x := by
      change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) τ) x = x
      exact SmoothSelfDiffeomorph3Family.AnchoredAt.apply
        (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x
    have hu :
        ((sol.identityDiffeomorph3GaugeOn hbackground).maps τ).pushforwardTangent x u = u := by
      change
        (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) τ).pushforwardTangent x u = u
      exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent
        (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x u
    have hv :
        ((sol.identityDiffeomorph3GaugeOn hbackground).maps τ).pushforwardTangent x v = v := by
      change
        (SmoothSelfDiffeomorph3Family.id (I := I) (M := M) τ).pushforwardTangent x v = v
      exact SmoothSelfDiffeomorph3Family.AnchoredAt.pushforwardTangent
        (Φ := SmoothSelfDiffeomorph3Family.id (I := I) (M := M)) hΦ x v
    rw [hu, hv, hx]
    rfl
  have hvel :
      sol.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          (sol.identityDiffeomorph3GaugeOn hbackground) t x u v =
        sol.toIntrinsicDeTurckSolution.metricVelocity t x u v := by
    exact congrFun
      (congrFun
        (congrFun
          (congrFun
            (sol.gaugeCorrectedPullbackVelocity_identityDiffeomorph3Gauge_eq_metricVelocity
              hbackground) t) x) u) v
  rw [hfun, hvel]
  exact hsource

/-- An intrinsic Ricci-DeTurck local solution whose background connection is already the
Levi-Civita family of the evolving metric. Slicewise `C¹` regularity is derived from the
Levi-Civita hypothesis, so this is the generic identity-gauge input: the DeTurck vector field
vanishes, and the identity gauge turns the DeTurck local solution into an intrinsic Ricci-flow
local solution. -/
structure LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  toIntrinsicDeTurckLocalSolution :
    IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp
  background_isLeviCivita :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
      toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.background_contMDiff
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t) 1 :=
  sol.toIntrinsicDeTurckLocalSolution.background_contMDiff_of_isLeviCivita
    sol.background_isLeviCivita

noncomputable def LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.toIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge
    sol.background_isLeviCivita

@[simp] theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge_metric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toIntrinsicLocalSolution_viaIdentityGauge.toIntrinsicSolution.metric =
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric := by
  rfl

@[simp] theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge_metricVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toIntrinsicLocalSolution_viaIdentityGauge.toIntrinsicSolution.metricVelocity =
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity := by
  rfl

noncomputable def LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp where
  source := sol.toIntrinsicDeTurckLocalSolution
  gauge := sol.toIntrinsicDeTurckLocalSolution.identityDiffeomorphGaugeOn
    sol.background_isLeviCivita
  transformedMetric := sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
  transformedVelocity := sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity
  transformed_inner := sol.toIntrinsicDeTurckLocalSolution.identityDiffeomorphGaugeOn_inner
    sol.background_isLeviCivita
  background_isLeviCivita := sol.background_isLeviCivita
  pullbackBackground_contMDiff :=
    sol.toIntrinsicDeTurckLocalSolution.identityDiffeomorphGaugeOn_pullbackBackground_contMDiff
      sol.background_isLeviCivita sol.background_contMDiff
  transformed_hasTimeDerivative :=
    intrinsicDeTurckSolution_hasTimeDerivativeOn
      (I := I) (M := M) sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution
  transformed_equation := by
    intro t ht
    have hIntrinsicDeTurck :
        SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M)
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t :=
      intrinsicDeTurckSolution_equation
        (I := I) (M := M)
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution ht
    have hIntrinsic :
        SatisfiesIntrinsicEquationAt (I := I) (M := M)
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity t :=
      (satisfiesIntrinsicDeTurckEquationAt_iff_of_isLeviCivita
        (I := I) (M := M)
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t
        sol.background_isLeviCivita).1 hIntrinsicDeTurck
    have hBackgroundEquation :
        SatisfiesEquationAt (I := I) (M := M)
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background
          sol.background_contMDiff
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity t :=
      (satisfiesIntrinsicEquationAt_iff_of_isLeviCivita
        (I := I) (M := M)
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
        sol.background_contMDiff
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity t
        sol.background_isLeviCivita).1 hIntrinsic
    have hconn_eq :
        SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          (sol.toIntrinsicDeTurckLocalSolution.identityDiffeomorphGaugeOn
            sol.background_isLeviCivita).maps
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t =
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t := by
      change SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          (SmoothSelfDiffeomorph2Family.id (I := I) (M := M))
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t =
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t
      exact SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_eq_at_anchored_time
        (I := I) (M := M) (Φ := SmoothSelfDiffeomorph2Family.id (I := I) (M := M))
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background
        (SmoothSelfDiffeomorph2Family.id_anchoredAt (I := I) (M := M) t)
    have hconn_eq' :
        (((sol.toIntrinsicDeTurckLocalSolution.identityDiffeomorphGaugeOn
          sol.background_isLeviCivita).maps t).pullbackCovariantDerivative
          (sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t)) =
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t := by
      simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using hconn_eq
    intro x u v
    simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply, hconn_eq'] using
      hBackgroundEquation x u v

@[simp] theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityGauge_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityGauge.source = sol.toIntrinsicDeTurckLocalSolution := by
  rfl

@[simp] theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityGauge_transformedMetric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityGauge.transformedMetric =
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric := by
  rfl

@[simp] theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityGauge_transformedVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityGauge.transformedVelocity =
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity := by
  rfl

noncomputable def LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.toIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge
    sol.background_isLeviCivita

@[simp] theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge.source =
      sol.toIntrinsicDeTurckLocalSolution := by
  rfl

@[simp] theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge_transformedMetric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge.transformedMetric =
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric := by
  change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric =
    sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
  simp

@[simp] theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge_transformedVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge.transformedVelocity =
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity := by
  rfl

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.identityDiffeomorph3Gauge_transformedMetric_eq_identityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge.transformedMetric =
      sol.toGaugeReduced_viaIdentityGauge.transformedMetric := by
  simp

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.identityDiffeomorph3Gauge_transformedVelocity_eq_identityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge.transformedVelocity =
      sol.toGaugeReduced_viaIdentityGauge.transformedVelocity := by
  simp

noncomputable def ChosenIntrinsicDeTurckLocalSolution.toLeviCivitaBackground
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp where
  toIntrinsicDeTurckLocalSolution := sol.1
  background_isLeviCivita :=
    usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2

/-- A chosen-background DeTurck local solution is gauge-reduced by the identity gauge, since the
chosen background is Levi-Civita by construction. -/
noncomputable def ChosenIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.toLeviCivitaBackground.toGaugeReduced_viaIdentityGauge

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityGauge_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityGauge.source = sol.1 := by
  rfl

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityGauge_transformedMetric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityGauge.transformedMetric =
      sol.1.toIntrinsicDeTurckSolution.metric := by
  rfl

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityGauge_transformedVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityGauge.transformedVelocity =
      sol.1.toIntrinsicDeTurckSolution.metricVelocity := by
  rfl

noncomputable def IntrinsicLocalSolution.toLeviCivitaBackgroundIntrinsicDeTurckLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (⟨sol.toChosenIntrinsicDeTurckLocalSolution,
    intrinsicLocalSolution_usesChosenBackground (I := I) (M := M) sol⟩ :
    ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
      |> ChosenIntrinsicDeTurckLocalSolution.toLeviCivitaBackground

noncomputable def IntrinsicLocalSolution.toGaugeReduced_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.toLeviCivitaBackgroundIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityGauge

@[simp] theorem IntrinsicLocalSolution.toGaugeReduced_viaIdentityGauge_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityGauge.source =
      sol.toChosenIntrinsicDeTurckLocalSolution := by
  rfl

@[simp] theorem IntrinsicLocalSolution.toGaugeReduced_viaIdentityGauge_transformedMetric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityGauge.transformedMetric =
      sol.toIntrinsicSolution.metric := by
  rfl

@[simp] theorem IntrinsicLocalSolution.toGaugeReduced_viaIdentityGauge_transformedVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityGauge.transformedVelocity =
      sol.toIntrinsicSolution.metricVelocity := by
  rfl

/-- The Levi-Civita-background DeTurck stationary local solution attached to Ricci-flat initial
data. -/
noncomputable def stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp :=
  ChosenIntrinsicDeTurckLocalSolution.toLeviCivitaBackground
    (⟨(stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toChosenIntrinsicDeTurckLocalSolution,
      intrinsicLocalSolution_usesChosenBackground (I := I) (M := M)
        (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat)⟩ :
      ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)

@[simp] theorem stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution =
      stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat := by
  rfl

theorem leviCivitaBackgroundIntrinsicDeTurckLocalSolution_nonempty_of_isRicciFlat
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
    (I := I) (M := M) hRicciFlat⟩

theorem stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        ((stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity)
          t x u v = 0 := by
  simpa using
    stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat

theorem stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_intrinsicRicciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M)
          ((stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
            (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric)
            t x u v = 0 := by
  simpa using
    stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) ivp hRicciFlat

theorem stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_intrinsicRicciFlowRHS_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M)
      (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
      t x u v = 0 := by
  simpa using
    stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_intrinsicRicciFlowRHS_eq_zero
      (I := I) (M := M) ivp hRicciFlat ht x u v

theorem stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_intrinsicRicciDeTurckRHS_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M)
      ((stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric)
      ((stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background)
      t x u v = 0 := by
  simpa using
    stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_intrinsicRicciDeTurckRHS_eq_zero
      (I := I) (M := M) ivp hRicciFlat ht x u v

theorem stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metric_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
      t x u v =
        ivp.initialMetric.inner x u v := by
  simpa using
    stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metric_eq_initial
      (I := I) (M := M) ivp hRicciFlat ht x u v

theorem stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_unique_metric_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.terminalTime
        sol.toIntrinsicDeTurckLocalSolution.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
      t x u v =
    metricTensor (I := I) (M := M)
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v := by
  let stat :=
    stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat
  have hzero_stat :
      ∀ t ∈ Set.Icc ivp.initialTime stat.toIntrinsicDeTurckLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x,
          stat.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0 := by
    simpa [stat] using
      stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
        (I := I) (M := M) hRicciFlat
  exact intrinsicDeTurckLocalSolution_unique_metric_of_zero_velocity
    (I := I) (M := M)
    stat.toIntrinsicDeTurckLocalSolution sol.toIntrinsicDeTurckLocalSolution
    stat.background_isLeviCivita sol.background_isLeviCivita hzero_stat hzero ht x u v

theorem stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_unique_metric_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M)
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.terminalTime
        sol.toIntrinsicDeTurckLocalSolution.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric
      t x u v =
    metricTensor (I := I) (M := M)
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v := by
  let stat :=
    stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat
  have hRicciZero_stat :
      ∀ t ∈ Set.Icc ivp.initialTime stat.toIntrinsicDeTurckLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M)
            stat.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v = 0 := by
    simpa [stat] using
      stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_intrinsicRicciTensor_eq_zero
        (I := I) (M := M) hRicciFlat
  exact intrinsicDeTurckLocalSolution_unique_metric_of_ricciTensor_zero
    (I := I) (M := M)
    stat.toIntrinsicDeTurckLocalSolution sol.toIntrinsicDeTurckLocalSolution
    stat.background_isLeviCivita sol.background_isLeviCivita
    hRicciZero_stat hRicciZero ht x u v

/-- The identity-gauge-reduced stationary local solution attached to Ricci-flat initial data. -/
noncomputable def stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
    (I := I) (M := M) ivp hRicciFlat).toGaugeReduced_viaIdentityGauge

@[simp] theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).source =
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toChosenIntrinsicDeTurckLocalSolution := by
  rfl

@[simp] theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_transformedMetric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).transformedMetric =
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.metric := by
  rfl

@[simp] theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_transformedVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).transformedVelocity =
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.metricVelocity := by
  rfl

theorem gaugeReducedLocalSolution_nonempty_of_isRicciFlat
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ⟨stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
    (I := I) (M := M) hRicciFlat⟩

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_transformedVelocity_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).transformedVelocity t x u v = 0 := by
  convert stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat using 1 <;> rfl

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_sourceVelocity_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).source.toIntrinsicDeTurckSolution.metricVelocity
          t x u v = 0 := by
  convert stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat using 1 <;> rfl

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_transformed_intrinsicRicciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M)
          (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
            (I := I) (M := M) hRicciFlat).transformedMetric t x u v = 0 := by
  let stat :=
    stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat
  have hzero :
      ∀ t ∈ Set.Icc ivp.initialTime stat.toIntrinsicLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x,
          stat.toIntrinsicLocalSolution.toIntrinsicSolution.metricVelocity t x u v = 0 := by
    convert stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_transformedVelocity_eq_zero
        (I := I) (M := M) hRicciFlat using 1 <;> rfl
  convert (intrinsicLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) stat.toIntrinsicLocalSolution).1 hzero using 1 <;> rfl

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_transformed_intrinsicRicciFlowRHS_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).source.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M)
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).transformedMetric t x u v = 0 :=
  intrinsicRicciFlowRHS_eq_zero_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M)
    (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).transformedMetric
    (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_transformed_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) hRicciFlat t ht x u v)

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_source_intrinsicRicciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M)
          (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
            (I := I) (M := M) hRicciFlat).source.toIntrinsicDeTurckSolution.metric t x u v = 0 := by
  let stat :=
    stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat
  have hzero :
      ∀ t ∈ Set.Icc ivp.initialTime stat.source.terminalTime,
        ∀ x : M, ∀ u v : TM x,
          stat.source.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0 := by
    simpa [stat] using
      stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_sourceVelocity_eq_zero
        (I := I) (M := M) hRicciFlat
  simpa [stat] using
    (intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) stat.source stat.background_isLeviCivita).1 hzero

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_source_intrinsicRicciFlowRHS_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).source.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M)
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).source.toIntrinsicDeTurckSolution.metric t x u v = 0 :=
  intrinsicRicciFlowRHS_eq_zero_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M)
    (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).source.toIntrinsicDeTurckSolution.metric
    (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_source_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) hRicciFlat t ht x u v)

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_source_intrinsicRicciDeTurckRHS_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).source.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M)
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).source.toIntrinsicDeTurckSolution.metric
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).source.toIntrinsicDeTurckSolution.background t x u v = 0 := by
  let stat :=
    stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat
  exact intrinsicRicciDeTurckRHS_eq_zero_of_isLeviCivita_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) stat.source.toIntrinsicDeTurckSolution.metric
    stat.source.toIntrinsicDeTurckSolution.background stat.background_isLeviCivita
    (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_source_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) hRicciFlat t ht x u v)

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_transformedMetric_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).source.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).transformedMetric t x u v =
      ivp.initialMetric.inner x u v := by
  convert stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_metric_eq_initial
      (I := I) (M := M) ivp hRicciFlat ht x u v using 1 <;> rfl

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_sourceMetric_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).source.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).source.toIntrinsicDeTurckSolution.metric t x u v =
      ivp.initialMetric.inner x u v := by
  convert stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metric_eq_initial
      (I := I) (M := M) ivp hRicciFlat ht x u v using 1 <;> rfl

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_unique_transformedMetric_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x, sol.transformedVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).source.terminalTime
        sol.source.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).transformedMetric t x u v =
      metricTensor (I := I) (M := M) sol.transformedMetric t x u v := by
  let stat :=
    stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat
  have hzero_stat :
      ∀ t ∈ Set.Icc ivp.initialTime stat.toLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x, stat.toLocalSolution.toSolution.metricVelocity t x u v = 0 := by
    convert stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_transformedVelocity_eq_zero
        (I := I) (M := M) hRicciFlat using 1 <;> rfl
  have hzero_sol :
      ∀ t ∈ Set.Icc ivp.initialTime sol.toLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x, sol.toLocalSolution.toSolution.metricVelocity t x u v = 0 := by
    convert hzero using 1 <;> rfl
  simpa [stat, GaugeReducedIntrinsicDeTurckLocalSolution.toLocalSolution_metric] using
    localSolution_unique_metric_of_zero_velocity
      (I := I) (M := M) stat.toLocalSolution sol.toLocalSolution
      hzero_stat hzero_sol ht x u v

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_unique_transformedConnection_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x, sol.transformedVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).source.terminalTime
        sol.source.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).toLocalSolution.toSolution.connection t σ x =
      sol.toLocalSolution.toSolution.connection t σ x := by
  let stat :=
    stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat
  have hzero_stat :
      ∀ t ∈ Set.Icc ivp.initialTime stat.toLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x, stat.toLocalSolution.toSolution.metricVelocity t x u v = 0 := by
    convert stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_transformedVelocity_eq_zero
        (I := I) (M := M) hRicciFlat using 1 <;> rfl
  have hzero_sol :
      ∀ t ∈ Set.Icc ivp.initialTime sol.toLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x, sol.toLocalSolution.toSolution.metricVelocity t x u v = 0 := by
    convert hzero using 1 <;> rfl
  simpa [stat] using
    localSolution_unique_connection_of_zero_velocity
      (I := I) (M := M) stat.toLocalSolution sol.toLocalSolution
      hzero_stat hzero_sol ht hσ

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_unique_transformedMetric_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).source.terminalTime
        sol.source.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).transformedMetric t x u v =
      metricTensor (I := I) (M := M) sol.transformedMetric t x u v := by
  let stat :=
    stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat
  have hRicciZero_sol :
      ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M)
            sol.toIntrinsicLocalSolution.toIntrinsicSolution.metric t x u v = 0 := by
    convert hRicciZero using 1 <;> rfl
  simpa [stat, GaugeReducedIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_metric] using
    stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_unique_metric_of_ricciTensor_zero
      (I := I) (M := M) ivp hRicciFlat sol.toIntrinsicLocalSolution
      hRicciZero_sol ht x u v

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_unique_transformedConnection_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M) sol.transformedMetric t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).source.terminalTime
        sol.source.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).toLocalSolution.toSolution.connection t σ x =
      sol.toLocalSolution.toSolution.connection t σ x := by
  let stat :=
    stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat
  have hRicciZero_sol :
      ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M)
            sol.toIntrinsicLocalSolution.toIntrinsicSolution.metric t x u v = 0 := by
    convert hRicciZero using 1 <;> rfl
  convert stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_unique_connection_of_ricciTensor_zero
      (I := I) (M := M) ivp hRicciFlat sol.toIntrinsicLocalSolution
      hRicciZero_sol ht hσ using 1 <;> rfl

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_unique_sourceMetric_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).source.terminalTime
        sol.source.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).source.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol.source.toIntrinsicDeTurckSolution.metric t x u v := by
  simpa [stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat,
    stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat,
    IntrinsicLocalSolution.toChosenIntrinsicDeTurckLocalSolution,
    IntrinsicLocalSolution.toIntrinsicDeTurckLocalSolution,
    IntrinsicSolution.toIntrinsicDeTurckSolution] using
    stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_unique_metric_of_zero_velocity
      (I := I) (M := M) ivp hRicciFlat sol.source sol.background_isLeviCivita
      hzero ht x u v

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_unique_sourceMetric_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).source.terminalTime
        sol.source.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).source.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol.source.toIntrinsicDeTurckSolution.metric t x u v := by
  simpa [stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat,
    stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat,
    IntrinsicLocalSolution.toChosenIntrinsicDeTurckLocalSolution,
    IntrinsicLocalSolution.toIntrinsicDeTurckLocalSolution,
    IntrinsicSolution.toIntrinsicDeTurckSolution] using
    stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_unique_metric_of_ricciTensor_zero
      (I := I) (M := M) ivp hRicciFlat sol.source sol.background_isLeviCivita
      hRicciZero ht x u v

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_unique_sourceConnection_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).source.terminalTime
        sol.source.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).source.canonicalConnection
        (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
            (I := I) (M := M) hRicciFlat).source.toIntrinsicDeTurckSolution.metric) t σ x =
      sol.source.canonicalConnection sol.background_isLeviCivita t σ x := by
  simpa [stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat,
    stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat,
    IntrinsicLocalSolution.toChosenIntrinsicDeTurckLocalSolution,
    IntrinsicLocalSolution.toIntrinsicDeTurckLocalSolution,
    IntrinsicSolution.toIntrinsicDeTurckSolution] using
    stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_unique_connection_of_zero_velocity
      (I := I) (M := M) ivp hRicciFlat sol.source sol.background_isLeviCivita
      hzero ht hσ

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_unique_sourceConnection_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.source.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).source.terminalTime
        sol.source.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).source.canonicalConnection
        (chosenLeviCivitaFamily_isLeviCivita (I := I) (M := M)
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
            (I := I) (M := M) hRicciFlat).source.toIntrinsicDeTurckSolution.metric) t σ x =
      sol.source.canonicalConnection sol.background_isLeviCivita t σ x := by
  simpa [stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat,
    stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat,
    IntrinsicLocalSolution.toChosenIntrinsicDeTurckLocalSolution,
    IntrinsicLocalSolution.toIntrinsicDeTurckLocalSolution,
    IntrinsicSolution.toIntrinsicDeTurckSolution] using
    stationaryRicciFlatChosenIntrinsicDeTurckLocalSolutionOfIsRicciFlat_unique_connection_of_ricciTensor_zero
      (I := I) (M := M) ivp hRicciFlat sol.source sol.background_isLeviCivita
      hRicciZero ht hσ

noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.toPulledBackLeviCivitaBackground
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp where
  toIntrinsicDeTurckLocalSolution := sol.toPulledBackIntrinsicDeTurckLocalSolution
  background_isLeviCivita := sol.pulledBackDeTurck_background_isLeviCivita

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackLeviCivitaBackground_metric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toPulledBackLeviCivitaBackground.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric =
      sol.transformedMetric := by
  rfl

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackLeviCivitaBackground_background
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toPulledBackLeviCivitaBackground.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background =
      SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background := by
  rfl

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackLeviCivitaBackground_timeSet
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toPulledBackLeviCivitaBackground.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.timeSet =
      sol.source.toIntrinsicDeTurckSolution.timeSet := by
  rfl

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackLeviCivitaBackground_toIntrinsicMetric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toPulledBackLeviCivitaBackground.toIntrinsicLocalSolution_viaIdentityGauge.toIntrinsicSolution.metric =
      sol.transformedMetric := by
  rfl

noncomputable def GaugeReducedIntrinsicDeTurckLocalSolution.toGaugeReduced_viaPulledBackIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.toPulledBackLeviCivitaBackground.toGaugeReduced_viaIdentityGauge

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.gaugeReducedViaPulledBackIdentityGauge_metric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaPulledBackIdentityGauge.transformedMetric =
      sol.transformedMetric := by
  rfl

@[simp] theorem GaugeReducedIntrinsicDeTurckLocalSolution.gaugeReducedViaPulledBackIdentityGauge_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaPulledBackIdentityGauge.source =
      sol.toPulledBackIntrinsicDeTurckLocalSolution := by
  rfl

/-- Compact-theorem package for intrinsic Ricci-DeTurck local solutions whose background is a
smooth Levi-Civita family for the evolving metric. -/
structure LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  /-- Existence of a local DeTurck solution with smooth Levi-Civita background. -/
  exists_solution :
    Nonempty (LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
  /-- Uniqueness of the evolving metric on common intervals among such DeTurck solutions. -/
  unique_metric :
    ∀ sol₁ sol₂ :
        LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Set.Icc ivp.initialTime
          (min sol₁.toIntrinsicDeTurckLocalSolution.terminalTime
            sol₂.toIntrinsicDeTurckLocalSolution.terminalTime),
        ∀ x : M, ∀ u v : TM x,
          metricTensor (I := I) (M := M)
            sol₁.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v =
          metricTensor (I := I) (M := M)
            sol₂.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v

theorem leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_nonempty_localSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  pkg.exists_solution

theorem leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_metric_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min sol₁.toIntrinsicDeTurckLocalSolution.terminalTime
        sol₂.toIntrinsicDeTurckLocalSolution.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      sol₁.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v =
    metricTensor (I := I) (M := M)
      sol₂.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v :=
  pkg.unique_metric sol₁ sol₂ t ht x u v

noncomputable def GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.toLeviCivitaBackground_viaPulledBack
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := by
    rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toPulledBackLeviCivitaBackground⟩
  unique_metric := by
    intro sol₁ sol₂ t ht x u v
    simpa [IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution,
      IntrinsicDeTurckSolution.toIntrinsicSolution] using
      pkg.unique_metric
        (sol₁.toIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution
          sol₁.background_isLeviCivita)
        (sol₂.toIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution
          sol₂.background_isLeviCivita)
        t ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.nonempty_pulledBackLeviCivitaBackground
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  pkg.toLeviCivitaBackground_viaPulledBack.exists_solution

theorem IntrinsicDeTurckLocalSolution.background_eq_canonicalConnection
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    {t : ℝ} {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toIntrinsicDeTurckSolution.background t σ x =
      sol.canonicalConnection hbackground t σ x := by
  letI : Bundle.RiemannianBundle TM :=
    ⟨(sol.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩
  have hLeviBackground :
      (sol.toIntrinsicDeTurckSolution.background t).IsLeviCivita :=
    hbackground t
  have hLeviCanonical :
      (sol.canonicalConnection hbackground t).IsLeviCivita := by
    show (((sol.toIntrinsicLocalSolution hbackground).toIntrinsicSolution.toSolution.connection t).IsLeviCivita)
    exact solution_isLeviCivita
      (sol := (sol.toIntrinsicLocalSolution hbackground).toIntrinsicSolution.toSolution) t
  exact
    CovariantDerivative.eq_of_isLeviCivita
      (I := I) (E := E) (M := M)
      (cov := sol.toIntrinsicDeTurckSolution.background t)
      (cov' := sol.canonicalConnection hbackground t)
      hLeviBackground hLeviCanonical hσ

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.background_eq_canonicalConnection
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x =
      sol.toIntrinsicDeTurckLocalSolution.canonicalConnection sol.background_isLeviCivita
        t σ x :=
  sol.toIntrinsicDeTurckLocalSolution.background_eq_canonicalConnection
    sol.background_isLeviCivita hσ

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.zero_velocity_iff_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0) ↔
      (∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M)
            sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v = 0) :=
  intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
    (I := I) (M := M) sol.toIntrinsicDeTurckLocalSolution sol.background_isLeviCivita

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.metricVelocity_eq_zero_iff_intrinsicRicciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime)
    (x : M) (u v : TM x) :
    sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0 ↔
      intrinsicRicciTensor (I := I) (M := M)
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v = 0 :=
  intrinsicDeTurckLocalSolution_metricVelocity_eq_zero_iff_intrinsicRicciTensor_eq_zero_of_isLeviCivita
    (I := I) (M := M) sol.toIntrinsicDeTurckLocalSolution sol.background_isLeviCivita
    ht x u v

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.metricVelocity_eq_zero_of_intrinsicRicciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime)
    {x : M} {u v : TM x}
    (hRicciZero : intrinsicRicciTensor (I := I) (M := M)
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v = 0) :
    sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0 :=
  (sol.metricVelocity_eq_zero_iff_intrinsicRicciTensor_eq_zero ht x u v).2 hRicciZero

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.metric_eq_initial_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v =
        ivp.initialMetric.inner x u v := by
  exact intrinsicDeTurckLocalSolution_metric_eq_initial_of_zero_velocity
    (I := I) (M := M) sol.toIntrinsicDeTurckLocalSolution sol.background_isLeviCivita
    hzero ht x u v

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.metric_eq_initial_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M)
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v =
        ivp.initialMetric.inner x u v := by
  exact intrinsicDeTurckLocalSolution_metric_eq_initial_of_ricciTensor_zero
    (I := I) (M := M) sol.toIntrinsicDeTurckLocalSolution sol.background_isLeviCivita
    hRicciZero ht x u v

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.background_eq_initial_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x =
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background
        ivp.initialTime σ x := by
  calc
    sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x =
        sol.toIntrinsicDeTurckLocalSolution.canonicalConnection sol.background_isLeviCivita
          t σ x :=
      sol.background_eq_canonicalConnection hσ
    _ = sol.toIntrinsicDeTurckLocalSolution.canonicalConnection sol.background_isLeviCivita
          ivp.initialTime σ x := by
      exact intrinsicDeTurckLocalSolution_connection_eq_initial_of_zero_velocity
        (I := I) (M := M) sol.toIntrinsicDeTurckLocalSolution sol.background_isLeviCivita
        hzero ht hσ
    _ = sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background
          ivp.initialTime σ x :=
      (sol.background_eq_canonicalConnection (t := ivp.initialTime) hσ).symm

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalSolution.background_eq_initial_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M)
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x =
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background
        ivp.initialTime σ x := by
  exact sol.background_eq_initial_of_zero_velocity
    ((intrinsicDeTurckLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol.toIntrinsicDeTurckLocalSolution sol.background_isLeviCivita).2
      hRicciZero) ht hσ

theorem stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_background_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background
      t σ x =
    (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background
      ivp.initialTime σ x := by
  let stat :=
    stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat
  have hzero :
      ∀ t ∈ Set.Icc ivp.initialTime stat.toIntrinsicDeTurckLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x,
          stat.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0 := by
    simpa [stat] using
      stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
        (I := I) (M := M) hRicciFlat
  simpa [stat] using
    stat.background_eq_initial_of_zero_velocity hzero ht hσ

theorem stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat_sourceBackground_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).source.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).source.toIntrinsicDeTurckSolution.background
      t σ x =
      (stationaryRicciFlatGaugeReducedLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).source.toIntrinsicDeTurckSolution.background
      ivp.initialTime σ x := by
  change
    (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x =
      (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
        (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background
        ivp.initialTime σ x
  exact stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_background_eq_initial
    (I := I) (M := M) hRicciFlat ht hσ

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pulledBackBackground_eq_canonicalConnection
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
      sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background) t σ x =
      sol.toPulledBackIntrinsicDeTurckLocalSolution.canonicalConnection
        sol.pulledBackDeTurck_background_isLeviCivita t σ x := by
  simpa [GaugeReducedIntrinsicDeTurckLocalSolution.toPulledBackLeviCivitaBackground,
    GaugeReducedIntrinsicDeTurckLocalSolution.toPulledBackIntrinsicDeTurckLocalSolution] using
    (sol.toPulledBackLeviCivitaBackground.background_eq_canonicalConnection hσ)

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness.background_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min sol₁.toIntrinsicDeTurckLocalSolution.terminalTime
        sol₂.toIntrinsicDeTurckLocalSolution.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x =
      sol₂.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x := by
  have ht₁ : t ∈ sol₁.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.timeSet :=
    sol₁.toIntrinsicDeTurckLocalSolution.interval_subset
      ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ sol₂.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.timeSet :=
    sol₂.toIntrinsicDeTurckLocalSolution.interval_subset
      ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  have hmetric : ∀ y : M, ∀ u v : TM y,
      metricTensor (I := I) (M := M)
        sol₁.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t y u v =
      metricTensor (I := I) (M := M)
        sol₂.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t y u v := by
    intro y u v
    exact pkg.unique_metric sol₁ sol₂ t ht y u v
  calc
    sol₁.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x =
        sol₁.toIntrinsicDeTurckLocalSolution.canonicalConnection sol₁.background_isLeviCivita
          t σ x :=
      sol₁.background_eq_canonicalConnection hσ
    _ = sol₂.toIntrinsicDeTurckLocalSolution.canonicalConnection sol₂.background_isLeviCivita
          t σ x := by
      exact intrinsicDeTurckLocalSolution_connection_eq_of_metric_eq
        (I := I) (M := M)
        sol₁.toIntrinsicDeTurckLocalSolution sol₂.toIntrinsicDeTurckLocalSolution
        sol₁.background_isLeviCivita sol₂.background_isLeviCivita ht₁ ht₂ hmetric hσ
    _ = sol₂.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x :=
      (sol₂.background_eq_canonicalConnection hσ).symm

theorem stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_unique_background_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.terminalTime
        sol.toIntrinsicDeTurckLocalSolution.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background
        t σ x =
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x := by
  let stat :=
    stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat
  have hzero_stat :
      ∀ t ∈ Set.Icc ivp.initialTime stat.toIntrinsicDeTurckLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x,
          stat.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metricVelocity t x u v = 0 := by
    simpa [stat] using
      stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
        (I := I) (M := M) hRicciFlat
  calc
    stat.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x =
        stat.toIntrinsicDeTurckLocalSolution.canonicalConnection stat.background_isLeviCivita
          t σ x :=
      stat.background_eq_canonicalConnection hσ
    _ = sol.toIntrinsicDeTurckLocalSolution.canonicalConnection sol.background_isLeviCivita
          t σ x := by
      exact intrinsicDeTurckLocalSolution_unique_connection_of_zero_velocity
        (I := I) (M := M)
        stat.toIntrinsicDeTurckLocalSolution sol.toIntrinsicDeTurckLocalSolution
        stat.background_isLeviCivita sol.background_isLeviCivita
        hzero_stat hzero ht hσ
    _ = sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x :=
      (sol.background_eq_canonicalConnection hσ).symm

theorem stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_unique_background_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.toIntrinsicDeTurckLocalSolution.terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M)
          sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min
        (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
          (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.terminalTime
        sol.toIntrinsicDeTurckLocalSolution.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat).toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background
        t σ x =
      sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x := by
  let stat :=
    stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat
      (I := I) (M := M) hRicciFlat
  have hRicciZero_stat :
      ∀ t ∈ Set.Icc ivp.initialTime stat.toIntrinsicDeTurckLocalSolution.terminalTime,
        ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M)
            stat.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.metric t x u v = 0 := by
    simpa [stat] using
      stationaryRicciFlatLeviCivitaBackgroundIntrinsicDeTurckLocalSolutionOfIsRicciFlat_intrinsicRicciTensor_eq_zero
        (I := I) (M := M) hRicciFlat
  calc
    stat.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x =
        stat.toIntrinsicDeTurckLocalSolution.canonicalConnection stat.background_isLeviCivita
          t σ x :=
      stat.background_eq_canonicalConnection hσ
    _ = sol.toIntrinsicDeTurckLocalSolution.canonicalConnection sol.background_isLeviCivita
          t σ x := by
      exact intrinsicDeTurckLocalSolution_unique_connection_of_ricciTensor_zero
        (I := I) (M := M)
        stat.toIntrinsicDeTurckLocalSolution sol.toIntrinsicDeTurckLocalSolution
        stat.background_isLeviCivita sol.background_isLeviCivita
        hRicciZero_stat hRicciZero ht hσ
    _ = sol.toIntrinsicDeTurckLocalSolution.toIntrinsicDeTurckSolution.background t σ x :=
      (sol.background_eq_canonicalConnection hσ).symm

theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness.pulledBackBackground_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.source.terminalTime sol₂.source.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
      sol₁.gauge.maps sol₁.source.toIntrinsicDeTurckSolution.background) t σ x =
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol₂.gauge.maps sol₂.source.toIntrinsicDeTurckSolution.background) t σ x := by
  simpa [GaugeReducedIntrinsicDeTurckLocalSolution.toPulledBackLeviCivitaBackground,
    GaugeReducedIntrinsicDeTurckLocalSolution.toPulledBackIntrinsicDeTurckLocalSolution] using
    (pkg.toLeviCivitaBackground_viaPulledBack.background_eq_on_common_interval
      sol₁.toPulledBackLeviCivitaBackground
      sol₂.toPulledBackLeviCivitaBackground ht hσ)

noncomputable def LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := by
    rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toIntrinsicLocalSolution_viaIdentityGauge⟩
  unique_metric := by
    intro sol₁ sol₂ t ht x u v
    exact pkg.unique_metric
      (sol₁.toLeviCivitaBackgroundIntrinsicDeTurckLocalSolution)
      (sol₂.toLeviCivitaBackgroundIntrinsicDeTurckLocalSolution)
      t (by
        simpa [IntrinsicLocalSolution.toLeviCivitaBackgroundIntrinsicDeTurckLocalSolution,
          ChosenIntrinsicDeTurckLocalSolution.toLeviCivitaBackground,
          IntrinsicLocalSolution.toChosenIntrinsicDeTurckLocalSolution,
          IntrinsicLocalSolution.toIntrinsicDeTurckLocalSolution,
          IntrinsicSolution.toIntrinsicDeTurckSolution] using ht)
      x u v

noncomputable def LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toIntrinsic_viaIdentityGauge.toOrdinary

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness.nonempty_localSolution_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  pkg.toOrdinary_viaIdentityGauge.exists_solution

noncomputable def LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := by
    rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toGaugeReduced_viaIdentityGauge⟩
  unique_metric := pkg.toIntrinsic_viaIdentityGauge.unique_metric

/-- The theorem-family version of the smooth Levi-Civita-background DeTurck package. -/
structure LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily where
  package :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
        (E := E) (H := H) (I := I) (M := M) ivp

noncomputable def LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsic_viaIdentityGauge
    (pkg : LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  fun ivp ↦ (pkg.package ivp).toIntrinsic_viaIdentityGauge

noncomputable def LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinary_viaIdentityGauge
    (pkg : LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  fun ivp ↦ (pkg.package ivp).toOrdinary_viaIdentityGauge

noncomputable def LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaIdentityGauge
    (pkg : LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := pkg.toIntrinsic_viaIdentityGauge

noncomputable def LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaIdentityGauge
    (pkg : LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  pkg.toIntrinsicFamily_viaIdentityGauge.toOrdinary

theorem LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily.nonempty_localSolution
    (pkg : LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  (pkg.toOrdinary_viaIdentityGauge ivp).exists_solution

noncomputable def GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily.toLeviCivitaBackground_viaPulledBack
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toLeviCivitaBackground_viaPulledBack

theorem GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily.nonempty_pulledBackLeviCivitaBackground
    (pkg : GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LeviCivitaBackgroundIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ((pkg.toLeviCivitaBackground_viaPulledBack).package ivp).exists_solution

noncomputable def IntrinsicLocalExistenceUniqueness.toLeviCivitaBackgroundIntrinsicDeTurck
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := by
    rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toLeviCivitaBackgroundIntrinsicDeTurckLocalSolution⟩
  unique_metric := by
    intro sol₁ sol₂ t ht x u v
    simpa [IntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution,
      IntrinsicDeTurckSolution.toIntrinsicSolution] using
      pkg.unique_metric
        (sol₁.toIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution
          sol₁.background_isLeviCivita)
        (sol₂.toIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution
          sol₂.background_isLeviCivita)
        t ht x u v

noncomputable def IntrinsicLocalExistenceUniqueness.toGaugeReduced_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toLeviCivitaBackgroundIntrinsicDeTurck.toGaugeReduced_viaIdentityGauge

/-- In the zero-dimensional tangent-fiber case, an arbitrary-background Ricci-DeTurck theorem
package converts to the gauge-reduced Ricci-flow theorem package through the identity gauge. -/
noncomputable def IntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaIdentityGauge_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := by
    rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toGaugeReduced_viaIdentityGauge_of_subsingleton_tangent⟩
  unique_metric := (pkg.toIntrinsic_of_subsingleton_tangent).unique_metric

/-- Empty-manifold specialization of the arbitrary-background DeTurck-to-gauge-reduced conversion. -/
noncomputable def IntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaIdentityGauge_of_isEmpty
    [IsEmpty M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp := by
  letI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  exact pkg.toGaugeReduced_viaIdentityGauge_of_subsingleton_tangent

noncomputable def IntrinsicLocalExistenceUniquenessFamily.toLeviCivitaBackgroundIntrinsicDeTurck
    (pkg : IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toLeviCivitaBackgroundIntrinsicDeTurck

noncomputable def IntrinsicLocalExistenceUniquenessFamily.toGaugeReduced_viaIdentityGauge
    (pkg : IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toGaugeReduced_viaIdentityGauge

/-- The family-level zero-dimensional conversion from arbitrary-background Ricci-DeTurck packages
to gauge-reduced Ricci-flow packages. -/
noncomputable def IntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaIdentityGauge_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toGaugeReduced_viaIdentityGauge_of_subsingleton_tangent

/-- Family-level empty-manifold conversion from arbitrary-background Ricci-DeTurck packages to
gauge-reduced Ricci-flow packages. -/
noncomputable def IntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaIdentityGauge_of_isEmpty
    [IsEmpty M]
    (pkg : IntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toGaugeReduced_viaIdentityGauge_of_isEmpty

noncomputable def LocalExistenceUniquenessFamily.toLeviCivitaBackgroundIntrinsicDeTurck
    (pkg : LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toIntrinsic.toLeviCivitaBackgroundIntrinsicDeTurck

noncomputable def LocalExistenceUniquenessFamily.toGaugeReduced_viaIdentityGauge
    (pkg : LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toIntrinsic.toGaugeReduced_viaIdentityGauge

/-- Zero-dimensional tangent-fiber version of the smooth Levi-Civita-background DeTurck theorem
package, obtained from the proved zero-dimensional intrinsic package. -/
noncomputable def leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_tangent
    [CompactSpace M] [∀ x : M, Subsingleton (TM x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_subsingleton_tangent (I := I) (M := M) ivp)
    |>.toLeviCivitaBackgroundIntrinsicDeTurck

noncomputable def leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily_of_subsingleton_tangent
    [CompactSpace M] [∀ x : M, Subsingleton (TM x)] :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_tangent
      (I := I) (M := M) ivp

noncomputable def gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_tangent
    [CompactSpace M] [∀ x : M, Subsingleton (TM x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_subsingleton_tangent (I := I) (M := M) ivp)
    |>.toGaugeReduced_viaIdentityGauge

noncomputable def gaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily_of_subsingleton_tangent
    [CompactSpace M] [∀ x : M, Subsingleton (TM x)] :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_tangent
      (I := I) (M := M) ivp

/-- Empty-compact-manifold version of the smooth Levi-Civita-background DeTurck theorem package,
obtained from the already proved intrinsic empty-manifold package. -/
noncomputable def leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_isEmpty
    [CompactSpace M] [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_isEmpty (I := I) (M := M) ivp)
    |>.toLeviCivitaBackgroundIntrinsicDeTurck

noncomputable def leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily_of_isEmpty
    [CompactSpace M] [IsEmpty M] :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    leviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness_of_isEmpty
      (I := I) (M := M) ivp

noncomputable def gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_isEmpty
    [CompactSpace M] [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_isEmpty (I := I) (M := M) ivp)
    |>.toGaugeReduced_viaIdentityGauge

noncomputable def gaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily_of_isEmpty
    [CompactSpace M] [IsEmpty M] :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    gaugeReducedIntrinsicDeTurckLocalExistenceUniqueness_of_isEmpty (I := I) (M := M) ivp

noncomputable def ChosenIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_of_pullbackBackgroundEquation
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {g' : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    (hinner : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g' t).inner x u v =
        (sol.1.toIntrinsicDeTurckSolution.metric t).inner ((gauge.maps t) x)
          (((gauge.maps t).pushforwardTangent x) u)
          (((gauge.maps t).pushforwardTangent x) v))
    (hpull : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.1.toIntrinsicDeTurckSolution.background t) 1)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M) g' gdot
      sol.1.toIntrinsicDeTurckSolution.timeSet)
    (heq : ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
      SatisfiesEquationAt (I := I) (M := M) g'
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.1.toIntrinsicDeTurckSolution.background) hpull gdot t) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  gauge.toIntrinsicLocalSolution_of_pullbackBackgroundEquation sol.1 hinner
    (usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2)
    hpull hderiv heq

theorem ChosenIntrinsicDeTurckLocalSolution.background_contMDiff
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.1.toIntrinsicDeTurckSolution.background t) 1 := by
  intro t
  rw [sol.2]
  exact CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
    (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution.metric t

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pullbackChosenBackgroundRicciCurvature_eq_trace_conj
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol.source)
    (t : ℝ) (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      sol.pullbackBackground_contMDiff t;
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
      sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v =
      LinearMap.trace ℝ (TM ((sol.gauge.maps t) x))
        ((((sol.gauge.maps t).tangentMap x).toLinearEquiv).conj
          ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciEndomorphism x u v)) := by
  let src : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
    ⟨sol.source, hchosen⟩
  exact sol.pullbackBackgroundRicciCurvature_eq_trace_conj src.background_contMDiff t x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_eq_neg_two_chosenBackgroundRicciCurvature_add_deTurckCorrection
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol.source)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      ChosenIntrinsicDeTurckLocalSolution.background_contMDiff
        (I := I) (M := M)
        (⟨sol.source, hchosen⟩ :
          ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) t;
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v +
      intrinsicDeTurckCorrection (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t x u v := by
  let src : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
    ⟨sol.source, hchosen⟩
  exact sol.source_velocity_eq_neg_two_backgroundRicciCurvature_add_deTurckCorrection
    src.background_contMDiff ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_eq_neg_two_chosenBackgroundRicciCurvature_add_deTurckCorrection_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol.source)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      ChosenIntrinsicDeTurckLocalSolution.background_contMDiff
        (I := I) (M := M)
        (⟨sol.source, hchosen⟩ :
          ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) t;
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v +
      intrinsicDeTurckCorrection (I := I) (M := M)
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background t x u v :=
  sol.source_velocity_eq_neg_two_chosenBackgroundRicciCurvature_add_deTurckCorrection
    hchosen (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_sub_deTurckCorrection_eq_neg_two_chosenBackgroundRicciCurvature
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol.source)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      ChosenIntrinsicDeTurckLocalSolution.background_contMDiff
        (I := I) (M := M)
        (⟨sol.source, hchosen⟩ :
          ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) t;
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v -
        intrinsicDeTurckCorrection (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
          sol.source.toIntrinsicDeTurckSolution.background t x u v =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v := by
  let src : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
    ⟨sol.source, hchosen⟩
  exact sol.source_velocity_sub_deTurckCorrection_eq_neg_two_backgroundRicciCurvature
    src.background_contMDiff ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_sub_deTurckCorrection_eq_neg_two_chosenBackgroundRicciCurvature_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol.source)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      ChosenIntrinsicDeTurckLocalSolution.background_contMDiff
        (I := I) (M := M)
        (⟨sol.source, hchosen⟩ :
          ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) t;
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t x u v -
        intrinsicDeTurckCorrection (I := I) (M := M)
          sol.source.toIntrinsicDeTurckSolution.metric
          sol.source.toIntrinsicDeTurckSolution.background t x u v =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature x u v :=
  sol.source_velocity_sub_deTurckCorrection_eq_neg_two_chosenBackgroundRicciCurvature
    hchosen (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_at_gauge_sub_transformed_pullbackSourceDeTurckCorrection_eq_neg_two_chosenBackgroundRicciCurvature
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol.source)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      ChosenIntrinsicDeTurckLocalSolution.background_contMDiff
        (I := I) (M := M)
        (⟨sol.source, hchosen⟩ :
          ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) t;
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t ((sol.gauge.maps t) x)
        ((sol.gauge.maps t).pushforwardTangent x u)
        ((sol.gauge.maps t).pushforwardTangent x v) -
      ((sol.transformedMetric t).inner x
          ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.source.toIntrinsicDeTurckSolution.metric) t)
            (sol.pulledBackSourceDeTurckVectorField t) x u) v +
        (sol.transformedMetric t).inner x u
          ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.source.toIntrinsicDeTurckSolution.metric) t)
            (sol.pulledBackSourceDeTurckVectorField t) x v)) =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x u)
          ((sol.gauge.maps t).pushforwardTangent x v) := by
  let src : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
    ⟨sol.source, hchosen⟩
  exact
    sol.source_velocity_at_gauge_sub_transformed_pullbackSourceDeTurckCorrection_eq_neg_two_backgroundRicciCurvature
      src.background_contMDiff ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.source_velocity_at_gauge_sub_transformed_pullbackSourceDeTurckCorrection_eq_neg_two_chosenBackgroundRicciCurvature_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol.source)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      ChosenIntrinsicDeTurckLocalSolution.background_contMDiff
        (I := I) (M := M)
        (⟨sol.source, hchosen⟩ :
          ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) t;
    sol.source.toIntrinsicDeTurckSolution.metricVelocity t ((sol.gauge.maps t) x)
        ((sol.gauge.maps t).pushforwardTangent x u)
        ((sol.gauge.maps t).pushforwardTangent x v) -
      ((sol.transformedMetric t).inner x
          ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.source.toIntrinsicDeTurckSolution.metric) t)
            (sol.pulledBackSourceDeTurckVectorField t) x u) v +
        (sol.transformedMetric t).inner x u
          ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps
              (chosenLeviCivitaFamily (I := I) (M := M)
                sol.source.toIntrinsicDeTurckSolution.metric) t)
            (sol.pulledBackSourceDeTurckVectorField t) x v)) =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x u)
          ((sol.gauge.maps t).pushforwardTangent x v) :=
  sol.source_velocity_at_gauge_sub_transformed_pullbackSourceDeTurckCorrection_eq_neg_two_chosenBackgroundRicciCurvature
    hchosen (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gaugeCorrectedSourceVelocity_eq_neg_two_chosenBackgroundRicciCurvature
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol.source)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      ChosenIntrinsicDeTurckLocalSolution.background_contMDiff
        (I := I) (M := M)
        (⟨sol.source, hchosen⟩ :
          ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) t;
    sol.gaugeCorrectedSourceVelocity t x u v =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x u)
          ((sol.gauge.maps t).pushforwardTangent x v) := by
  let src : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
    ⟨sol.source, hchosen⟩
  exact sol.gaugeCorrectedSourceVelocity_eq_neg_two_backgroundRicciCurvature
    src.background_contMDiff ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.gaugeCorrectedSourceVelocity_eq_neg_two_chosenBackgroundRicciCurvature_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol.source)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM :=
      ⟨(sol.source.toIntrinsicDeTurckSolution.metric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      ChosenIntrinsicDeTurckLocalSolution.background_contMDiff
        (I := I) (M := M)
        (⟨sol.source, hchosen⟩ :
          ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) t;
    sol.gaugeCorrectedSourceVelocity t x u v =
      (-2 : ℝ) *
        (sol.source.toIntrinsicDeTurckSolution.background t).ricciCurvature
          ((sol.gauge.maps t) x)
          ((sol.gauge.maps t).pushforwardTangent x u)
          ((sol.gauge.maps t).pushforwardTangent x v) :=
  sol.gaugeCorrectedSourceVelocity_eq_neg_two_chosenBackgroundRicciCurvature
    hchosen (sol.localInterval_subset_timeSet ht) x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_neg_two_trace_conj_pullbackChosenBackgroundRicciEndomorphism
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol.source)
    {t : ℝ} (ht : t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      sol.pullbackBackground_contMDiff t;
    sol.transformedVelocity t x u v =
      (-2 : ℝ) *
        LinearMap.trace ℝ (TM ((sol.gauge.maps t) x))
          ((((sol.gauge.maps t).tangentMap x).toLinearEquiv).conj
            ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciEndomorphism x u v)) := by
  let src : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
    ⟨sol.source, hchosen⟩
  exact sol.transformed_velocity_eq_neg_two_trace_conj_pullbackBackgroundRicciEndomorphism
    src.background_contMDiff ht x u v

theorem GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_neg_two_trace_conj_pullbackChosenBackgroundRicciEndomorphism_on_localInterval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol.source)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.source.terminalTime)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨(sol.transformedMetric t).toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
      sol.pullbackBackground_contMDiff t;
    sol.transformedVelocity t x u v =
      (-2 : ℝ) *
        LinearMap.trace ℝ (TM ((sol.gauge.maps t) x))
          ((((sol.gauge.maps t).tangentMap x).toLinearEquiv).conj
            ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
              sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciEndomorphism x u v)) :=
  sol.transformed_velocity_eq_neg_two_trace_conj_pullbackChosenBackgroundRicciEndomorphism
    hchosen (sol.localInterval_subset_timeSet ht) x u v

noncomputable def ChosenIntrinsicDeTurckLocalSolution.identityDiffeomorphGaugeOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  identityDiffeomorphGaugeOn_of_isLeviCivita
    (I := I) (M := M)
    sol.1.toIntrinsicDeTurckSolution.metric
    sol.1.toIntrinsicDeTurckSolution.background
    sol.1.toIntrinsicDeTurckSolution.timeSet
    ivp.initialTime
    (usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2)

theorem ChosenIntrinsicDeTurckLocalSolution.identityDiffeomorphGaugeOn_inner
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (u v : TM x) :
    (sol.1.toIntrinsicDeTurckSolution.metric t).inner x u v =
      (sol.1.toIntrinsicDeTurckSolution.metric t).inner
        ((sol.identityDiffeomorphGaugeOn.maps t) x)
        (((sol.identityDiffeomorphGaugeOn.maps t).pushforwardTangent x) u)
        (((sol.identityDiffeomorphGaugeOn.maps t).pushforwardTangent x) v) := by
  have hΦ : (SmoothSelfDiffeomorph2Family.id (I := I) (M := M)).AnchoredAt t :=
    SmoothSelfDiffeomorph2Family.id_anchoredAt (I := I) (M := M) t
  change (sol.1.toIntrinsicDeTurckSolution.metric t).inner x u v =
      (sol.1.toIntrinsicDeTurckSolution.metric t).inner
        (((SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) t) x)
        ((((SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) t).pushforwardTangent x) u)
        ((((SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) t).pushforwardTangent x) v)
  rw [
    SmoothSelfDiffeomorph2Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) hΦ x u,
    SmoothSelfDiffeomorph2Family.AnchoredAt.pushforwardTangent
      (Φ := SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) hΦ x v,
    SmoothSelfDiffeomorph2Family.AnchoredAt.apply
      (Φ := SmoothSelfDiffeomorph2Family.id (I := I) (M := M)) hΦ x]

theorem ChosenIntrinsicDeTurckLocalSolution.identityDiffeomorphGaugeOn_pullbackBackground_contMDiff
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.identityDiffeomorphGaugeOn.maps
          sol.1.toIntrinsicDeTurckSolution.background t) 1 := by
  intro t
  have hconn :
      SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        sol.identityDiffeomorphGaugeOn.maps
        sol.1.toIntrinsicDeTurckSolution.background t =
      sol.1.toIntrinsicDeTurckSolution.background t := by
    change SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
        (SmoothSelfDiffeomorph2Family.id (I := I) (M := M))
        sol.1.toIntrinsicDeTurckSolution.background t =
      sol.1.toIntrinsicDeTurckSolution.background t
    exact SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_eq_at_anchored_time
      (I := I) (M := M) (Φ := SmoothSelfDiffeomorph2Family.id (I := I) (M := M))
      sol.1.toIntrinsicDeTurckSolution.background
      (SmoothSelfDiffeomorph2Family.id_anchoredAt (I := I) (M := M) t)
  rw [hconn]
  exact sol.background_contMDiff t

noncomputable def ChosenIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.toIntrinsicLocalSolution_of_pullbackBackgroundEquation
    sol.identityDiffeomorphGaugeOn
    (fun t x u v ↦ sol.identityDiffeomorphGaugeOn_inner t x u v)
    sol.identityDiffeomorphGaugeOn_pullbackBackground_contMDiff
    (intrinsicDeTurckSolution_hasTimeDerivativeOn
      (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution)
    (by
      intro t ht
      have hLevi :
          CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
            (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background :=
        usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2
      have hIntrinsicDeTurck :
          SatisfiesIntrinsicDeTurckEquationAt (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.metricVelocity
            sol.1.toIntrinsicDeTurckSolution.background t :=
        intrinsicDeTurckSolution_equation
          (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution ht
      have hIntrinsic :
          SatisfiesIntrinsicEquationAt (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.metricVelocity t :=
        (satisfiesIntrinsicDeTurckEquationAt_iff_of_isLeviCivita
          (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.metricVelocity
          sol.1.toIntrinsicDeTurckSolution.background t hLevi).1 hIntrinsicDeTurck
      have hBackgroundEquation :
          SatisfiesEquationAt (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background
            sol.background_contMDiff
            sol.1.toIntrinsicDeTurckSolution.metricVelocity t :=
        (satisfiesIntrinsicEquationAt_iff_of_isLeviCivita
          (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.background_contMDiff
          sol.1.toIntrinsicDeTurckSolution.metricVelocity t hLevi).1 hIntrinsic
      have hconn :
          SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.identityDiffeomorphGaugeOn.maps
            sol.1.toIntrinsicDeTurckSolution.background t =
          sol.1.toIntrinsicDeTurckSolution.background t := by
        change SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            (SmoothSelfDiffeomorph2Family.id (I := I) (M := M))
            sol.1.toIntrinsicDeTurckSolution.background t =
          sol.1.toIntrinsicDeTurckSolution.background t
        exact SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_eq_at_anchored_time
          (I := I) (M := M)
          (Φ := SmoothSelfDiffeomorph2Family.id (I := I) (M := M))
          sol.1.toIntrinsicDeTurckSolution.background
          (SmoothSelfDiffeomorph2Family.id_anchoredAt (I := I) (M := M) t)
      have hconn' :
          (sol.identityDiffeomorphGaugeOn.maps t).pullbackCovariantDerivative
            (sol.1.toIntrinsicDeTurckSolution.background t) =
          sol.1.toIntrinsicDeTurckSolution.background t := by
        simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using hconn
      intro x u v
      simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply, hconn'] using
        hBackgroundEquation x u v)

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge_terminalTime
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toIntrinsicLocalSolution_viaIdentityGauge.terminalTime = sol.1.terminalTime := by
  rfl

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge_metric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toIntrinsicLocalSolution_viaIdentityGauge.toIntrinsicSolution.metric =
      sol.1.toIntrinsicDeTurckSolution.metric := by
  rfl

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.toIntrinsicLocalSolution_viaIdentityGauge_metricVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toIntrinsicLocalSolution_viaIdentityGauge.toIntrinsicSolution.metricVelocity =
      sol.1.toIntrinsicDeTurckSolution.metricVelocity := by
  rfl

theorem ChosenIntrinsicDeTurckLocalExistenceUniqueness.nonempty_gaugeReduced_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) := by
  rcases pkg.exists_solution with ⟨sol⟩
  exact ⟨sol.toGaugeReduced_viaIdentityGauge⟩

theorem ChosenIntrinsicDeTurckLocalExistenceUniqueness.nonempty_intrinsicLocalSolution_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) := by
  rcases pkg.exists_solution with ⟨sol⟩
  exact ⟨sol.toIntrinsicLocalSolution_viaIdentityGauge⟩

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := pkg.nonempty_intrinsicLocalSolution_viaIdentityGauge
  unique_metric := (pkg.toIntrinsic).unique_metric

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toLeviCivitaBackground_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LeviCivitaBackgroundIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toIntrinsic_viaIdentityGauge.toLeviCivitaBackgroundIntrinsicDeTurck

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaIdentityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toLeviCivitaBackground_viaIdentityGauge.toGaugeReduced_viaIdentityGauge

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaIdentityGauge
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toGaugeReduced_viaIdentityGauge

noncomputable def ChosenIntrinsicDeTurckLocalSolution.toGaugeReduced_viaDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfLeviCivita
    sol.1 gauge3 (usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2) hderiv

noncomputable def ChosenIntrinsicDeTurckLocalSolution.toGaugeReduced_viaDiffeomorph3GaugeInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x,
        HasDerivAt
          (fun τ ↦
            (sol.1.toIntrinsicDeTurckSolution.metric τ).inner ((gauge3.maps τ) x)
              ((gauge3.maps τ).pushforwardTangent x u)
              ((gauge3.maps τ).pushforwardTangent x v))
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v) t) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  GaugeReducedIntrinsicDeTurckLocalSolution.ofDiffeomorph3GaugeCorrectedVelocityOfLeviCivitaInnerDerivative
    sol.1 gauge3 (usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2) hderiv

theorem ChosenIntrinsicDeTurckLocalExistenceUniqueness.nonempty_gaugeReduced_viaDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((gauge3 sol).maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    Nonempty (GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) := by
  rcases pkg.exists_solution with ⟨sol⟩
  exact ⟨sol.toGaugeReduced_viaDiffeomorph3Gauge (gauge3 sol) (hderiv sol)⟩

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_ofDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := ⟨sol.toGaugeReduced_viaDiffeomorph3Gauge gauge3 hderiv⟩
  unique_metric := pkg.toIntrinsic_viaIdentityGauge.unique_metric

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((gauge3 sol).maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := pkg.nonempty_gaugeReduced_viaDiffeomorph3Gauge gauge3 hderiv
  unique_metric := pkg.toIntrinsic_viaIdentityGauge.unique_metric

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((gauge3 sol).maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReduced_viaDiffeomorph3Gauge gauge3 hderiv).toIntrinsic

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((gauge3 sol).maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3Gauge gauge3 hderiv).toOrdinary

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaDiffeomorph3Gauge
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (gauge3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((gauge3 ivp sol).maps).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toGaugeReduced_viaDiffeomorph3Gauge (gauge3 ivp) (hderiv ivp)

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3Gauge
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (gauge3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((gauge3 ivp sol).maps).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReduced_viaDiffeomorph3Gauge gauge3 hderiv).toIntrinsicFamily

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3Gauge
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (gauge3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((gauge3 ivp sol).maps).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3Gauge gauge3 hderiv).toOrdinary

theorem ChosenIntrinsicDeTurckLocalExistenceUniqueness.nonempty_gaugeReduced_viaDiffeomorph3GaugeInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TM x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner (((gauge3 sol).maps τ) x)
                (((gauge3 sol).maps τ).pushforwardTangent x u)
                (((gauge3 sol).maps τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (gauge3 sol) t x u v) t) :
    Nonempty (GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) := by
  rcases pkg.exists_solution with ⟨sol⟩
  exact ⟨sol.toGaugeReduced_viaDiffeomorph3GaugeInnerDerivative (gauge3 sol) (hderiv sol)⟩

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_ofDiffeomorph3GaugeInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x,
        HasDerivAt
          (fun τ ↦
            (sol.1.toIntrinsicDeTurckSolution.metric τ).inner ((gauge3.maps τ) x)
              ((gauge3.maps τ).pushforwardTangent x u)
              ((gauge3.maps τ).pushforwardTangent x v))
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v) t) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := ⟨sol.toGaugeReduced_viaDiffeomorph3GaugeInnerDerivative gauge3 hderiv⟩
  unique_metric := pkg.toIntrinsic_viaIdentityGauge.unique_metric

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaDiffeomorph3GaugeInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TM x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner (((gauge3 sol).maps τ) x)
                (((gauge3 sol).maps τ).pushforwardTangent x u)
                (((gauge3 sol).maps τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (gauge3 sol) t x u v) t) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := pkg.nonempty_gaugeReduced_viaDiffeomorph3GaugeInnerDerivative gauge3 hderiv
  unique_metric := pkg.toIntrinsic_viaIdentityGauge.unique_metric

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3GaugeInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TM x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner (((gauge3 sol).maps τ) x)
                (((gauge3 sol).maps τ).pushforwardTangent x u)
                (((gauge3 sol).maps τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (gauge3 sol) t x u v) t) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReduced_viaDiffeomorph3GaugeInnerDerivative gauge3 hderiv).toIntrinsic

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3GaugeInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TM x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner (((gauge3 sol).maps τ) x)
                (((gauge3 sol).maps τ).pushforwardTangent x u)
                (((gauge3 sol).maps τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (gauge3 sol) t x u v) t) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3GaugeInnerDerivative gauge3 hderiv).toOrdinary

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaDiffeomorph3GaugeInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (gauge3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TM x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((gauge3 ivp sol).maps τ) x)
                  (((gauge3 ivp sol).maps τ).pushforwardTangent x u)
                  (((gauge3 ivp sol).maps τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (gauge3 ivp sol) t x u v) t) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toGaugeReduced_viaDiffeomorph3GaugeInnerDerivative
      (gauge3 ivp) (hderiv ivp)

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (gauge3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TM x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((gauge3 ivp sol).maps τ) x)
                  (((gauge3 ivp sol).maps τ).pushforwardTangent x u)
                  (((gauge3 ivp sol).maps τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (gauge3 ivp sol) t x u v) t) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReduced_viaDiffeomorph3GaugeInnerDerivative gauge3 hderiv).toIntrinsicFamily

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (gauge3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TM x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((gauge3 ivp sol).maps τ) x)
                  (((gauge3 ivp sol).maps τ).pushforwardTangent x u)
                  (((gauge3 ivp sol).maps τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (gauge3 ivp sol) t x u v) t) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeInnerDerivative gauge3 hderiv).toOrdinary

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaDiffeomorph3GaugeFlowInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflow : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SatisfiesGaugeFlowOn (I := I) (M := M)
        (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TM x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner (((maps3 sol) τ) x)
                (((maps3 sol) τ).pushforwardTangent x u)
                (((maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                (I := I) (M := M)
                (g := sol.1.toIntrinsicDeTurckSolution.metric)
                (background := sol.1.toIntrinsicDeTurckSolution.background)
                (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                (t₀ := ivp.initialTime)
                (maps3 sol) (anchored sol) (hflow sol)) t x u v) t) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReduced_viaDiffeomorph3GaugeInnerDerivative
    (fun sol ↦
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
        (I := I) (M := M)
        (g := sol.1.toIntrinsicDeTurckSolution.metric)
        (background := sol.1.toIntrinsicDeTurckSolution.background)
        (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
        (t₀ := ivp.initialTime)
        (maps3 sol) (anchored sol) (hflow sol))
    hderiv

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3GaugeFlowInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflow : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SatisfiesGaugeFlowOn (I := I) (M := M)
        (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TM x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner (((maps3 sol) τ) x)
                (((maps3 sol) τ).pushforwardTangent x u)
                (((maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                (I := I) (M := M)
                (g := sol.1.toIntrinsicDeTurckSolution.metric)
                (background := sol.1.toIntrinsicDeTurckSolution.background)
                (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                (t₀ := ivp.initialTime)
                (maps3 sol) (anchored sol) (hflow sol)) t x u v) t) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReduced_viaDiffeomorph3GaugeFlowInnerDerivative
    maps3 anchored hflow hderiv).toIntrinsic

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3GaugeFlowInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflow : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SatisfiesGaugeFlowOn (I := I) (M := M)
        (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TM x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner (((maps3 sol) τ) x)
                (((maps3 sol) τ).pushforwardTangent x u)
                (((maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                (I := I) (M := M)
                (g := sol.1.toIntrinsicDeTurckSolution.metric)
                (background := sol.1.toIntrinsicDeTurckSolution.background)
                (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                (t₀ := ivp.initialTime)
                (maps3 sol) (anchored sol) (hflow sol)) t x u v) t) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3GaugeFlowInnerDerivative
    maps3 anchored hflow hderiv).toOrdinary

/-- Direct gauge-reduced route from primitive pointwise `C³` gauge-flow derivative data plus
scalar inner-product derivative facts. This packages the primitive ODE data into the existing
raw-flow scalar-derivative route without first exposing only the scalar package. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))))
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TM x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner (((maps3 sol) τ) x)
                (((maps3 sol) τ).pushforwardTangent x u)
                (((maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                (I := I) (M := M)
                (g := sol.1.toIntrinsicDeTurckSolution.metric)
                (background := sol.1.toIntrinsicDeTurckSolution.background)
                (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                (t₀ := ivp.initialTime)
                (maps3 sol) (anchored sol) (hflowDeriv sol)) t x u v) t) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReduced_viaDiffeomorph3GaugeFlowInnerDerivative maps3 anchored
    (fun sol ↦
      SatisfiesGaugeFlowOn.of_hasMFDerivWithinAt
        (I := I) (M := M)
        (Φ := (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
        (fun t ht x ↦ by
          change HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)))
          exact hflowDeriv sol t ht x))
    hderiv

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))))
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TM x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner (((maps3 sol) τ) x)
                (((maps3 sol) τ).pushforwardTangent x u)
                (((maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                (I := I) (M := M)
                (g := sol.1.toIntrinsicDeTurckSolution.metric)
                (background := sol.1.toIntrinsicDeTurckSolution.background)
                (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                (t₀ := ivp.initialTime)
                (maps3 sol) (anchored sol) (hflowDeriv sol)) t x u v) t) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReduced_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    maps3 anchored hflowDeriv hderiv).toIntrinsic

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))))
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TM x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner (((maps3 sol) τ) x)
                (((maps3 sol) τ).pushforwardTangent x u)
                (((maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                (I := I) (M := M)
                (g := sol.1.toIntrinsicDeTurckSolution.metric)
                (background := sol.1.toIntrinsicDeTurckSolution.background)
                (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                (t₀ := ivp.initialTime)
                (maps3 sol) (anchored sol) (hflowDeriv sol)) t x u v) t) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    maps3 anchored hflowDeriv hderiv).toOrdinary

/-- Raw gauge-flow reduction using a time-derivative statement for the pulled-back metric instead
of scalar inner-product derivative facts. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3GaugeFlowTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflow : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SatisfiesGaugeFlowOn (I := I) (M := M)
        (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
            (I := I) (M := M)
            (g := sol.1.toIntrinsicDeTurckSolution.metric)
            (background := sol.1.toIntrinsicDeTurckSolution.background)
            (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
            (t₀ := ivp.initialTime)
            (maps3 sol) (anchored sol) (hflow sol)))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReduced_viaDiffeomorph3Gauge
    (fun sol ↦
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
        (I := I) (M := M)
        (g := sol.1.toIntrinsicDeTurckSolution.metric)
        (background := sol.1.toIntrinsicDeTurckSolution.background)
        (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
        (t₀ := ivp.initialTime)
        (maps3 sol) (anchored sol) (hflow sol))
    hpullDerivative).toIntrinsic

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3GaugeFlowTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflow : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SatisfiesGaugeFlowOn (I := I) (M := M)
        (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
            (I := I) (M := M)
            (g := sol.1.toIntrinsicDeTurckSolution.metric)
            (background := sol.1.toIntrinsicDeTurckSolution.background)
            (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
            (t₀ := ivp.initialTime)
            (maps3 sol) (anchored sol) (hflow sol)))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3GaugeFlowTimeDerivative
    maps3 anchored hflow hpullDerivative).toOrdinary

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaDiffeomorph3GaugeFlowInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TM x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)) t x u v) t) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toGaugeReduced_viaDiffeomorph3GaugeFlowInnerDerivative
      (maps3 ivp) (anchored ivp) (hflow ivp) (hderiv ivp)

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TM x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)) t x u v) t) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReduced_viaDiffeomorph3GaugeFlowInnerDerivative
    maps3 anchored hflow hderiv).toIntrinsicFamily

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeFlowInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TM x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)) t x u v) t) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeFlowInnerDerivative
    maps3 anchored hflow hderiv).toOrdinary

/-- Family-level direct gauge-reduced route from primitive pointwise `C³` gauge-flow derivative data
plus scalar inner-product derivative facts. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TM x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)) t x u v) t) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toGaugeReduced_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
      (maps3 ivp) (anchored ivp) (hflowDeriv ivp) (hderiv ivp)

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TM x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)) t x u v) t) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReduced_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    maps3 anchored hflowDeriv hderiv).toIntrinsicFamily

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TM x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)) t x u v) t) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    maps3 anchored hflowDeriv hderiv).toOrdinary

/-- Family-level raw gauge-flow reduction using a time-derivative statement for each pulled-back
metric instead of scalar inner-product derivative facts. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReduced_viaDiffeomorph3Gauge
    (fun ivp sol ↦
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
        (I := I) (M := M)
        (g := sol.1.toIntrinsicDeTurckSolution.metric)
        (background := sol.1.toIntrinsicDeTurckSolution.background)
        (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
        (t₀ := ivp.initialTime)
        (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol))
    hpullDerivative).toIntrinsicFamily

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeFlowTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeFlowTimeDerivative
    maps3 anchored hflow hpullDerivative).toOrdinary

/-- A chosen-background Ricci-DeTurck local solution equipped with enough non-identity `C³`
gauge data to become a gauge-reduced Ricci-flow local solution. -/
structure GaugeReducibleChosenIntrinsicDeTurckLocalSolution
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  source : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp
  gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
    source.1.toIntrinsicDeTurckSolution.metric source.1.toIntrinsicDeTurckSolution.background
    source.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime
  hasTimeDerivative : HasTimeDerivativeOn (I := I) (M := M)
    (gauge3.maps.pullbackMetricFamily source.1.toIntrinsicDeTurckSolution.metric)
    (source.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
    source.1.toIntrinsicDeTurckSolution.timeSet

noncomputable def ChosenIntrinsicDeTurckLocalSolution.toGaugeReducible_viaDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp where
  source := sol
  gauge3 := gauge3
  hasTimeDerivative := hderiv

noncomputable def GaugeReducibleChosenIntrinsicDeTurckLocalSolution.toGaugeReduced
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducibleChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.source.toGaugeReduced_viaDiffeomorph3Gauge sol.gauge3 sol.hasTimeDerivative

/-- Scalar-derivative version of `GaugeReducibleChosenIntrinsicDeTurckLocalSolution`, matching the
most explicit current analytic boundary for the gauge-pulled metric. -/
structure InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  source : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp
  gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
    source.1.toIntrinsicDeTurckSolution.metric source.1.toIntrinsicDeTurckSolution.background
    source.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime
  inner_hasDerivAt : ∀ ⦃t : ℝ⦄, t ∈ source.1.toIntrinsicDeTurckSolution.timeSet →
    ∀ x : M, ∀ u v : TM x,
      HasDerivAt
        (fun τ ↦
          (source.1.toIntrinsicDeTurckSolution.metric τ).inner ((gauge3.maps τ) x)
            ((gauge3.maps τ).pushforwardTangent x u)
            ((gauge3.maps τ).pushforwardTangent x v))
        (source.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v) t

noncomputable def GaugeReducibleChosenIntrinsicDeTurckLocalSolution.toInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducibleChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp where
  source := sol.source
  gauge3 := sol.gauge3
  inner_hasDerivAt := by
    intro t ht x u v
    simpa [metricTensor, SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner] using
      sol.hasTimeDerivative ht x u v

noncomputable def ChosenIntrinsicDeTurckLocalSolution.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (sol.toGaugeReducible_viaDiffeomorph3Gauge gauge3 hderiv).toInnerDerivative

noncomputable def InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution.toGaugeReducible
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducibleChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  source := sol.source
  gauge3 := sol.gauge3
  hasTimeDerivative :=
    (sol.source.1).gaugeCorrectedPullbackMetric_hasTimeDerivativeOn_of_inner_hasDerivAt
      sol.gauge3 sol.inner_hasDerivAt

noncomputable def InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution.toGaugeReduced
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.toGaugeReducible.toGaugeReduced

/-- A chosen-background DeTurck local solution satisfies the explicit scalar-derivative
gauge-reducibility interface via the identity `C³` gauge. -/
noncomputable def ChosenIntrinsicDeTurckLocalSolution.toInnerDerivativeGaugeReducible_viaIdentityDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp where
  source := sol
  gauge3 :=
    sol.1.identityDiffeomorph3GaugeOn
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2)
  inner_hasDerivAt :=
    sol.1.identityDiffeomorph3Gauge_inner_hasDerivAt
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2)

noncomputable def ChosenIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  sol.toInnerDerivativeGaugeReducible_viaIdentityDiffeomorph3Gauge.toGaugeReduced

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.toInnerDerivativeGaugeReducible_viaIdentityDiffeomorph3Gauge_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toInnerDerivativeGaugeReducible_viaIdentityDiffeomorph3Gauge.source = sol := by
  rfl

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge_source
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge.source = sol.1 := by
  rfl

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge_transformedMetric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge.transformedMetric =
      sol.1.toIntrinsicDeTurckSolution.metric := by
  change (SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
      sol.1.toIntrinsicDeTurckSolution.metric =
      sol.1.toIntrinsicDeTurckSolution.metric
  simp

@[simp] theorem ChosenIntrinsicDeTurckLocalSolution.toGaugeReduced_viaIdentityDiffeomorph3Gauge_transformedVelocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge.transformedVelocity =
      sol.1.toIntrinsicDeTurckSolution.metricVelocity := by
  let hbackground := usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2
  change sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
      (sol.1.identityDiffeomorph3GaugeOn hbackground) =
      sol.1.toIntrinsicDeTurckSolution.metricVelocity
  exact sol.1.gaugeCorrectedPullbackVelocity_identityDiffeomorph3Gauge_eq_metricVelocity hbackground

theorem ChosenIntrinsicDeTurckLocalSolution.identityDiffeomorph3Gauge_transformedMetric_eq_identityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge.transformedMetric =
      sol.toGaugeReduced_viaIdentityGauge.transformedMetric := by
  simp

theorem ChosenIntrinsicDeTurckLocalSolution.identityDiffeomorph3Gauge_transformedVelocity_eq_identityGauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.toGaugeReduced_viaIdentityDiffeomorph3Gauge.transformedVelocity =
      sol.toGaugeReduced_viaIdentityGauge.transformedVelocity := by
  simp

/-- A chosen-background DeTurck local solution is gauge-reducible by the identity `C³` gauge.
This closes the final gauge-reducibility boundary in the already-Levi-Civita background case; the
remaining analytic input for generic point 4 is therefore the chosen-background DeTurck theorem
package itself. -/
noncomputable def ChosenIntrinsicDeTurckLocalSolution.toGaugeReducible_viaIdentityDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducibleChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp where
  source := sol
  gauge3 :=
    sol.1.identityDiffeomorph3GaugeOn
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2)
  hasTimeDerivative := by
    let hbackground :=
      usesChosenBackground_isLeviCivita (I := I) (M := M) sol.1 sol.2
    change HasTimeDerivativeOn (I := I) (M := M)
      ((SmoothSelfDiffeomorph3Family.id (I := I) (M := M)).pullbackMetricFamily
        sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (sol.1.identityDiffeomorph3GaugeOn hbackground))
      sol.1.toIntrinsicDeTurckSolution.timeSet
    rw [SmoothSelfDiffeomorph3Family.id_pullbackMetricFamily,
      sol.1.gaugeCorrectedPullbackVelocity_identityDiffeomorph3Gauge_eq_metricVelocity hbackground]
    exact intrinsicDeTurckSolution_hasTimeDerivativeOn
      (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution

/-- The chosen-background DeTurck theorem package plus one gauge-reducible DeTurck solution.
This is enough to produce the conditional gauge-reduced Ricci-flow theorem package. -/
structure GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  chosen_package :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp
  exists_gaugeReducible :
    Nonempty (GaugeReducibleChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaIdentityDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  chosen_package := pkg
  exists_gaugeReducible := by
    rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toGaugeReducible_viaIdentityDiffeomorph3Gauge⟩

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_ofDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  chosen_package := pkg
  exists_gaugeReducible := ⟨sol.toGaugeReducible_viaDiffeomorph3Gauge gauge3 hderiv⟩

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((gauge3 sol).maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  chosen_package := pkg
  exists_gaugeReducible := by
    rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toGaugeReducible_viaDiffeomorph3Gauge (gauge3 sol) (hderiv sol)⟩

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaDiffeomorph3GaugeFlowTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflow : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SatisfiesGaugeFlowOn (I := I) (M := M)
        (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
            (I := I) (M := M)
            (g := sol.1.toIntrinsicDeTurckSolution.metric)
            (background := sol.1.toIntrinsicDeTurckSolution.background)
            (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
            (t₀ := ivp.initialTime)
            (maps3 sol) (anchored sol) (hflow sol)))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3Gauge
    (fun sol ↦
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
        (I := I) (M := M)
        (g := sol.1.toIntrinsicDeTurckSolution.metric)
        (background := sol.1.toIntrinsicDeTurckSolution.background)
        (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
        (t₀ := ivp.initialTime)
        (maps3 sol) (anchored sol) (hflow sol))
    hpullDerivative

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))))
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
            (I := I) (M := M)
            (g := sol.1.toIntrinsicDeTurckSolution.metric)
            (background := sol.1.toIntrinsicDeTurckSolution.background)
            (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
            (t₀ := ivp.initialTime)
            (maps3 sol) (anchored sol) (hflowDeriv sol)))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3Gauge
    (fun sol ↦
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
        (I := I) (M := M)
        (g := sol.1.toIntrinsicDeTurckSolution.metric)
        (background := sol.1.toIntrinsicDeTurckSolution.background)
        (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
        (t₀ := ivp.initialTime)
        (maps3 sol) (anchored sol) (hflowDeriv sol))
    hpullDerivative

noncomputable def GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := by
    rcases pkg.exists_gaugeReducible with ⟨sol⟩
    exact ⟨sol.toGaugeReduced⟩
  unique_metric := pkg.chosen_package.toIntrinsic_viaIdentityGauge.unique_metric

noncomputable def GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReduced.toIntrinsic

noncomputable def GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReduced.toOrdinary

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))))
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
            (I := I) (M := M)
            (g := sol.1.toIntrinsicDeTurckSolution.metric)
            (background := sol.1.toIntrinsicDeTurckSolution.background)
            (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
            (t₀ := ivp.initialTime)
            (maps3 sol) (anchored sol) (hflowDeriv sol)))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    maps3 anchored hflowDeriv hpullDerivative).toIntrinsic

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))))
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
            (I := I) (M := M)
            (g := sol.1.toIntrinsicDeTurckSolution.metric)
            (background := sol.1.toIntrinsicDeTurckSolution.background)
            (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
            (t₀ := ivp.initialTime)
            (maps3 sol) (anchored sol) (hflowDeriv sol)))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    maps3 anchored hflowDeriv hpullDerivative).toOrdinary

theorem GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness.nonempty_localSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  pkg.toOrdinary.exists_solution

theorem GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness.connection_eq_on_common_interval
    [CompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toSolution.connection t σ x = sol₂.toSolution.connection t σ x :=
  localExistenceUniqueness_connection_eq_on_common_interval
    (I := I) (M := M) (pkg := pkg.toOrdinary) sol₁ sol₂ ht hσ

/-- Scalar-derivative theorem package version of
`GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness`. -/
structure InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  chosen_package :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp
  exists_gaugeReducible :
    Nonempty (InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)

noncomputable def GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness.toInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  chosen_package := pkg.chosen_package
  exists_gaugeReducible := by
    rcases pkg.exists_gaugeReducible with ⟨sol⟩
    exact ⟨sol.toInnerDerivative⟩

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toInnerDerivativeGaugeReducible_ofDiffeomorph3GaugeTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  chosen_package := pkg
  exists_gaugeReducible :=
    ⟨sol.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeTimeDerivative gauge3 hderiv⟩

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((gauge3 sol).maps.pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  chosen_package := pkg
  exists_gaugeReducible := by
    rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeTimeDerivative
      (gauge3 sol) (hderiv sol)⟩

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflow : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SatisfiesGaugeFlowOn (I := I) (M := M)
        (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
            (I := I) (M := M)
            (g := sol.1.toIntrinsicDeTurckSolution.metric)
            (background := sol.1.toIntrinsicDeTurckSolution.background)
            (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
            (t₀ := ivp.initialTime)
            (maps3 sol) (anchored sol) (hflow sol)))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeTimeDerivative
    (fun sol ↦
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
        (I := I) (M := M)
        (g := sol.1.toIntrinsicDeTurckSolution.metric)
        (background := sol.1.toIntrinsicDeTurckSolution.background)
        (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
        (t₀ := ivp.initialTime)
        (maps3 sol) (anchored sol) (hflow sol))
    hpullDerivative

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))))
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
            (I := I) (M := M)
            (g := sol.1.toIntrinsicDeTurckSolution.metric)
            (background := sol.1.toIntrinsicDeTurckSolution.background)
            (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
            (t₀ := ivp.initialTime)
            (maps3 sol) (anchored sol) (hflowDeriv sol)))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    maps3 anchored hflowDeriv hpullDerivative).toInnerDerivative

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toInnerDerivativeGaugeReducible_ofDiffeomorph3GaugeInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
      ∀ x : M, ∀ u v : TM x,
        HasDerivAt
          (fun τ ↦
            (sol.1.toIntrinsicDeTurckSolution.metric τ).inner ((gauge3.maps τ) x)
              ((gauge3.maps τ).pushforwardTangent x u)
              ((gauge3.maps τ).pushforwardTangent x v))
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  chosen_package := pkg
  exists_gaugeReducible :=
    ⟨{
       source := sol
       gauge3 := gauge3
       inner_hasDerivAt := hderiv }⟩

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TM x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner (((gauge3 sol).maps τ) x)
                (((gauge3 sol).maps τ).pushforwardTangent x u)
                (((gauge3 sol).maps τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (gauge3 sol) t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  chosen_package := pkg
  exists_gaugeReducible := by
    rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨{
      source := sol
      gauge3 := gauge3 sol
      inner_hasDerivAt := hderiv sol }⟩

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflow : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SatisfiesGaugeFlowOn (I := I) (M := M)
        (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TM x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner (((maps3 sol) τ) x)
                (((maps3 sol) τ).pushforwardTangent x u)
                (((maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                (I := I) (M := M)
                (g := sol.1.toIntrinsicDeTurckSolution.metric)
                (background := sol.1.toIntrinsicDeTurckSolution.background)
                (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                (t₀ := ivp.initialTime)
                (maps3 sol) (anchored sol) (hflow sol)) t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeInnerDerivative
    (fun sol ↦
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
        (I := I) (M := M)
        (g := sol.1.toIntrinsicDeTurckSolution.metric)
        (background := sol.1.toIntrinsicDeTurckSolution.background)
        (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
        (t₀ := ivp.initialTime)
        (maps3 sol) (anchored sol) (hflow sol))
    hderiv

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hflowDeriv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x))))
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TM x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner (((maps3 sol) τ) x)
                (((maps3 sol) τ).pushforwardTangent x u)
                (((maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                (I := I) (M := M)
                (g := sol.1.toIntrinsicDeTurckSolution.metric)
                (background := sol.1.toIntrinsicDeTurckSolution.background)
                (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                (t₀ := ivp.initialTime)
                (maps3 sol) (anchored sol) (hflowDeriv sol)) t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowInnerDerivative
    maps3 anchored
    (fun sol ↦
      SatisfiesGaugeFlowOn.of_hasMFDerivWithinAt
        (I := I) (M := M)
        (Φ := (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily)
        (X := intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
        (fun t ht x ↦ by
          change HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)))
          exact hflowDeriv sol t ht x))
    hderiv

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toInnerDerivativeGaugeReducible_viaIdentityDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  chosen_package := pkg
  exists_gaugeReducible := by
    rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toInnerDerivativeGaugeReducible_viaIdentityDiffeomorph3Gauge⟩

noncomputable def InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp where
  chosen_package := pkg.chosen_package
  exists_gaugeReducible := by
    rcases pkg.exists_gaugeReducible with ⟨sol⟩
    exact ⟨sol.toGaugeReducible⟩

noncomputable def InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible.toGaugeReduced

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaIdentityDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toInnerDerivativeGaugeReducible_viaIdentityDiffeomorph3Gauge.toGaugeReduced

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaIdentityDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReduced_viaIdentityDiffeomorph3Gauge.toIntrinsic

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaIdentityDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toIntrinsic_viaIdentityDiffeomorph3Gauge.toOrdinary

theorem ChosenIntrinsicDeTurckLocalExistenceUniqueness.nonempty_gaugeReduced_viaIdentityDiffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  pkg.toGaugeReduced_viaIdentityDiffeomorph3Gauge.exists_solution

noncomputable def InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReduced.toOrdinary

theorem InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness.nonempty_localSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  pkg.toOrdinary.exists_solution

theorem InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness.connection_eq_on_common_interval
    [CompactSpace M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toSolution.connection t σ x = sol₂.toSolution.connection t σ x :=
  pkg.toGaugeReducible.connection_eq_on_common_interval sol₁ sol₂ ht hσ

/-- The theorem-family version of the final packaged non-identity gauge-reduction boundary. -/
structure GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily where
  package :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
        (E := E) (H := H) (I := I) (M := M) ivp

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaIdentityDiffeomorph3Gauge
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toGaugeReducible_viaIdentityDiffeomorph3Gauge

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3Gauge
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (gauge3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((gauge3 ivp sol).maps).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toGaugeReducible_viaDiffeomorph3Gauge (gauge3 ivp) (hderiv ivp)

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toGaugeReducible_viaDiffeomorph3GaugeFlowTimeDerivative
      (maps3 ivp) (anchored ivp) (hflow ivp) (hpullDerivative ivp)

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
      (maps3 ivp) (anchored ivp) (hflowDeriv ivp) (hpullDerivative ivp)

noncomputable def GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced
    (pkg : GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toGaugeReduced

noncomputable def GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinary
    (pkg : GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  fun ivp ↦ (pkg.package ivp).toOrdinary

noncomputable def GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily
    (pkg : GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReduced.toIntrinsicFamily

noncomputable def GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily
    (pkg : GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  pkg.toIntrinsicFamily.toOrdinary

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    maps3 anchored hflowDeriv hpullDerivative).toIntrinsicFamily

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    maps3 anchored hflowDeriv hpullDerivative).toOrdinary

theorem GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.nonempty_localSolution
    (pkg : GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  (pkg.toOrdinary ivp).exists_solution

theorem GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.connection_eq_on_common_interval
    [CompactSpace M]
    (pkg : GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toSolution.connection t σ x = sol₂.toSolution.connection t σ x :=
  (pkg.package ivp).connection_eq_on_common_interval sol₁ sol₂ ht hσ

/-- The theorem-family version when the time-regularity input is supplied as scalar
inner-product derivatives. -/
structure InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily where
  package :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
        (E := E) (H := H) (I := I) (M := M) ivp

noncomputable def GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivative
    (pkg : GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toInnerDerivative

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (gauge3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((gauge3 ivp sol).maps).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gauge3 ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeTimeDerivative
      (gauge3 ivp) (hderiv ivp)

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowTimeDerivative
      (maps3 ivp) (anchored ivp) (hflow ivp) (hpullDerivative ivp)

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    maps3 anchored hflowDeriv hpullDerivative).toInnerDerivative

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (gauge3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric sol.1.toIntrinsicDeTurckSolution.background
          sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TM x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((gauge3 ivp sol).maps τ) x)
                  (((gauge3 ivp sol).maps τ).pushforwardTangent x u)
                  (((gauge3 ivp sol).maps τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (gauge3 ivp sol) t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeInnerDerivative
      (gauge3 ivp) (hderiv ivp)

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TM x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflow ivp sol)) t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowInnerDerivative
      (maps3 ivp) (anchored ivp) (hflow ivp) (hderiv ivp)

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TM x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((maps3 ivp sol) τ) x)
                  (((maps3 ivp sol) τ).pushforwardTangent x u)
                  (((maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
                  (I := I) (M := M)
                  (g := sol.1.toIntrinsicDeTurckSolution.metric)
                  (background := sol.1.toIntrinsicDeTurckSolution.background)
                  (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                  (t₀ := ivp.initialTime)
                  (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)) t x u v) t) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toInnerDerivativeGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeInnerDerivative
      (maps3 ivp) (anchored ivp) (hflowDeriv ivp) (hderiv ivp)

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toInnerDerivativeGaugeReducible_viaIdentityDiffeomorph3Gauge
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toInnerDerivativeGaugeReducible_viaIdentityDiffeomorph3Gauge

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaIdentityDiffeomorph3Gauge
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (pkg.package ivp).toGaugeReduced_viaIdentityDiffeomorph3Gauge

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaIdentityDiffeomorph3Gauge
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReduced_viaIdentityDiffeomorph3Gauge.toIntrinsicFamily

noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaIdentityDiffeomorph3Gauge
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  pkg.toIntrinsicFamily_viaIdentityDiffeomorph3Gauge.toOrdinary

theorem ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.nonempty_gaugeReduced_viaIdentityDiffeomorph3Gauge
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :=
  ((pkg.toGaugeReduced_viaIdentityDiffeomorph3Gauge).package ivp).exists_solution

noncomputable def InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible
    (pkg : InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toGaugeReducible

noncomputable def InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinary
    (pkg : InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible.toOrdinary

noncomputable def InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily
    (pkg : InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible.toIntrinsicFamily

noncomputable def InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily
    (pkg : InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  pkg.toIntrinsicFamily.toOrdinary

theorem InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.nonempty_localSolution
    (pkg : InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  (pkg.toOrdinary ivp).exists_solution

theorem InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.connection_eq_on_common_interval
    [CompactSpace M]
    (pkg : InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toSolution.connection t σ x = sol₂.toSolution.connection t σ x :=
  (pkg.package ivp).connection_eq_on_common_interval sol₁ sol₂ ht hσ

theorem ChosenIntrinsicDeTurckLocalExistenceUniqueness.transformedMetric_eq_on_common_interval_of_same_gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    {g₁' g₂' : MetricFamily (I := I) (M := M)}
    (hinner₁ : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g₁' t).inner x u v =
        (sol₁.1.toIntrinsicDeTurckSolution.metric t).inner ((Φ t) x)
          (((Φ t).pushforwardTangent x) u)
          (((Φ t).pushforwardTangent x) v))
    (hinner₂ : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      (g₂' t).inner x u v =
        (sol₂.1.toIntrinsicDeTurckSolution.metric t).inner ((Φ t) x)
          (((Φ t).pushforwardTangent x) u)
          (((Φ t).pushforwardTangent x) v))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) g₁' t x u v =
      metricTensor (I := I) (M := M) g₂' t x u v := by
  calc
    metricTensor (I := I) (M := M) g₁' t x u v
      = (sol₁.1.toIntrinsicDeTurckSolution.metric t).inner ((Φ t) x)
          (((Φ t).pushforwardTangent x) u)
          (((Φ t).pushforwardTangent x) v) := hinner₁ t x u v
    _ = (sol₂.1.toIntrinsicDeTurckSolution.metric t).inner ((Φ t) x)
          (((Φ t).pushforwardTangent x) u)
          (((Φ t).pushforwardTangent x) v) :=
        pkg.unique_metric sol₁ sol₂ t ht ((Φ t) x)
          (((Φ t).pushforwardTangent x) u)
          (((Φ t).pushforwardTangent x) v)
    _ = metricTensor (I := I) (M := M) g₂' t x u v := (hinner₂ t x u v).symm

theorem IntrinsicDeTurckLocalSolution.pullbackBackgroundConnection_contMDiffCovariantDerivative_initial_of_anchored
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    (hΦ : Φ.AnchoredAt ivp.initialTime)
    (hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
        sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1 := by
  have hconn :
      ((Φ ivp.initialTime).pullbackCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime)) =
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime := by
    simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply] using
      sol.pullbackBackgroundConnection_eq_initial_of_anchored (Φ := Φ) hΦ
  simpa [SmoothSelfDiffeomorph2Family.pullbackConnectionFamily_apply, hconn] using hbackground

theorem IntrinsicDeTurckLocalSolution.pullbackBackgroundCurvatureTensor_eq_initial_of_anchored
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    (hΦ : Φ.AnchoredAt ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (x : M) (u v w : TM x) :
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime).curvatureTensor x u v w =
    (sol.toIntrinsicDeTurckSolution.background ivp.initialTime).curvatureTensor x u v w := by
  have hconn :
      SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
        sol.toIntrinsicDeTurckSolution.background ivp.initialTime =
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime :=
    sol.pullbackBackgroundConnection_eq_initial_of_anchored (Φ := Φ) hΦ
  revert hpull
  rw [hconn]
  intro hpull
  letI := hpull
  rfl

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.pullbackBackgroundConnection_contMDiffCovariantDerivative_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
        sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1 :=
  sol.pullbackBackgroundConnection_contMDiffCovariantDerivative_initial_of_anchored
    gauge.anchored hbackground

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.pullbackBackgroundCurvatureTensor_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (x : M) (u v w : TM x) :
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime).curvatureTensor x u v w =
    (sol.toIntrinsicDeTurckSolution.background ivp.initialTime).curvatureTensor x u v w := by
  exact
    sol.pullbackBackgroundCurvatureTensor_eq_initial_of_anchored
      (Φ := gauge.maps) gauge.anchored x u v w

theorem IntrinsicDeTurckLocalSolution.pullbackBackgroundRicciCurvature_eq_initial_of_anchored
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    [RiemannianBundle TM]
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    (hΦ : Φ.AnchoredAt ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (x : M) (u w : TM x) :
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w =
    (sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w := by
  have hconn :
      SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
        sol.toIntrinsicDeTurckSolution.background ivp.initialTime =
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime :=
    sol.pullbackBackgroundConnection_eq_initial_of_anchored (Φ := Φ) hΦ
  revert hpull
  rw [hconn]
  intro hpull
  letI := hpull
  rfl

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.pullbackBackgroundRicciCurvature_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    [RiemannianBundle TM]
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (x : M) (u w : TM x) :
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w =
    (sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w := by
  exact
    sol.pullbackBackgroundRicciCurvature_eq_initial_of_anchored
      (Φ := gauge.maps) gauge.anchored x u w

theorem AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.pullbackBackgroundConnection_contMDiffCovariantDerivative_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
        gauge3.maps sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1 := by
  simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily,
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toDiffeomorph2Gauge] using
    gauge3.toDiffeomorph2Gauge.pullbackBackgroundConnection_contMDiffCovariantDerivative_initial
      sol hbackground

theorem AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.pullbackBackgroundCurvatureTensor_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (x : M) (u v w : TM x) :
    (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      gauge3.maps sol.toIntrinsicDeTurckSolution.background ivp.initialTime).curvatureTensor x u v w =
    (sol.toIntrinsicDeTurckSolution.background ivp.initialTime).curvatureTensor x u v w := by
  letI hpull₂ :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.toDiffeomorph2Gauge.maps
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1 := by
    simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toDiffeomorph2Gauge] using hpull
  simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily,
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toDiffeomorph2Gauge] using
    gauge3.toDiffeomorph2Gauge.pullbackBackgroundCurvatureTensor_eq_initial sol x u v w

theorem AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.pullbackBackgroundRicciCurvature_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    [RiemannianBundle TM]
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (x : M) (u w : TM x) :
    (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      gauge3.maps sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w =
    (sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w := by
  letI hpull₂ :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.toDiffeomorph2Gauge.maps
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1 := by
    simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toDiffeomorph2Gauge] using hpull
  simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily,
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toDiffeomorph2Gauge] using
    gauge3.toDiffeomorph2Gauge.pullbackBackgroundRicciCurvature_eq_initial sol x u w

theorem IntrinsicDeTurckLocalSolution.background_isLeviCivita_initialMetric
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hbackground : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background) :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
    (sol.toIntrinsicDeTurckSolution.background ivp.initialTime).IsLeviCivita := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  exact
    (CovariantDerivative.isLeviCivita_iff_of_inner_eq
      (I := I) (E := E) (M := M)
      (cov := sol.toIntrinsicDeTurckSolution.background ivp.initialTime)
      (g := sol.toIntrinsicDeTurckSolution.metric ivp.initialTime)
      (g' := ivp.initialMetric)
      (fun y u v ↦ intrinsicDeTurckLocalSolution_metric_eq_initial
        (E := E) (H := H) (I := I) (M := M) sol y u v)).mp
      (hbackground ivp.initialTime)

theorem IntrinsicDeTurckLocalSolution.pullbackBackgroundRicciCurvature_eq_zero_initial_of_anchored
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    (hΦ : Φ.AnchoredAt ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (hLevi :
      letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      (sol.toIntrinsicDeTurckSolution.background ivp.initialTime).IsLeviCivita)
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (x : M) (u w : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w = 0 := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  calc
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
        sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w =
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w := by
          exact sol.pullbackBackgroundRicciCurvature_eq_initial_of_anchored
            (Φ := Φ) hΦ x u w
    _ = 0 := by
      exact ((InitialValueProblem.isRicciFlat_iff (I := I) (M := M) ivp
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) hLevi).1 hRicciFlat) x u w

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.pullbackBackgroundRicciCurvature_eq_zero_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (hLevi :
      letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      (sol.toIntrinsicDeTurckSolution.background ivp.initialTime).IsLeviCivita)
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (x : M) (u w : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w = 0 := by
  exact sol.pullbackBackgroundRicciCurvature_eq_zero_initial_of_anchored
    (Φ := gauge.maps) gauge.anchored hLevi hRicciFlat x u w

theorem IntrinsicDeTurckLocalSolution.pullbackBackgroundRicciCurvature_eq_zero_initial_of_anchored_of_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    (hΦ : Φ.AnchoredAt ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (hbackgroundLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (x : M) (u w : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w = 0 := by
  exact sol.pullbackBackgroundRicciCurvature_eq_zero_initial_of_anchored
    (Φ := Φ) hΦ (sol.background_isLeviCivita_initialMetric hbackgroundLevi)
    hRicciFlat x u w

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.pullbackBackgroundRicciCurvature_eq_zero_initial_of_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (hbackgroundLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (x : M) (u w : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w = 0 := by
  exact sol.pullbackBackgroundRicciCurvature_eq_zero_initial_of_anchored_of_isLeviCivita
    (Φ := gauge.maps) gauge.anchored hbackgroundLevi hRicciFlat x u w

theorem AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.pullbackBackgroundRicciCurvature_eq_zero_initial_of_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (hbackgroundLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (x : M) (u w : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
    (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      gauge3.maps sol.toIntrinsicDeTurckSolution.background
      ivp.initialTime).ricciCurvature x u w = 0 := by
  letI hpull₂ :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.toDiffeomorph2Gauge.maps
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1 := by
    simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toDiffeomorph2Gauge] using hpull
  simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily,
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toDiffeomorph2Gauge] using
    gauge3.toDiffeomorph2Gauge.pullbackBackgroundRicciCurvature_eq_zero_initial_of_isLeviCivita
      sol hbackgroundLevi hRicciFlat x u w

theorem IntrinsicDeTurckLocalSolution.pullbackBackgroundRicciCurvature_eq_zero_initial_of_diffeomorph3Gauge_of_isLeviCivita
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (hbackgroundLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background)
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (x : M) (u w : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
    (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      gauge3.maps sol.toIntrinsicDeTurckSolution.background
      ivp.initialTime).ricciCurvature x u w = 0 :=
  gauge3.pullbackBackgroundRicciCurvature_eq_zero_initial_of_isLeviCivita
    sol hbackgroundLevi hRicciFlat x u w

theorem IntrinsicDeTurckLocalSolution.pullbackChosenBackgroundRicciCurvature_eq_zero_initial_of_anchored
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol)
    {Φ : SmoothSelfDiffeomorph2Family (I := I) (M := M)}
    (hΦ : Φ.AnchoredAt ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (x : M) (u w : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) Φ
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w = 0 := by
  exact sol.pullbackBackgroundRicciCurvature_eq_zero_initial_of_anchored_of_isLeviCivita
    (Φ := Φ) hΦ
    (usesChosenBackground_isLeviCivita (I := I) (M := M) sol hchosen)
    hRicciFlat x u w

theorem AnchoredIntrinsicDeTurckDiffeomorphGaugeOn.pullbackChosenBackgroundRicciCurvature_eq_zero_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol)
    (gauge : AnchoredIntrinsicDeTurckDiffeomorphGaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (x : M) (u w : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M) gauge.maps
      sol.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w = 0 := by
  exact sol.pullbackChosenBackgroundRicciCurvature_eq_zero_initial_of_anchored
    hchosen (Φ := gauge.maps) gauge.anchored hRicciFlat x u w

theorem AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.pullbackChosenBackgroundRicciCurvature_eq_zero_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (x : M) (u w : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
    (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      gauge3.maps sol.toIntrinsicDeTurckSolution.background
      ivp.initialTime).ricciCurvature x u w = 0 := by
  letI hpull₂ :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.toDiffeomorph2Gauge.maps
          sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1 := by
    simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily,
      AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toDiffeomorph2Gauge] using hpull
  simpa [SmoothSelfDiffeomorph3Family.pullbackConnectionFamily,
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.toDiffeomorph2Gauge] using
    gauge3.toDiffeomorph2Gauge.pullbackChosenBackgroundRicciCurvature_eq_zero_initial
      sol hchosen hRicciFlat x u w

theorem IntrinsicDeTurckLocalSolution.pullbackChosenBackgroundRicciCurvature_eq_zero_initial_of_diffeomorph3Gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hchosen : UsesChosenBackground (I := I) (M := M) sol)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.toIntrinsicDeTurckSolution.metric sol.toIntrinsicDeTurckSolution.background
      sol.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    [hpull :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
          gauge3.maps sol.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (x : M) (u w : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
    (SmoothSelfDiffeomorph3Family.pullbackConnectionFamily (I := I) (M := M)
      gauge3.maps sol.toIntrinsicDeTurckSolution.background
      ivp.initialTime).ricciCurvature x u w = 0 :=
  gauge3.pullbackChosenBackgroundRicciCurvature_eq_zero_initial
    sol hchosen hRicciFlat x u w

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pullbackBackgroundRicciCurvature_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    [RiemannianBundle TM]
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.source.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (x : M) (u w : TM x) :
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background
            ivp.initialTime) 1 :=
      sol.pullbackBackground_contMDiff ivp.initialTime;
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
      sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background
      ivp.initialTime).ricciCurvature x u w =
    (sol.source.toIntrinsicDeTurckSolution.background ivp.initialTime).ricciCurvature x u w := by
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background
          ivp.initialTime) 1 :=
    sol.pullbackBackground_contMDiff ivp.initialTime
  exact sol.source.pullbackBackgroundRicciCurvature_eq_initial_of_anchored
    (Φ := sol.gauge.maps) sol.gauge.anchored x u w

theorem GaugeReducedIntrinsicDeTurckLocalSolution.pullbackBackgroundRicciCurvature_eq_zero_initial_of_isRicciFlat
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    [hbackground :
      CovariantDerivative.ContMDiffCovariantDerivative
        (sol.source.toIntrinsicDeTurckSolution.background ivp.initialTime) 1]
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (x : M) (u w : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
    letI :
        CovariantDerivative.ContMDiffCovariantDerivative
          (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
            sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background
            ivp.initialTime) 1 :=
      sol.pullbackBackground_contMDiff ivp.initialTime;
    (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
      sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background
      ivp.initialTime).ricciCurvature x u w = 0 := by
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background
          ivp.initialTime) 1 :=
    sol.pullbackBackground_contMDiff ivp.initialTime
  exact
    sol.source.pullbackBackgroundRicciCurvature_eq_zero_initial_of_anchored_of_isLeviCivita
      (Φ := sol.gauge.maps) sol.gauge.anchored sol.background_isLeviCivita
      hRicciFlat x u w

end RicciFlow
