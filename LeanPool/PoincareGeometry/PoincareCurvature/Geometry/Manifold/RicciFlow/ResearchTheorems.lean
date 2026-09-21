/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction
/-!
# Ricci--DeTurck gauge-reduction capstone

The frozen affine evolution is useful analytic infrastructure, but it is not
the geometric result that motivates the Ricci-flow formalization.  This module
exposes the research-facing gauge-reduction theorem: once a gauge-reduced
Ricci--DeTurck solution has the anchored `C^3` pullback and its verified
time-derivative data, the transformed metric is an intrinsic Ricci flow with
the same initial metric.  Its velocity is simultaneously the intrinsic
`-2 Ric` tensor and the trace of the conjugated pulled-back background Ricci
endomorphism.

The last equality is the coordinate-free curvature transport statement behind
the DeTurck trick, rather than a routine autonomous ODE consequence.
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

/-- **Raw gauge-to-Ricci-flow capstone.**  Starting with a chosen-background
Ricci--DeTurck local solution, an anchored `C^3` gauge and the scalar
time-derivative formula for its pulled-back metric construct the complete
gauge-reduced solution package.  The package records the exact transformed
metric and velocity, and certifies that the transformed evolution is an
intrinsic Ricci flow with the original initial metric. -/
theorem ChosenIntrinsicDeTurckLocalSolution.ricciDeTurckGaugeReduction_of_innerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.1.toIntrinsicDeTurckSolution.metric
      source.1.toIntrinsicDeTurckSolution.background
      source.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    (hderiv : ∀ ⦃t : ℝ⦄,
      t ∈ source.1.toIntrinsicDeTurckSolution.timeSet →
      ∀ (x : M) (u v : TM x),
        HasDerivAt
          (fun τ ↦
            (source.1.toIntrinsicDeTurckSolution.metric τ).inner
              ((gauge3.maps τ) x)
              ((gauge3.maps τ).pushforwardTangent x u)
              ((gauge3.maps τ).pushforwardTangent x v))
          (source.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            gauge3 t x u v) t) :
    ∃ reduced : GaugeReducedIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      reduced.source = source.1 ∧
      reduced.gauge.maps = gauge3.maps.toSmoothSelfDiffeomorph2Family ∧
      reduced.transformedMetric =
        gauge3.maps.pullbackMetricFamily source.1.toIntrinsicDeTurckSolution.metric ∧
      reduced.transformedVelocity =
        source.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 ∧
      IsIntrinsicRicciFlowOn (I := I) (M := M)
        reduced.transformedMetric reduced.transformedVelocity
        source.1.toIntrinsicDeTurckSolution.timeSet ∧
      reduced.transformedMetric ivp.initialTime = ivp.initialMetric := by
  let reduced :=
    source.toGaugeReduced_viaDiffeomorph3GaugeInnerDerivative gauge3 hderiv
  refine ⟨reduced, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · exact reduced.isIntrinsicRicciFlowOn
  · exact reduced.transformedMetric_eq_initial

/-- **Ricci--DeTurck gauge reduction.**  A verified gauge-reduced solution
simultaneously supplies an intrinsic Ricci-flow solution, preserves the initial
metric, follows the reverse DeTurck gauge equation, and identifies the
transformed velocity with `-2 Ric` of the transformed metric.  The
Levi--Civita field in the conclusion is the pulled-back source background,
which is the geometric mechanism that removes the DeTurck correction. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.ricciDeTurckGaugeReduction
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IsIntrinsicRicciFlowOn (I := I) (M := M)
        sol.transformedMetric sol.transformedVelocity
        sol.source.toIntrinsicDeTurckSolution.timeSet ∧
      sol.transformedMetric ivp.initialTime = ivp.initialMetric ∧
      (∀ {t : ℝ}, t ∈ sol.source.toIntrinsicDeTurckSolution.timeSet →
        ∀ (x : M) (u v : TM x),
          sol.transformedVelocity t x u v =
            (-2 : ℝ) * intrinsicRicciTensor (I := I) (M := M)
              sol.transformedMetric t x u v) ∧
      FollowsIntrinsicDeTurckOn (I := I) (M := M)
        sol.gauge.maps.toSmoothSelfMapFamily
        sol.source.toIntrinsicDeTurckSolution.metric
        sol.source.toIntrinsicDeTurckSolution.background
        sol.source.toIntrinsicDeTurckSolution.timeSet ∧
      CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
        (I := I) (M := M) sol.transformedMetric
        (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
          sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background) := by
  refine ⟨sol.isIntrinsicRicciFlowOn, sol.transformedMetric_eq_initial, ?_,
    sol.gauge_follows, sol.pullbackBackground_isLeviCivita⟩
  intro t ht x u v
  exact sol.transformed_velocity_eq_neg_two_intrinsicRicciTensor ht x u v

/-- **Curvature-transport readout of the gauge reduction.**  On the local
interval, the same transformed velocity from
`ricciDeTurckGaugeReduction` is `-2` times the trace of the tangent-map
conjugate of the pulled-back source-background Ricci endomorphism.  This is the
curvature-level identity that connects the gauge-fixed PDE to intrinsic
Ricci-flow geometry. -/
theorem GaugeReducedIntrinsicDeTurckLocalSolution.ricciDeTurckGaugeReduction_trace
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : GaugeReducedIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ∀ {t : ℝ}, t ∈ Set.Icc ivp.initialTime sol.source.terminalTime →
      ∀ (x : M) (u v : TM x),
        letI : Bundle.RiemannianBundle TM :=
          ⟨(sol.transformedMetric t).toRiemannianMetric⟩
        letI :
            CovariantDerivative.ContMDiffCovariantDerivative
              (SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
                sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
          sol.pullbackBackground_contMDiff t
        sol.transformedVelocity t x u v =
          (-2 : ℝ) *
            LinearMap.trace ℝ (TM ((sol.gauge.maps t) x))
              ((((sol.gauge.maps t).tangentMap x).toLinearEquiv).conj
                ((SmoothSelfDiffeomorph2Family.pullbackConnectionFamily (I := I) (M := M)
                  sol.gauge.maps sol.source.toIntrinsicDeTurckSolution.background t).ricciEndomorphism
                  x u v)) := by
  have hsourceBackground :
      ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative
          (sol.source.toIntrinsicDeTurckSolution.background t) 1 :=
    sol.source.background_contMDiff_of_isLeviCivita sol.background_isLeviCivita
  intro t ht x u v
  exact sol.transformed_velocity_eq_neg_two_trace_conj_pullbackBackgroundRicciEndomorphism_on_localInterval
    hsourceBackground ht x u v

end RicciFlow
