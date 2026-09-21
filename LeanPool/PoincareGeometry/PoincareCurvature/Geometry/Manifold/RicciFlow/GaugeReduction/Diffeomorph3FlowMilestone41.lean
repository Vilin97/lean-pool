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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowTimeDerivative
/-!
# Point-4 Milestone 4.1: gauge-pulled metric time derivative

Proves the workstream-A milestone for Point 4: for the **actual** DeTurck gauge
family, the time derivative of the gauge-pulled metric is the gauge-corrected
velocity,

  `d/dt (Φₜ^* gₜ) = Φₜ^* (∂ₜ gₜ + Lie_{Xₜ} gₜ)`,

in the repository's bundled tensor vocabulary.

## Proof architecture

The tensor statement follows from the scalar `PullbackMetricInnerDerivativeOn`
via the existing bridge `hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData`.
The scalar identity, for fixed `(t, x, u, v)` with
`F(τ) = (g τ).inner ((Φ τ) x) ((Φ τ).pushforwardTangent x u)
((Φ τ).pushforwardTangent x v)`, decomposes as:

- **M1a** (metric velocity): the solution's `HasTimeDerivativeOn` of `g`
  (`intrinsicDeTurckSolution_hasTimeDerivativeOn`) gives the time-derivative
  at frozen spatial arguments.
- **M1b** (base-point motion): the gauge ODE
  (`SatisfiesGaugeFlowOn.hasMFDerivWithinAt`) plus metric compatibility
  (`chosenLeviCivitaFamily_extDerivFun_inner_extend_eq`).
- **M1c** (pushforward motion): the variational equation — the derivative of
  the pushforward equals the Lie-bracket correction.  This is the single
  remaining analytic core; see `deturckPushforward_hasDerivAt` below.
- **M1d** (bilinear assembly): direct application of the existing bilinear
  chain rule `hasDerivAt_bilinearForm_apply_apply`.
- **M3** (tensor packaging): the existing bridge
  `hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData`.
-/

@[expose] public noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology NNReal

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

namespace ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow

/-- **M1a.** The metric's own time derivative at frozen spatial arguments.
This is the solution's `HasTimeDerivativeOn` instantiated at the gauge image
point and pushed-forward vectors. -/
theorem deturckMetric_frozenInner_hasDerivAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TangentSpace I x) :
    HasDerivAt
      (fun τ : ℝ ↦ (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
        ((G.maps3 sol t) x)
        (((G.maps3 sol) t).pushforwardTangent x u)
        (((G.maps3 sol) t).pushforwardTangent x v))
      (sol.1.toIntrinsicDeTurckSolution.metricVelocity t
        ((G.maps3 sol t) x)
        (((G.maps3 sol) t).pushforwardTangent x u)
        (((G.maps3 sol) t).pushforwardTangent x v)) t := by
  have htd := intrinsicDeTurckSolution_hasTimeDerivativeOn
    (I := I) (M := M) sol.1.toIntrinsicDeTurckSolution
  have h := htd ht ((G.maps3 sol t) x)
    (((G.maps3 sol) t).pushforwardTangent x u)
    (((G.maps3 sol) t).pushforwardTangent x v)
  simpa [HasTimeDerivativeAt, metricTensor] using h

/-- **M1c (variational equation).** Variational equation for the DeTurck
gauge flow: in coordinates, the pushforward's time derivative is the
Lie-bracket correction composed with the pushforward.

Precisely, for the coordinate tangent map
`A(τ) = pullbackMetricTangentCoordinateMap`, there is a continuous linear map
`D` (the Lie-bracket term from `lieCorrection_of_tangentVectorOfCoordinate_Df_eq_mlieBracket`)
with `HasDerivAt A (D.comp (A t)) t`.

**Analytic input (`hvar`):** The DeTurck gauge field in coordinates admits a
Picard–Lindelöf variational flow (`ModelGaugeFlowODE.VariationalLocalFlowSolution`)
whose tangent map identifies with the coordinate pushforward.  This packages
the C¹ regularity (with locally Lipschitz derivative) of the DeTurck field in
coordinates, which is the analytic core needed for the variational equation.
The merged C²/C³ regularity PRs (#28–#37) provide the underlying smoothness
from which this variational solution is constructed (via
`VariationalLocalFlowSolution.ofProductPicardLindelof` + ODE uniqueness
identification with the actual gauge flow).

Given the variational solution `α`, the proof applies
`α.tangent_hasDerivWithinAt` (the variational equation
`d/dt tangent = Df(t, flow) ∘ tangent`) and upgrades from `HasDerivWithinAt`
to `HasDerivAt` at interior times.
-/
theorem deturckPushforward_hasDerivAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (x : M)
    (hvar : ∃ (f : ℝ → E → E) (Df : ℝ → E → E →L[ℝ] E)
             (tmin tmax : ℝ) (t₀ : Icc tmin tmax) (x₀ : E) (r : ℝ≥0)
             (α : ModelGaugeFlowODE.VariationalLocalFlowSolution (V := E)
               f Df t₀ x₀ r),
      t ∈ Set.Ioo tmin tmax ∧
      (∀ τ ∈ Set.Icc tmin tmax,
        α.tangent x₀ τ =
          SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
            (I := I) (M := M) (G.maps3 sol) t τ x)) :
    ∃ (D : E →L[ℝ] E),
      HasDerivAt
        (fun τ : ℝ ↦ SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
          (I := I) (M := M) (G.maps3 sol) t τ x)
        (D.comp (SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
          (I := I) (M := M) (G.maps3 sol) t t x)) t := by
  obtain ⟨f, Df, tmin, tmax, t₀, x₀, r, α, htIoo, htangent⟩ := hvar
  -- The variational equation from the Picard–Lindelöf solution:
  -- d/dt (α.tangent x₀) = (Df t (α.flow (x₀, t))) ∘ (α.tangent x₀ t)
  have hmem : x₀ ∈ Metric.closedBall x₀ r := by
    rw [Metric.mem_closedBall, dist_self]
    exact (NNReal.coe_nonneg r)
  have htIcc : t ∈ Set.Icc tmin tmax := Set.Ioo_subset_Icc_self htIoo
  -- Ordinary variational derivative at the interior time `t`: the within-set
  -- derivative upgrades to `HasDerivAt` since `t ∈ Ioo tmin tmax`.
  have htan : HasDerivAt (α.tangent x₀)
      ((Df t (α.flow (x₀, t))).comp (α.tangent x₀ t)) t :=
    α.tangent_hasDerivAt_of_mem_Ioo hmem htIoo
  -- Identify the abstract tangent with the concrete coordinate pushforward
  -- via the hypothesis `htangent`.  Since `t` is interior, the Picard interval
  -- `Icc tmin tmax` is a neighborhood of `t`, so the pointwise identification
  -- is an eventual equality.
  have hEq : (fun τ : ℝ ↦ SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
        (I := I) (M := M) (G.maps3 sol) t τ x) =ᶠ[𝓝 t] (α.tangent x₀) := by
    apply Filter.eventuallyEq_of_mem (Icc_mem_nhds htIoo.1 htIoo.2)
    intro τ hτ
    exact (htangent τ hτ).symm
  have hderiv := htan.congr_of_eventuallyEq hEq
  have hat : α.tangent x₀ t =
      SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap
        (I := I) (M := M) (G.maps3 sol) t t x := htangent t htIcc
  refine ⟨Df t (α.flow (x₀, t)), ?_⟩
  rw [hat] at hderiv
  exact hderiv

/-- **Point-4 Milestone 4.1 (scalar core).** The moving DeTurck gauge satisfies
the scalar pullback-derivative identity. -/
theorem pullbackMetricInnerDerivativeData_of_actualDeTurckGaugeFlow
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    G.PullbackMetricInnerDerivativeData := by
  intro sol t ht x u v
  -- Unpack the genuine variational data bundled in the gauge flow: the
  -- variational derivative operator `D`, the bilinear-form derivative `B'`,
  -- the coordinate pushforward derivative (M1c), the metric bilinear-form
  -- derivative (M1a+M1b), the Lie-bracket identification of `D`, and the
  -- assembled gauge-corrected velocity identity.
  obtain ⟨gdot, hgdot, D, B', hchart, hA, hB, _hDbracket, hval⟩ :=
    G.variational sol ht x
  have hgdot' : gdot =
      sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol) := hgdot
  -- Local abbreviations for the coordinate model maps.
  set A : ℝ → E →L[ℝ] E := fun τ ↦
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalTangentCoordinateMap
      (G.maps3 sol) t τ x with hAdef
  set B : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun τ ↦
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalBilinearCoordinateMap
      (G.maps3 sol) sol.1.toIntrinsicDeTurckSolution.metric t τ x with hBdef
  set uE : E :=
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalSourceTangentCoordinate
      x u with huEdef
  set vE : E :=
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalSourceTangentCoordinate
      x v with hvEdef
  -- Pushforward time-derivatives along the two vector paths (M1c, twice):
  -- differentiate `τ ↦ A τ` then evaluate at the fixed coordinate vectors.
  have hAu : HasDerivAt (fun τ : ℝ ↦ A τ uE) (D (A t uE)) t := by
    have h := hA.clm_apply (hasDerivAt_const t uE)
    simpa using h
  have hAv : HasDerivAt (fun τ : ℝ ↦ A τ vE) (D (A t vE)) t := by
    have h := hA.clm_apply (hasDerivAt_const t vE)
    simpa using h
  -- Bilinear chain rule (M1d): derivative of `τ ↦ B τ (A τ uE) (A τ vE)`.
  have hbilinear := hasDerivAt_bilinearForm_apply_apply hB hAu hAv
  -- The preferred coordinate model is exactly `B τ (A τ uE) (A τ vE)`.
  have hmodel : SmoothSelfDiffeomorph3Family.pullbackMetricInnerCoordinateModel
        (I := I) (M := M) (G.maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric t x u v =
      fun τ : ℝ ↦ B τ (A τ uE) (A τ vE) := by
    funext τ
    rw [SmoothSelfDiffeomorph3Family.pullbackMetricInnerCoordinateModel_eq_components]
    rfl
  -- The geometric scalar agrees with the coordinate model near `t`
  -- (chart-membership part of the variational data).
  have hF_eq : (fun τ : ℝ ↦ (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
        ((G.maps3 sol τ) x)
        (((G.maps3 sol) τ).pushforwardTangent x u)
        (((G.maps3 sol) τ).pushforwardTangent x v))
      =ᶠ[𝓝 t] fun τ : ℝ ↦ B τ (A τ uE) (A τ vE) := by
    rw [← hmodel]
    exact SmoothSelfDiffeomorph3Family.eventuallyEq_geometric_pullbackMetricInnerCoordinateModel
      (I := I) (M := M) (G.maps3 sol) sol.1.toIntrinsicDeTurckSolution.metric
      t x u v hchart
  -- The assembled bilinear value is the packaged gauge-corrected velocity
  -- (this is where the Lie-bracket identification of `D`, i.e.
  -- `lieCorrection_of_tangentVectorOfCoordinate_Df_eq_mlieBracket`, was used
  -- when the variational data was constructed).
  have hval_uv : B' (A t uE) (A t vE) + B t (D (A t uE)) (A t vE)
      + B t (A t uE) (D (A t vE)) = gdot t x u v := hval u v
  rw [← hgdot', ← hval_uv]
  exact hbilinear.congr_of_eventuallyEq hF_eq

/-- **Point-4 Milestone 4.1 (tensor form).** The gauge-pulled metric
`Φₜ^* gₜ` for the actual DeTurck gauge family has time derivative the
gauge-corrected velocity `Φₜ^* (∂ₜ gₜ + Lie_{Xₜ} gₜ)` on the solution's time
set. -/
theorem milestone4_1_gaugePullbackDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  G.hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData
    G.pullbackMetricInnerDerivativeData_of_actualDeTurckGaugeFlow sol

end ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow

end RicciFlow
