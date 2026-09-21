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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowExistence
/-!
# Subsingleton-tangent time-derivative closure for `C^3` gauge flows

This module closes the non-identity gauge-pulled metric time-derivative
obligation in the zero-dimensional tangent-fiber case.  No chain-rule
calculation is needed there: every metric component and every corrected
velocity component vanishes.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- On subsingleton tangent fibers, every component of the concrete corrected
velocity for a `C^3` DeTurck gauge vanishes. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime)
    {t : ℝ} (ht : t ∈ source.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TM x) :
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v = 0 := by
  have hvel :
      source.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x)
          ((gauge3.maps t).pushforwardTangent x u)
          ((gauge3.maps t).pushforwardTangent x v) = 0 :=
    source.toIntrinsicDeTurckSolution.metricVelocity_eq_zero_of_subsingleton_tangent
      ht ((gauge3.maps t) x)
      ((gauge3.maps t).pushforwardTangent x u)
      ((gauge3.maps t).pushforwardTangent x v)
  have hu : u = 0 := Subsingleton.elim u 0
  have hv : v = 0 := Subsingleton.elim v 0
  have hvel0 :
      source.toIntrinsicDeTurckSolution.metricVelocity t ((gauge3.maps t) x) 0 0 = 0 := by
    simpa [hu, hv] using hvel
  simp [IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge,
    hvel0, hu, hv]

/-- On subsingleton tangent fibers, any `C^3` DeTurck gauge supplies the required
time derivative of the gauge-pulled metric. -/
theorem IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocity_hasTimeDerivativeOn_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (source : IntrinsicDeTurckLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (gauge3 : AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      source.toIntrinsicDeTurckSolution.metric source.toIntrinsicDeTurckSolution.background
      source.toIntrinsicDeTurckSolution.timeSet ivp.initialTime) :
    HasTimeDerivativeOn (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3)
      source.toIntrinsicDeTurckSolution.timeSet := by
  intro t ht x u v
  have hmetric :
      (fun τ : ℝ ↦ metricTensor (I := I) (M := M)
        (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
        τ x u v) = fun _ : ℝ ↦ 0 := by
    funext τ
    exact SmoothSelfDiffeomorph3Family.pullbackMetricFamily_inner_eq_zero_of_subsingleton_tangent
      (I := I) (M := M) gauge3.maps source.toIntrinsicDeTurckSolution.metric τ x u v
  have hvelocity :
      source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v = 0 :=
    source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_zero_of_subsingleton_tangent
      gauge3 ht x u v
  change HasDerivAt
    (fun τ : ℝ ↦ metricTensor (I := I) (M := M)
      (gauge3.maps.pullbackMetricFamily source.toIntrinsicDeTurckSolution.metric)
      τ x u v)
    (source.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge gauge3 t x u v) t
  rw [hmetric, hvelocity]
  exact (hasDerivAt_const (x := t) (c := (0 : ℝ)) :
    HasDerivAt (fun _ : ℝ ↦ (0 : ℝ)) 0 t)

namespace ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow

/-- Fixed-IVP bundled non-identity `C^3` gauge flows automatically satisfy the
pulled-metric time-derivative obligation on subsingleton tangent fibers. -/
theorem hpullDerivative_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  sol.1.gaugeCorrectedPullbackVelocity_hasTimeDerivativeOn_of_subsingleton_tangent
    (G.gauge sol)

/-- Model-space synonym for `hpullDerivative_of_subsingleton_tangent`. -/
theorem hpullDerivative_of_subsingleton_model
    [Subsingleton E]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  G.hpullDerivative_of_subsingleton_tangent sol

/-- Empty-manifold synonym for `hpullDerivative_of_subsingleton_tangent`. -/
theorem hpullDerivative_of_isEmpty
    [IsEmpty M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  haveI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  exact G.hpullDerivative_of_subsingleton_tangent sol

end ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow

namespace ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily

/-- Theorem-family bundled non-identity `C^3` gauge flows automatically satisfy
the pulled-metric time-derivative obligation on subsingleton tangent fibers. -/
theorem hpullDerivative_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  (G.forInitialValueProblem ivp).hpullDerivative_of_subsingleton_tangent sol

/-- Model-space synonym for theorem-family `hpullDerivative_of_subsingleton_tangent`. -/
theorem hpullDerivative_of_subsingleton_model
    [Subsingleton E]
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  G.hpullDerivative_of_subsingleton_tangent ivp sol

/-- Empty-manifold synonym for theorem-family `hpullDerivative_of_subsingleton_tangent`. -/
theorem hpullDerivative_of_isEmpty
    [IsEmpty M]
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  haveI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  exact G.hpullDerivative_of_subsingleton_tangent ivp sol

end ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily

/-- A chosen-background DeTurck theorem family becomes gauge-reducible from any
geometric `C^3` intrinsic gauge-flow family on subsingleton tangent fibers,
without an additional time-derivative input. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    G (G.hpullDerivative_of_subsingleton_tangent)

/-- Gauge-reduced DeTurck theorem-family projection from any geometric `C^3`
intrinsic gauge-flow family on subsingleton tangent fibers. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent G).toGaugeReduced

/-- Intrinsic Ricci-flow theorem-family projection from any geometric `C^3`
intrinsic gauge-flow family on subsingleton tangent fibers. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReduced_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent G).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection from any geometric `C^3`
intrinsic gauge-flow family on subsingleton tangent fibers. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent G).toOrdinary

/-- Model-space synonym of the subsingleton-tangent geometric gauge-flow route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_model
    [Subsingleton E]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent G

/-- Gauge-reduced theorem-family model-space synonym of the subsingleton-tangent
geometric gauge-flow route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_model
    [Subsingleton E]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_model G).toGaugeReduced

/-- Intrinsic theorem-family model-space synonym of the subsingleton-tangent
geometric gauge-flow route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_model
    [Subsingleton E]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReduced_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_model G).toIntrinsicFamily

/-- Ordinary theorem-family model-space synonym of the subsingleton-tangent
geometric gauge-flow route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_model
    [Subsingleton E]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_model G).toOrdinary

/-- Empty-manifold synonym of the subsingleton-tangent geometric gauge-flow route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowFamily_of_isEmpty
    [IsEmpty M]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) := by
  haveI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  exact pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent G

/-- Gauge-reduced theorem-family empty-manifold synonym of the
subsingleton-tangent geometric gauge-flow route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaDiffeomorph3GaugeFlowFamily_of_isEmpty
    [IsEmpty M]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamily_of_isEmpty G).toGaugeReduced

/-- Intrinsic theorem-family empty-manifold synonym of the subsingleton-tangent
geometric gauge-flow route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamily_of_isEmpty
    [IsEmpty M]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReduced_viaDiffeomorph3GaugeFlowFamily_of_isEmpty G).toIntrinsicFamily

/-- Ordinary theorem-family empty-manifold synonym of the subsingleton-tangent
geometric gauge-flow route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeFlowFamily_of_isEmpty
    [IsEmpty M]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamily_of_isEmpty G).toOrdinary

/-- Raw intrinsic gauge-flow existence needs no additional derivative input on
subsingleton tangent fibers. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaGaugeFlowExistence_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamily_of_subsingleton_tangent
    G.toDiffeomorph3GaugeFlowFamily

/-- Raw intrinsic gauge-flow existence projects directly to gauge-reduced
DeTurck theorem families on subsingleton tangent fibers without additional
derivative input. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaGaugeFlowExistence_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaGaugeFlowExistence_of_subsingleton_tangent G).toGaugeReduced

/-- Raw intrinsic gauge-flow existence projects to intrinsic Ricci-flow theorem
families on subsingleton tangent fibers without additional derivative input. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaGaugeFlowExistence_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReduced_viaGaugeFlowExistence_of_subsingleton_tangent G).toIntrinsicFamily

/-- Raw intrinsic gauge-flow existence projects to ordinary Ricci-flow theorem
families on subsingleton tangent fibers without additional derivative input. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaGaugeFlowExistence_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaGaugeFlowExistence_of_subsingleton_tangent G).toOrdinary

/-- Model-space synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaGaugeFlowExistence_of_subsingleton_model
    [Subsingleton E]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaGaugeFlowExistence_of_subsingleton_tangent G

/-- Gauge-reduced theorem-family model-space synonym of the raw gauge-flow
existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaGaugeFlowExistence_of_subsingleton_model
    [Subsingleton E]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaGaugeFlowExistence_of_subsingleton_model G).toGaugeReduced

/-- Intrinsic theorem-family model-space synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaGaugeFlowExistence_of_subsingleton_model
    [Subsingleton E]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReduced_viaGaugeFlowExistence_of_subsingleton_model G).toIntrinsicFamily

/-- Ordinary theorem-family model-space synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaGaugeFlowExistence_of_subsingleton_model
    [Subsingleton E]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaGaugeFlowExistence_of_subsingleton_model G).toOrdinary

/-- Empty-manifold synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaGaugeFlowExistence_of_isEmpty
    [IsEmpty M]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) := by
  haveI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  exact pkg.toGaugeReducible_viaGaugeFlowExistence_of_subsingleton_tangent G

/-- Gauge-reduced theorem-family empty-manifold synonym of the raw gauge-flow
existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReduced_viaGaugeFlowExistence_of_isEmpty
    [IsEmpty M]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaGaugeFlowExistence_of_isEmpty G).toGaugeReduced

/-- Intrinsic theorem-family empty-manifold synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaGaugeFlowExistence_of_isEmpty
    [IsEmpty M]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReduced_viaGaugeFlowExistence_of_isEmpty G).toIntrinsicFamily

/-- Ordinary theorem-family empty-manifold synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaGaugeFlowExistence_of_isEmpty
    [IsEmpty M]
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaGaugeFlowExistence_of_isEmpty G).toOrdinary

/-- A fixed-IVP chosen-background DeTurck theorem package becomes gauge-reducible
from any geometric `C^3` intrinsic gauge-flow bundle on subsingleton tangent
fibers, without an additional time-derivative input. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    G (G.hpullDerivative_of_subsingleton_tangent)

/-- Fixed-IVP gauge-reduced projection from any geometric `C^3` intrinsic
gauge-flow bundle on subsingleton tangent fibers. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_tangent G).toGaugeReduced

/-- Fixed-IVP intrinsic projection from any geometric `C^3` intrinsic gauge-flow
bundle on subsingleton tangent fibers. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReduced_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_tangent G).toIntrinsic

/-- Fixed-IVP ordinary projection from any geometric `C^3` intrinsic gauge-flow
bundle on subsingleton tangent fibers. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_tangent G).toOrdinary

/-- Fixed-IVP model-space synonym of the geometric gauge-flow bundle route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_model
    [Subsingleton E]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_tangent G

/-- Fixed-IVP gauge-reduced model-space synonym of the geometric gauge-flow bundle route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_model
    [Subsingleton E]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_model G).toGaugeReduced

/-- Fixed-IVP intrinsic model-space synonym of the geometric gauge-flow bundle route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_model
    [Subsingleton E]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReduced_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_model G).toIntrinsic

/-- Fixed-IVP ordinary model-space synonym of the geometric gauge-flow bundle route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_model
    [Subsingleton E]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_model G).toOrdinary

/-- Fixed-IVP empty-manifold synonym of the geometric gauge-flow bundle route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaDiffeomorph3GaugeFlowBundle_of_isEmpty
    [IsEmpty M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp := by
  haveI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  exact pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_tangent G

/-- Fixed-IVP gauge-reduced empty-manifold synonym of the geometric gauge-flow bundle route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaDiffeomorph3GaugeFlowBundle_of_isEmpty
    [IsEmpty M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundle_of_isEmpty G).toGaugeReduced

/-- Fixed-IVP intrinsic empty-manifold synonym of the geometric gauge-flow bundle route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3GaugeFlowBundle_of_isEmpty
    [IsEmpty M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReduced_viaDiffeomorph3GaugeFlowBundle_of_isEmpty G).toIntrinsic

/-- Fixed-IVP ordinary empty-manifold synonym of the geometric gauge-flow bundle route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3GaugeFlowBundle_of_isEmpty
    [IsEmpty M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3GaugeFlowBundle_of_isEmpty G).toOrdinary

/-- Fixed-IVP raw intrinsic gauge-flow existence needs no additional derivative
input on subsingleton tangent fibers. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaGaugeFlowExistence_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundle_of_subsingleton_tangent
    G.toDiffeomorph3GaugeFlow

/-- Fixed-IVP raw intrinsic gauge-flow existence projects directly to
gauge-reduced DeTurck theorem packages on subsingleton tangent fibers without
additional derivative input. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaGaugeFlowExistence_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaGaugeFlowExistence_of_subsingleton_tangent G).toGaugeReduced

/-- Fixed-IVP intrinsic projection from raw intrinsic gauge-flow existence on
subsingleton tangent fibers without additional derivative input. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaGaugeFlowExistence_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReduced_viaGaugeFlowExistence_of_subsingleton_tangent G).toIntrinsic

/-- Fixed-IVP ordinary projection from raw intrinsic gauge-flow existence on
subsingleton tangent fibers without additional derivative input. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaGaugeFlowExistence_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaGaugeFlowExistence_of_subsingleton_tangent G).toOrdinary

/-- Fixed-IVP model-space synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaGaugeFlowExistence_of_subsingleton_model
    [Subsingleton E]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaGaugeFlowExistence_of_subsingleton_tangent G

/-- Fixed-IVP gauge-reduced model-space synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaGaugeFlowExistence_of_subsingleton_model
    [Subsingleton E]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaGaugeFlowExistence_of_subsingleton_model G).toGaugeReduced

/-- Fixed-IVP intrinsic model-space synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaGaugeFlowExistence_of_subsingleton_model
    [Subsingleton E]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReduced_viaGaugeFlowExistence_of_subsingleton_model G).toIntrinsic

/-- Fixed-IVP ordinary model-space synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaGaugeFlowExistence_of_subsingleton_model
    [Subsingleton E]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaGaugeFlowExistence_of_subsingleton_model G).toOrdinary

/-- Fixed-IVP empty-manifold synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaGaugeFlowExistence_of_isEmpty
    [IsEmpty M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp := by
  haveI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  exact pkg.toGaugeReducible_viaGaugeFlowExistence_of_subsingleton_tangent G

/-- Fixed-IVP gauge-reduced empty-manifold synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReduced_viaGaugeFlowExistence_of_isEmpty
    [IsEmpty M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    GaugeReducedIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaGaugeFlowExistence_of_isEmpty G).toGaugeReduced

/-- Fixed-IVP intrinsic empty-manifold synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaGaugeFlowExistence_of_isEmpty
    [IsEmpty M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReduced_viaGaugeFlowExistence_of_isEmpty G).toIntrinsic

/-- Fixed-IVP ordinary empty-manifold synonym of the raw gauge-flow existence route. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaGaugeFlowExistence_of_isEmpty
    [IsEmpty M]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaGaugeFlowExistence_of_isEmpty G).toOrdinary

section Compact

variable [CompactSpace M]

/-- Zero-dimensional fixed-IVP point-4 closure routed through raw `C^3`
intrinsic gauge-flow existence.  This deliberately uses the same
chosen-DeTurck-to-gauge-reduced path as the general point-4 theorem interface. -/
noncomputable def localExistenceUniqueness_viaGaugeFlowExistence_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (chosenIntrinsicDeTurckLocalExistenceUniqueness_of_subsingleton_tangent
      (I := I) (M := M) ivp).toOrdinary_viaGaugeFlowExistence_of_subsingleton_tangent
    (IntrinsicDeTurckGaugeFlowExistence.identityOfSubsingletonTangent
      (I := I) (M := M) ivp)

/-- Zero-dimensional theorem-family point-4 closure routed through raw `C^3`
intrinsic gauge-flow existence. -/
noncomputable def localExistenceUniquenessFamily_viaGaugeFlowExistence_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)] :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_subsingleton_tangent
      (I := I) (M := M)).toOrdinaryFamily_viaGaugeFlowExistence_of_subsingleton_tangent
    (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfSubsingletonTangent
      (I := I) (M := M))

/-- Model-space synonym of
`localExistenceUniqueness_viaGaugeFlowExistence_of_subsingleton_tangent`. -/
noncomputable def localExistenceUniqueness_viaGaugeFlowExistence_of_subsingleton_model
    [Subsingleton E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  localExistenceUniqueness_viaGaugeFlowExistence_of_subsingleton_tangent
    (I := I) (M := M) ivp

/-- Theorem-family model-space synonym of
`localExistenceUniquenessFamily_viaGaugeFlowExistence_of_subsingleton_tangent`. -/
noncomputable def localExistenceUniquenessFamily_viaGaugeFlowExistence_of_subsingleton_model
    [Subsingleton E] :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  localExistenceUniquenessFamily_viaGaugeFlowExistence_of_subsingleton_tangent
    (I := I) (M := M)

/-- Empty-manifold fixed-IVP point-4 closure routed through raw `C^3`
intrinsic gauge-flow existence. -/
noncomputable def localExistenceUniqueness_viaGaugeFlowExistence_of_isEmpty
    [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp := by
  letI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  exact localExistenceUniqueness_viaGaugeFlowExistence_of_subsingleton_tangent
    (I := I) (M := M) ivp

/-- Empty-manifold theorem-family point-4 closure routed through raw `C^3`
intrinsic gauge-flow existence. -/
noncomputable def localExistenceUniquenessFamily_viaGaugeFlowExistence_of_isEmpty
    [IsEmpty M] :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) := by
  letI : ∀ x : M, Subsingleton (TM x) := fun x ↦ isEmptyElim x
  exact localExistenceUniquenessFamily_viaGaugeFlowExistence_of_subsingleton_tangent
    (I := I) (M := M)

end Compact

end RicciFlow
