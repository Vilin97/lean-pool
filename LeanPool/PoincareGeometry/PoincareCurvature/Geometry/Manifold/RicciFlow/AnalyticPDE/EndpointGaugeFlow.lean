/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowDerivative
/-!
# Endpoint gauge-flow reductions for Ricci-DeTurck charts

This extension module keeps endpoint-only gauge-flow theorem routes out of the
large foundational analytic evolution file.  The core `AnalyticPDE` module
contains the Banach-evolution and chart interfaces; this file adds downstream
wrappers that turn primitive endpoint derivative data for `C^3`
diffeomorphism-family gauges into scalar-derivative theorem-family packages.
-/

@[expose] public noncomputable section

open Set
open scoped Bundle Manifold ContDiff NNReal Topology

namespace RicciFlow
namespace AnalyticPDE
namespace MetricLocusEvolution

open PoincareCurvature.Bundle.Trivialization
open PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
/-- Bundled global endpoint derivative gauge-flow data for Ricci-DeTurck Banach-chart
families.  It packages exactly the endpoint chart data, primitive `C^3` gauge-flow
derivative, and scalar inner-product derivative hypotheses needed to pass from
Ricci-DeTurck chart solutions to scalar-derivative gauge-reducible Ricci-flow
theorem families. -/
structure EndpointDerivativeGaugeFlowFamilyData
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F] where
  T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ
  a : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  L : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  Kpic : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  Kstate : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
      (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp)
  metric :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      MetricFamily (I := I) (M := M)
  background :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ConnectionFamily (I := I) (M := M)
  metric_eq_curve :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v
  initial_hasTimeDerivative :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
        (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime
  terminal_hasTimeDerivative :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
        (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime
  chartRHS_eq_intrinsic :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          (chart ivp).A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric ivp sol) (background ivp sol) t x u v
  hbackground :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      background ivp sol = chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol)
  encode :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp),
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) (chart ivp) candidate.1
  maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)
  anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 ivp sol) ivp.initialTime
  hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
    (I := I) (M := M) maps3
  hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
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
                (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)) t x u v) t

/-- Endpoint-only global chart route from primitive pointwise `C^3` gauge-flow ODE
derivative data and scalar inner-product derivative data, retaining the scalar-derivative
gauge theorem-family endpoint. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_endpointTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
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
      (E := F) (H := H) (I := I) (M := M) :=
  innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background metric_eq_curve
    (boundaryTimeDerivativeFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_endpointTimeDerivative
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric
      initial_hasTimeDerivative terminal_hasTimeDerivative)
    chartRHS_eq_intrinsic hbackground encode maps3 anchored hflowDeriv hderiv

/-- Bundled global endpoint derivative gauge-flow data yields the scalar-derivative
gauge-reducible theorem family. -/
theorem EndpointDerivativeGaugeFlowFamilyData.toInnerDerivativeGaugeReducibleFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointDerivativeGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachCharts_endpointTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    (M := M) (F := F) (I := I) D.T D.a D.L D.Kpic D.Kstate D.chart D.metric
    D.background D.metric_eq_curve D.initial_hasTimeDerivative D.terminal_hasTimeDerivative
    D.chartRHS_eq_intrinsic D.hbackground D.encode D.maps3 D.anchored D.hflowDeriv D.hderiv

/-- Bundled global endpoint derivative gauge-flow data yields the chosen-background
Ricci-DeTurck theorem family before gauge reduction. -/
theorem EndpointDerivativeGaugeFlowFamilyData.toChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointDerivativeGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (D.toInnerDerivativeGaugeReducibleFamily.package ivp).chosen_package

/-- Bundled global endpoint derivative gauge-flow data projects to the compact intrinsic
Ricci-flow theorem family. -/
theorem EndpointDerivativeGaugeFlowFamilyData.toIntrinsicLocalExistenceUniquenessFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointDerivativeGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toIntrinsicFamily

/-- Bundled global endpoint derivative gauge-flow data projects to the ordinary compact
Ricci-flow theorem family. -/
theorem EndpointDerivativeGaugeFlowFamilyData.toLocalExistenceUniquenessFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointDerivativeGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toOrdinaryFamily

/-- Bundled interval-scoped endpoint derivative gauge-flow data for Ricci-DeTurck
Banach-chart families.  This is the closed-interval counterpart of
`EndpointDerivativeGaugeFlowFamilyData`. -/
structure EndpointDerivativeGaugeFlowFamilyDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F] where
  T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ
  a : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  L : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  Kpic : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  Kstate : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0
  chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
      (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp)
  metric :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      MetricFamily (I := I) (M := M)
  background :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ConnectionFamily (I := I) (M := M)
  metric_eq_curve :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v
  initial_hasTimeDerivative :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
        (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime
  terminal_hasTimeDerivative :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
        (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime
  chartRHS_eq_intrinsic :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          (chart ivp).A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric ivp sol) (background ivp sol) t x u v
  hbackground :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
      background ivp sol = chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol)
  encode :
    ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
      (candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) (chart ivp) candidate.1
  maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)
  anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 ivp sol) ivp.initialTime
  hflowDeriv : ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
    (I := I) (M := M) maps3
  hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
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
                (maps3 ivp sol) (anchored ivp sol) (hflowDeriv ivp sol)) t x u v) t

/-- Interval-scoped endpoint-only route from primitive pointwise `C^3` gauge-flow ODE
derivative data and scalar inner-product derivative data, retaining the scalar-derivative
gauge theorem-family endpoint. -/
theorem innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_endpointTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (metric :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        MetricFamily (I := I) (M := M))
    (background :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (_sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ConnectionFamily (I := I) (M := M))
    (metric_eq_curve :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M) (metric ivp sol) t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        HasTimeDerivativeAt (I := I) (M := M) (metric ivp sol)
          (fun τ x u v ↦ (chart ivp).A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            (chart ivp).A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (metric ivp sol) (background ivp sol) t x u v)
    (hbackground :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (sol : BanachEvolutionLocalSolutionIn (chart ivp).A
          (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
          (InitialValueProblem.toContinuousSectionSpace
            (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)),
        background ivp sol =
          chosenLeviCivitaFamily (I := I) (M := M) (metric ivp sol))
    (encode :
      ∀ (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
        (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp),
        TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
          (M := M) (F := F) (I := I) (chart ivp) candidate.1)
    (maps3 : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (anchored : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hflowDeriv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
          HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
            (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x))))
    (hderiv : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
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
      (E := F) (H := H) (I := I) (M := M) :=
  innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_boundaryTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric background metric_eq_curve
    (boundaryTimeDerivativeFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_endpointTimeDerivative
      (M := M) (F := F) (I := I) T a L Kpic Kstate chart metric
      initial_hasTimeDerivative terminal_hasTimeDerivative)
    chartRHS_eq_intrinsic hbackground encode maps3 anchored hflowDeriv hderiv

/-- Bundled interval endpoint derivative gauge-flow data yields the scalar-derivative
gauge-reducible theorem family. -/
theorem EndpointDerivativeGaugeFlowFamilyDataOnIcc.toInnerDerivativeGaugeReducibleFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointDerivativeGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  innerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_timeDependentGeometricRicciDeTurckBanachChartsOnIcc_endpointTimeDerivative_chartRHS_chosenCandidateEncoding_and_diffeomorph3GaugeFlowDerivativeInnerDerivative
    (M := M) (F := F) (I := I) D.T D.a D.L D.Kpic D.Kstate D.chart D.metric
    D.background D.metric_eq_curve D.initial_hasTimeDerivative D.terminal_hasTimeDerivative
    D.chartRHS_eq_intrinsic D.hbackground D.encode D.maps3 D.anchored D.hflowDeriv D.hderiv

/-- Bundled interval endpoint derivative gauge-flow data yields the chosen-background
Ricci-DeTurck theorem family before gauge reduction. -/
theorem EndpointDerivativeGaugeFlowFamilyDataOnIcc.toChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointDerivativeGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (D.toInnerDerivativeGaugeReducibleFamily.package ivp).chosen_package

/-- Bundled interval endpoint derivative gauge-flow data projects to the compact intrinsic
Ricci-flow theorem family. -/
theorem EndpointDerivativeGaugeFlowFamilyDataOnIcc.toIntrinsicLocalExistenceUniquenessFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointDerivativeGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toIntrinsicFamily

/-- Bundled interval endpoint derivative gauge-flow data projects to the ordinary compact
Ricci-flow theorem family. -/
theorem EndpointDerivativeGaugeFlowFamilyDataOnIcc.toLocalExistenceUniquenessFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (D : EndpointDerivativeGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toOrdinaryFamily

end MetricLocusEvolution
end AnalyticPDE
end RicciFlow
