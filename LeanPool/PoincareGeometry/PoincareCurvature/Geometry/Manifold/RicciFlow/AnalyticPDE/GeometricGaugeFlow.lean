/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EndpointGaugeFlow
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowExistence
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowTimeDerivative
/-!
# Geometric endpoint gauge-flow reductions

This extension module packages endpoint Ricci-DeTurck chart data whose gauge input
is the geometric `SatisfiesGaugeFlowOn` formulation.  It turns pulled-back metric
time-derivative data into the scalar derivative endpoint needed by the
derivative-level bundles via the reusable `C^3` gauge-flow bridge, keeping the
larger analytic endpoint file stable.
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
/-- Bundled fixed-IVP endpoint data whose non-identity gauge input is a
geometric `C^3` intrinsic DeTurck gauge flow. -/
structure EndpointGeometricGaugeFlowData
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0} where
  chart : TimeDependentGeometricRicciDeTurckBanachChart
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover
    ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate
  metric : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
    (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
    (InitialValueProblem.toContinuousSectionSpace
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      MetricFamily (I := I) (M := M)
  background : ∀ _sol : BanachEvolutionLocalSolutionIn chart.A
    (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
    (InitialValueProblem.toContinuousSectionSpace
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ConnectionFamily (I := I) (M := M)
  metric_eq_curve : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
    (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
    (InitialValueProblem.toContinuousSectionSpace
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          metricTensor (I := I) (M := M) (metric sol) t x u v = sol.curve t x u v
  initial_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
    (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
    (InitialValueProblem.toContinuousSectionSpace
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      HasTimeDerivativeAt (I := I) (M := M) (metric sol)
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) ivp.initialTime
  terminal_hasTimeDerivative : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
    (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
    (InitialValueProblem.toContinuousSectionSpace
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      HasTimeDerivativeAt (I := I) (M := M) (metric sol)
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) sol.terminalTime
  chartRHS_eq_intrinsic : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
    (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
    (InitialValueProblem.toContinuousSectionSpace
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
        ∀ (x : M) (u v : TangentSpace I x),
          chart.A t (sol.curve t) x u v =
            intrinsicRicciDeTurckRHS (I := I) (M := M)
              (metric sol) (background sol) t x u v
  hbackground : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
    (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
    (InitialValueProblem.toContinuousSectionSpace
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
      background sol = chosenLeviCivitaFamily (I := I) (M := M) (metric sol)
  encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp,
    TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate.1
  gaugeFlow : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
    (E := F) (H := H) (I := I) (M := M) ivp
  hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp,
    HasTimeDerivativeOn (I := I) (M := M)
      ((gaugeFlow.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (gaugeFlow.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet

namespace EndpointGeometricGaugeFlowData

/-- Fixed-IVP geometric endpoint gauge-flow data yields the chosen-background
Ricci-DeTurck theorem package. -/
theorem toChosenIntrinsicDeTurckLocalExistenceUniqueness
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (D : EndpointGeometricGaugeFlowData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      (ivp := ivp) (T := T) (a := a) (L := L)
      (Kpic := Kpic) (Kstate := Kstate)) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp :=
  TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_endpointTimeDerivative_chartRHS_and_chosenCandidateEncoding
      (M := M) (F := F) (I := I) D.chart D.metric D.background D.metric_eq_curve
      D.initial_hasTimeDerivative D.terminal_hasTimeDerivative
      D.chartRHS_eq_intrinsic D.hbackground D.encode

/-- Fixed-IVP geometric endpoint gauge-flow data yields the gauge-reducible
Ricci-flow theorem package. -/
noncomputable def toGaugeReducible
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (D : EndpointGeometricGaugeFlowData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      (ivp := ivp) (T := T) (a := a) (L := L)
      (Kpic := Kpic) (Kstate := Kstate)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp :=
  D.toChosenIntrinsicDeTurckLocalExistenceUniqueness
    |>.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleTimeDerivative
      D.gaugeFlow D.hpullDerivative

/-- Fixed-IVP geometric endpoint gauge-flow data projects to the intrinsic
Ricci-flow theorem package. -/
noncomputable def toIntrinsicLocalExistenceUniqueness
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (D : EndpointGeometricGaugeFlowData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      (ivp := ivp) (T := T) (a := a) (L := L)
      (Kpic := Kpic) (Kstate := Kstate)) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  D.toGaugeReducible.toIntrinsic

/-- Fixed-IVP geometric endpoint gauge-flow data projects to the ordinary
Ricci-flow theorem package. -/
noncomputable def toLocalExistenceUniqueness
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (D : EndpointGeometricGaugeFlowData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      (ivp := ivp) (T := T) (a := a) (L := L)
      (Kpic := Kpic) (Kstate := Kstate)) :
    LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  D.toIntrinsicLocalExistenceUniqueness.toOrdinary

end EndpointGeometricGaugeFlowData

/-- Replace the geometric gauge-flow component of fixed-IVP endpoint data by a
raw `C^3` diffeomorphism-flow existence witness. -/
def EndpointGeometricGaugeFlowData.withGaugeFlowExistence
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (D : EndpointGeometricGaugeFlowData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      (ivp := ivp) (T := T) (a := a) (L := L)
      (Kpic := Kpic) (Kstate := Kstate))
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := F) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        (((G.toDiffeomorph3GaugeFlow).maps3 sol).pullbackMetricFamily
          sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          ((G.toDiffeomorph3GaugeFlow).gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    EndpointGeometricGaugeFlowData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      (ivp := ivp) (T := T) (a := a) (L := L)
      (Kpic := Kpic) (Kstate := Kstate) where
  chart := D.chart
  metric := D.metric
  background := D.background
  metric_eq_curve := D.metric_eq_curve
  initial_hasTimeDerivative := D.initial_hasTimeDerivative
  terminal_hasTimeDerivative := D.terminal_hasTimeDerivative
  chartRHS_eq_intrinsic := D.chartRHS_eq_intrinsic
  hbackground := D.hbackground
  encode := D.encode
  gaugeFlow := G.toDiffeomorph3GaugeFlow
  hpullDerivative := hpullDerivative

/-- Replace the geometric gauge-flow component of fixed-IVP endpoint data by a
raw `C^3` diffeomorphism-flow existence witness carrying named scalar
pullback-metric derivative data. -/
def EndpointGeometricGaugeFlowData.withGaugeFlowExistencePullbackMetricInnerDerivative
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (D : EndpointGeometricGaugeFlowData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      (ivp := ivp) (T := T) (a := a) (L := L)
      (Kpic := Kpic) (Kstate := Kstate))
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := F) (H := H) (I := I) (M := M) ivp)
    (hinner : G.PullbackMetricInnerDerivativeData) :
    EndpointGeometricGaugeFlowData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      (ivp := ivp) (T := T) (a := a) (L := L)
      (Kpic := Kpic) (Kstate := Kstate) :=
  D.withGaugeFlowExistence G (fun sol => by
    simpa using G.hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData hinner sol)

/-- Replace the geometric gauge-flow component of fixed-IVP endpoint data by a
raw `C^3` diffeomorphism-flow existence witness carrying coordinate-level
scalar pullback-metric derivative data. -/
def EndpointGeometricGaugeFlowData.withGaugeFlowExistenceCoordinatePullbackMetricInnerDerivative
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (D : EndpointGeometricGaugeFlowData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      (ivp := ivp) (T := T) (a := a) (L := L)
      (Kpic := Kpic) (Kstate := Kstate))
    (G : IntrinsicDeTurckGaugeFlowExistence
      (E := F) (H := H) (I := I) (M := M) ivp)
    (hcoord : G.CoordinatePullbackMetricInnerDerivativeData) :
    EndpointGeometricGaugeFlowData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      (ivp := ivp) (T := T) (a := a) (L := L)
      (Kpic := Kpic) (Kstate := Kstate) :=
  D.withGaugeFlowExistencePullbackMetricInnerDerivative G
    (G.pullbackMetricInnerDerivativeData_of_coordinate hcoord)

/-- Bundled global endpoint data whose non-identity gauge input is a geometric
`C^3` intrinsic DeTurck gauge-flow family. -/
structure EndpointGeometricGaugeFlowFamilyData
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
  gaugeFlow : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
    (E := F) (H := H) (I := I) (M := M)
  hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((gaugeFlow.maps3 ivp sol).pullbackMetricFamily
          sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          (gaugeFlow.gauge ivp sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet

namespace EndpointGeometricGaugeFlowFamilyData

/-- Restrict global geometric endpoint gauge-flow family data to a fixed initial
value problem. -/
def forInitialValueProblem
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
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover))
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)) :
    EndpointGeometricGaugeFlowData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      (ivp := ivp) (T := D.T ivp) (a := D.a ivp) (L := D.L ivp)
      (Kpic := D.Kpic ivp) (Kstate := D.Kstate ivp) where
  chart := D.chart ivp
  metric := D.metric ivp
  background := D.background ivp
  metric_eq_curve := D.metric_eq_curve ivp
  initial_hasTimeDerivative := D.initial_hasTimeDerivative ivp
  terminal_hasTimeDerivative := D.terminal_hasTimeDerivative ivp
  chartRHS_eq_intrinsic := D.chartRHS_eq_intrinsic ivp
  hbackground := D.hbackground ivp
  encode := D.encode ivp
  gaugeFlow := D.gaugeFlow.forInitialValueProblem ivp
  hpullDerivative := D.hpullDerivative ivp

end EndpointGeometricGaugeFlowFamilyData

/-- Replace the geometric gauge-flow component of global endpoint family data by
a raw theorem-family `C^3` diffeomorphism-flow existence witness. -/
def EndpointGeometricGaugeFlowFamilyData.withGaugeFlowExistence
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
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := F) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol).pullbackMetricFamily
            sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) where
  T := D.T
  a := D.a
  L := D.L
  Kpic := D.Kpic
  Kstate := D.Kstate
  chart := D.chart
  metric := D.metric
  background := D.background
  metric_eq_curve := D.metric_eq_curve
  initial_hasTimeDerivative := D.initial_hasTimeDerivative
  terminal_hasTimeDerivative := D.terminal_hasTimeDerivative
  chartRHS_eq_intrinsic := D.chartRHS_eq_intrinsic
  hbackground := D.hbackground
  encode := D.encode
  gaugeFlow := G.toDiffeomorph3GaugeFlowFamily
  hpullDerivative := hpullDerivative

/-- Replace the geometric gauge-flow component of global endpoint family data by
a raw theorem-family `C^3` diffeomorphism-flow existence witness carrying named
scalar pullback-metric derivative data. -/
def EndpointGeometricGaugeFlowFamilyData.withGaugeFlowExistencePullbackMetricInnerDerivative
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
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := F) (H := H) (I := I) (M := M))
    (hinner : G.PullbackMetricInnerDerivativeData) :
    EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) :=
  D.withGaugeFlowExistence G (fun ivp sol => by
    simpa using G.hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData hinner ivp sol)

/-- Replace the geometric gauge-flow component of global endpoint family data by
a raw theorem-family `C^3` diffeomorphism-flow existence witness carrying
coordinate-level scalar pullback-metric derivative data. -/
def EndpointGeometricGaugeFlowFamilyData.withGaugeFlowExistenceCoordinatePullbackMetricInnerDerivative
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
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := F) (H := H) (I := I) (M := M))
    (hcoord : G.CoordinatePullbackMetricInnerDerivativeData) :
    EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) :=
  D.withGaugeFlowExistencePullbackMetricInnerDerivative G
    (G.pullbackMetricInnerDerivativeData_of_coordinate hcoord)

/-- Replace the geometric gauge-flow component by the canonical identity `C³` flow available for
chosen-background intrinsic DeTurck solutions. -/
noncomputable def EndpointGeometricGaugeFlowFamilyData.withChosenBackgroundIdentityGaugeFlow
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
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) :=
  D.withGaugeFlowExistence
    (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfChosenBackground
      (E := F) (H := H) (I := I) (M := M))
    (fun ivp sol ↦
      IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfChosenBackground_hpullDerivative
        (E := F) (H := H) (I := I) (M := M) ivp sol)

/-- Convert geometric global endpoint gauge-flow data to the derivative-level
endpoint bundle. -/
def EndpointGeometricGaugeFlowFamilyData.toEndpointDerivativeGaugeFlowFamilyData
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
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    EndpointDerivativeGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) where
  T := D.T
  a := D.a
  L := D.L
  Kpic := D.Kpic
  Kstate := D.Kstate
  chart := D.chart
  metric := D.metric
  background := D.background
  metric_eq_curve := D.metric_eq_curve
  initial_hasTimeDerivative := D.initial_hasTimeDerivative
  terminal_hasTimeDerivative := D.terminal_hasTimeDerivative
  chartRHS_eq_intrinsic := D.chartRHS_eq_intrinsic
  hbackground := D.hbackground
  encode := D.encode
  maps3 := D.gaugeFlow.maps3
  anchored := D.gaugeFlow.anchored
  hflowDeriv := D.gaugeFlow.derivativeFamily
  hderiv := by
    intro ivp sol t ht x u v
    simpa using
      D.gaugeFlow.innerHasDerivAt_of_hasTimeDerivativeOn
        D.hpullDerivative ivp sol ht x u v

/-- Geometric global endpoint gauge-flow data yields the scalar-derivative
gauge-reducible theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyData.toInnerDerivativeGaugeReducibleFamily
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
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  D.toEndpointDerivativeGaugeFlowFamilyData.toInnerDerivativeGaugeReducibleFamily

/-- Geometric global endpoint gauge-flow data yields the chosen-background
Ricci-DeTurck theorem family before gauge reduction. -/
theorem EndpointGeometricGaugeFlowFamilyData.toChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
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
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (D.forInitialValueProblem ivp).toChosenIntrinsicDeTurckLocalExistenceUniqueness

/-- Geometric global endpoint gauge-flow data projects to the gauge-reducible
Ricci-flow theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyData.toGaugeReducibleFamily
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
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toGaugeReducible

/-- Geometric global endpoint gauge-flow data projects to the compact intrinsic
Ricci-flow theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyData.toIntrinsicLocalExistenceUniquenessFamily
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
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toIntrinsicFamily

/-- Geometric global endpoint gauge-flow data projects to the ordinary compact
Ricci-flow theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyData.toLocalExistenceUniquenessFamily
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
    (D : EndpointGeometricGaugeFlowFamilyData (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toOrdinaryFamily

/-- Bundled interval endpoint data whose non-identity gauge input is a geometric
`C^3` intrinsic DeTurck gauge-flow family. -/
structure EndpointGeometricGaugeFlowFamilyDataOnIcc
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
  gaugeFlow : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
    (E := F) (H := H) (I := I) (M := M)
  hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((gaugeFlow.maps3 ivp sol).pullbackMetricFamily
          sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          (gaugeFlow.gauge ivp sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Replace the geometric gauge-flow component of interval endpoint family data by
a raw theorem-family `C^3` diffeomorphism-flow existence witness. -/
def EndpointGeometricGaugeFlowFamilyDataOnIcc.withGaugeFlowExistence
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
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := F) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          (((G.toDiffeomorph3GaugeFlowFamily).maps3 ivp sol).pullbackMetricFamily
            sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            ((G.toDiffeomorph3GaugeFlowFamily).gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) where
  T := D.T
  a := D.a
  L := D.L
  Kpic := D.Kpic
  Kstate := D.Kstate
  chart := D.chart
  metric := D.metric
  background := D.background
  metric_eq_curve := D.metric_eq_curve
  initial_hasTimeDerivative := D.initial_hasTimeDerivative
  terminal_hasTimeDerivative := D.terminal_hasTimeDerivative
  chartRHS_eq_intrinsic := D.chartRHS_eq_intrinsic
  hbackground := D.hbackground
  encode := D.encode
  gaugeFlow := G.toDiffeomorph3GaugeFlowFamily
  hpullDerivative := hpullDerivative

/-- Replace the geometric gauge-flow component of interval endpoint family data by
a raw theorem-family `C^3` diffeomorphism-flow existence witness carrying named
scalar pullback-metric derivative data. -/
def EndpointGeometricGaugeFlowFamilyDataOnIcc.withGaugeFlowExistencePullbackMetricInnerDerivative
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
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := F) (H := H) (I := I) (M := M))
    (hinner : G.PullbackMetricInnerDerivativeData) :
    EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) :=
  D.withGaugeFlowExistence G (fun ivp sol => by
    simpa using G.hasTimeDerivativeOn_of_pullbackMetricInnerDerivativeData hinner ivp sol)

/-- Replace the geometric gauge-flow component of interval endpoint family data by
a raw theorem-family `C^3` diffeomorphism-flow existence witness carrying
coordinate-level scalar pullback-metric derivative data. -/
def EndpointGeometricGaugeFlowFamilyDataOnIcc.withGaugeFlowExistenceCoordinatePullbackMetricInnerDerivative
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
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover))
    (G : IntrinsicDeTurckGaugeFlowExistenceFamily
      (E := F) (H := H) (I := I) (M := M))
    (hcoord : G.CoordinatePullbackMetricInnerDerivativeData) :
    EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) :=
  D.withGaugeFlowExistencePullbackMetricInnerDerivative G
    (G.pullbackMetricInnerDerivativeData_of_coordinate hcoord)

/-- Replace the interval endpoint geometric gauge-flow component by the canonical identity `C³`
flow available for chosen-background intrinsic DeTurck solutions. -/
noncomputable def EndpointGeometricGaugeFlowFamilyDataOnIcc.withChosenBackgroundIdentityGaugeFlow
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
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) :=
  D.withGaugeFlowExistence
    (IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfChosenBackground
      (E := F) (H := H) (I := I) (M := M))
    (fun ivp sol ↦
      IntrinsicDeTurckGaugeFlowExistenceFamily.identityOfChosenBackground_hpullDerivative
        (E := F) (H := H) (I := I) (M := M) ivp sol)

/-- Convert geometric interval endpoint gauge-flow data to the derivative-level
endpoint bundle. -/
def EndpointGeometricGaugeFlowFamilyDataOnIcc.toEndpointDerivativeGaugeFlowFamilyDataOnIcc
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
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    EndpointDerivativeGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) where
  T := D.T
  a := D.a
  L := D.L
  Kpic := D.Kpic
  Kstate := D.Kstate
  chart := D.chart
  metric := D.metric
  background := D.background
  metric_eq_curve := D.metric_eq_curve
  initial_hasTimeDerivative := D.initial_hasTimeDerivative
  terminal_hasTimeDerivative := D.terminal_hasTimeDerivative
  chartRHS_eq_intrinsic := D.chartRHS_eq_intrinsic
  hbackground := D.hbackground
  encode := D.encode
  maps3 := D.gaugeFlow.maps3
  anchored := D.gaugeFlow.anchored
  hflowDeriv := D.gaugeFlow.derivativeFamily
  hderiv := by
    intro ivp sol t ht x u v
    simpa using
      D.gaugeFlow.innerHasDerivAt_of_hasTimeDerivativeOn
        D.hpullDerivative ivp sol ht x u v

/-- Geometric interval endpoint gauge-flow data yields the scalar-derivative
gauge-reducible theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyDataOnIcc.toInnerDerivativeGaugeReducibleFamily
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
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    InnerDerivativeGaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  D.toEndpointDerivativeGaugeFlowFamilyDataOnIcc.toInnerDerivativeGaugeReducibleFamily

/-- Geometric interval endpoint gauge-flow data yields the chosen-background
Ricci-DeTurck theorem family before gauge reduction. -/
theorem EndpointGeometricGaugeFlowFamilyDataOnIcc.toChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
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
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    (D.toInnerDerivativeGaugeReducibleFamily.package ivp).chosen_package

/-- Geometric interval endpoint gauge-flow data projects to the gauge-reducible
Ricci-flow theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyDataOnIcc.toGaugeReducibleFamily
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
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toGaugeReducible

/-- Geometric interval endpoint gauge-flow data projects to the compact intrinsic
Ricci-flow theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyDataOnIcc.toIntrinsicLocalExistenceUniquenessFamily
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
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toIntrinsicFamily

/-- Geometric interval endpoint gauge-flow data projects to the ordinary compact
Ricci-flow theorem family. -/
theorem EndpointGeometricGaugeFlowFamilyDataOnIcc.toLocalExistenceUniquenessFamily
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
    (D : EndpointGeometricGaugeFlowFamilyDataOnIcc (I := I)
      (x0 := x0) (et := et) (het := het) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) :=
  D.toInnerDerivativeGaugeReducibleFamily.toOrdinaryFamily

end MetricLocusEvolution
end AnalyticPDE
end RicciFlow
