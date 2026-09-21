/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothRealizationGaugeRoutes
/-!
# Metric-cone handoffs for smooth Ricci-DeTurck realization routes

This module keeps the heavy gauge-route layer unchanged and packages one more proof-level handoff:
positive-radius ambient interval closure data selects the standard metric-cone shrink, and the
existing terminal-fit compatibility for reverse encodings then produces the genuine symmetric-carrier
closure datum together with the chosen-background, intrinsic, and ordinary theorem packages.
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

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)

local instance metricConeRoutesBilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))

local instance metricConeRoutesBilFNormedSpace : NormedSpace ℝ BilF :=
  (inferInstance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ))

section GlobalClosure

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
variable [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
variable [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
variable [IsManifold I (minSmoothness ℝ 3) M]
variable [IsManifold I ((2 : ℕ∞) + 1) M]
variable [CompleteSpace F]
variable {κ : Type*} [Finite κ] [T2Space M]
variable [FiniteDimensional ℝ F] [Nontrivial F]

/-- A positive-radius ambient interval closure package selects the standard metric-cone shrink and,
once reverse-encoded candidates are known to fit in that selected interval, produces both the
genuine symmetric-carrier closure datum and the chosen-background, intrinsic, and ordinary theorem
packages.  This is the fully bundled version of the metric-cone shrink handoff. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_symmetricCarrier_theoremPackages
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
      (ha' : a' ≤ a)
      (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0))
      (hball : Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover),
      0 < a' ∧
        ((∀ candidate : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp,
          (D.encode candidate).sol.terminalTime ≤ T') →
          let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime
          ∃ Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
            x0 et het Kc hKc Ko hKo hKoEq hcover chart',
            Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (IntrinsicLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (LocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp)) := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  refine ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos, ?_⟩
  intro hencode_terminal
  let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha'le htime
  let Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart' :=
    SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofShrunkRicciDeTurckChartClosureDataOnIcc
      (M := M) (F := F) (I := I) (D := D)
      hT' hT'le ha'le htime hball hencode_terminal
  refine ⟨Dsym, ?_, ?_, ?_⟩
  · exact ⟨Dsym.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩
  · exact ⟨Dsym.toIntrinsicLocalExistenceUniqueness⟩
  · exact ⟨Dsym.toLocalExistenceUniqueness⟩

/-- A positive-radius ambient interval closure package selects the standard metric-cone shrink and
returns the compact theorem packages without any terminal-fit hypothesis.  The terminal-fit
assumption is needed only for the stronger handoff to an actual shrunk symmetric-carrier closure
datum. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_theoremPackages_and_conditional_symmetricCarrier
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
      (ha' : a' ≤ a)
      (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0))
      (hball : Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover),
      0 < a' ∧
        Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
          (E := F) (H := H) (I := I) (M := M) ivp) ∧
        Nonempty (IntrinsicLocalExistenceUniqueness
          (E := F) (H := H) (I := I) (M := M) ivp) ∧
        Nonempty (LocalExistenceUniqueness
          (E := F) (H := H) (I := I) (M := M) ivp) ∧
        ((∀ candidate : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp,
          (D.encode candidate).sol.terminalTime ≤ T') →
          let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime
          ∃ Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
            x0 et het Kc hKc Ko hKo hKoEq hcover chart',
            True) := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  refine
    ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos,
      ?_, ?_, ?_, ?_⟩
  · exact ⟨D.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩
  · exact ⟨D.toIntrinsicLocalExistenceUniqueness⟩
  · exact ⟨D.toLocalExistenceUniqueness⟩
  · intro hencode_terminal
    let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha'le htime
    refine ⟨?_, trivial⟩
    exact
      SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofShrunkRicciDeTurckChartClosureDataOnIcc
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime hball hencode_terminal

/-- A positive-radius ambient interval closure package also selects the standard metric-cone shrink
and gives the clipped local uniqueness readout on that shrink, without requiring full arbitrary
candidate intervals to fit inside the selected interval. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_localUniquenessReadout
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
      (ha' : a' ≤ a)
      (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0))
      (hball : Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover),
      0 < a' ∧
        ∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
          t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M)
              sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                metricTensor (I := I) (M := M)
                  sol₂.1.toIntrinsicDeTurckSolution.metric t x u v := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  refine ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos, ?_⟩
  intro sol₁ sol₂ t ht x u v
  exact
    RicciDeTurckChartClosureDataOnIcc.metric_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
      (M := M) (F := F) (I := I) (D := D)
      hT' hT'le ha'le htime sol₁ sol₂ ht x u v

/-- A positive-radius ambient interval closure package also selects the standard metric-cone shrink
and gives the clipped local connection-uniqueness readout on that shrink. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_localConnectionReadout
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
      (ha' : a' ≤ a)
      (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0))
      (hball : Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover),
      0 < a' ∧
        ∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
          t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
          ∀ {x : M} {σ : Π y : M, TangentSpace I y},
            MDiffAt (T% σ) x →
            sol₁.1.canonicalConnection
              (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
              sol₂.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                t σ x := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  refine ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos, ?_⟩
  intro sol₁ sol₂ t ht x σ hσ
  exact
    RicciDeTurckChartClosureDataOnIcc.connection_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
      (M := M) (F := F) (I := I) (D := D)
      hT' hT'le ha'le htime sol₁ sol₂ ht hσ

/-- A positive-radius ambient interval closure package selects one standard metric-cone shrink
and gives both clipped local metric and connection uniqueness readouts on that same shrink. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_localMetricConnectionReadout
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
      (ha' : a' ≤ a)
      (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0))
      (hball : Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover),
      0 < a' ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
          t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M)
              sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                metricTensor (I := I) (M := M)
                  sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
          t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
          ∀ {x : M} {σ : Π y : M, TangentSpace I y},
            MDiffAt (T% σ) x →
            sol₁.1.canonicalConnection
              (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
              sol₂.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                t σ x) := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  refine ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos, ?_, ?_⟩
  · intro sol₁ sol₂ t ht x u v
    exact
      RicciDeTurckChartClosureDataOnIcc.metric_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ ht x u v
  · intro sol₁ sol₂ t ht x σ hσ
    exact
      RicciDeTurckChartClosureDataOnIcc.connection_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ ht hσ

/-- A positive-radius ambient interval closure package selects one standard
metric-cone shrink and gives local metric/connection uniqueness on every
prescribed shorter terminal `S` visible inside that shrink.  This avoids baking
the clipped `min (min T₁ T₂) T'` endpoint into continuation arguments. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_localRestrictedMetricConnectionReadout
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
      (ha' : a' ≤ a)
      (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0))
      (hball : Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover),
      0 < a' ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {S : ℝ},
          ivp.initialTime < S → S ≤ sol₁.1.terminalTime →
          S ≤ sol₂.1.terminalTime → S ≤ T' → ∀ {t : ℝ},
          t ∈ Icc ivp.initialTime S → ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M)
              sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                metricTensor (I := I) (M := M)
                  sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {S : ℝ},
          ivp.initialTime < S → S ≤ sol₁.1.terminalTime →
          S ≤ sol₂.1.terminalTime → S ≤ T' → ∀ {t : ℝ},
          t ∈ Icc ivp.initialTime S →
          ∀ {x : M} {σ : Π y : M, TangentSpace I y},
            MDiffAt (T% σ) x →
            sol₁.1.canonicalConnection
              (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
              sol₂.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                t σ x) := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  refine ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos, ?_, ?_⟩
  · intro sol₁ sol₂ S hS₀ hS₁ hS₂ hST' t ht x u v
    exact
      RicciDeTurckChartClosureDataOnIcc.metric_eq_on_restricted_interval_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ hS₀ hS₁ hS₂ hST' ht x u v
  · intro sol₁ sol₂ S hS₀ hS₁ hS₂ hST' t ht x σ hσ
    exact
      RicciDeTurckChartClosureDataOnIcc.connection_eq_on_restricted_interval_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ hS₀ hS₁ hS₂ hST' ht hσ

/-- A positive-radius ambient interval closure package selects one standard
metric-cone shrink and gives both clipped local metric/connection uniqueness
readouts, plus full-common-interval readouts when the selected shrink contains
the common candidate terminal. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_localMetricConnectionReadout_with_fullCommon
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
      (ha' : a' ≤ a)
      (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0))
      (hball : Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover),
      0 < a' ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
          t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M)
              sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                metricTensor (I := I) (M := M)
                  sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
          t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
          ∀ {x : M} {σ : Π y : M, TangentSpace I y},
            MDiffAt (T% σ) x →
            sol₁.1.canonicalConnection
              (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
              sol₂.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                t σ x) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp),
          min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T' → ∀ {t : ℝ},
          t ∈ Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M)
              sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                metricTensor (I := I) (M := M)
                  sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp),
          min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T' → ∀ {t : ℝ},
          t ∈ Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime) →
          ∀ {x : M} {σ : Π y : M, TangentSpace I y},
            MDiffAt (T% σ) x →
            sol₁.1.canonicalConnection
              (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
              sol₂.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                t σ x) := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  refine ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos, ?_, ?_, ?_, ?_⟩
  · intro sol₁ sol₂ t ht x u v
    exact
      RicciDeTurckChartClosureDataOnIcc.metric_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ ht x u v
  · intro sol₁ sol₂ t ht x σ hσ
    exact
      RicciDeTurckChartClosureDataOnIcc.connection_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ ht hσ
  · intro sol₁ sol₂ hcommonT t ht x u v
    have htclip :
        t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') := by
      simpa [min_eq_left hcommonT] using ht
    exact
      RicciDeTurckChartClosureDataOnIcc.metric_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ htclip x u v
  · intro sol₁ sol₂ hcommonT t ht x σ hσ
    have htclip :
        t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') := by
      simpa [min_eq_left hcommonT] using ht
    exact
      RicciDeTurckChartClosureDataOnIcc.connection_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ htclip hσ

/-- A positive-radius ambient interval closure package selects one standard metric-cone shrink and
returns both closure-theorem-package consequences, conditional on terminal fit, and the clipped
local metric/connection uniqueness readouts, which do not require terminal fit. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_theoremPackages_localMetricConnectionReadout
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
      (ha' : a' ≤ a)
      (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0))
      (hball : Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover),
      0 < a' ∧
        (((∀ candidate : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp,
          (D.encode candidate).sol.terminalTime ≤ T') →
          let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime
          ∃ Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
            x0 et het Kc hKc Ko hKo hKoEq hcover chart',
            Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (IntrinsicLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (LocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp)) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
          t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M)
              sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                metricTensor (I := I) (M := M)
                  sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
          t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
          ∀ {x : M} {σ : Π y : M, TangentSpace I y},
            MDiffAt (T% σ) x →
            sol₁.1.canonicalConnection
              (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
              sol₂.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                t σ x)) := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  refine ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos, ?_, ?_, ?_⟩
  · intro hencode_terminal
    let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha'le htime
    let Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
        x0 et het Kc hKc Ko hKo hKoEq hcover chart' :=
      SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofShrunkRicciDeTurckChartClosureDataOnIcc
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime hball hencode_terminal
    refine ⟨Dsym, ?_, ?_, ?_⟩
    · exact ⟨Dsym.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩
    · exact ⟨Dsym.toIntrinsicLocalExistenceUniqueness⟩
    · exact ⟨Dsym.toLocalExistenceUniqueness⟩
  · intro sol₁ sol₂ t ht x u v
    exact
      RicciDeTurckChartClosureDataOnIcc.metric_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ ht x u v
  · intro sol₁ sol₂ t ht x σ hσ
    exact
      RicciDeTurckChartClosureDataOnIcc.connection_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ ht hσ

/-- A positive-radius ambient interval closure package selects one standard
metric-cone shrink and returns both the terminal-fit theorem-package handoff
and the prescribed-terminal metric/connection uniqueness readouts on that same
selected shrink.

This is the continuation-oriented companion to
`exists_metricCone_shrunk_theoremPackages_localMetricConnectionReadout`: callers
can choose any shorter terminal `S` visible inside both candidates and the
selected shrink instead of using the clipped `min (min T₁ T₂) T'` endpoint. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_theoremPackages_localRestrictedMetricConnectionReadout
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
      (ha' : a' ≤ a)
      (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0))
      (hball : Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover),
      0 < a' ∧
        (((∀ candidate : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp,
          (D.encode candidate).sol.terminalTime ≤ T') →
          let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime
          ∃ Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
            x0 et het Kc hKc Ko hKo hKoEq hcover chart',
            Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (IntrinsicLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (LocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp)) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {S : ℝ},
          ivp.initialTime < S → S ≤ sol₁.1.terminalTime →
          S ≤ sol₂.1.terminalTime → S ≤ T' → ∀ {t : ℝ},
          t ∈ Icc ivp.initialTime S → ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M)
              sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                metricTensor (I := I) (M := M)
                  sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {S : ℝ},
          ivp.initialTime < S → S ≤ sol₁.1.terminalTime →
          S ≤ sol₂.1.terminalTime → S ≤ T' → ∀ {t : ℝ},
          t ∈ Icc ivp.initialTime S →
          ∀ {x : M} {σ : Π y : M, TangentSpace I y},
            MDiffAt (T% σ) x →
            sol₁.1.canonicalConnection
              (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
              sol₂.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                t σ x)) := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  refine ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos, ?_, ?_, ?_⟩
  · intro hencode_terminal
    let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha'le htime
    let Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
        x0 et het Kc hKc Ko hKo hKoEq hcover chart' :=
      SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofShrunkRicciDeTurckChartClosureDataOnIcc
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime hball hencode_terminal
    refine ⟨Dsym, ?_, ?_, ?_⟩
    · exact ⟨Dsym.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩
    · exact ⟨Dsym.toIntrinsicLocalExistenceUniqueness⟩
    · exact ⟨Dsym.toLocalExistenceUniqueness⟩
  · intro sol₁ sol₂ S hS₀ hS₁ hS₂ hST' t ht x u v
    exact
      RicciDeTurckChartClosureDataOnIcc.metric_eq_on_restricted_interval_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ hS₀ hS₁ hS₂ hST' ht x u v
  · intro sol₁ sol₂ S hS₀ hS₁ hS₂ hST' t ht x σ hσ
    exact
      RicciDeTurckChartClosureDataOnIcc.connection_eq_on_restricted_interval_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ hS₀ hS₁ hS₂ hST' ht hσ

/-- A continuation-oriented metric-cone handoff that keeps all readouts tied to
one selected shrink: terminal-fit theorem packages, prescribed shorter-terminal
metric/connection uniqueness, and full-common-interval metric/connection
uniqueness whenever the selected shrink contains the common candidate terminal. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_theoremPackages_localRestrictedMetricConnectionReadout_with_fullCommon
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
      (ha' : a' ≤ a)
      (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0))
      (hball : Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover),
      0 < a' ∧
        (((∀ candidate : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp,
          (D.encode candidate).sol.terminalTime ≤ T') →
          let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime
          ∃ Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
            x0 et het Kc hKc Ko hKo hKoEq hcover chart',
            Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (IntrinsicLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (LocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp)) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {S : ℝ},
          ivp.initialTime < S → S ≤ sol₁.1.terminalTime →
          S ≤ sol₂.1.terminalTime → S ≤ T' → ∀ {t : ℝ},
          t ∈ Icc ivp.initialTime S → ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M)
              sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                metricTensor (I := I) (M := M)
                  sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {S : ℝ},
          ivp.initialTime < S → S ≤ sol₁.1.terminalTime →
          S ≤ sol₂.1.terminalTime → S ≤ T' → ∀ {t : ℝ},
          t ∈ Icc ivp.initialTime S →
          ∀ {x : M} {σ : Π y : M, TangentSpace I y},
            MDiffAt (T% σ) x →
            sol₁.1.canonicalConnection
              (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
              sol₂.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                t σ x) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp),
          min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T' → ∀ {t : ℝ},
          t ∈ Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M)
              sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                metricTensor (I := I) (M := M)
                  sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp),
          min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T' → ∀ {t : ℝ},
          t ∈ Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime) →
          ∀ {x : M} {σ : Π y : M, TangentSpace I y},
            MDiffAt (T% σ) x →
            sol₁.1.canonicalConnection
              (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
              sol₂.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                t σ x)) := by
  rcases D.exists_metricCone_shrunk_theoremPackages_localRestrictedMetricConnectionReadout
      (M := M) (F := F) (I := I) ha with
    ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos,
      hpackages, hmetric, hconnection⟩
  refine
    ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos,
      hpackages, hmetric, hconnection, ?_, ?_⟩
  · intro sol₁ sol₂ hcommonT t ht x u v
    exact hmetric sol₁ sol₂
      (S := min sol₁.1.terminalTime sol₂.1.terminalTime)
      (lt_min sol₁.1.initial_lt_terminal sol₂.1.initial_lt_terminal)
      (min_le_left _ _) (min_le_right _ _) hcommonT ht x u v
  · intro sol₁ sol₂ hcommonT t ht x σ hσ
    exact hconnection sol₁ sol₂
      (S := min sol₁.1.terminalTime sol₂.1.terminalTime)
      (lt_min sol₁.1.initial_lt_terminal sol₂.1.initial_lt_terminal)
      (min_le_left _ _) (min_le_right _ _) hcommonT ht hσ

/-- A positive-radius ambient interval closure package selects one standard metric-cone shrink and
returns the terminal-fit theorem-package handoff, the clipped local metric/connection uniqueness
readouts, and the corresponding full-common-interval readouts when the selected shrink contains the
common candidate terminal. -/
theorem RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_theoremPackages_localMetricConnectionReadout_with_fullCommon
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
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
      (ha' : a' ≤ a)
      (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0))
      (hball : Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover),
      0 < a' ∧
        (((∀ candidate : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp,
          (D.encode candidate).sol.terminalTime ≤ T') →
          let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime
          ∃ Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
            x0 et het Kc hKc Ko hKo hKoEq hcover chart',
            Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (IntrinsicLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (LocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp)) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
          t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M)
              sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                metricTensor (I := I) (M := M)
                  sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
          t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
          ∀ {x : M} {σ : Π y : M, TangentSpace I y},
            MDiffAt (T% σ) x →
            sol₁.1.canonicalConnection
              (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
              sol₂.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                t σ x) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp),
          min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T' → ∀ {t : ℝ},
          t ∈ Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime) →
          ∀ (x : M) (u v : TangentSpace I x),
            metricTensor (I := I) (M := M)
              sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                metricTensor (I := I) (M := M)
                  sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
        (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp),
          min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T' → ∀ {t : ℝ},
          t ∈ Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime) →
          ∀ {x : M} {σ : Π y : M, TangentSpace I y},
            MDiffAt (T% σ) x →
            sol₁.1.canonicalConnection
              (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
              sol₂.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                t σ x)) := by
  rcases D.exists_metricCone_shrunk_theoremPackages_localMetricConnectionReadout
      (M := M) (F := F) (I := I) ha with
    ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos,
      hpackages, hmetric, hconnection⟩
  refine
    ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos,
      hpackages, hmetric, hconnection, ?_, ?_⟩
  · intro sol₁ sol₂ hcommonT t ht x u v
    have htclip :
        t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') := by
      simpa [min_eq_left hcommonT] using ht
    exact hmetric sol₁ sol₂ htclip x u v
  · intro sol₁ sol₂ hcommonT t ht x σ hσ
    have htclip :
        t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') := by
      simpa [min_eq_left hcommonT] using ht
    exact hconnection sol₁ sol₂ htclip hσ

end GlobalClosure

end MetricLocusEvolution
end AnalyticPDE
end RicciFlow
