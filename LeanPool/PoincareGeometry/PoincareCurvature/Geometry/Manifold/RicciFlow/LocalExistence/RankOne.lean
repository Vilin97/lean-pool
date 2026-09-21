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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.LocalExistence

/-!
# Rank-one stationary Ricci-flow consequences

This thin extension module keeps the rank-one local-existence consequences out of
the core point-4 boundary.  The mathematical input is that on tangent fibers of
real dimension at most one, the curvature tensor is alternating in two linearly
dependent slots, hence Ricci curvature vanishes.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

section Ordinary

/-- Under the rank-one tangent-fiber hypothesis, the Ricci tensor of any ordinary local solution
vanishes at every time and point. -/
theorem localSolution_ricciTensor_eq_zero_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciTensor (I := I) (M := M)
      sol.toSolution.metric sol.toSolution.connection sol.toSolution.hconnection t x u v = 0 :=
  ricciTensor_eq_zero_of_finrank_le_one
    (I := I) (M := M) hfin sol.toSolution.metric sol.toSolution.connection
    sol.toSolution.hconnection t x u v

/-- Model-space version of `localSolution_ricciTensor_eq_zero_of_finrank_le_one`. -/
theorem localSolution_ricciTensor_eq_zero_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciTensor (I := I) (M := M)
      sol.toSolution.metric sol.toSolution.connection sol.toSolution.hconnection t x u v = 0 :=
  localSolution_ricciTensor_eq_zero_of_finrank_le_one
    (I := I) (M := M) (fun y ↦ tangent_finrank_le_one_of_model (I := I) (M := M) y)
    sol t x u v

/-- Under the rank-one tangent-fiber hypothesis, every ordinary local solution has zero metric
velocity on its local interval. -/
theorem localSolution_metricVelocity_eq_zero_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    sol.toSolution.metricVelocity t x u v = 0 :=
  localSolution_metricVelocity_eq_zero_of_ricciTensor_eq_zero
    (I := I) (M := M) sol ht
    (localSolution_ricciTensor_eq_zero_of_finrank_le_one
      (I := I) (M := M) hfin sol t x u v)

/-- Model-space version of `localSolution_metricVelocity_eq_zero_of_finrank_le_one`. -/
theorem localSolution_metricVelocity_eq_zero_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    sol.toSolution.metricVelocity t x u v = 0 :=
  localSolution_metricVelocity_eq_zero_of_finrank_le_one
    (I := I) (M := M) (fun y ↦ tangent_finrank_le_one_of_model (I := I) (M := M) y)
    sol ht x u v

/-- Under the rank-one tangent-fiber hypothesis, every ordinary local solution is stationary in
metric tensor components on its local interval. -/
theorem localSolution_metric_eq_initial_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toSolution.metric t x u v =
      ivp.initialMetric.inner x u v :=
  localSolution_metric_eq_initial_of_ricciTensor_zero
    (I := I) (M := M) sol
    (fun τ _hτ y a b =>
      localSolution_ricciTensor_eq_zero_of_finrank_le_one
        (I := I) (M := M) hfin sol τ y a b)
    ht x u v

/-- Model-space version of `localSolution_metric_eq_initial_of_finrank_le_one`. -/
theorem localSolution_metric_eq_initial_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toSolution.metric t x u v =
      ivp.initialMetric.inner x u v :=
  localSolution_metric_eq_initial_of_finrank_le_one
    (I := I) (M := M) (fun y ↦ tangent_finrank_le_one_of_model (I := I) (M := M) y)
    sol ht x u v

/-- Under the rank-one tangent-fiber hypothesis, every ordinary local solution keeps its initial
Levi-Civita connection on its local interval. -/
theorem localSolution_connection_eq_initial_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toSolution.connection t σ x =
      sol.toSolution.connection ivp.initialTime σ x :=
  localSolution_connection_eq_initial_of_ricciTensor_zero
    (I := I) (M := M) sol
    (fun τ _hτ y a b =>
      localSolution_ricciTensor_eq_zero_of_finrank_le_one
        (I := I) (M := M) hfin sol τ y a b)
    ht hσ

/-- Model-space version of `localSolution_connection_eq_initial_of_finrank_le_one`. -/
theorem localSolution_connection_eq_initial_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toSolution.connection t σ x =
      sol.toSolution.connection ivp.initialTime σ x :=
  localSolution_connection_eq_initial_of_finrank_le_one
    (I := I) (M := M) (fun y ↦ tangent_finrank_le_one_of_model (I := I) (M := M) y)
    sol ht hσ

/-- Under the rank-one tangent-fiber hypothesis, any two ordinary local solutions have the same
metric tensor on their common initial interval. -/
theorem localSolution_unique_metric_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toSolution.metric t x u v :=
  localSolution_unique_metric_of_ricciTensor_zero
    (I := I) (M := M) sol₁ sol₂
    (fun τ _hτ y a b =>
      localSolution_ricciTensor_eq_zero_of_finrank_le_one
        (I := I) (M := M) hfin sol₁ τ y a b)
    (fun τ _hτ y a b =>
      localSolution_ricciTensor_eq_zero_of_finrank_le_one
        (I := I) (M := M) hfin sol₂ τ y a b)
    ht x u v

/-- Model-space version of `localSolution_unique_metric_of_finrank_le_one`. -/
theorem localSolution_unique_metric_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toSolution.metric t x u v :=
  localSolution_unique_metric_of_finrank_le_one
    (I := I) (M := M) (fun y ↦ tangent_finrank_le_one_of_model (I := I) (M := M) y)
    sol₁ sol₂ ht x u v

/-- Under the rank-one tangent-fiber hypothesis, any two ordinary local solutions have the same
Levi-Civita connection on their common initial interval. -/
theorem localSolution_unique_connection_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toSolution.connection t σ x = sol₂.toSolution.connection t σ x :=
  localSolution_unique_connection_of_ricciTensor_zero
    (I := I) (M := M) sol₁ sol₂
    (fun τ _hτ y a b =>
      localSolution_ricciTensor_eq_zero_of_finrank_le_one
        (I := I) (M := M) hfin sol₁ τ y a b)
    (fun τ _hτ y a b =>
      localSolution_ricciTensor_eq_zero_of_finrank_le_one
        (I := I) (M := M) hfin sol₂ τ y a b)
    ht hσ

/-- Model-space version of `localSolution_unique_connection_of_finrank_le_one`. -/
theorem localSolution_unique_connection_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toSolution.connection t σ x = sol₂.toSolution.connection t σ x :=
  localSolution_unique_connection_of_finrank_le_one
    (I := I) (M := M) (fun y ↦ tangent_finrank_le_one_of_model (I := I) (M := M) y)
    sol₁ sol₂ ht hσ

end Ordinary

section Intrinsic

variable [SigmaCompactSpace M]

/-- Under the rank-one tangent-fiber hypothesis, the intrinsic Ricci tensor of any intrinsic local
solution vanishes at every time and point. -/
theorem intrinsicLocalSolution_ricciTensor_eq_zero_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0 :=
  intrinsicRicciTensor_eq_zero_of_finrank_le_one
    (I := I) (M := M) hfin sol.toIntrinsicSolution.metric t x u v

/-- Model-space version of `intrinsicLocalSolution_ricciTensor_eq_zero_of_finrank_le_one`. -/
theorem intrinsicLocalSolution_ricciTensor_eq_zero_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0 :=
  intrinsicLocalSolution_ricciTensor_eq_zero_of_finrank_le_one
    (I := I) (M := M) (fun y ↦ tangent_finrank_le_one_of_model (I := I) (M := M) y)
    sol t x u v

/-- Under the rank-one tangent-fiber hypothesis, every intrinsic local solution has zero metric
velocity on its local interval. -/
theorem intrinsicLocalSolution_metricVelocity_eq_zero_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    sol.toIntrinsicSolution.metricVelocity t x u v = 0 :=
  intrinsicLocalSolution_metricVelocity_eq_zero_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) sol ht
    (intrinsicLocalSolution_ricciTensor_eq_zero_of_finrank_le_one
      (I := I) (M := M) hfin sol t x u v)

/-- Model-space version of `intrinsicLocalSolution_metricVelocity_eq_zero_of_finrank_le_one`. -/
theorem intrinsicLocalSolution_metricVelocity_eq_zero_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    sol.toIntrinsicSolution.metricVelocity t x u v = 0 :=
  intrinsicLocalSolution_metricVelocity_eq_zero_of_finrank_le_one
    (I := I) (M := M) (fun y ↦ tangent_finrank_le_one_of_model (I := I) (M := M) y)
    sol ht x u v

/-- Under the rank-one tangent-fiber hypothesis, every intrinsic local solution is stationary in
metric tensor components on its local interval. -/
theorem intrinsicLocalSolution_metric_eq_initial_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v =
      ivp.initialMetric.inner x u v :=
  intrinsicLocalSolution_metric_eq_initial_of_ricciTensor_zero
    (I := I) (M := M) sol
    (fun τ _hτ y a b =>
      intrinsicLocalSolution_ricciTensor_eq_zero_of_finrank_le_one
        (I := I) (M := M) hfin sol τ y a b)
    ht x u v

/-- Model-space version of `intrinsicLocalSolution_metric_eq_initial_of_finrank_le_one`. -/
theorem intrinsicLocalSolution_metric_eq_initial_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v =
      ivp.initialMetric.inner x u v :=
  intrinsicLocalSolution_metric_eq_initial_of_finrank_le_one
    (I := I) (M := M) (fun y ↦ tangent_finrank_le_one_of_model (I := I) (M := M) y)
    sol ht x u v

/-- Under the rank-one tangent-fiber hypothesis, every intrinsic local solution keeps its initial
canonical Levi-Civita connection on its local interval. -/
theorem intrinsicLocalSolution_connection_eq_initial_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toIntrinsicSolution.toSolution.connection t σ x =
      sol.toIntrinsicSolution.toSolution.connection ivp.initialTime σ x :=
  intrinsicLocalSolution_connection_eq_initial_of_ricciTensor_zero
    (I := I) (M := M) sol
    (fun τ _hτ y a b =>
      intrinsicLocalSolution_ricciTensor_eq_zero_of_finrank_le_one
        (I := I) (M := M) hfin sol τ y a b)
    ht hσ

/-- Model-space version of `intrinsicLocalSolution_connection_eq_initial_of_finrank_le_one`. -/
theorem intrinsicLocalSolution_connection_eq_initial_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toIntrinsicSolution.toSolution.connection t σ x =
      sol.toIntrinsicSolution.toSolution.connection ivp.initialTime σ x :=
  intrinsicLocalSolution_connection_eq_initial_of_finrank_le_one
    (I := I) (M := M) (fun y ↦ tangent_finrank_le_one_of_model (I := I) (M := M) y)
    sol ht hσ

/-- Under the rank-one tangent-fiber hypothesis, any two intrinsic local solutions have the same
metric tensor on their common initial interval. -/
theorem intrinsicLocalSolution_unique_metric_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v :=
  intrinsicLocalSolution_unique_metric_of_ricciTensor_zero
    (I := I) (M := M) sol₁ sol₂
    (fun τ _hτ y a b =>
      intrinsicLocalSolution_ricciTensor_eq_zero_of_finrank_le_one
        (I := I) (M := M) hfin sol₁ τ y a b)
    (fun τ _hτ y a b =>
      intrinsicLocalSolution_ricciTensor_eq_zero_of_finrank_le_one
        (I := I) (M := M) hfin sol₂ τ y a b)
    ht x u v

/-- Model-space version of `intrinsicLocalSolution_unique_metric_of_finrank_le_one`. -/
theorem intrinsicLocalSolution_unique_metric_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v :=
  intrinsicLocalSolution_unique_metric_of_finrank_le_one
    (I := I) (M := M) (fun y ↦ tangent_finrank_le_one_of_model (I := I) (M := M) y)
    sol₁ sol₂ ht x u v

/-- Under the rank-one tangent-fiber hypothesis, any two intrinsic local solutions have the same
canonical Levi-Civita connection on their common initial interval. -/
theorem intrinsicLocalSolution_unique_connection_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toIntrinsicSolution.toSolution.connection t σ x =
      sol₂.toIntrinsicSolution.toSolution.connection t σ x :=
  intrinsicLocalSolution_unique_connection_of_ricciTensor_zero
    (I := I) (M := M) sol₁ sol₂
    (fun τ _hτ y a b =>
      intrinsicLocalSolution_ricciTensor_eq_zero_of_finrank_le_one
        (I := I) (M := M) hfin sol₁ τ y a b)
    (fun τ _hτ y a b =>
      intrinsicLocalSolution_ricciTensor_eq_zero_of_finrank_le_one
        (I := I) (M := M) hfin sol₂ τ y a b)
    ht hσ

/-- Model-space version of `intrinsicLocalSolution_unique_connection_of_finrank_le_one`. -/
theorem intrinsicLocalSolution_unique_connection_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toIntrinsicSolution.toSolution.connection t σ x =
      sol₂.toIntrinsicSolution.toSolution.connection t σ x :=
  intrinsicLocalSolution_unique_connection_of_finrank_le_one
    (I := I) (M := M) (fun y ↦ tangent_finrank_le_one_of_model (I := I) (M := M) y)
    sol₁ sol₂ ht hσ

end Intrinsic

end RicciFlow
