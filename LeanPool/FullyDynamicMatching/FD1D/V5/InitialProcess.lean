/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.V5.ContinuousProcess

/-! # Initial Process -/

namespace FD1D

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace V5.ContinuousProcess

variable {L m : ℕ}

/-! ## Spatial evolution from an arbitrary initial law -/

/-- The continuous spatial law after `t` policy steps, starting from `μ₀`. -/
def spatialLawFrom (μ₀ : Measure (SpatialState m))
    (a : ℝ) (fallback : Fin m) (t : ℕ) :
    Measure (SpatialState m) :=
  TrajectoryBridge.iterateLaw
    (spatialKernel (L := L) a fallback) μ₀ t

@[simp]
theorem spatialLawFrom_zero
    (μ₀ : Measure (SpatialState m)) (a : ℝ) (fallback : Fin m) :
    spatialLawFrom (L := L) μ₀ a fallback 0 = μ₀ :=
  rfl

@[simp]
theorem spatialLawFrom_succ
    (μ₀ : Measure (SpatialState m)) (a : ℝ)
    (fallback : Fin m) (t : ℕ) :
    spatialLawFrom (L := L) μ₀ a fallback (t + 1) =
      spatialKernel (L := L) a fallback ∘ₘ
        spatialLawFrom (L := L) μ₀ a fallback t :=
  rfl

instance spatialLawFrom.isProbabilityMeasure
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀]
    (a : ℝ) (fallback : Fin m) (t : ℕ) :
    IsProbabilityMeasure (spatialLawFrom (L := L) μ₀ a fallback t) := by
  induction t with
  | zero =>
      rw [spatialLawFrom_zero]
      infer_instance
  | succ t ih =>
      rw [spatialLawFrom_succ]
      infer_instance

private theorem comap_comp_measure_from
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (κ : Kernel β γ) (f : α → β) (hf : Measurable f)
    (μ : Measure α) :
    κ.comap f hf ∘ₘ μ = κ ∘ₘ Measure.map f μ := by
  rw [← Kernel.comp_deterministic_eq_comap κ hf]
  rw [← Measure.comp_assoc]
  rw [Measure.deterministic_comp_eq_map hf]

/--
If `μ₀` projects to the finite count law `ν₀`, every later spatial marginal
projects to the corresponding iterate of the finite count kernel.
-/
theorem map_spatialCount_spatialLawFrom
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀]
    (ν₀ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hμ₀ : Measure.map (spatialCount L) μ₀ = ν₀.toMeasure)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    Measure.map (spatialCount L)
        (spatialLawFrom (L := L) μ₀ a fallback t) =
      ((Dynamics.kernel
        (L := L) (m := m) a ha hm).iterate t ν₀).toMeasure := by
  induction t with
  | zero =>
      simpa using hμ₀
  | succ t ih =>
      rw [spatialLawFrom_succ]
      rw [Measure.map_comp _ _ (spatialCount_measurable L)]
      rw [spatialKernel_map_count a ha hm fallback]
      rw [comap_comp_measure_from]
      rw [ih]
      rw [FiniteKernel.toMeasure_step]
      rfl

/-! ## Joint process and trajectory laws -/

/-- Attach an independent first demand/replenishment pair to `μ₀`. -/
def initialProcessLawFrom (μ₀ : Measure (SpatialState m)) :
    Measure (ProcessState m) :=
  μ₀.prod noiseLaw

@[simp]
theorem initialProcessLawFrom_eq_product
    (μ₀ : Measure (SpatialState m)) :
    initialProcessLawFrom μ₀ = μ₀.prod noiseLaw :=
  rfl

instance initialProcessLawFrom.isProbabilityMeasure
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (initialProcessLawFrom μ₀) := by
  unfold initialProcessLawFrom
  infer_instance

/-- The joint process law at time `t`, starting from spatial law `μ₀`. -/
def processLawFrom (μ₀ : Measure (SpatialState m))
    (a : ℝ) (fallback : Fin m) (t : ℕ) :
    Measure (ProcessState m) :=
  TrajectoryBridge.iterateLaw
    (processKernel (L := L) a fallback) (initialProcessLawFrom μ₀) t

instance processLawFrom.isProbabilityMeasure
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀]
    (a : ℝ) (fallback : Fin m) (t : ℕ) :
    IsProbabilityMeasure (processLawFrom (L := L) μ₀ a fallback t) := by
  induction t with
  | zero =>
      rw [processLawFrom, TrajectoryBridge.iterateLaw_zero]
      infer_instance
  | succ t ih =>
      rw [processLawFrom, TrajectoryBridge.iterateLaw_succ]
      change IsProbabilityMeasure
        (processKernel (L := L) a fallback ∘ₘ
          processLawFrom (L := L) μ₀ a fallback t)
      infer_instance

/-- Current noise stays independent of the live inventory for every `μ₀`. -/
theorem processLawFrom_eq_product
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀]
    (a : ℝ) (fallback : Fin m) (t : ℕ) :
    processLawFrom (L := L) μ₀ a fallback t =
      (spatialLawFrom (L := L) μ₀ a fallback t).prod noiseLaw := by
  induction t with
  | zero =>
      rfl
  | succ t ih =>
      rw [processLawFrom, TrajectoryBridge.iterateLaw_succ]
      change
        processKernel (L := L) a fallback ∘ₘ
            processLawFrom (L := L) μ₀ a fallback t =
          (spatialLawFrom (L := L) μ₀ a fallback (t + 1)).prod noiseLaw
      rw [ih, processKernel_comp_product, spatialLawFrom_succ]

/-- One path-space law for the joint process initialized by `μ₀`. -/
def trajectoryLawFrom
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀]
    (a : ℝ) (fallback : Fin m) :
    Measure (ℕ → ProcessState m) :=
  TrajectoryBridge.trajectoryLaw
    (initialProcessLawFrom μ₀) (processKernel (L := L) a fallback)

instance trajectoryLawFrom.isProbabilityMeasure
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀]
    (a : ℝ) (fallback : Fin m) :
    IsProbabilityMeasure
      (trajectoryLawFrom (L := L) μ₀ a fallback) := by
  unfold trajectoryLawFrom TrajectoryBridge.trajectoryLaw
  infer_instance

/-- Each trajectory coordinate has the recursively iterated joint-state law. -/
theorem trajectoryLawFrom_marginal
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀]
    (a : ℝ) (fallback : Fin m) (t : ℕ) :
    Measure.map (fun path : ℕ → ProcessState m => path t)
        (trajectoryLawFrom (L := L) μ₀ a fallback) =
      processLawFrom (L := L) μ₀ a fallback t := by
  exact TrajectoryBridge.trajectoryLaw_marginal
    (initialProcessLawFrom μ₀) (processKernel (L := L) a fallback) t

/-- Every trajectory count coordinate has the corresponding finite iterate. -/
theorem trajectoryLawFrom_count_marginal
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀]
    (ν₀ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hμ₀ : Measure.map (spatialCount L) μ₀ = ν₀.toMeasure)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    Measure.map
        (fun path : ℕ → ProcessState m =>
          spatialCount L (path t).1)
        (trajectoryLawFrom (L := L) μ₀ a fallback) =
      ((Dynamics.kernel
        (L := L) (m := m) a ha hm).iterate t ν₀).toMeasure := by
  have hrewrite :
      Measure.map
          (fun path : ℕ → ProcessState m =>
            spatialCount L (path t).1)
          (trajectoryLawFrom (L := L) μ₀ a fallback) =
        Measure.map (spatialCount L)
          (Measure.map Prod.fst
            (Measure.map (fun path : ℕ → ProcessState m => path t)
              (trajectoryLawFrom (L := L) μ₀ a fallback))) := by
    symm
    rw [Measure.map_map (spatialCount_measurable L) measurable_fst]
    rw [Measure.map_map
      ((spatialCount_measurable L).comp measurable_fst)
      (measurable_pi_apply t)]
    rfl
  rw [hrewrite]
  rw [trajectoryLawFrom_marginal]
  rw [processLawFrom_eq_product]
  rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact map_spatialCount_spatialLawFrom μ₀ ν₀ hμ₀
    a ha hm fallback t

/-! ## One-period cost from an arbitrary initial law -/

/-- The configured-cost observable is integrable under each generalized spatial law. -/
theorem actualConfigurationSquaredCost_spatialLawFrom_integrable
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀]
    (a : ℝ) (hm : 0 < m) (fallback : Fin m) (t : ℕ) :
    Integrable
      (fun s : SpatialState m =>
        Dynamics.actualConfigurationSquaredCost
          a hm (toConfiguration L s))
      (spatialLawFrom (L := L) μ₀ a fallback t) := by
  have hprod :
      Integrable
        (processSquaredCost L a (SupplyConfiguration.canonicalFallback hm))
        ((spatialLawFrom (L := L) μ₀ a fallback t).prod noiseLaw) :=
    processSquaredCost_integrable L a
      (SupplyConfiguration.canonicalFallback hm) _
  have hinter := hprod.integral_prod_left
  simpa only [
    integral_processSquaredCost_noise_eq_actualConfigurationSquaredCost]
    using hinter

/-- Joint-state expected cost equals the generalized spatial configured-cost integral. -/
theorem integral_processSquaredCost_processLawFrom
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀]
    (a : ℝ) (hm : 0 < m) (fallback : Fin m) (t : ℕ) :
    (∫ z : ProcessState m,
        processSquaredCost L a (SupplyConfiguration.canonicalFallback hm) z
          ∂processLawFrom (L := L) μ₀ a fallback t) =
      ∫ s : SpatialState m,
        Dynamics.actualConfigurationSquaredCost
          a hm (toConfiguration L s)
          ∂spatialLawFrom (L := L) μ₀ a fallback t := by
  rw [processLawFrom_eq_product]
  have hprod :
      Integrable
        (processSquaredCost L a (SupplyConfiguration.canonicalFallback hm))
        ((spatialLawFrom (L := L) μ₀ a fallback t).prod noiseLaw) :=
    processSquaredCost_integrable L a
      (SupplyConfiguration.canonicalFallback hm) _
  rw [integral_prod _ hprod]
  apply integral_congr_ae
  filter_upwards with s
  exact
    integral_processSquaredCost_noise_eq_actualConfigurationSquaredCost
      L a hm s

/-- One-period cost on the generalized path-space law. -/
def trajectoryExpectedSquaredCostFrom
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀]
    (a : ℝ) (hm : 0 < m) (fallback : Fin m) (t : ℕ) : ℝ :=
  ∫ path : ℕ → ProcessState m,
    processSquaredCost L a (SupplyConfiguration.canonicalFallback hm) (path t)
      ∂trajectoryLawFrom (L := L) μ₀ a fallback

/-- Generalized trajectory cost equals the spatial configured-cost integral. -/
theorem trajectoryExpectedSquaredCostFrom_eq_spatial
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀]
    (a : ℝ) (hm : 0 < m) (fallback : Fin m) (t : ℕ) :
    trajectoryExpectedSquaredCostFrom (L := L) μ₀ a hm fallback t =
      ∫ s : SpatialState m,
        Dynamics.actualConfigurationSquaredCost
          a hm (toConfiguration L s)
          ∂spatialLawFrom (L := L) μ₀ a fallback t := by
  unfold trajectoryExpectedSquaredCostFrom
  calc
    (∫ path : ℕ → ProcessState m,
        processSquaredCost L a (SupplyConfiguration.canonicalFallback hm) (path t)
          ∂trajectoryLawFrom (L := L) μ₀ a fallback) =
        ∫ z : ProcessState m,
          processSquaredCost L a (SupplyConfiguration.canonicalFallback hm) z
            ∂Measure.map (fun path : ℕ → ProcessState m => path t)
              (trajectoryLawFrom (L := L) μ₀ a fallback) := by
      symm
      exact integral_map (measurable_pi_apply t).aemeasurable
        (processSquaredCost_measurable L a
          (SupplyConfiguration.canonicalFallback hm)).aestronglyMeasurable
    _ = ∫ z : ProcessState m,
          processSquaredCost L a (SupplyConfiguration.canonicalFallback hm) z
            ∂processLawFrom (L := L) μ₀ a fallback t := by
      rw [trajectoryLawFrom_marginal]
    _ = ∫ s : SpatialState m,
          Dynamics.actualConfigurationSquaredCost
            a hm (toConfiguration L s)
            ∂spatialLawFrom (L := L) μ₀ a fallback t :=
      integral_processSquaredCost_processLawFrom μ₀ a hm fallback t

/-- The generalized one-period cost is bounded by the matching finite iterate. -/
theorem trajectoryExpectedSquaredCostFrom_le_envelope
    (μ₀ : Measure (SpatialState m)) [IsProbabilityMeasure μ₀]
    (ν₀ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hμ₀ : Measure.map (spatialCount L) μ₀ = ν₀.toMeasure)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    trajectoryExpectedSquaredCostFrom (L := L) μ₀ a hm fallback t ≤
      ((Dynamics.kernel
        (L := L) (m := m) a ha hm).iterate t ν₀).expect
        (Transport.stateSquaredCostEnvelope a) := by
  rw [trajectoryExpectedSquaredCostFrom_eq_spatial]
  apply FiniteLaw.integral_le_expect_of_map_eq
    (spatialLawFrom (L := L) μ₀ a fallback t)
    ((Dynamics.kernel
      (L := L) (m := m) a ha hm).iterate t ν₀)
    (spatialCount L)
    (fun s : SpatialState m =>
      Dynamics.actualConfigurationSquaredCost
        a hm (toConfiguration L s))
    (Transport.stateSquaredCostEnvelope a)
  · exact (spatialCount_measurable L).aemeasurable
  · exact actualConfigurationSquaredCost_spatialLawFrom_integrable
      μ₀ a hm fallback t
  · filter_upwards with s
    simpa [Dynamics.actualConfigurationSquaredCost] using
      (Transport.expectedActualSquaredDistance_le_stateEnvelope
        (L := L) (m := m) a ha hm (toConfiguration L s)
        (SupplyConfiguration.canonicalFallback hm))
  · exact map_spatialCount_spatialLawFrom
      μ₀ ν₀ hμ₀ a ha hm fallback t

/-! ## Fixed-initial-state specializations -/

/-- A finite point law is represented by the corresponding measure-theoretic Dirac law. -/
theorem toMeasure_dirac
    {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [DecidableEq α] (x : α) :
    (FiniteLaw.dirac x).toMeasure = Measure.dirac x := by
  apply FiniteLaw.measure_ext_of_singletons
  intro y
  rw [FiniteLaw.toMeasure_apply_singleton]
  by_cases h : y = x
  · subst y
    simp [FiniteLaw.mass_dirac]
  · have h' : x ≠ y := Ne.symm h
    simp [FiniteLaw.mass_dirac, h, h']

/-- The count pushforward of a fixed spatial state is its finite point law. -/
theorem map_spatialCount_dirac (L : ℕ) (s₀ : SpatialState m) :
    Measure.map (spatialCount L) (Measure.dirac s₀) =
      (FiniteLaw.dirac (spatialCount L s₀)).toMeasure := by
  rw [Measure.map_dirac' (spatialCount_measurable L)]
  exact (toMeasure_dirac (spatialCount L s₀)).symm

/-- Spatial evolution from the fixed initial state `s₀`. -/
def spatialLawFromState (s₀ : SpatialState m)
    (a : ℝ) (fallback : Fin m) (t : ℕ) :
    Measure (SpatialState m) :=
  spatialLawFrom (L := L) (Measure.dirac s₀) a fallback t

/-- The initial joint law for a fixed spatial state. -/
def initialProcessLawFromState (s₀ : SpatialState m) :
    Measure (ProcessState m) :=
  initialProcessLawFrom (Measure.dirac s₀)

/-- Joint process evolution from a fixed spatial state. -/
def processLawFromState (s₀ : SpatialState m)
    (a : ℝ) (fallback : Fin m) (t : ℕ) :
    Measure (ProcessState m) :=
  processLawFrom (L := L) (Measure.dirac s₀) a fallback t

/-- Path-space law from a fixed spatial state. -/
def trajectoryLawFromState (s₀ : SpatialState m)
    (a : ℝ) (fallback : Fin m) :
    Measure (ℕ → ProcessState m) :=
  trajectoryLawFrom (L := L) (Measure.dirac s₀) a fallback

/-- One-period trajectory cost from a fixed spatial state. -/
def trajectoryExpectedSquaredCostFromState
    (s₀ : SpatialState m) (a : ℝ) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) : ℝ :=
  trajectoryExpectedSquaredCostFrom
    (L := L) (Measure.dirac s₀) a hm fallback t

/-- Fixed-state spatial counts follow the finite kernel from the matching point law. -/
theorem map_spatialCount_spatialLawFromState
    (s₀ : SpatialState m)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    Measure.map (spatialCount L)
        (spatialLawFromState (L := L) s₀ a fallback t) =
      ((Dynamics.kernel
        (L := L) (m := m) a ha hm).iterate t
          (FiniteLaw.dirac (spatialCount L s₀))).toMeasure := by
  exact map_spatialCount_spatialLawFrom
    (Measure.dirac s₀) (FiniteLaw.dirac (spatialCount L s₀))
      (map_spatialCount_dirac L s₀) a ha hm fallback t

/-- Fixed-state process laws retain the spatial/noise product factorization. -/
theorem processLawFromState_eq_product
    (s₀ : SpatialState m) (a : ℝ) (fallback : Fin m) (t : ℕ) :
    processLawFromState (L := L) s₀ a fallback t =
      (spatialLawFromState (L := L) s₀ a fallback t).prod noiseLaw := by
  exact processLawFrom_eq_product (Measure.dirac s₀) a fallback t

/-- Fixed-state trajectory coordinates have the corresponding process laws. -/
theorem trajectoryLawFromState_marginal
    (s₀ : SpatialState m) (a : ℝ) (fallback : Fin m) (t : ℕ) :
    Measure.map (fun path : ℕ → ProcessState m => path t)
        (trajectoryLawFromState (L := L) s₀ a fallback) =
      processLawFromState (L := L) s₀ a fallback t := by
  exact trajectoryLawFrom_marginal (Measure.dirac s₀) a fallback t

/-- Fixed-state trajectory counts follow the finite kernel from the matching point law. -/
theorem trajectoryLawFromState_count_marginal
    (s₀ : SpatialState m)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    Measure.map
        (fun path : ℕ → ProcessState m =>
          spatialCount L (path t).1)
        (trajectoryLawFromState (L := L) s₀ a fallback) =
      ((Dynamics.kernel
        (L := L) (m := m) a ha hm).iterate t
          (FiniteLaw.dirac (spatialCount L s₀))).toMeasure := by
  exact trajectoryLawFrom_count_marginal
    (Measure.dirac s₀) (FiniteLaw.dirac (spatialCount L s₀))
      (map_spatialCount_dirac L s₀) a ha hm fallback t

/-- Fixed-state trajectory cost equals its spatial configured-cost integral. -/
theorem trajectoryExpectedSquaredCostFromState_eq_spatial
    (s₀ : SpatialState m) (a : ℝ) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    trajectoryExpectedSquaredCostFromState (L := L) s₀ a hm fallback t =
      ∫ s : SpatialState m,
        Dynamics.actualConfigurationSquaredCost
          a hm (toConfiguration L s)
          ∂spatialLawFromState (L := L) s₀ a fallback t := by
  exact trajectoryExpectedSquaredCostFrom_eq_spatial
    (Measure.dirac s₀) a hm fallback t

/-- Fixed-state trajectory cost is bounded by its finite-kernel iterate. -/
theorem trajectoryExpectedSquaredCostFromState_le_envelope
    (s₀ : SpatialState m)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    trajectoryExpectedSquaredCostFromState (L := L) s₀ a hm fallback t ≤
      ((Dynamics.kernel
        (L := L) (m := m) a ha hm).iterate t
          (FiniteLaw.dirac (spatialCount L s₀))).expect
        (Transport.stateSquaredCostEnvelope a) := by
  exact trajectoryExpectedSquaredCostFrom_le_envelope
    (Measure.dirac s₀) (FiniteLaw.dirac (spatialCount L s₀))
      (map_spatialCount_dirac L s₀) a ha hm fallback t

end ContinuousProcess

end V5

end

end FD1D
