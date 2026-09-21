/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.ShiftCompactTestConvergence
import LeanPool.MarkovProcess.MarkovProcess.Kernel.PositiveC0OperatorMeasure
import LeanPool.MarkovProcess.MarkovProcess.Path.RandomShiftMeasurability

/-!
# Dominated convergence for tests along random times

This file records path-side dominated-convergence tools for a sequence of measurable random
times converging pointwise to a limiting random time.  The measure is any finite measure on
continuous-path space; no Markov or kernel assumption is used.  The deterministic-sequence
versions are in `ContinuousPathShiftCompactTestConvergence.lean`.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty CompactlySupported

namespace MarkovProcess

noncomputable section

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- Integrals of a bounded continuous state observable at pointwise convergent measurable random
times converge under any finite path measure. -/
theorem tendsto_integral_continuousPath_eval_randomTime_of_tendsto
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (T : ℕ → ContinuousPath alpha → NNReal) (Tlim : ContinuousPath alpha → NNReal)
    (hT : ∀ n, Measurable (T n))
    (hlim : ∀ omega, Tendsto (fun n ↦ T n omega) atTop (nhds (Tlim omega)))
    (g : alpha → ℝ) (hg : Continuous g) (C : ℝ) (hgC : ∀ y, ‖g y‖ ≤ C) :
    Tendsto (fun n ↦ ∫ omega, g (omega (T n omega)) ∂mu) atTop
      (nhds (∫ omega, g (omega (Tlim omega)) ∂mu)) := by
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [] with n
    exact ((hg.measurable.comp
      (ContinuousPath.measurable_eval_of_measurable (T n) (hT n))).stronglyMeasurable
      ).aestronglyMeasurable
  · exact ⟨C, Filter.Eventually.of_forall fun n ↦ ae_of_all _ fun omega ↦ hgC _⟩
  · filter_upwards [] with omega
    exact hg.continuousAt.tendsto.comp
      (omega.continuous.continuousAt.tendsto.comp (hlim omega))

omit [MeasurableSpace alpha] [BorelSpace alpha] in
/-- Integrals of a compactly supported test of finitely many dense-time coordinates of the path
shifted by pointwise convergent measurable random times converge under any finite path
measure. -/
theorem tendsto_integral_continuousPath_finiteDenseEvaluation_shift_randomTime_of_tendsto
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (T : ℕ → ContinuousPath alpha → NNReal) (Tlim : ContinuousPath alpha → NNReal)
    (hT : ∀ n, Measurable (T n))
    (hlim : ∀ omega, Tendsto (fun n ↦ T n omega) atTop (nhds (Tlim omega)))
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    Tendsto (fun n ↦ ∫ omega, f (fun j : J ↦
        omega (T n omega + DenseTime.castOrderEmbedding j)) ∂mu) atTop
      (nhds (∫ omega, f (fun j : J ↦
        omega (Tlim omega + DenseTime.castOrderEmbedding j)) ∂mu)) := by
  let f0 : C₀(J → alpha, ℝ) := PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  have hcont : Continuous (fun p : NNReal × ContinuousPath alpha ↦
      f (fun j : J ↦ p.2 (p.1 + DenseTime.castOrderEmbedding j))) := by
    refine f.continuous.comp (continuous_pi fun j ↦ ?_)
    exact ContinuousEval.continuous_eval.comp
      (continuous_snd.prodMk (continuous_fst.add continuous_const))
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [] with n
    exact (hcont.measurable.comp
      ((hT n).prodMk measurable_id)).stronglyMeasurable.aestronglyMeasurable
  · refine ⟨‖f0‖, Filter.Eventually.of_forall fun n ↦ ?_⟩
    filter_upwards [] with omega
    simpa only [f0, PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply,
      Real.norm_eq_abs] using! f0.toBCF.norm_coe_le_norm
      (fun j : J ↦ omega (T n omega + DenseTime.castOrderEmbedding j))
  · filter_upwards [] with omega
    apply f.continuous.continuousAt.tendsto.comp
    rw [tendsto_pi_nhds]
    intro j
    exact omega.continuous.continuousAt.tendsto.comp
      ((hlim omega).add tendsto_const_nhds)

end

end MarkovProcess
