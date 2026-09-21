/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.AllTimeFiniteMarginals

/-!
# Dominated convergence for shifted continuous-path tests

This file records path-side dominated-convergence tools for deterministic times approached by
dense times. The measure is any finite measure on continuous-path space; no Markov or kernel
assumption is used.
-/

noncomputable section PortComputability

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty CompactlySupported

namespace MarkovProcess

section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [LocallyCompactSpace alpha]

omit [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] in
/-- Integrals of a bounded continuous state observable along convergent continuous-path
coordinates converge under any finite path measure. -/
theorem tendsto_integral_continuousPath_eval_of_tendsto
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (s : NNReal) (q : ℕ → DenseTime)
    (hq : Tendsto (fun n ↦ DenseTime.castOrderEmbedding (q n)) atTop (nhds s))
    (g : alpha → ℝ) (hg : Continuous g) (C : ℝ)
    (hgC : ∀ y, ‖g y‖ ≤ C) :
    Tendsto
      (fun n ↦ ∫ omega, g (omega (DenseTime.castOrderEmbedding (q n))) ∂mu)
      atTop (nhds (∫ omega, g (omega s) ∂mu)) := by
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [] with n
    exact (hg.comp (ContinuousPath.continuous_eval (alpha := alpha)
      (DenseTime.castOrderEmbedding (q n)))).aestronglyMeasurable
  · exact ⟨C, Filter.Eventually.of_forall fun n ↦ ae_of_all _ fun omega ↦
      hgC (omega (DenseTime.castOrderEmbedding (q n)))⟩
  · filter_upwards [] with omega
    exact hg.continuousAt.tendsto.comp
      (omega.continuous.continuousAt.tendsto.comp hq)

omit [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] in
/-- Compact-test integrals of finitely many relative dense-time coordinates converge when the
deterministic shift times converge. The finite coordinate set may be empty. -/
theorem tendsto_integral_continuousPath_finiteDenseEvaluation_shift
    (mu : Measure (ContinuousPath alpha)) [IsFiniteMeasure mu]
    (s : NNReal) (q : ℕ → DenseTime)
    (hq : Tendsto (fun n ↦ DenseTime.castOrderEmbedding (q n)) atTop (nhds s))
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    Tendsto
      (fun n ↦ ∫ omega, f (fun j : J ↦
        omega (DenseTime.castOrderEmbedding (q n) +
          DenseTime.castOrderEmbedding j)) ∂mu)
      atTop
      (nhds (∫ omega, f (fun j : J ↦
        omega (s + DenseTime.castOrderEmbedding j)) ∂mu)) := by
  let f₀ : C₀(J → alpha, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [] with n
    exact (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation
      (fun j : J ↦ DenseTime.castOrderEmbedding (q n) +
        DenseTime.castOrderEmbedding j))).aestronglyMeasurable
  · refine ⟨‖f₀‖, Filter.Eventually.of_forall fun n ↦ ?_⟩
    filter_upwards [] with omega
    simpa only [f₀, PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply,
      Real.norm_eq_abs] using! f₀.toBCF.norm_coe_le_norm
      (fun j : J ↦ omega (DenseTime.castOrderEmbedding (q n) +
        DenseTime.castOrderEmbedding j))
  · filter_upwards [] with omega
    apply f.continuous.continuousAt.tendsto.comp
    rw [tendsto_pi_nhds]
    intro j
    exact omega.continuous.continuousAt.tendsto.comp
      (hq.add tendsto_const_nhds)

end
end MarkovProcess

end PortComputability
