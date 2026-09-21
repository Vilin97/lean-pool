/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FellerRestrictedRestart
import LeanPool.MarkovProcess.MarkovProcess.Restart.CountableStoppingRestart

/-!
# Conditional restart of the Feller trajectory at countable-range stopping times

For a finite `NNReal`-valued stopping time with countable range, the conditional expectation of a
bounded strongly measurable functional of the canonical Feller trajectory shifted at that time,
given the stopped sigma-algebra, is the path-kernel expectation started from the state at that
time.  The proof feeds the all-time event-restricted deterministic restart identity into the
generic countable-range stopping-time bridge.

The stopping time here has countable range.  An arbitrary finite stopping time is covered in
`Trajectory/FellerStoppingConditional.lean`, and a `WithTop`-valued time that can be infinite in
`Trajectory/StoppingLtTop.lean`.
-/

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup
section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- At a finite stopping time with countable range, the conditional expectation of a bounded
functional of the shifted Feller trajectory given the stopped sigma-algebra is its path-kernel
expectation started from the state at that time. -/
theorem IsFellerKernelSemigroup.continuousPathTrajectory_condExp_shift_countableStoppingTime
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (tau : ContinuousPath alpha → NNReal)
    (htau : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (tau omega : WithTop NNReal)))
    (htauRange : (Set.range tau).Countable)
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousPathTrajectory P hP default) x)[fun omega ↦
        F (ContinuousPath.shift (tau omega) omega)|htau.measurableSpace] =ᵐ[
      (continuousPathTrajectory P hP default) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default)
        (omega (tau omega)) := by
  apply
    ContinuousPath.condExp_shift_stoppingTime_ae_eq_integral_pathKernel_of_restart_on_range
      (continuousPathTrajectory P hP default) x tau htau htauRange
  · intro S _
    exact hFeller.continuousPathTrajectory_restrict_map_shift
      P hP default hK x S
  · exact hF
  · exact hFC

end
end MarkovProcess.SubMarkovKernelSemigroup

end PortComputability
