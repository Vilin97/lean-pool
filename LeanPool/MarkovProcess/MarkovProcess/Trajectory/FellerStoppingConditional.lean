/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FellerStoppingRestart
import LeanPool.MarkovProcess.MarkovProcess.Path.StoppedValueMeasurability

/-!
# Conditional expectation of the Feller trajectory at finite stopping times

For every finite `NNReal`-valued stopping time of the canonical filtration, the conditional
expectation of a bounded strongly measurable functional of the shifted canonical Feller
trajectory, given the stopped sigma-algebra, is the path-kernel expectation started from the
state at the stopping time.  The proof feeds the event-restricted stopping-time restart identity
into the generic conditional-expectation bridge; measurability of the restarted expectation for
the stopped sigma-algebra comes from progressive measurability of the coordinate process.

The stopping time here is finite and `NNReal`-valued.  A `WithTop`-valued time that can be
infinite is covered, on the event where it is finite, in `Trajectory/StoppingLtTop.lean`; no
Hunt-process property is asserted.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- At a finite stopping time, the conditional expectation of a bounded functional of the shifted
Feller trajectory given the stopped sigma-algebra is its path-kernel expectation started from the
state at the stopping time. -/
theorem IsFellerKernelSemigroup.continuousPathTrajectory_condExp_shift_stoppingTime
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousPathTrajectory P hP default) x)[fun omega ↦
        F (ContinuousPath.shift (T omega) omega)|hT.measurableSpace] =ᵐ[
      (continuousPathTrajectory P hP default) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default)
        (omega (T omega)) := by
  apply condExp_comp_ae_eq_integral_kernel_of_restrict_map
    ((continuousPathTrajectory P hP default) x)
    (Kernel.comap (continuousPathTrajectory P hP default) (fun omega ↦ omega (T omega))
      (ContinuousPath.measurable_eval_stoppingTime_borel T hT))
    (fun omega ↦ ContinuousPath.shift (T omega) omega)
    (ContinuousPath.measurable_shift_stoppingTime T hT)
    hT.measurableSpace_le
    (hFeller.continuousPathTrajectory_restrict_map_shift_stoppingTime P hP default hK x T hT)
    F hF ?_ C hFC
  have hBase : StronglyMeasurable[hT.measurableSpace]
      (fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default) (omega (T omega))) :=
    hF.integral_kernel.comp_measurable (ContinuousPath.measurable_eval_stoppingTime T hT)
  simpa only [Kernel.comap_apply] using hBase

end
end MarkovProcess.SubMarkovKernelSemigroup
