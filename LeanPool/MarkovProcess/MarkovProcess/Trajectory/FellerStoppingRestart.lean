/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FellerRestrictedRestart
import LeanPool.MarkovProcess.MarkovProcess.Restart.CountableStoppingRestartMeasure
import LeanPool.MarkovProcess.MarkovProcess.Path.RandomTimeCompactTestConvergence
import LeanPool.MarkovProcess.MarkovProcess.Path.DenseRestrictionIntegral
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.DenseRestrictionIntegral
import LeanPool.MarkovProcess.MarkovProcess.Path.StoppingTimeDyadicCeiling

/-!
# Event-restricted restart of the Feller trajectory at finite stopping times

The canonical continuous trajectory of a conservative Feller kernel semigroup restarts after
restriction to an event in the stopped sigma-algebra of any finite `NNReal`-valued stopping time
for the canonical filtration.  The proof approximates the stopping time from above by its dyadic
ceilings, which have countable range, applies the all-time deterministic restart identity on
their level sets, identifies every finite dense future marginal by compact tests and dominated
convergence, and concludes by measure identification on dense restrictions.

The stopping time here is finite and `NNReal`-valued.  A `WithTop`-valued time that can be
infinite is covered, on the event where it is finite, in `Trajectory/StoppingLtTop.lean`; no
Hunt-process property is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

/-- Restricting the Feller trajectory to an event in the stopped sigma-algebra of a finite
stopping time and then shifting by that stopping time gives the trajectory kernel restarted
from the state at the stopping time. -/
theorem IsFellerKernelSemigroup.continuousPathTrajectory_restrict_map_shift_stoppingTime
    (P : SubMarkovKernelSemigroup alpha) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    ∀ A : Set (ContinuousPath alpha), MeasurableSet[hT.measurableSpace] A →
      (((continuousPathTrajectory P hP default) x).restrict A).map
          (fun omega ↦ ContinuousPath.shift (T omega) omega) =
        Kernel.comap (continuousPathTrajectory P hP default)
            (fun omega ↦ omega (T omega))
            (ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
          (((continuousPathTrajectory P hP default) x).restrict A) := by
  intro A hA
  set Q := continuousPathTrajectory P hP default with hQ
  set mu := (Q x).restrict A with hmu
  set Tn : ℕ → ContinuousPath alpha → NNReal := fun n omega ↦ dyadicCeiling n (T omega) with hTn
  have hTnStop : ∀ n, IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ ((Tn n omega : NNReal) : WithTop NNReal)) :=
    fun n ↦ isStoppingTime_dyadicCeiling hT n
  have hTnMeas : ∀ n, Measurable (Tn n) :=
    fun n ↦ ContinuousPath.measurable_of_isStoppingTime _ (hTnStop n)
  have hATn : ∀ n, MeasurableSet[(hTnStop n).measurableSpace] A := fun n ↦
    IsStoppingTime.measurableSpace_mono hT (hTnStop n)
      (fun omega ↦ WithTop.coe_le_coe.mpr (le_dyadicCeiling n (T omega))) A hA
  have hstep : ∀ n, mu.map (fun omega ↦ ContinuousPath.shift (Tn n omega) omega) =
      Kernel.comap Q (fun omega ↦ omega (Tn n omega))
        (ContinuousPath.measurable_eval_stoppingTime_borel _ (hTnStop n)) ∘ₘ mu := fun n ↦
    ContinuousPath.restrict_map_shift_stoppingTime_eq_pathKernel_comp_of_restart_on_range
      Q x (Tn n) (hTnStop n) (countable_range_dyadicCeiling_comp n T)
      (fun S _ ↦ hFeller.continuousPathTrajectory_restrict_map_shift P hP default hK x S)
      A (hATn n)
  apply MarkovProcess.Measure.map_denseRestriction_injective
  apply MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
  intro J
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  set L : Kernel alpha (J → alpha) :=
    (finiteSetKernel P (denseTimePhysicalSet J)).map
      (DenseTimePath.pullbackPhysicalSet J) with hL
  set g : alpha → ℝ := fun y ↦ ∫ z, f z ∂L y with hg
  have hg_cont : Continuous g :=
    hFeller.continuous_integral_map_finiteSetKernel_pullbackPhysicalSet hP J f
  set C := ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f‖ with hC
  have hg_bound : ∀ y, ‖g y‖ ≤ C := fun y ↦
    hP.norm_integral_map_finiteSetKernel_pullbackPhysicalSet_le J f y
  have hlimT : ∀ omega, Tendsto (fun n ↦ Tn n omega) atTop (nhds (T omega)) :=
    fun omega ↦ tendsto_dyadicCeiling (T omega)
  have hright := tendsto_integral_continuousPath_eval_randomTime_of_tendsto
    mu Tn T hTnMeas hlimT g hg_cont C hg_bound
  have hleft := tendsto_integral_continuousPath_finiteDenseEvaluation_shift_randomTime_of_tendsto
    mu Tn T hTnMeas hlimT J f
  have htest : StronglyMeasurable (fun omega : ContinuousPath alpha ↦
      f (J.restrict (ContinuousPath.denseRestriction omega))) :=
    (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation
      (fun j : J ↦ DenseTime.castOrderEmbedding j))).stronglyMeasurable
  have heq : ∀ n, (∫ omega, f (fun j : J ↦
        omega (Tn n omega + DenseTime.castOrderEmbedding j)) ∂mu) =
      ∫ omega, g (omega (Tn n omega)) ∂mu := by
    intro n
    have hm := congrArg (fun rho : Measure (ContinuousPath alpha) ↦
      (rho.map ContinuousPath.denseRestriction).map J.restrict) (hstep n)
    have hi := congrArg (fun rho : Measure (J → alpha) ↦ ∫ z, f z ∂rho) hm
    rw [ContinuousPath.integral_map_denseRestriction_map_restrict,
      continuousPathTrajectory_integral_map_denseRestriction_map_restrict_comp_comap
        P hP default hK] at hi
    rw [integral_map
      (ContinuousPath.measurable_shift_of_measurable (Tn n) (hTnMeas n)).aemeasurable
      htest.aestronglyMeasurable] at hi
    simpa only [ContinuousPath.denseRestriction_apply, ContinuousPath.shift_apply, hg, hL]
      using! hi
  have hlimits :
      (∫ omega, f (fun j : J ↦ omega (T omega + DenseTime.castOrderEmbedding j)) ∂mu) =
        ∫ omega, g (omega (T omega)) ∂mu :=
    tendsto_nhds_unique hleft (by simpa only [heq] using hright)
  rw [ContinuousPath.integral_map_denseRestriction_map_restrict,
    continuousPathTrajectory_integral_map_denseRestriction_map_restrict_comp_comap
      P hP default hK]
  rw [integral_map
    (ContinuousPath.measurable_shift_stoppingTime T hT).aemeasurable
    htest.aestronglyMeasurable]
  simpa only [ContinuousPath.denseRestriction_apply, ContinuousPath.shift_apply, hg, hL]
    using! hlimits

end
end MarkovProcess.SubMarkovKernelSemigroup
