/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.Basic
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.C0SemigroupJoint
public import LeanPool.MarkovProcess.MarkovProcess.Feller.Semigroup
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.PositiveC0OperatorMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.Order.IsLUB


/-!
# All-time marginals of continuous-path trajectories

This file supplies the rational-approximation input for extending the already proved dense-time
marginals to arbitrary nonnegative real times.  The extension uses path continuity on one side
and Feller `C₀`-orbit continuity on the other.

No continuous-time Markov, strong Markov, or Hunt-process assertion is made here.
-/

@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess

section

/-- Nonnegative rational times admit a sequence converging to every nonnegative real time. -/
theorem exists_denseTime_seq_tendsto (t : NNReal) :
    ∃ q : ℕ → DenseTime,
      Tendsto (fun n ↦ DenseTime.castOrderEmbedding (q n)) atTop (nhds t) := by
  obtain ⟨q, _, _, hq⟩ := ContinuousPath.denseRange_castOrderEmbedding
    |>.exists_seq_strictAnti_tendsto
    DenseTime.castOrderEmbedding.monotone t
  exact ⟨q, by simpa only [Function.comp_apply] using! hq⟩

namespace SubMarkovKernelSemigroup
namespace IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

/-- Feller time continuity upgrades the rational marginals of the continuous-path trajectory to
every nonnegative real time. -/
theorem continuousPathTrajectory_map_eval_nnreal
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hF : P.IsFellerKernelSemigroup) (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (t : NNReal) :
    (continuousPathTrajectory P hP default).map (fun path ↦ path t) = P t := by
  obtain ⟨q, hq⟩ := exists_denseTime_seq_tendsto t
  let : IsMarkovKernel (P t) := hP.isMarkovKernel t
  apply Kernel.ext
  intro x
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let K := continuousPathTrajectory P hP default
  let f0 : C₀(alpha, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  have hpath : Tendsto
      (fun n ↦ ∫ omega, f (omega (DenseTime.castOrderEmbedding (q n))) ∂K x)
      atTop (nhds (∫ omega, f (omega t) ∂K x)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · filter_upwards [] with n
      exact (f.continuous.comp
        (ContinuousPath.continuous_eval (alpha := alpha)
          (DenseTime.castOrderEmbedding (q n)))).aestronglyMeasurable
    · refine ⟨‖f0‖, Filter.Eventually.of_forall fun n ↦ ?_⟩
      filter_upwards [] with omega
      simpa only [f0, PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply,
        Real.norm_eq_abs] using! f0.toBCF.norm_coe_le_norm
        (omega (DenseTime.castOrderEmbedding (q n)))
    · filter_upwards [] with omega
      exact Filter.Tendsto.comp f.continuous.continuousAt
        (Filter.Tendsto.comp omega.continuous.continuousAt hq)
  have hsemigroup : Tendsto
      (fun n ↦ kernelIntegral (P (DenseTime.castOrderEmbedding (q n))) f x)
      atTop (nhds (kernelIntegral (P t) f x)) := by
    have hpair : Tendsto
        (fun n ↦ (DenseTime.castOrderEmbedding (q n), x)) atTop (nhds (t, x)) :=
      hq.prodMk_nhds tendsto_const_nhds
    have horbit :=
      (hF.c0Semigroup.continuous_apply_apply f0).tendsto (t, x) |>.comp hpair
    simpa only [IsFellerKernelSemigroup.c0Semigroup_apply_apply,
      PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply] using! horbit
  have heq : ∀ n,
      (∫ omega, f (omega (DenseTime.castOrderEmbedding (q n))) ∂K x) =
        kernelIntegral (P (DenseTime.castOrderEmbedding (q n))) f x := by
    intro n
    have hm := congrArg (fun L : Kernel alpha alpha ↦ L x)
      (continuousPathTrajectory_map_eval P hP default hK (q n))
    have hi := congrArg (fun mu : Measure alpha ↦ ∫ y, f y ∂mu) hm
    change (∫ y, f y ∂(K.map
      (ContinuousPath.eval (DenseTime.castOrderEmbedding (q n)))) x) =
        kernelIntegral (P (DenseTime.castOrderEmbedding (q n))) f x at hi
    have heval : Measurable (ContinuousPath.eval (alpha := alpha)
        (DenseTime.castOrderEmbedding (q n))) :=
      (ContinuousPath.continuous_eval (alpha := alpha)
        (DenseTime.castOrderEmbedding (q n))).borel_measurable.mono
          le_rfl (le_of_eq BorelSpace.measurable_eq)
    have hmap :
        (K.map (ContinuousPath.eval (DenseTime.castOrderEmbedding (q n)))) x =
          (K x).map (ContinuousPath.eval (DenseTime.castOrderEmbedding (q n))) :=
      Kernel.map_apply K heval x
    rw [hmap, integral_map] at hi
    · exact hi
    · exact heval.aemeasurable
    · exact f.continuous.aestronglyMeasurable
  have hsame :
      (fun n ↦ ∫ omega, f (omega (DenseTime.castOrderEmbedding (q n))) ∂K x) =
        fun n ↦ kernelIntegral (P (DenseTime.castOrderEmbedding (q n))) f x :=
    funext heq
  rw [hsame] at hpath
  have hlimit := tendsto_nhds_unique hpath hsemigroup
  change (∫ y, f y ∂(K.map (ContinuousPath.eval t)) x) =
    kernelIntegral (P t) f x
  have heval : Measurable (ContinuousPath.eval (alpha := alpha) t) :=
    (ContinuousPath.continuous_eval (alpha := alpha) t).borel_measurable.mono
      le_rfl (le_of_eq BorelSpace.measurable_eq)
  have hmap : (K.map (ContinuousPath.eval t)) x = (K x).map (ContinuousPath.eval t) :=
    Kernel.map_apply K heval x
  rw [hmap, integral_map]
  · exact hlimit
  · exact heval.aemeasurable
  · exact f.continuous.aestronglyMeasurable

end IsConservative
end SubMarkovKernelSemigroup

end
end MarkovProcess

end PortComputability
