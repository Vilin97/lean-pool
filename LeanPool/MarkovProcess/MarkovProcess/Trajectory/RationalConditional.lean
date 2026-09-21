/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Restart.RationalRestart
import LeanPool.MarkovProcess.MarkovProcess.Restart.RationalRestrictedRestart
import LeanPool.MarkovProcess.MarkovProcess.Restart.ConditionalMarkov

/-!
# Rational-time conditional Markov identities for the continuous trajectory

This file derives two local consequences of the rational joint restart law for the canonical
continuous-path trajectory.  First, restricting to any event in the canonical filtration and
then shifting at a rational time gives the path kernel restarted from the state at that time.
Second, every bounded strongly measurable functional of the shifted path satisfies the
corresponding conditional-expectation formula.

The times here are rational.  The strong Markov property at an arbitrary finite stopping time
is in `Trajectory/FellerStoppingRestart.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

private theorem continuousPathTrajectory_rationalJoint_apply
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (S : DenseTime) :
    ((continuousPathTrajectory P hP default) x).map (fun omega ↦
        (ContinuousPath.densePastRestriction S omega,
          ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega)) =
      (((continuousPathTrajectory P hP default) x).map
          (ContinuousPath.densePastRestriction S)) ⊗ₘ
        Kernel.comap (continuousPathTrajectory P hP default)
          (ContinuousPath.densePastTerminal S)
          (ContinuousPath.measurable_densePastTerminal S) := by
  have h := congrArg (fun K : Kernel alpha
      ((Set.Iic S → alpha) × ContinuousPath alpha) ↦ K x)
    (continuousPathTrajectory_map_densePastRestriction_prod_shift
      P hP default hK S)
  change ((continuousPathTrajectory P hP default).map (fun omega ↦
      (ContinuousPath.densePastRestriction S omega,
        ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega))) x =
    ContinuousPath.rationalPastFutureRestartKernel
      (continuousPathTrajectory P hP default) S x at h
  rw [Kernel.map_apply (continuousPathTrajectory P hP default)
      ((ContinuousPath.measurable_densePastRestriction S).prodMk
        (ContinuousPath.measurable_shift_fixed (DenseTime.castOrderEmbedding S))) x,
    ContinuousPath.rationalPastFutureRestartKernel_apply
      (continuousPathTrajectory P hP default) S x] at h
  exact h

/-- At a rational time, shifting the continuous trajectory after restriction to a past event is
the continuous path kernel restarted from the state at that time. -/
theorem continuousPathTrajectory_restrict_map_shift_denseTime
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (S : DenseTime) :
    ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha)
        (DenseTime.castOrderEmbedding S)] A →
        (((continuousPathTrajectory P hP default) x).restrict A).map
            (ContinuousPath.shift (DenseTime.castOrderEmbedding S)) =
          Kernel.comap (continuousPathTrajectory P hP default)
              (ContinuousPath.coordinateProcess (alpha := alpha)
                (DenseTime.castOrderEmbedding S))
              (ContinuousPath.measurable_coordinateProcess
                (DenseTime.castOrderEmbedding S)) ∘ₘ
            (((continuousPathTrajectory P hP default) x).restrict A) := by
  exact ContinuousPath.restrict_map_shift_eq_pathKernel_comp_of_rational_joint
    (continuousPathTrajectory P hP default) x S
      (continuousPathTrajectory_rationalJoint_apply P hP default hK x S)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- At a rational time, the conditional expectation of a bounded functional of the shifted
trajectory is its path-kernel expectation started from the current state. -/
theorem continuousPathTrajectory_condExp_shift_denseTime
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (x : alpha) (S : DenseTime)
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : Real) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousPathTrajectory P hP default) x)[fun omega ↦
        F (ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega)|
      ContinuousPath.canonicalFiltration (alpha := alpha)
        (DenseTime.castOrderEmbedding S)] =ᵐ[(continuousPathTrajectory P hP default) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousPathTrajectory P hP default)
        (omega (DenseTime.castOrderEmbedding S)) := by
  apply ContinuousPath.condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
    (continuousPathTrajectory P hP default) x (DenseTime.castOrderEmbedding S)
  · exact continuousPathTrajectory_restrict_map_shift_denseTime P hP default hK x S
  · exact hF
  · exact hFC

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
