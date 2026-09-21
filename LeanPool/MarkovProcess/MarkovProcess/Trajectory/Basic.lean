/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.DenseTime.TrajectoryMarginals
import LeanPool.MarkovProcess.MarkovProcess.Continuity.KolmogorovDenseTimeContinuousSupport

/-!
# Continuous-path trajectory kernels

This file transports the canonical dense-time trajectory of a conservative kernel semigroup to
continuous paths.  The explicit default is used only by the previously established measurable
extension away from the continuous-restriction range.  A coordinate Kolmogorov condition makes
that fallback irrelevant and transports the proved rational-time marginal identities.

No continuous-time Markov property, strong Markov property, Hunt-process assertion, or PDE
increment estimate is claimed.
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

/-- The canonical dense-time trajectory transported through the measurable continuous-extension
map.  Under the Kolmogorov hypothesis used below, its law is independent of `default`. -/
def continuousPathTrajectory (P : SubMarkovKernelSemigroup alpha)
    (hP : P.IsConservative) (default : ContinuousPath alpha) :
    Kernel alpha (ContinuousPath alpha) :=
  Kernel.toContinuousPathKernel
    (denseTimeTrajectory P hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding) default

/-- The transported continuous-path trajectory is a Markov kernel in its initial-state
parameter. -/
instance isMarkovKernel_continuousPathTrajectory
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha) :
    IsMarkovKernel (continuousPathTrajectory P hP default) := by
  unfold continuousPathTrajectory
  exact Kernel.isMarkovKernel_toContinuousPathKernel _ default

/-- Under the coordinate Kolmogorov estimate, the continuous-path trajectory law is independent
of the explicit fallback path used by the measurable extension. -/
theorem continuousPathTrajectory_eq
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default₁ default₂ : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p) :
    continuousPathTrajectory P hP default₁ =
      continuousPathTrajectory P hP default₂ := by
  let kappa := denseTimeTrajectory P hP DenseTime.enumeration
    DenseTime.castOrderEmbedding.toEmbedding
  exact Kernel.IsSupportedOnContinuousPaths.toContinuousPathKernel_eq kappa
    (Kernel.IsSupportedOnContinuousPaths.of_isKolmogorovCoordinate kappa hK)
    default₁ default₂

/-- Every rational-time evaluation of the continuous-path transport has the prescribed
semigroup marginal, provided the canonical dense-time coordinate process satisfies the
parameterwise Kolmogorov condition. -/
theorem continuousPathTrajectory_map_eval
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (r : DenseTime) :
    (continuousPathTrajectory P hP default).map
        (fun path ↦ path (DenseTime.castOrderEmbedding r)) =
      P (DenseTime.castOrderEmbedding r) := by
  let kappa := denseTimeTrajectory P hP DenseTime.enumeration
    DenseTime.castOrderEmbedding.toEmbedding
  have hback :
      (continuousPathTrajectory P hP default).map ContinuousPath.denseRestriction = kappa := by
    exact Kernel.map_denseRestriction_toContinuousPathKernel_of_isKolmogorovCoordinate
      kappa default hK
  have hfun :
      (fun path : ContinuousPath alpha ↦ path (DenseTime.castOrderEmbedding r)) =
        (fun path : DenseTime → alpha ↦ path r) ∘ ContinuousPath.denseRestriction := by
    rfl
  rw [hfun, Kernel.map_comp_right]
  · rw [hback]
    exact denseTimeTrajectory_map_eval P hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding r
  · exact ContinuousPath.measurable_denseRestriction
  · exact measurable_pi_apply r

/-- Every finite enumeration-prefix marginal of the continuous-path transport is the already
constructed dense-time prefix law. -/
theorem continuousPathTrajectory_map_prefix
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (n : ℕ) :
    (continuousPathTrajectory P hP default).map
        (denseTimeTrajectoryPrefix DenseTime.enumeration n ∘
          ContinuousPath.denseRestriction) =
      denseTimePrefixKernel P DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding n := by
  let kappa := denseTimeTrajectory P hP DenseTime.enumeration
    DenseTime.castOrderEmbedding.toEmbedding
  have hback :
      (continuousPathTrajectory P hP default).map ContinuousPath.denseRestriction = kappa := by
    exact Kernel.map_denseRestriction_toContinuousPathKernel_of_isKolmogorovCoordinate
      kappa default hK
  rw [Kernel.map_comp_right]
  · rw [hback]
    exact denseTimeTrajectory_map_prefix P hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding n
  · exact ContinuousPath.measurable_denseRestriction
  · exact measurable_denseTimeTrajectoryPrefix DenseTime.enumeration n

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess
