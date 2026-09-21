/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.KernelIdentification
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.DenseRestrictionMarginals
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.DenseTimeFiniteSetKernelShift
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.DenseTimeFiniteShift
import LeanPool.MarkovProcess.MarkovProcess.Kernel.FiniteRestrictionIdentification

/-!
# Rational-time shifts of continuous trajectory laws

The canonical continuous trajectory kernel restarts after every nonnegative rational time.  The
proof first identifies all finite rational-coordinate marginals of the shifted path and then uses
uniqueness on the dense product path space and injectivity of dense restriction.  This is an
unconditional law identity; conditional and strong Markov statements require additional work.
-/

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

/-- Shifting the canonical continuous trajectory by a rational time gives the trajectory law
mixed against the transition kernel at that time. -/
theorem continuousPathTrajectory_map_shift_denseTime
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (default : ContinuousPath alpha)
    (hK : ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p)
    (s : DenseTime) :
    (continuousPathTrajectory P hP default).map
        (ContinuousPath.shift (DenseTime.castOrderEmbedding s)) =
      (continuousPathTrajectory P hP default).comp
        (P (DenseTime.castOrderEmbedding s)) := by
  apply Kernel.map_denseRestriction_injective
  apply Kernel.eq_of_map_finiteRestriction_eq
  intro I
  have hShift :=
    ContinuousPath.measurable_shift_fixed (alpha := alpha) (DenseTime.castOrderEmbedding s)
  have hDense := ContinuousPath.measurable_denseRestriction (alpha := alpha)
  have hRestrict := Finset.measurable_restrict (X := fun _ ↦ alpha) I
  have hRestrictAdd :=
    Finset.measurable_restrict (X := fun _ ↦ alpha) (DenseTime.addFinset s I)
  have hPullback := DenseTimePath.measurable_pullbackAddFinset (alpha := alpha) s I
  have hleft :
      I.restrict ∘ (ContinuousPath.denseRestriction (alpha := alpha) ∘
          ContinuousPath.shift (alpha := alpha) (DenseTime.castOrderEmbedding s)) =
        DenseTimePath.pullbackAddFinset (alpha := alpha) s I ∘
          ((DenseTime.addFinset s I).restrict ∘
            ContinuousPath.denseRestriction (alpha := alpha)) := by
    funext omega
    change
      I.restrict (ContinuousPath.denseRestriction
        (ContinuousPath.shift (DenseTime.castOrderEmbedding s) omega)) =
        DenseTimePath.pullbackAddFinset s I
          ((DenseTime.addFinset s I).restrict (ContinuousPath.denseRestriction omega))
    rw [ContinuousPath.denseRestriction_shift]
    exact DenseTimePath.restrict_shift s I (ContinuousPath.denseRestriction omega)
  let Q := continuousPathTrajectory P hP default
  calc
    (((Q.map (ContinuousPath.shift (DenseTime.castOrderEmbedding s))).map
          ContinuousPath.denseRestriction).map I.restrict) =
        Q.map (I.restrict ∘ (ContinuousPath.denseRestriction ∘
          ContinuousPath.shift (DenseTime.castOrderEmbedding s))) := by
      rw [← Kernel.map_comp_right
          (Q.map (ContinuousPath.shift (DenseTime.castOrderEmbedding s))) hDense hRestrict,
        ← Kernel.map_comp_right Q hShift (hRestrict.comp hDense)]
      rw [Function.comp_assoc]
    _ = Q.map (DenseTimePath.pullbackAddFinset s I ∘
          ((DenseTime.addFinset s I).restrict ∘ ContinuousPath.denseRestriction)) := by
      rw [hleft]
    _ = (((Q.map ContinuousPath.denseRestriction).map
          (DenseTime.addFinset s I).restrict).map
            (DenseTimePath.pullbackAddFinset s I)) := by
      rw [← Function.comp_assoc,
        Kernel.map_comp_right Q hDense (hPullback.comp hRestrictAdd),
        Kernel.map_comp_right (Q.map ContinuousPath.denseRestriction) hRestrictAdd hPullback]
    _ = ((finiteSetKernel P (denseTimePhysicalSet (DenseTime.addFinset s I))).map
          (DenseTimePath.pullbackPhysicalSet (DenseTime.addFinset s I))).map
            (DenseTimePath.pullbackAddFinset s I) := by
      rw [continuousPathTrajectory_map_denseRestriction_map_restrict P hP default hK]
    _ = (finiteSetKernel P (denseTimePhysicalSet (DenseTime.addFinset s I))).map
          (DenseTimePath.pullbackAddFinset s I ∘
            DenseTimePath.pullbackPhysicalSet (DenseTime.addFinset s I)) := by
      rw [Kernel.map_comp_right _
        (DenseTimePath.measurable_pullbackPhysicalSet (alpha := alpha)
          (DenseTime.addFinset s I)) hPullback]
    _ = ((finiteSetKernel P (denseTimePhysicalSet I)).map
          (DenseTimePath.pullbackPhysicalSet I)).comp
            (P (DenseTime.castOrderEmbedding s)) :=
      finiteSetKernel_map_pullback_addFinset P hP s I
    _ = ((Q.map ContinuousPath.denseRestriction).map I.restrict).comp
          (P (DenseTime.castOrderEmbedding s)) := by
      rw [continuousPathTrajectory_map_denseRestriction_map_restrict P hP default hK]
    _ = (((Q.comp (P (DenseTime.castOrderEmbedding s))).map
          ContinuousPath.denseRestriction).map I.restrict) := by
      rw [Kernel.map_comp, Kernel.map_comp]

end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess

end PortComputability
