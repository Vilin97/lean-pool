/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Continuity.DenseTimeContinuousExtension
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Identifying continuous-path kernels from dense-time restrictions

Restriction to the fixed dense time carrier is injective on kernels whose target is continuous-path
space.  A measurable left inverse is obtained from the total continuous-extension map.  This is a
deterministic property of continuous paths; it makes no stochastic-process, Markov, or regularity
claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace Kernel

noncomputable section

variable {alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- Pushing a continuous-path kernel to dense-time paths and then applying the measurable total
continuous extension recovers the original kernel. -/
@[simp]
theorem map_denseRestriction_map_continuousExtension
    (kappa : Kernel beta (ContinuousPath alpha)) (default : ContinuousPath alpha) :
    (kappa.map ContinuousPath.denseRestriction).map
        (ContinuousPath.continuousExtension default) = kappa := by
  rw [← Kernel.map_comp_right]
  · have hcomp : ContinuousPath.continuousExtension default ∘
        ContinuousPath.denseRestriction = id := by
      funext omega
      exact ContinuousPath.continuousExtension_denseRestriction default omega
    rw [hcomp, Kernel.map_id]
  · exact ContinuousPath.measurable_denseRestriction
  · exact ContinuousPath.measurable_continuousExtension default

/-- A kernel on continuous-path space is determined by its pushforward to the fixed dense time
carrier. -/
theorem map_denseRestriction_injective :
    Function.Injective
      (fun kappa : Kernel beta (ContinuousPath alpha) ↦
        kappa.map ContinuousPath.denseRestriction) := by
  intro kappa eta h
  ext x s hs
  have himage : MeasurableSet (ContinuousPath.denseRestriction '' s) :=
    ContinuousPath.measurableEmbedding_denseRestriction.measurableSet_image' hs
  have hx := congrArg
    (fun z : Kernel beta (DenseTime → alpha) ↦
      z x (ContinuousPath.denseRestriction '' s)) h
  dsimp only at hx
  rw [Kernel.map_apply' _ ContinuousPath.measurable_denseRestriction x himage,
    Kernel.map_apply' _ ContinuousPath.measurable_denseRestriction x himage] at hx
  simpa only [ContinuousPath.denseRestriction_injective.preimage_image] using hx

/-- Equality of continuous-path kernels is equivalent to equality after restriction to the fixed
dense time carrier. -/
theorem map_denseRestriction_eq_iff {kappa eta : Kernel beta (ContinuousPath alpha)} :
    kappa.map ContinuousPath.denseRestriction = eta.map ContinuousPath.denseRestriction ↔
      kappa = eta := by
  constructor
  · intro h
    exact map_denseRestriction_injective (alpha := alpha) (beta := beta) h
  · exact fun h ↦ congrArg
      (fun z : Kernel beta (ContinuousPath alpha) ↦
        z.map ContinuousPath.denseRestriction) h

end
end Kernel
end MarkovProcess
