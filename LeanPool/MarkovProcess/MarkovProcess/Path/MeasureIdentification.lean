/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Continuity.DenseTimeContinuousExtension

/-!
# Identifying continuous-path measures from dense-time restrictions

A measure on continuous-path space is determined by its pushforward to the fixed dense time
carrier. This is the measure-level counterpart of continuous-path kernel identification and is a
deterministic property of continuous paths.
-/

open MeasureTheory

namespace MarkovProcess
namespace Measure

noncomputable section

variable {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- A measure on continuous-path space is determined by its pushforward to the fixed dense time
carrier. -/
theorem map_denseRestriction_injective :
    Function.Injective
      (fun mu : MeasureTheory.Measure (ContinuousPath alpha) ↦
        mu.map ContinuousPath.denseRestriction) := by
  intro mu nu h
  ext s hs
  have himage : MeasurableSet (ContinuousPath.denseRestriction '' s) :=
    ContinuousPath.measurableEmbedding_denseRestriction.measurableSet_image' hs
  have hmap := congrArg
    (fun rho : MeasureTheory.Measure (DenseTime → alpha) ↦
      rho (ContinuousPath.denseRestriction '' s)) h
  dsimp only at hmap
  rw [MeasureTheory.Measure.map_apply ContinuousPath.measurable_denseRestriction himage,
    MeasureTheory.Measure.map_apply ContinuousPath.measurable_denseRestriction himage] at hmap
  simpa only [ContinuousPath.denseRestriction_injective.preimage_image] using hmap

/-- Equality of continuous-path measures is equivalent to equality after restriction to the fixed
dense time carrier. -/
theorem map_denseRestriction_eq_iff
    {mu nu : MeasureTheory.Measure (ContinuousPath alpha)} :
    mu.map ContinuousPath.denseRestriction = nu.map ContinuousPath.denseRestriction ↔
      mu = nu := by
  constructor
  · intro h
    exact map_denseRestriction_injective (alpha := alpha) h
  · intro h
    exact congrArg
      (fun rho : MeasureTheory.Measure (ContinuousPath alpha) ↦
        rho.map ContinuousPath.denseRestriction) h

end
end Measure
end MarkovProcess
