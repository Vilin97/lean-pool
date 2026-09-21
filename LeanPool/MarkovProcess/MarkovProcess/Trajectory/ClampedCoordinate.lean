/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.StoppedValueMeasurability

/-!
# Measurability of clamped path coordinates

This file records the joint measurability of a continuous-path coordinate whose time argument is
clamped at a deterministic horizon.  It is the common progressive-measurability input for
adapted integral functionals.

Main result: `ContinuousPath.measurable_clampedCoordinate`.

No stochastic-process law or stopping-time identity is asserted.
-/

open MeasureTheory
open scoped NNReal

namespace MarkovProcess.ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [TopologicalSpace.PseudoMetrizableSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- The coordinate at a real time clamped to `[0, t]` is jointly measurable for the Borel
structure in time and the canonical filtration at `t`. -/
theorem measurable_clampedCoordinate (t : NNReal) :
    Measurable[(borel ℝ).prod (canonicalFiltration (alpha := alpha) t)]
      (fun p : ℝ × ContinuousPath alpha ↦ p.2 (min (Real.toNNReal p.1) t)) := by
  have htime : Measurable[(borel ℝ).prod (canonicalFiltration (alpha := alpha) t)]
      (fun p : ℝ × ContinuousPath alpha ↦ min (Real.toNNReal p.1) t) :=
    (measurable_real_toNNReal.comp measurable_fst).min measurable_const
  have hpair : Measurable[(borel ℝ).prod (canonicalFiltration (alpha := alpha) t),
      Subtype.instMeasurableSpace.prod (canonicalFiltration (alpha := alpha) t)]
      (fun p : ℝ × ContinuousPath alpha ↦
        ((⟨min (Real.toNNReal p.1) t, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Set.Iic t), p.2)) :=
    (Measurable.subtype_mk htime).prodMk measurable_snd
  exact ((progMeasurable_coordinateProcess (alpha := alpha) t).comp_measurable hpair).measurable

end MarkovProcess.ContinuousPath
