/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Path.Basic
public import LeanPool.MarkovProcess.MarkovProcess.Time.CountableDenseTime
public import Mathlib.MeasureTheory.Constructions.Polish.Basic


/-!
# Continuous extension from dense-time paths

This file embeds ordinary continuous paths into paths on the fixed dense time carrier. It proves
that the image is measurable and supplies a measurable total inverse. The inverse is the genuine
continuous extension on the image and is arbitrarily equal to a caller-supplied default path away
from the image.

No probability law is shown to be supported on this image, and no continuous modification,
stochastic-process association, or path-regularity claim is made here.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory Set

namespace MarkovProcess

section

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Restriction of a continuous path to the fixed dense time carrier. -/
def denseRestriction (omega : ContinuousPath alpha) : DenseTime → alpha :=
  fun q ↦ omega (DenseTime.castOrderEmbedding q)

@[simp]
theorem denseRestriction_apply (omega : ContinuousPath alpha) (q : DenseTime) :
    denseRestriction omega q = omega (DenseTime.castOrderEmbedding q) := rfl

/-- The nonnegative rational times are dense in nonnegative real time. -/
theorem denseRange_castOrderEmbedding : DenseRange DenseTime.castOrderEmbedding := by
  rw [DenseRange]
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨q, haq, hqb⟩ := DenseTime.exists_cast_btwn hab
  exact ⟨DenseTime.castOrderEmbedding q, ⟨q, rfl⟩, haq, hqb⟩

/-- A continuous path is determined by its values at the dense times. -/
theorem denseRestriction_injective [T2Space alpha] :
    Function.Injective (denseRestriction (alpha := alpha)) := by
  intro omega eta h
  apply ContinuousMap.ext
  have heq : (omega : NNReal → alpha) = eta :=
    denseRange_castOrderEmbedding.equalizer omega.continuous eta.continuous h
  exact congrFun heq

/-- A total extension, equal to the inverse on the restriction range and arbitrarily equal to
`default` away from that range. -/
def continuousExtension (default : ContinuousPath alpha) :
    (DenseTime → alpha) → ContinuousPath alpha :=
  Function.extend denseRestriction id (fun _ ↦ default)

@[simp]
theorem continuousExtension_denseRestriction [T2Space alpha]
    (default omega : ContinuousPath alpha) :
    continuousExtension (alpha := alpha) default (denseRestriction omega) = omega := by
  exact Function.Injective.extend_apply denseRestriction_injective _ _ _

theorem denseRestriction_continuousExtension_of_mem_range [T2Space alpha]
    (default : ContinuousPath alpha) {x : DenseTime → alpha}
    (hx : x ∈ Set.range (denseRestriction (alpha := alpha))) :
    denseRestriction (continuousExtension (alpha := alpha) default x) = x := by
  obtain ⟨omega, rfl⟩ := hx
  rw [continuousExtension_denseRestriction]

@[simp]
theorem continuousExtension_of_notMem_range (default : ContinuousPath alpha)
    {x : DenseTime → alpha} (hx : x ∉ Set.range (denseRestriction (alpha := alpha))) :
    continuousExtension (alpha := alpha) default x = default := by
  exact Function.extend_apply' id (fun _ ↦ default) x hx

section Measurable

variable [MeasurableSpace alpha] [BorelSpace alpha]

/-- Dense-time restriction is coordinatewise Borel measurable. -/
theorem measurable_denseRestriction : Measurable (denseRestriction (alpha := alpha)) := by
  rw [measurable_pi_iff]
  intro q
  exact
    (continuous_eval (alpha := alpha) (DenseTime.castOrderEmbedding q)).borel_measurable.mono
      le_rfl (le_of_eq BorelSpace.measurable_eq)

variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- Dense-time restriction is a measurable embedding. -/
theorem measurableEmbedding_denseRestriction :
    MeasurableEmbedding (denseRestriction (alpha := alpha)) :=
  measurable_denseRestriction.measurableEmbedding denseRestriction_injective

/-- The set of dense-time paths admitting a continuous extension is measurable. -/
theorem measurableSet_range_denseRestriction :
    MeasurableSet (Set.range (denseRestriction (alpha := alpha))) :=
  measurableEmbedding_denseRestriction.measurableSet_range

/-- The total extension is measurable; away from the measurable restriction range its value is
the arbitrary path `default`. -/
theorem measurable_continuousExtension (default : ContinuousPath alpha) :
    Measurable (continuousExtension (alpha := alpha) default) :=
  measurableEmbedding_denseRestriction.measurable_extend measurable_id measurable_const

end Measurable
end ContinuousPath
end
end MarkovProcess

end PortComputability
