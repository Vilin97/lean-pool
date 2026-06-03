/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Order.CompleteSublattice
import LeanPool.QuasiBorelSpaces.MeasureTheory.Pack
import LeanPool.QuasiBorelSpaces.MeasureTheory.Measure
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.ProbabilityMeasure

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.ProbabilityMeasure`.
-/


namespace MeasureTheory

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

lemma isProbabilityMeasure_bind_measurable
    {f : A → Measure B} [∀ x, IsProbabilityMeasure (f x)] (hf : Measurable f)
    (μ : Measure A) [IsProbabilityMeasure μ]
    : IsProbabilityMeasure (μ.bind f) := by
  let κ : ProbabilityTheory.Kernel A B := ⟨f, hf⟩
  have : ProbabilityTheory.IsMarkovKernel κ := ⟨fun _ ↦ inferInstance⟩
  have : MeasureTheory.IsProbabilityMeasure (μ.bind κ) := inferInstance
  exact this

namespace ProbabilityMeasure

/-- Monadic bind for probability measures. -/
noncomputable def bind
    (μ : ProbabilityMeasure A)
    (f : A → ProbabilityMeasure B)
    : ProbabilityMeasure B :=
  open Classical in
  if h : Measurable f then
    {
      val := μ.toMeasure.bind fun x ↦ (f x).toMeasure,
      property := by
        apply isProbabilityMeasure_bind_measurable
        apply Measurable.subtype_val
        exact h
    }
  else
    f μ.nonempty.some

lemma lintegral_bind
    (μ : ProbabilityMeasure A)
    {f : A → ProbabilityMeasure B} (hf : Measurable f)
    {k : B → ENNReal} (hk : Measurable k)
    : ∫⁻ x, k x ∂μ.bind f = ∫⁻ a, ∫⁻ x, k x ∂f a ∂μ := by
  simp only [bind, hf, ↓reduceDIte, coe_mk]
  rw [MeasureTheory.Measure.lintegral_bind]
  · apply hf.subtype_val.aemeasurable
  · apply hk.aemeasurable

@[fun_prop]
lemma measurable_bind
    (f : A → ProbabilityMeasure B)
    : Measurable (bind · f) := by
  wlog hA : Nonempty (ProbabilityMeasure A)
  · simp only [not_nonempty_iff] at hA
    apply measurable_of_empty
  wlog hf : Measurable f
  · simp only [bind, hf, ↓reduceDIte]
    change Measurable fun _ ↦ f hA.some.nonempty.some
    apply measurable_const
  simp only [bind, hf, ↓reduceDIte]
  apply Measurable.subtype_mk
  apply Measurable.fun_comp (MeasureTheory.Measure.measurable_bind' ?_)
  · apply Measurable.subtype_val
    apply measurable_id'
  · apply hf.subtype_val

end ProbabilityMeasure

end MeasureTheory
