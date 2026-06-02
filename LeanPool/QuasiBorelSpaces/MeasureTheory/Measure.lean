/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.Probability.Kernel.MeasurableLIntegral
import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import Mathlib.Probability.Kernel.Defs

/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.Measure

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.Measure`.
-/


namespace MeasureTheory.Measure

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

lemma measurable_map'
    {f : A → B → C} (hf : Measurable fun (x, y) ↦ f x y)
    {μ : A → Measure B} (hμ₁ : Measurable μ) [∀ x, IsFiniteMeasure (μ x)]
    : Measurable (fun x ↦ map (f x) (μ x)) := by
  apply measurable_of_measurable_coe
  intro X hX
  have hf' (x) : Measurable (f x) := by
    apply Measurable.of_uncurry_left
    exact hf
  simp only [hf', hX, map_apply]
  let κ : ProbabilityTheory.Kernel A B := ⟨μ, hμ₁⟩
  change Measurable fun b ↦ κ b (Prod.mk b ⁻¹' (Function.uncurry f ⁻¹' X))
  apply ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite
  · apply hf hX
  · infer_instance

lemma measurable_apply
    {μ : A → Measure B} (hμ : Measurable μ) (hμ' : ProbabilityTheory.IsSFiniteKernel ⟨μ, hμ⟩)
    {i : A → Set B} (hi : Measurable fun x : _ × _ ↦ x.1 ∈ i x.2)
    : Measurable (fun x ↦ μ x (i x)) := by
  have hi' {x} : MeasurableSet (i x) := by
    change MeasurableSet { a | a ∈ i x }
    rw [measurableSet_setOf]
    have : Measurable (fun y : B ↦ (y, x)) := by fun_prop
    apply Measurable.fun_comp hi this
  simp only [← MeasureTheory.lintegral_indicator_one, hi']
  apply Measurable.lintegral_kernel_prod_left (κ := ⟨μ, hμ⟩)
  apply Measurable.ite
  · simp only [measurableSet_setOf]
    fun_prop
  · fun_prop
  · fun_prop

/-- The push-forward of a measure by a partial function. -/
noncomputable def mapOption (f : A → Option B) (μ : Measure A) : Measure B :=
  open Classical in
  let μ' := μ.restrict {x | (f x).isSome}
  if h : NeZero μ' then
    have : Nonempty B := by
      by_contra hB
      have {x} : ¬(f x).isSome := by
        cases h : f x with
        | none => simp only [Option.isSome_none, Bool.false_eq_true, not_false_eq_true]
        | some y =>
          have : Nonempty B := ⟨y⟩
          contradiction
      rcases h with ⟨h⟩
      simp only [
        this, Bool.false_eq_true, Set.setOf_false,
        restrict_empty, ne_eq, not_true_eq_false, μ'] at h
    μ'.map (Option.elim' this.some id ∘ f)
  else
    0

@[simp]
lemma lintegral_mapOption
    {k : B → ENNReal} (hk : Measurable k)
    {f : A → Option B} (hf : Measurable f)
    (μ : Measure A)
    : ∫⁻ b, k b ∂(mapOption f μ)
    = ∫⁻ a, Option.elim (f a) 0 k ∂μ := by
  by_cases h : NeZero (μ.restrict {x | (f x).isSome = true})
  · simp only [mapOption, h, ↓reduceDIte]
    rw [lintegral_map, ← MeasureTheory.lintegral_indicator]
    · simp only [Set.indicator, Set.mem_setOf_eq, Function.comp_apply]
      apply lintegral_congr fun a ↦ ?_
      cases f a <;> rfl
    · simp only [measurableSet_setOf]
      fun_prop
    · fun_prop
    · fun_prop
  · simp only [mapOption, h, ↓reduceDIte, lintegral_zero_measure]
    simp only [not_neZero, restrict_eq_zero] at h
    nth_rw 1 [← MeasureTheory.setLIntegral_measure_zero _ (fun a ↦ (f a).elim 0 k) h]
    rw [← MeasureTheory.lintegral_indicator]
    · simp only [Set.indicator, Set.mem_setOf_eq]
      apply lintegral_congr fun a ↦ ?_
      cases f a <;> rfl
    · simp only [measurableSet_setOf]
      fun_prop

instance : MeasurableSMul₂ ENNReal (Measure B) where
  measurable_smul := by
    rw [MeasureTheory.Measure.measurable_measure]
    intro s hs
    simp only [Function.uncurry, smul_apply, smul_eq_mul]
    apply Measurable.smul (f := Prod.fst)
    · fun_prop
    · apply Measurable.comp (MeasureTheory.Measure.measurable_coe hs)
      fun_prop

end MeasureTheory.Measure
