/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Topology.Constructions.SumProd


/-!
# Conservative cemetery extension of a sub-Markov kernel

This file adjoins an isolated cemetery state to a measurable state space and
extends one sub-Markov kernel to a Markov kernel.  It deliberately makes no
claim about preservation of kernel composition or semigroup laws.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*}

/-- A state space with one additional isolated cemetery state. -/
abbrev Cemetery (α : Type*) := α ⊕ Unit

/-- Embed a live state into the cemetery extension. -/
abbrev Cemetery.alive (x : α) : Cemetery α := Sum.inl x

/-- The cemetery state. -/
abbrev Cemetery.delta : Cemetery α := Sum.inr ()

/-- The added cemetery state is isolated in the inherited sum topology. -/
theorem Cemetery.isOpen_singleton_delta [TopologicalSpace α] :
    IsOpen ({Cemetery.delta} : Set (Cemetery α)) := by
  simpa only [Cemetery.delta, Set.range_unique] using
    (isOpen_range_inr : IsOpen (Set.range (Sum.inr : Unit → α ⊕ Unit)))

namespace Kernel

variable [MeasurableSpace α]

/-- The conservative extension of a sub-Markov kernel obtained by sending its
missing mass to the cemetery state and making that state absorbing. -/
noncomputable def cemeteryExtension (κ : ProbabilityTheory.Kernel α α) :
    ProbabilityTheory.Kernel (Cemetery α) (Cemetery α) where
  toFun := Sum.elim
    (fun x ↦ Measure.map Cemetery.alive (κ x) +
      (1 - κ x Set.univ) • Measure.dirac Cemetery.delta)
    (fun _ ↦ Measure.dirac Cemetery.delta)
  measurable' := measurable_fun_sum
    (by
      have h :=
        (ProbabilityTheory.Kernel.map κ Cemetery.alive).measurable.add
          (((measurable_const : Measurable (fun _ : α => (1 : ℝ≥0∞))).sub
            (κ.measurable_coe MeasurableSet.univ)).smul_measure
            (Measure.dirac Cemetery.delta))
      simpa only [Function.comp_def, Sum.elim_inl, Pi.add_def, Pi.sub_apply,
        ProbabilityTheory.Kernel.map_apply κ measurable_inl] using!
        h)
    measurable_const

theorem cemeteryExtension_alive_apply (κ : ProbabilityTheory.Kernel α α) (x : α) :
    cemeteryExtension κ (Cemetery.alive x) =
      Measure.map Cemetery.alive (κ x) +
        (1 - κ x Set.univ) • Measure.dirac Cemetery.delta :=
  by
    rw [cemeteryExtension, ProbabilityTheory.Kernel.coe_mk]
    rfl

@[simp]
theorem cemeteryExtension_delta_apply (κ : ProbabilityTheory.Kernel α α) :
    cemeteryExtension κ Cemetery.delta = Measure.dirac Cemetery.delta :=
  by
    rw [cemeteryExtension, ProbabilityTheory.Kernel.coe_mk]
    rfl

theorem cemeteryExtension_alive_apply' (κ : ProbabilityTheory.Kernel α α) (x : α)
    {s : Set (Cemetery α)} (hs : MeasurableSet s) :
    cemeteryExtension κ (Cemetery.alive x) s =
      κ x (Cemetery.alive ⁻¹' s) +
        (1 - κ x Set.univ) * s.indicator 1 Cemetery.delta := by
  rw [cemeteryExtension_alive_apply, Measure.add_apply, Measure.map_apply measurable_inl hs,
    Measure.smul_apply, Measure.dirac_apply' _ hs]
  rfl

/-- On measurable sets of live states, the extension agrees exactly with the
original kernel. -/
theorem cemeteryExtension_alive_image (κ : ProbabilityTheory.Kernel α α) (x : α)
    {s : Set α} (hs : MeasurableSet s) :
    cemeteryExtension κ (Cemetery.alive x) (Cemetery.alive '' s) = κ x s := by
  change cemeteryExtension κ (Cemetery.alive x) (Sum.inl '' s) = κ x s
  rw [cemeteryExtension_alive_apply' κ x hs.inl_image]
  rw [Sum.inl_injective.preimage_image]
  have hnot : Cemetery.delta ∉ Sum.inl '' s := by
    rintro ⟨y, -, hy⟩
    exact Sum.inl_ne_inr hy
  rw [Set.indicator_of_notMem hnot, mul_zero, add_zero]

/-- The mass assigned to the cemetery singleton is exactly the missing mass. -/
theorem cemeteryExtension_alive_singleton_delta (κ : ProbabilityTheory.Kernel α α) (x : α) :
    cemeteryExtension κ (Cemetery.alive x) {Cemetery.delta} = 1 - κ x Set.univ := by
  have hdelta : MeasurableSet ({Cemetery.delta} : Set (Cemetery α)) := by
    simpa only [Set.range_unique] using
      (measurableSet_range_inr : MeasurableSet (Set.range (Sum.inr : Unit → α ⊕ Unit)))
  rw [cemeteryExtension_alive_apply' κ x hdelta]
  have hpre : Cemetery.alive ⁻¹' ({Cemetery.delta} : Set (Cemetery α)) = ∅ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Sum.inl_ne_inr, Set.notMem_empty]
  rw [hpre, measure_empty]
  simp only [Set.indicator_of_mem, Set.mem_singleton_iff, Pi.one_apply, mul_one, zero_add]

theorem cemeteryExtension_delta_apply' (κ : ProbabilityTheory.Kernel α α)
    {s : Set (Cemetery α)} (hs : MeasurableSet s) :
    cemeteryExtension κ Cemetery.delta s = s.indicator 1 Cemetery.delta := by
  rw [cemeteryExtension_delta_apply, Measure.dirac_apply' _ hs]

theorem cemeteryExtension_alive_univ (κ : ProbabilityTheory.Kernel α α)
    (hκ : IsSubMarkovKernel κ) (x : α) :
    cemeteryExtension κ (Cemetery.alive x) Set.univ = 1 := by
  rw [cemeteryExtension_alive_apply' κ x MeasurableSet.univ]
  simp only [Set.preimage_univ, Set.indicator_of_mem, Set.mem_univ, Pi.one_apply, mul_one]
  rw [add_comm]
  exact tsub_add_cancel_of_le (hκ x)

theorem cemeteryExtension_delta_univ (κ : ProbabilityTheory.Kernel α α) :
    cemeteryExtension κ Cemetery.delta Set.univ = 1 := by
  rw [cemeteryExtension_delta_apply' κ MeasurableSet.univ]
  simp only [Set.indicator_of_mem, Set.mem_univ, Pi.one_apply]

/-- The conservative cemetery extension is a Markov kernel. -/
theorem isMarkovKernel_cemeteryExtension (κ : ProbabilityTheory.Kernel α α)
    (hκ : IsSubMarkovKernel κ) : IsMarkovKernel (cemeteryExtension κ) := by
  refine ⟨fun z ↦ ⟨?_⟩⟩
  cases z with
  | inl x => exact cemeteryExtension_alive_univ κ hκ x
  | inr u => cases u; exact cemeteryExtension_delta_univ κ

/-- The cemetery state is absorbing under the conservative extension. -/
theorem cemeteryExtension_absorbing (κ : ProbabilityTheory.Kernel α α) :
    cemeteryExtension κ Cemetery.delta = Measure.dirac Cemetery.delta :=
  cemeteryExtension_delta_apply κ

end Kernel

end MarkovProcess
