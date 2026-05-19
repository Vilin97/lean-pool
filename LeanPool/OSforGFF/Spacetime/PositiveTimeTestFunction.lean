/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.Spacetime.DiscreteSymmetry

/-!
# Positive Time Test Functions and Star Operations

This file defines test functions supported in the positive time region and implements
the star operation (complex conjugation composed with time reflection) for test functions.

## Main definitions

* `HasPositiveTime`: Predicate for spacetime points with positive time component
* `positiveTimeSet`: The set of all positive time points
* `PositiveTimeTestFunction`: Test functions supported in the positive time region
* `starTestFunction`: Star operation combining time reflection and complex conjugation
* `starRingEnd_iteratedFDeriv_norm_eq`: Helper lemma for norm preservation under star operation

## Main results

* `is_open_positiveTimeSet`: The positive time set is open
* `Star TestFunctionℂ`: Star instance for complex test functions
-/

noncomputable section

open TopologicalSpace Function SchwartzMap QFT

/-- A spacetime point has positive time if its time component is positive -/
def HasPositiveTime (x : SpaceTime) : Prop := getTimeComponent x > 0

/-- The set of all spacetime points with positive time -/
def positiveTimeSet : Set SpaceTime := {x | HasPositiveTime x}

/-- The positive time set is open -/
lemma is_open_positiveTimeSet : IsOpen positiveTimeSet :=
  isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ => ℝ) (0 : Fin STDimension))

/-- Submodule of **real-valued** test functions supported in the positive time region -/
def PositiveTimeTestFunctions.submodule : Submodule ℝ TestFunction where
  carrier := { f : TestFunction | tsupport f ⊆ positiveTimeSet }
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    suffices h : tsupport (0 : TestFunction) = ∅ by
      rw [h]
      apply Set.empty_subset
    rw [tsupport_eq_empty_iff]
    rfl
  add_mem' := fun {f g} hf hg => Set.Subset.trans (tsupport_add f g) (Set.union_subset hf hg)
  smul_mem' := by
    intro c f hf
    refine (tsupport_smul_subset_right (fun _ : SpaceTime => c) f).trans hf

/-- Type of real-valued test functions supported in the positive time region -/
abbrev PositiveTimeTestFunction : Type := PositiveTimeTestFunctions.submodule

instance : AddCommMonoid PositiveTimeTestFunction := by infer_instance
instance : AddCommGroup PositiveTimeTestFunction := by infer_instance

/-- Linear combinations of positive-time test functions are positive-time test functions. -/
lemma PositiveTimeTestFunction.sum_smul_mem
    {n : ℕ} (f : Fin n → PositiveTimeTestFunction) (c : Fin n → ℝ) :
    ∃ g : PositiveTimeTestFunction, g.val = ∑ i, c i • (f i).val := by
  -- Use the fact that PositiveTimeTestFunctions.submodule is closed under finite linear
  -- combinations
  use ∑ i, c i • (f i)
  -- The sum automatically lives in the submodule by the submodule properties
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]

/-- Submodule of **complex-valued** test functions supported in the positive time region.
    This is a ℂ-submodule since ℂ-scalar multiplication preserves support.
-/
def PositiveTimeTestFunctionsℂ.submodule : Submodule ℂ TestFunctionℂ where
  carrier := { f : TestFunctionℂ | tsupport f ⊆ positiveTimeSet }
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    suffices h : tsupport (0 : TestFunctionℂ) = ∅ by
      rw [h]
      apply Set.empty_subset
    rw [tsupport_eq_empty_iff]
    rfl
  add_mem' := fun {f g} hf hg => Set.Subset.trans (tsupport_add f g) (Set.union_subset hf hg)
  smul_mem' := by
    intro c f hf
    refine (tsupport_smul_subset_right (fun _ : SpaceTime => c) f).trans hf

/-- Type of complex-valued test functions supported in the positive time region -/
abbrev PositiveTimeTestFunctionℂ : Type := PositiveTimeTestFunctionsℂ.submodule

instance : AddCommMonoid PositiveTimeTestFunctionℂ := by infer_instance
instance : AddCommGroup PositiveTimeTestFunctionℂ := by infer_instance

lemma PositiveTimeTestFunctionℂ.zero_on_nonpositive
    (f : PositiveTimeTestFunctionℂ) {x : SpaceTime}
    (hx : getTimeComponent x ≤ 0) : f.val x = 0 := by
  classical
  have hx_not_support : x ∉ tsupport f.val := by
    intro hx_mem
    have hx_pos : getTimeComponent x > 0 := by
      have hx_mem_pos : x ∈ positiveTimeSet := f.property hx_mem
      simpa [positiveTimeSet, HasPositiveTime] using hx_mem_pos
    have : getTimeComponent x < getTimeComponent x := lt_of_le_of_lt hx hx_pos
    exact (lt_irrefl _ this)
  exact image_eq_zero_of_notMem_tsupport hx_not_support

/-- Helper lemma: starRingEnd ℂ commutes through derivatives and preserves norms -/
lemma starRingEnd_iteratedFDeriv_norm_eq (g : TestFunctionℂ) (n : ℕ) (x : SpaceTime) :
  ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (g x)) x‖ = ‖iteratedFDeriv ℝ n g x‖ := by
  -- Use the fact that starRingEnd ℂ = Complex.conjLIE (as functions)
  have h : (fun x => starRingEnd ℂ (g x)) = Complex.conjLIE ∘ g := by
    ext y
    rw [Function.comp_apply]
    -- Use the fact that conjLIE and starRingEnd are the same
    exact congr_fun (@RCLike.conjLIE_apply ℂ _) (g y)
  rw [h]
  -- Now apply the norm preservation lemma for LinearIsometryEquiv
  exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left Complex.conjLIE g x n

/-- Star operation on test functions: time reflection followed by complex conjugation -/
noncomputable def starTestFunction (f : TestFunctionℂ) : TestFunctionℂ :=
  -- Apply time reflection then complex conjugation pointwise
  let f_reflected := compTimeReflection f
  -- Apply complex conjugation to each value
  ⟨fun x => starRingEnd ℂ (f_reflected x),
   -- Smoothness: starRingEnd is smooth and compTimeReflection gives smooth functions
   by
     -- Apply the continuous linear map contDiff lemma
     apply ContDiff.comp
     · -- starRingEnd ℂ is smooth
       exact ContinuousLinearMap.contDiff (Complex.conjLIE.toContinuousLinearMap)
     · -- f_reflected is smooth
       exact f_reflected.smooth ⊤,
   -- Decay
   fun k n => by
     -- Use the bound from f_reflected and the fact that starRingEnd is an isometry
     obtain ⟨C, hC⟩ := f_reflected.decay' k n
     use C
     intro x
     -- Since starRingEnd ℂ is complex conjugation, which is an isometry,
     -- it preserves the norms of derivatives. This follows from standard properties
     -- of linear isometries and the chain rule for derivatives.
     have h_eq : ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (f_reflected x)) x‖ = ‖iteratedFDeriv
       ℝ n f_reflected x‖ :=
       starRingEnd_iteratedFDeriv_norm_eq f_reflected n x
     calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (f_reflected x)) x‖
         = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f_reflected x‖ := by rw [h_eq]
       _ ≤ C := hC x⟩

/-- Star instance for complex test functions -/
noncomputable instance : Star TestFunctionℂ where
  star f := starTestFunction f

lemma PositiveTimeTestFunction.zero_on_nonpositive
    (f : PositiveTimeTestFunction) {x : SpaceTime}
    (hx : getTimeComponent x ≤ 0) : f.val x = 0 := by
  classical
  have hx_not_support : x ∉ tsupport f.val := by
    intro hx_mem
    have hx_pos : getTimeComponent x > 0 := by
      have hx_mem_pos : x ∈ positiveTimeSet := f.property hx_mem
      simpa [positiveTimeSet, HasPositiveTime] using hx_mem_pos
    have : getTimeComponent x < getTimeComponent x := lt_of_le_of_lt hx hx_pos
    exact (lt_irrefl _ this)
  exact image_eq_zero_of_notMem_tsupport hx_not_support

end
