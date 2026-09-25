/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.MeasureBridge

/-! # Kernel Bridge -/

@[expose] public section

namespace FD1D

noncomputable section

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory

/-!
# Finite-law and finite-kernel measure bridges

This file proves that the measure representations in `MeasureBridge` commute
with the project's finite pushforward and one-step kernel operations.
-/

namespace FiniteLaw

variable {α β : Type*} [Fintype α] [Fintype β]

omit [Fintype α] in
/-- Measures on a finite measurable-singleton space are determined by point masses. -/
theorem measure_ext_of_singletons [Finite α] [MeasurableSpace α]
     {μ ν : Measure α}
    (h : ∀ x, μ ({x} : Set α) = ν ({x} : Set α)) :
    μ = ν :=
  Measure.ext_of_singleton h

/-- The independent product of two finite laws. -/
def product (μ : FiniteLaw α) (ν : FiniteLaw β) :
    FiniteLaw (α × β) where
  mass p := μ.mass p.1 * ν.mass p.2
  mass_nonneg p := mul_nonneg (μ.mass_nonneg p.1) (ν.mass_nonneg p.2)
  sum_mass := by
    rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum,
      μ.sum_mass, ν.sum_mass, one_mul]

@[simp]
theorem mass_product (μ : FiniteLaw α) (ν : FiniteLaw β) (x : α) (y : β) :
    (μ.product ν).mass (x, y) = μ.mass x * ν.mass y :=
  rfl

/-- Finite-law products become ordinary product measures. -/
@[simp]
theorem toMeasure_product
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) :
    (μ.product ν).toMeasure = μ.toMeasure.prod ν.toMeasure := by
  apply measure_ext_of_singletons
  rintro ⟨x, y⟩
  rw [toMeasure_apply_singleton, mass_product,
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    toMeasure_apply_singleton, toMeasure_apply_singleton,
    ENNReal.ofReal_mul (μ.mass_nonneg x)]

/-- Converting a finite-law pushforward to a measure is ordinary measure pushforward. -/
@[simp]
theorem toMeasure_map [DecidableEq β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : FiniteLaw α) (f : α → β) (hf : Measurable f) :
    Measure.map f μ.toMeasure = (μ.map f).toMeasure := by
  classical
  apply measure_ext_of_singletons
  intro y
  rw [Measure.map_apply hf (MeasurableSet.singleton y),
    toMeasure_apply_singleton, mass_map]
  rw [toMeasure, PMF.toMeasure_apply_fintype]
  simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff,
    toPMF_apply]
  rw [← Finset.sum_filter]
  symm
  simpa using
    (ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ.filter fun x => f x = y)
      (fun x hx => μ.mass_nonneg x))

end FiniteLaw

namespace FiniteKernel

variable {α : Type*} [Fintype α]

/-- A finite kernel's measure-valued row has the prescribed transition mass. -/
theorem toKernel_apply_singleton [MeasurableSpace α]
    [MeasurableSingletonClass α] (K : FiniteKernel α) (x y : α) :
    K.toKernel x ({y} : Set α) = ENNReal.ofReal (K x y) := by
  rw [toKernel_apply, FiniteLaw.toMeasure_apply_singleton, rowLaw_mass]

/-- Integrating one finite-kernel row agrees with its elementary weighted sum. -/
theorem integral_toKernel [MeasurableSpace α] [MeasurableSingletonClass α]
    (K : FiniteKernel α) (x : α) (f : α → ℝ) :
    ∫ y, f y ∂K.toKernel x = ∑ y, K x y * f y := by
  rw [toKernel_apply, FiniteLaw.integral_toMeasure_eq_expect]
  simp only [FiniteLaw.expect, rowLaw_mass]

/-- Mathlib kernel composition realizes the project's finite-law step. -/
@[simp]
theorem toMeasure_step [MeasurableSpace α]
    [MeasurableSingletonClass α] (K : FiniteKernel α) (μ : FiniteLaw α) :
    K.toKernel ∘ₘ μ.toMeasure = (K.step μ).toMeasure := by
  classical
  apply FiniteLaw.measure_ext_of_singletons
  intro y
  rw [Measure.bind_apply (MeasurableSet.singleton y)
    (Kernel.aemeasurable K.toKernel)]
  rw [lintegral_fintype]
  simp only [toKernel_apply, FiniteLaw.toMeasure_apply_singleton,
    rowLaw_mass, mass_step]
  calc
    ∑ x, ENNReal.ofReal (K x y) * ENNReal.ofReal (μ.mass x) =
        ∑ x, ENNReal.ofReal (μ.mass x * K x y) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [ENNReal.ofReal_mul (μ.mass_nonneg x)]
      exact mul_comm _ _
    _ = ENNReal.ofReal (∑ x, μ.mass x * K x y) := by
      symm
      simpa using
        (ENNReal.ofReal_sum_of_nonneg
          (s := Finset.univ)
          (fun x hx =>
            mul_nonneg (μ.mass_nonneg x) (K.trans_nonneg x y)))

end FiniteKernel

end

end FD1D
