/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Pointwise Riesz measures of positive operators on `C₀`

A positive continuous linear operator on real continuous functions vanishing at infinity gives,
after evaluation at a point, a positive linear functional on compactly supported continuous
functions. The real Riesz--Markov--Kakutani theorem represents this functional by a regular,
locally finite measure.

This file makes only this pointwise construction. It does not prove that the measures depend
measurably on the evaluation point, have bounded total mass, form a kernel, or satisfy any
semigroup or stochastic-process law.
-/

open CompactlySupported MeasureTheory
open scoped ZeroAtInfty

namespace MarkovProcess

variable {α : Type*} [TopologicalSpace α]

/-- Evaluation at a point, as a bounded linear functional on `C₀(α, ℝ)`. -/
noncomputable def c0EvalCLM (x : α) : C₀(α, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl } 1 fun f ↦ by
    rw [one_mul, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF x

/-- Evaluation, unfolded. -/
@[simp]
theorem c0EvalCLM_apply (x : α) (f : C₀(α, ℝ)) : c0EvalCLM x f = f x :=
  rfl

namespace PositiveC0OperatorMeasure

/-- Pointwise preservation of nonnegative functions by an operator on `C₀(α, ℝ)`. -/
def IsPositive (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) : Prop :=
  ∀ f : C₀(α, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T f x

/-- A positive operator on `C₀` is monotone for the pointwise order. -/
theorem apply_le_apply_of_isPositive
    (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)
    {f g : C₀(α, ℝ)} (hfg : ∀ x, f x ≤ g x) (x : α) :
    T f x ≤ T g x := by
  have hnonneg : ∀ y, 0 ≤ (g - f) y := fun y ↦ sub_nonneg.mpr (hfg y)
  have h := hT (g - f) hnonneg x
  rw [map_sub] at h
  exact sub_nonneg.mp h

/-- The canonical real-linear inclusion of compactly supported continuous functions into `C₀`. -/
noncomputable def compactlySupportedToC0LinearMap : C_c(α, ℝ) →ₗ[ℝ] C₀(α, ℝ) where
  toFun f := f
  map_add' f g := by
    ext x
    rfl
  map_smul' c f := by
    ext x
    rfl

@[simp]
theorem compactlySupportedToC0LinearMap_apply (f : C_c(α, ℝ)) (x : α) :
    compactlySupportedToC0LinearMap f x = f x :=
  rfl

variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)

/-- Evaluation at `x` after applying `T`, restricted from `C₀(α, ℝ)` to compactly supported
continuous functions, as a positive linear functional. -/
noncomputable def functional (x : α) : C_c(α, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f ↦ T (compactlySupportedToC0LinearMap f) x
      map_add' := by
        intro f g
        rw [map_add, map_add]
        rfl
      map_smul' := by
        intro c f
        rw [map_smul, map_smul]
        rfl }
    fun f hf ↦ hT (compactlySupportedToC0LinearMap f) (fun y ↦ hf y) x

@[simp]
theorem functional_apply (x : α) (f : C_c(α, ℝ)) :
    functional T hT x f = T (compactlySupportedToC0LinearMap f) x :=
  rfl

variable [T2Space α] [LocallyCompactSpace α] [MeasurableSpace α] [BorelSpace α]

/-- The regular Riesz measure representing point evaluation after applying `T`. -/
noncomputable def measure (x : α) : Measure α :=
  RealRMK.rieszMeasure (functional T hT x)

instance regular_measure (x : α) : (measure T hT x).Regular :=
  RealRMK.regular_rieszMeasure (functional T hT x)

instance isFiniteMeasureOnCompacts_measure (x : α) :
    IsFiniteMeasureOnCompacts (measure T hT x) :=
  inferInstance

/-- The pointwise Riesz measure represents `T` exactly on every compactly supported continuous
function. -/
@[simp]
theorem integral_measure (x : α) (f : C_c(α, ℝ)) :
    ∫ y, f y ∂(measure T hT x) = T (compactlySupportedToC0LinearMap f) x := by
  rw [measure, RealRMK.integral_rieszMeasure]
  rfl

end PositiveC0OperatorMeasure

end MarkovProcess
