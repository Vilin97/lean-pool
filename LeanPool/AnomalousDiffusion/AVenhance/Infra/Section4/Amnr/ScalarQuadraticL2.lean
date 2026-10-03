/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SpatialFluxCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureSpatialWords
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureEnergyIntegrability
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemporalPairing
public import Mathlib.MeasureTheory.Function.L2Space

/-! Exact conversion between scalar quadratic energy and the L2 norm. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

theorem amnr_scalar_eLpNorm_two_eq_sqrt {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfsq : Integrable (fun z => f z ^ 2) μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ z, f z ^ 2 ∂μ)) := by
  have hm := (memLp_two_iff_integrable_sq hf).mpr hfsq
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_eq_rpow, one_div]

/-- A nonnegative quadratic energy bound gives the corresponding scalar L2
bound without weakening it to a pointwise estimate. -/
theorem amnr_scalar_eLpNorm_two_le_of_square {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfsq : Integrable (fun z => f z ^ 2) μ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : (∫ z, f z ^ 2 ∂μ) ≤ B ^ 2) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal B := by
  rw [amnr_scalar_eLpNorm_two_eq_sqrt hf hfsq]
  apply ENNReal.ofReal_le_ofReal
  exact (Real.sqrt_le_iff).mpr ⟨hB, hbound⟩

/-- Conversely, finite scalar L2 control bounds the actual quadratic integral. -/
theorem amnr_scalar_square_le_of_eLpNorm_two {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    {B : ℝ} (hB : 0 ≤ B) (hbound : eLpNorm f 2 μ ≤ ENNReal.ofReal B) :
    (∫ z, f z ^ 2 ∂μ) ≤ B ^ 2 := by
  have hm : MemLp f 2 μ := hbound.trans_lt (by finiteness)
  have hi := hm.integrable_sq
  rw [amnr_scalar_eLpNorm_two_eq_sqrt hf hi, ENNReal.ofReal_le_ofReal_iff hB] at hbound
  exact (Real.sqrt_le_iff).mp hbound |>.2

end AVenhance.Infra.Section4
