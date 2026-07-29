/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.TestFunction.Amplitude
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! TODO: Add doc-string. -/

@[expose] public section

open Filter
open scoped Topology

namespace NumberField.Odlyzko

theorem tendsto_sin_sub_mul_cos_div_pow_three :
    Tendsto (fun x : ℝ ↦ (Real.sin x - x * Real.cos x) / x ^ 3)
      (𝓝[≠] 0) (𝓝 (1 / 3 : ℝ)) := by
  apply HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun x : ℝ ↦ Real.sin x * x) (g' := fun x : ℝ ↦ 3 * x ^ 2)
  · filter_upwards with x
    exact ((Real.hasDerivAt_sin x).sub
      ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))).congr_deriv (by
        grind)
  · filter_upwards with x
    exact (hasDerivAt_pow 3 x).congr_deriv (by norm_num)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp_all
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    change Tendsto (Real.sin - id * Real.cos) (𝓝 0) (𝓝 0)
    -- Stated at the Pi-algebra type so `tendsto` lands there; at v4.32 `simpa`
    -- no longer bridges the pointwise spelling on its own.
    have h : Continuous (Real.sin - id * Real.cos) :=
      Real.continuous_sin.sub (continuous_id.mul Real.continuous_cos)
    simpa using h.tendsto 0
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    have h : Continuous (fun x : ℝ ↦ x ^ 3) := by fun_prop
    simpa using h.tendsto 0
  · have hsinc : Tendsto Real.sinc (𝓝[≠] 0) (𝓝 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by
        simpa using Real.continuous_sinc.tendsto 0)
    have h : Tendsto (fun x : ℝ ↦ Real.sin x * x / (3 * x ^ 2))
        (𝓝[≠] 0) (𝓝 (1 / 3)) := (hsinc.div_const 3).congr' (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Real.sinc_of_ne_zero hx]
      grind)
    simp_all

theorem tendsto_tartarAmplitude_punctured_zero :
    Tendsto Tartar.amplitude (𝓝[≠] 0) (𝓝 1) := by
  convert (tendsto_sin_sub_mul_cos_div_pow_three.const_mul 3).congr' ?_ using 1
  · norm_num
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [tartarAmplitude_eq_of_ne hx]
  ring

theorem tartarAmplitude_continuousAt_zero :
    ContinuousAt Tartar.amplitude 0 := by
  rw [continuousAt_iff_punctured_nhds, tartarAmplitude_zero]
  exact tendsto_tartarAmplitude_punctured_zero

@[fun_prop]
theorem tartarAmplitude_continuous : Continuous Tartar.amplitude := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · simpa [hx] using tartarAmplitude_continuousAt_zero
  · exact tartarAmplitude_continuousAt_of_ne hx

@[fun_prop]
theorem tartarTestFunction_continuous : Continuous Tartar.testFunction := by
  unfold Tartar.testFunction
  fun_prop

end NumberField.Odlyzko
