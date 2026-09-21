/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # Pole normalization of sine-square metric evolution -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology

namespace LichnerowiczObata
/-- Removing the quadratic vanishing factor determines the limiting
sine-square normalization. The limit is taken from positive parameters. -/
theorem tendsto_sine_normalized_quadratic {G : ℝ → ℝ} {C freq : ℝ}
    (hG : Tendsto G (𝓝[>] 0) (𝓝 C)) (hf : freq ≠ 0) :
    Tendsto (fun r => r ^ 2 * G r / Real.sin (freq * r) ^ 2)
      (𝓝[>] 0) (𝓝 (C / freq ^ 2)) := by
  have hd : Tendsto (fun r : ℝ => (freq * Real.sinc (freq * r)) ^ 2)
      (𝓝[>] 0) (𝓝 (freq ^ 2)) := by
    have hp : ContinuousAt (fun r : ℝ => (freq * Real.sinc (freq * r)) ^ 2) 0 := by
      fun_prop
    simpa only [mul_zero, Real.sinc_zero, mul_one] using
      hp.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := hG.div hd (pow_ne_zero 2 hf)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := ne_of_gt hr
  change G r / (freq * Real.sinc (freq * r)) ^ 2 = _
  rw [Real.sinc_of_ne_zero (mul_ne_zero hf hr0)]
  field_simp [hf, hr0]

/-- A constant sine-square normalization is fixed by the center limit,
even when only a short positive interval is available. -/
theorem sine_normalized_eq_of_pole_limit {G : ℝ → ℝ} {C freq ε A : ℝ}
    (hG : Tendsto G (𝓝[>] 0) (𝓝 C)) (hf : freq ≠ 0) (hε : 0 < ε)
    (hconst : ∀ r ∈ Ioo 0 ε, r ^ 2 * G r / Real.sin (freq * r) ^ 2 = A) :
    A = C / freq ^ 2 := by
  have he : (fun r => r ^ 2 * G r / Real.sin (freq * r) ^ 2) =ᶠ[𝓝[>] 0]
      (fun _ => A) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with r hr hsmall
    exact hconst r ⟨hr, hsmall⟩
  exact tendsto_nhds_unique tendsto_const_nhds
    ((tendsto_sine_normalized_quadratic hG hf).congr' he)

end LichnerowiczObata
