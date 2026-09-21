/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingReal

/-!
# Conventional exponential L²-norm form

This file repackages the already proved maximal second-moment estimate as
`‖M_h f‖₂ ≤ C 2^(-h/10) ‖f‖₂`, with a positive absolute constant and no
restriction on the real modulation parameter.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson

theorem fixedHeight_floor_decay_le_rpow (height : ℕ) :
    1 / (2 : ℝ) ^ ((height - 1) / 5) ≤
      2 * (2 : ℝ) ^ (-(height : ℝ) / 5) := by
  have hn : height ≤ 5 * ((height - 1) / 5) + 5 := by omega
  have hnR : (height : ℝ) ≤ 5 * (((height - 1) / 5 : ℕ) : ℝ) + 5 := by
    exact_mod_cast hn
  have he : (height : ℝ) / 5 ≤ (((height - 1) / 5 : ℕ) : ℝ) + 1 := by linarith
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast, Real.rpow_one] at hp
  have hinv : 1 / (2 : ℝ) ^ ((height - 1) / 5) ≤
      2 / (2 : ℝ) ^ ((height : ℝ) / 5) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      (by simpa only [one_mul, mul_comm] using hp)
  calc
    _ ≤ 2 / (2 : ℝ) ^ ((height : ℝ) / 5) := hinv
    _ = _ := by rw [neg_div, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]; rfl

theorem paperFixedHeightQuadraticMaximal_sq_lintegral_rpow_decay
    (height : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫⁻ x, paperFixedHeightQuadraticMaximal height f x ^ 2) ≤
      ENNReal.ofReal (141993451776 * positiveDyadicAmplitudeBound ^ 2 *
        (2 : ℝ) ^ (-(height : ℝ) / 5)) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  apply (paperFixedHeightQuadraticMaximal_sq_lintegral_decay height hf).trans
  apply mul_le_mul' ?_ le_rfl
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left (fixedHeight_floor_decay_le_rpow height)
    (by positivity : 0 ≤ 70996725888 * positiveDyadicAmplitudeBound ^ 2)
  calc
    _ = (70996725888 * positiveDyadicAmplitudeBound ^ 2) *
        (1 / (2 : ℝ) ^ ((height - 1) / 5)) := by ring
    _ ≤ (70996725888 * positiveDyadicAmplitudeBound ^ 2) *
        (2 * (2 : ℝ) ^ (-(height : ℝ) / 5)) := h
    _ = _ := by ring

/-- A positive absolute constant depending only on the fixed dyadic cutoff. -/
noncomputable def fixedHeightL2DecayConstant : ℝ :=
  1000000 * (positiveDyadicAmplitudeBound + 1)

theorem fixedHeightL2DecayConstant_pos : 0 < fixedHeightL2DecayConstant := by
  unfold fixedHeightL2DecayConstant
  positivity [positiveDyadicAmplitudeBound_nonneg]

theorem fixedHeightL2DecayConstant_sq_ge :
    141993451776 * positiveDyadicAmplitudeBound ^ 2 ≤ fixedHeightL2DecayConstant ^ 2 := by
  unfold fixedHeightL2DecayConstant
  nlinarith [positiveDyadicAmplitudeBound_nonneg, sq_nonneg positiveDyadicAmplitudeBound]

theorem eLpNorm_two_sq_lintegral {ε : Type*} [ENorm ε] (f : ℝ → ε) :
    eLpNorm f 2 ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.rpow_mul_natCast]
  norm_num

/-- The conventional fixed-height quadratic maximal `L²` decay estimate,
with exponent `1/10`, for the paper's actual unrestricted real supremum. -/
theorem paperFixedHeightQuadraticMaximal_eLpNorm_decay
    (height : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) :
    eLpNorm (paperFixedHeightQuadraticMaximal height f) 2 ≤
      ENNReal.ofReal (fixedHeightL2DecayConstant *
        (2 : ℝ) ^ (-(height : ℝ) / 10)) * eLpNorm f 2 := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  rw [ENNReal.rpow_two, ENNReal.rpow_two, mul_pow,
    eLpNorm_two_sq_lintegral (paperFixedHeightQuadraticMaximal height f),
    eLpNorm_two_sq_lintegral f]
  simp only [enorm_eq_self]
  rw [← ENNReal.ofReal_pow (by positivity [fixedHeightL2DecayConstant_pos])]
  apply (paperFixedHeightQuadraticMaximal_sq_lintegral_rpow_decay height hf).trans
  apply mul_le_mul' ?_ le_rfl
  apply ENNReal.ofReal_le_ofReal
  have hp : ((2 : ℝ) ^ (-(height : ℝ) / 10)) ^ 2 =
      (2 : ℝ) ^ (-(height : ℝ) / 5) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [mul_pow, hp]
  exact mul_le_mul_of_nonneg_right fixedHeightL2DecayConstant_sq_ge (by positivity)

theorem memLp_paperFixedHeightQuadraticMaximal
    (height : ℕ) {f : ℝ → ℂ} (hf : MemLp f 2) :
    MemLp (paperFixedHeightQuadraticMaximal height f) 2 := by
  refine ⟨(measurable_paperFixedHeightQuadraticMaximal height hf).aestronglyMeasurable,
    (paperFixedHeightQuadraticMaximal_eLpNorm_decay height hf).trans_lt ?_⟩
  exact ENNReal.mul_lt_top (by finiteness) hf.eLpNorm_lt_top

end QuadraticCarleson
