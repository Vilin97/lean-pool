/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPHarmonicCells

/-!
# Pressure Gradient Origin Gap Harmonic Moment

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4

/-- The harmonic moment coefficient is uniform on the admissible fixed collars. -/
theorem origin_harmonic_moment_constant_le_gap_absolute
    (C ρ : ℝ) (x : Vec3) (hC : 0 ≤ C) (hρlo : 1/128 ≤ ρ) (hρhi : ρ ≤ 1) :
    originHarmonicMomentConstant C ρ x ≤ originHarmonicAbsoluteMomentConstant (65536*C) := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by norm_num) hρlo
  have hpow : ρ^(-4 : ℝ) ≤ 268435456 := by
    have hh := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1/128) hρlo
      (by norm_num : (-4 : ℝ) ≤ 0)
    exact hh.trans_eq (by norm_num)
  have he : C*ρ^(-3 : ℝ)/ρ = C*ρ^(-4 : ℝ) := by
    norm_num [Real.rpow_neg, Real.rpow_natCast]
    field_simp
  have hfirst : C*ρ^(-3 : ℝ)/ρ ≤ 268435456*C := by
    rw [he]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hpow hC
  have hsecond : C*ρ^(-3 : ℝ)/((Real.pi*4/3)^(1/3 : ℝ)*ρ) ≤
      268435456*C/(Real.pi*4/3)^(1/3 : ℝ) := by
    have hh := div_le_div_of_nonneg_right hfirst
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi*4/3) (1/3 : ℝ))
    convert hh using 1
    ring
  have hv : volume (vec3Ball x ρ) ≤ ENNReal.ofReal (Real.pi*4/3) := by
    rw [volume_vec3Ball_eq]
    have hh : ENNReal.ofReal ρ ≤ 1 := by
      exact (ENNReal.ofReal_le_ofReal hρhi).trans_eq (by simp)
    exact (mul_le_mul' (pow_le_one₀ (by positivity) hh) le_rfl).trans_eq (one_mul _)
  unfold originHarmonicMomentConstant originHarmonicAbsoluteMomentConstant
  apply mul_le_mul'
  · exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hv (by norm_num))
  · apply add_le_add
    · apply ENNReal.rpow_le_rpow _ (by norm_num)
      change ENNReal.ofReal (C*ρ^(-3 : ℝ)/ρ) ≤ _
      simpa only [show (4096 : ℝ)*(65536*C) = 268435456*C by ring] using
        ENNReal.ofReal_le_ofReal hfirst
    · apply ENNReal.rpow_le_rpow _ (by norm_num)
      change ENNReal.ofReal (C*ρ^(-3 : ℝ)/((Real.pi*4/3)^(1/3 : ℝ)*ρ)) ≤ _
      simpa only [show (4096 : ℝ)*(65536*C) = 268435456*C by ring] using
        ENNReal.ofReal_le_ofReal hsecond


end CKN.Core.Step4
