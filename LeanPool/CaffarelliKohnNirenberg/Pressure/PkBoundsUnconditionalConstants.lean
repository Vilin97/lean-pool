/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalCore
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalScale

/-!
# Pk Bounds Unconditional Constants

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

/-! Explicit constants used by the three unconditional pressure estimates. -/

/-- Combined coefficient for the three velocity-tensor pressure corrections. -/
@[expose]
noncomputable def pressureP234Constant : ℝ :=
  3 *
    (9 * sobolevPoincareL6Constant.toReal *
      (18 * cutoffSecondDerivativeConstant + 720 * cutoffGradientConstant) *
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ)) *
    (4 * Real.pi / 3) ^ (2 / 3 : ℝ)

/-- Combined coefficient for the two pressure-cutoff corrections. -/
@[expose]
noncomputable def pressureP56Constant : ℝ :=
  2 *
    ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
      (18 * cutoffSecondDerivativeConstant + 240 * cutoffGradientConstant)) *
    (4 * Real.pi / 3) ^ (2 / 3 : ℝ)

/-- Common coefficient dominating the velocity and pressure cutoff contributions. -/
noncomputable def pressureP12Constant : ℝ :=
  max pressureP234Constant pressureP56Constant

/-- Exponent-dependent coefficient for the force-cutoff contribution. -/
@[expose]
noncomputable def pressureP13Constant (q : ℝ) : ℝ :=
  6 * cutoffGradientConstant *
    (4 * Real.pi / 3) ^ (1 - 1 / q) *
    (4 * Real.pi / 3) ^ (2 / 3 : ℝ)

lemma pressure_cutoff_constants_nonneg {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    0 ≤ cutoffGradientConstant ∧ 0 ≤ cutoffSecondDerivativeConstant := by
  constructor
  · have h := pressure_cutoff_spatialDeriv_bound x₀ hρ x₀ (0 : Fin 3)
    have h' : 0 ≤ cutoffGradientConstant / ρ := (abs_nonneg _).trans h
    rcases (div_nonneg_iff.mp h') with hpos | hneg
    · exact hpos.1
    · exfalso
      linarith only [hρ, hneg.2]
  · have h := pressure_cutoff_mixedSecond_bound x₀ hρ x₀ (0 : Fin 3) 0
    have h' : 0 ≤ cutoffSecondDerivativeConstant / ρ ^ 2 :=
      (abs_nonneg _).trans h
    have hρsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ
    rcases (div_nonneg_iff.mp h') with hpos | hneg
    · exact hpos.1
    · exfalso
      linarith only [hρsq, hneg.2]

lemma pressureP234Constant_nonneg {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    0 ≤ pressureP234Constant := by
  have hC := pressure_cutoff_constants_nonneg (x₀ := x₀) hρ
  rcases hC with ⟨hC₁, hC₂⟩
  have hS : 0 ≤ sobolevPoincareL6Constant.toReal := ENNReal.toReal_nonneg
  have hv : 0 < 4 * Real.pi / 3 := by positivity
  unfold pressureP234Constant
  positivity

lemma pressureP56Constant_nonneg {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    0 ≤ pressureP56Constant := by
  have hC := pressure_cutoff_constants_nonneg (x₀ := x₀) hρ
  rcases hC with ⟨hC₁, hC₂⟩
  have hS : 0 ≤ sobolevPoincareL6Constant.toReal := ENNReal.toReal_nonneg
  have hv : 0 < 4 * Real.pi / 3 := by positivity
  unfold pressureP56Constant
  positivity

lemma pressureP13Constant_nonneg {x₀ : Vec3} {ρ q : ℝ} (hρ : 0 < ρ) :
    0 ≤ pressureP13Constant q := by
  have hC := pressure_cutoff_constants_nonneg (x₀ := x₀) hρ
  rcases hC with ⟨hC₁, hC₂⟩
  have hv : 0 < 4 * Real.pi / 3 := by positivity
  unfold pressureP13Constant
  positivity

lemma pressure_volume_ball {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    volume (vec3Ball x₀ r) =
      ENNReal.ofReal ((4 * Real.pi / 3) * r ^ (3 : ℕ)) := by
  rw [volume_vec3Ball_eq]
  rw [← ENNReal.ofReal_pow hr.le 3]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma pressure_rpow_three_halves {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ (3 / 2 : ℝ) = ρ * Real.sqrt ρ := by
  calc
    ρ ^ (3 / 2 : ℝ) = ρ ^ (1 + 1 / 2 : ℝ) := by congr 1; norm_num
    _ = ρ ^ (1 : ℝ) * ρ ^ (1 / 2 : ℝ) := Real.rpow_add hρ _ _
    _ = ρ * Real.sqrt ρ := by
      rw [Real.rpow_one]
      rw [Real.sqrt_eq_rpow]

lemma pressure_rpow_div {r ρ a : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    (r / ρ) ^ a = r ^ a * ρ ^ (-a) := by
  rw [div_eq_mul_inv, Real.mul_rpow hr.le (inv_nonneg.mpr hρ.le),
    Real.inv_rpow hρ.le, ← Real.rpow_neg hρ.le]

end CKN
