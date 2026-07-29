/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.TestFunction.Fourier
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! TODO: Add doc-string. -/

@[expose] public section

open MeasureTheory Set

namespace NumberField.Odlyzko

theorem integral_tartarWeight_mul_sq :
    ∫ t : ℝ, Tartar.weight t * t ^ 2 = 4 / 15 := by
  rw [tartarWeight_eq_indicator]
  have hind :
      (fun t : ℝ ↦
        (Set.Icc (-1 : ℝ) 1).indicator (fun u ↦ 1 - u ^ 2) t * t ^ 2) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun t ↦ (1 - t ^ 2) * t ^ 2) := by
    funext t
    exact (Set.indicator_mul_left (M₀ := ℝ) (Set.Icc (-1 : ℝ) 1)
      (fun u : ℝ ↦ 1 - u ^ 2) (fun u : ℝ ↦ u ^ 2)).symm
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [show (fun t : ℝ ↦ (1 - t ^ 2) * t ^ 2) =
      (fun t : ℝ ↦ t ^ 2 - t ^ 4) by grind,
    intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun t : ℝ ↦ t ^ 2)).intervalIntegrable (-1) 1)
      ((by fun_prop : Continuous (fun t : ℝ ↦ t ^ 4)).intervalIntegrable (-1) 1),
    integral_pow, integral_pow]
  norm_num

theorem tartarWeight_mul_sq_integrable :
    Integrable (fun t : ℝ ↦ Tartar.weight t * t ^ 2) := by
  rw [tartarWeight_eq_indicator]
  have hind :
      (fun t : ℝ ↦
        (Set.Icc (-1 : ℝ) 1).indicator (fun u ↦ 1 - u ^ 2) t * t ^ 2) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun t ↦ (1 - t ^ 2) * t ^ 2) := by
    funext t
    exact (Set.indicator_mul_left (M₀ := ℝ) (Set.Icc (-1 : ℝ) 1)
      (fun u : ℝ ↦ 1 - u ^ 2) (fun u : ℝ ↦ u ^ 2)).symm
  rw [hind]
  exact (by fun_prop : Continuous (fun t : ℝ ↦ (1 - t ^ 2) * t ^ 2)).continuousOn
    |>.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem one_sub_sq_div_ten_le_tartarAmplitude (x : ℝ) :
    1 - x ^ 2 / 10 ≤ Tartar.amplitude x := by
  rw [tartarAmplitude_eq_cosineTransform]
  have hleft :
      Integrable (fun t : ℝ ↦ Tartar.weight t * (1 - (x * t) ^ 2 / 2)) := by
    have hi := tartarWeight_integrable.sub
      (tartarWeight_mul_sq_integrable.const_mul (x ^ 2 / 2))
    convert hi using 1
    funext t
    simp only [Pi.sub_apply]
    ring
  have hcos := tartarWeight_mul_cos_integrable x
  have hint :
      (∫ t : ℝ, Tartar.weight t * (1 - (x * t) ^ 2 / 2)) ≤
        ∫ t : ℝ, Tartar.weight t * Real.cos (x * t) := by
    apply integral_mono hleft hcos
    intro t
    exact mul_le_mul_of_nonneg_left Real.one_sub_sq_div_two_le_cos
      (tartarWeight_nonneg t)
  have hcalc :
      ∫ t : ℝ, Tartar.weight t * (1 - (x * t) ^ 2 / 2) =
        4 / 3 - x ^ 2 * (2 / 15) := by
    calc
      ∫ t : ℝ, Tartar.weight t * (1 - (x * t) ^ 2 / 2)
          = ∫ t : ℝ, (Tartar.weight t -
              (x ^ 2 / 2) * (Tartar.weight t * t ^ 2)) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with t
            ring
      _ = (∫ t : ℝ, Tartar.weight t) -
              (∫ t : ℝ, (x ^ 2 / 2) * (Tartar.weight t * t ^ 2)) :=
            MeasureTheory.integral_sub tartarWeight_integrable
              (tartarWeight_mul_sq_integrable.const_mul (x ^ 2 / 2))
      _ = (∫ t : ℝ, Tartar.weight t) -
              (x ^ 2 / 2) * ∫ t : ℝ, Tartar.weight t * t ^ 2 := by
            rw [MeasureTheory.integral_const_mul]
      _ = 4 / 3 - x ^ 2 * (2 / 15) := by
        rw [integral_tartarWeight, integral_tartarWeight_mul_sq]
        ring
  grind

theorem one_sub_tartarTestFunction_le_sq_div_five (x : ℝ) :
    1 - Tartar.testFunction x ≤ x ^ 2 / 5 := by
  rw [Tartar.testFunction]
  have hamp := one_sub_sq_div_ten_le_tartarAmplitude x
  nlinarith [sq_nonneg (Tartar.amplitude x - 1)]

end NumberField.Odlyzko
