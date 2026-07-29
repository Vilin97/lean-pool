/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Numerics.CosineTaylor
public import LeanPool.Odlyzko.TestFunction.Quadratic

/-! TODO: Add doc-string. -/

@[expose] public section

open MeasureTheory Set

namespace NumberField.Odlyzko

/-- A tartar amplitude lower six used in the Odlyzko-bound argument. -/
noncomputable def tartarAmplitudeLowerSix (x : ℝ) : ℝ :=
  1 - x ^ 2 / 10 + x ^ 4 / 280 - x ^ 6 / 15120

private theorem tartarWeight_mul_pow_integrable (n : ℕ) :
    Integrable (fun t : ℝ ↦ Tartar.weight t * t ^ n) := by
  rw [tartarWeight_eq_indicator]
  have hind :
      (fun t : ℝ ↦
        (Set.Icc (-1 : ℝ) 1).indicator (fun u ↦ 1 - u ^ 2) t * t ^ n) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun t ↦ (1 - t ^ 2) * t ^ n) := by
    funext t
    exact (Set.indicator_mul_left (M₀ := ℝ) (Set.Icc (-1 : ℝ) 1)
      (fun u : ℝ ↦ 1 - u ^ 2) (fun u : ℝ ↦ u ^ n)).symm
  rw [hind]
  exact (by fun_prop : Continuous (fun t : ℝ ↦ (1 - t ^ 2) * t ^ n)).continuousOn
    |>.integrableOn_Icc.integrable_indicator measurableSet_Icc

private theorem integral_tartarWeight_mul_pow_four :
    ∫ t : ℝ, Tartar.weight t * t ^ 4 = 4 / 35 := by
  rw [tartarWeight_eq_indicator]
  have hind :
      (fun t : ℝ ↦
        (Set.Icc (-1 : ℝ) 1).indicator (fun u ↦ 1 - u ^ 2) t * t ^ 4) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun t ↦ (1 - t ^ 2) * t ^ 4) := by
    funext t
    exact (Set.indicator_mul_left (M₀ := ℝ) (Set.Icc (-1 : ℝ) 1)
      (fun u : ℝ ↦ 1 - u ^ 2) (fun u : ℝ ↦ u ^ 4)).symm
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [show (fun t : ℝ ↦ (1 - t ^ 2) * t ^ 4) =
      (fun t : ℝ ↦ t ^ 4 - t ^ 6) by grind,
    intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun t : ℝ ↦ t ^ 4)).intervalIntegrable (-1) 1)
      ((by fun_prop : Continuous (fun t : ℝ ↦ t ^ 6)).intervalIntegrable (-1) 1),
    integral_pow, integral_pow]
  norm_num

private theorem integral_tartarWeight_mul_pow_six :
    ∫ t : ℝ, Tartar.weight t * t ^ 6 = 4 / 63 := by
  rw [tartarWeight_eq_indicator]
  have hind :
      (fun t : ℝ ↦
        (Set.Icc (-1 : ℝ) 1).indicator (fun u ↦ 1 - u ^ 2) t * t ^ 6) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun t ↦ (1 - t ^ 2) * t ^ 6) := by
    funext t
    exact (Set.indicator_mul_left (M₀ := ℝ) (Set.Icc (-1 : ℝ) 1)
      (fun u : ℝ ↦ 1 - u ^ 2) (fun u : ℝ ↦ u ^ 6)).symm
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [show (fun t : ℝ ↦ (1 - t ^ 2) * t ^ 6) =
      (fun t : ℝ ↦ t ^ 6 - t ^ 8) by grind,
    intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun t : ℝ ↦ t ^ 6)).intervalIntegrable (-1) 1)
      ((by fun_prop : Continuous (fun t : ℝ ↦ t ^ 8)).intervalIntegrable (-1) 1),
    integral_pow, integral_pow]
  norm_num

theorem tartarAmplitudeLowerSix_le {x : ℝ} (hx : |x| ≤ 4) :
    tartarAmplitudeLowerSix x ≤ Tartar.amplitude x := by
  rw [tartarAmplitude_eq_cosineTransform]
  let p : ℝ → ℝ := fun t ↦ Tartar.weight t * cosLowerSix (x * t)
  have hp : Integrable p := by
    have h0 := tartarWeight_integrable
    have h2 := (tartarWeight_mul_pow_integrable 2).const_mul (x ^ 2 / 2)
    have h4 := (tartarWeight_mul_pow_integrable 4).const_mul (x ^ 4 / 24)
    have h6 := (tartarWeight_mul_pow_integrable 6).const_mul (x ^ 6 / 720)
    convert ((h0.sub h2).add h4).sub h6 using 1
    funext t
    simp only [Pi.sub_apply, Pi.add_apply, p, cosLowerSix]
    ring
  have hmono :
      (∫ t : ℝ, p t) ≤ ∫ t : ℝ, Tartar.weight t * Real.cos (x * t) := by
    apply integral_mono hp (tartarWeight_mul_cos_integrable x)
    intro t
    by_cases hwt : Tartar.weight t = 0
    · simp [p, hwt]
    apply mul_le_mul_of_nonneg_left
    · apply cosLowerSix_le_cos
      have htmem : t ∈ Set.Icc (-1 : ℝ) 1 :=
        support_tartarWeight_subset (by simp_all)
      have ht : |t| ≤ 1 := by grind
      calc
        |x * t| = |x| * |t| := abs_mul _ _
        _ ≤ 4 * 1 := mul_le_mul hx ht (abs_nonneg _) (by norm_num)
        _ = 4 := by norm_num
    · exact tartarWeight_nonneg t
  have hcalc :
      ∫ t : ℝ, p t =
        4 / 3 - (x ^ 2 / 2) * (4 / 15) +
          (x ^ 4 / 24) * (4 / 35) - (x ^ 6 / 720) * (4 / 63) := by
    change ∫ t : ℝ, Tartar.weight t * cosLowerSix (x * t) = _
    have h2 := tartarWeight_mul_pow_integrable 2
    have h4 := tartarWeight_mul_pow_integrable 4
    have h6 := tartarWeight_mul_pow_integrable 6
    have h2c := h2.const_mul (x ^ 2 / 2)
    have h4c := h4.const_mul (x ^ 4 / 24)
    have h6c := h6.const_mul (x ^ 6 / 720)
    have h02 := tartarWeight_integrable.sub h2c
    have h024 := h02.add h4c
    change Integrable (fun t : ℝ ↦ Tartar.weight t -
      (x ^ 2 / 2) * (Tartar.weight t * t ^ 2)) at h02
    change Integrable (fun t : ℝ ↦ Tartar.weight t -
      (x ^ 2 / 2) * (Tartar.weight t * t ^ 2) +
      (x ^ 4 / 24) * (Tartar.weight t * t ^ 4)) at h024
    calc
      ∫ t : ℝ, Tartar.weight t * cosLowerSix (x * t) =
          ∫ t : ℝ, (Tartar.weight t -
            (x ^ 2 / 2) * (Tartar.weight t * t ^ 2) +
            (x ^ 4 / 24) * (Tartar.weight t * t ^ 4) -
            (x ^ 6 / 720) * (Tartar.weight t * t ^ 6)) := by
              apply integral_congr_ae
              filter_upwards [] with t
              simp only [cosLowerSix]
              ring
      _ = (∫ t : ℝ, Tartar.weight t) -
            (x ^ 2 / 2) * (∫ t : ℝ, Tartar.weight t * t ^ 2) +
            (x ^ 4 / 24) * (∫ t : ℝ, Tartar.weight t * t ^ 4) -
            (x ^ 6 / 720) * (∫ t : ℝ, Tartar.weight t * t ^ 6) := by
              calc
                _ = (∫ t : ℝ, Tartar.weight t -
                      (x ^ 2 / 2) * (Tartar.weight t * t ^ 2) +
                      (x ^ 4 / 24) * (Tartar.weight t * t ^ 4)) -
                    ∫ t : ℝ, (x ^ 6 / 720) * (Tartar.weight t * t ^ 6) := by
                      apply integral_sub
                      · simp_all
                      · grind
                _ = ((∫ t : ℝ, Tartar.weight t -
                      (x ^ 2 / 2) * (Tartar.weight t * t ^ 2)) +
                    ∫ t : ℝ, (x ^ 4 / 24) * (Tartar.weight t * t ^ 4)) -
                    ∫ t : ℝ, (x ^ 6 / 720) * (Tartar.weight t * t ^ 6) := by
                      rw [integral_add]
                      · simp_all
                      · grind
                _ = _ := by
                      rw [integral_sub tartarWeight_integrable h2c,
                        integral_const_mul, integral_const_mul, integral_const_mul]
      _ = _ := by
        rw [integral_tartarWeight, integral_tartarWeight_mul_sq,
          integral_tartarWeight_mul_pow_four, integral_tartarWeight_mul_pow_six]
  calc
    tartarAmplitudeLowerSix x =
        (3 / 4 : ℝ) * (4 / 3 - (x ^ 2 / 2) * (4 / 15) +
          (x ^ 4 / 24) * (4 / 35) - (x ^ 6 / 720) * (4 / 63)) := by
            simp only [tartarAmplitudeLowerSix]
            ring
    _ = (3 / 4 : ℝ) * ∫ t : ℝ, p t := by simp_all
    _ ≤ (3 / 4 : ℝ) * ∫ t : ℝ, Tartar.weight t * Real.cos (x * t) := by simp_all

end NumberField.Odlyzko
