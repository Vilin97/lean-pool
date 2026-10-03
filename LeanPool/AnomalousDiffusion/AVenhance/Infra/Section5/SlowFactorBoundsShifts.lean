/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsProduct
public import Mathlib.Data.Nat.Choose.Bounds

/-! Fixed derivative shifts in factorial analytic bounds. -/

@[expose] public section

noncomputable section
open scoped ContDiff ENNReal
open MeasureTheory Homogenization AVenhance.FaaDiBruno
open AVenhance.Infra.Section4 AVenhance.Infra.Ergodic AVenhance.Infra.Torus
namespace AVenhance.Infra.Section5

/-- A fixed derivative shift costs a fixed factorial and doubles the rate. -/
theorem slowFactor_shift_factorial_le (n j : ℕ) :
    ((n + j).factorial : ℝ) ≤ j.factorial * (2 : ℝ) ^ j * n.factorial * 2 ^ n := by
  have hc := Nat.choose_le_two_pow (n + j) j
  have hh := Nat.add_choose_mul_factorial_mul_factorial n j
  have hb : (n + j).factorial ≤ 2 ^ (n + j) * n.factorial * j.factorial := by
    rw [← hh]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)
  have hr : ((n + j).factorial : ℝ) ≤ (2 : ℝ) ^ (n + j) * n.factorial * j.factorial := by
    exact_mod_cast hb
  calc
    _ ≤ _ := hr
    _ = _ := by rw [pow_add]; ring

/-- Moving to a larger derivative rate preserves the analytic envelope. -/
theorem slowFactor_rate_mono {F L L' : ℝ} (hF : 0 ≤ F) (hL : 0 ≤ L)
    (hLL' : L ≤ L') (n : ℕ) : F * n.factorial * L ^ n ≤ F * n.factorial * L' ^ n := by
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hLL' _) (by positivity)

/-- Shifting an averaged analytic field by a fixed ordered word. -/
theorem slowFactor_word_shift_eLpNorm_le {f : Vec 2 → ℝ} {F L : ℝ}
    (hF : 0 ≤ F) (hL : 0 ≤ L) (p : ℝ≥0∞) (μ : Measure (Vec 2))
    (hb : ∀ w, eLpNorm (amnrSpaceWord w f) p μ ≤
      ENNReal.ofReal (F * w.length.factorial * L ^ w.length))
    (η w : List (Fin 2)) :
    eLpNorm (amnrSpaceWord w (amnrSpaceWord η f)) p μ ≤
      ENNReal.ofReal ((F * η.length.factorial * (2 * L) ^ η.length) *
        w.length.factorial * (2 * L) ^ w.length) := by
  rw [← amnrSpaceWord_append]
  apply (hb (w ++ η)).trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [List.length_append]
  calc
    _ ≤ F * (η.length.factorial * (2 : ℝ) ^ η.length * w.length.factorial *
        2 ^ w.length) * L ^ (w.length + η.length) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (slowFactor_shift_factorial_le _ _) hF) (by positivity)
    _ = _ := by rw [pow_add, mul_pow, mul_pow]; ring

/-- Only positive T jets are consumed, even when w is empty. -/
theorem slowFactor_positive_temperature_shift {T : Vec 2 → ℝ} {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (p : ℝ≥0∞) (μ : Measure (Vec 2))
    (hT : ∀ w, 0 < w.length → eLpNorm (amnrSpaceWord w T) p μ ≤
      ENNReal.ofReal (M * w.length.factorial * L ^ w.length))
    (η : List (Fin 2)) (hη : 0 < η.length) (w : List (Fin 2)) :
    eLpNorm (amnrSpaceWord w (amnrSpaceWord η T)) p μ ≤
      ENNReal.ofReal ((M * η.length.factorial * (2 * L) ^ η.length) *
        w.length.factorial * (2 * L) ^ w.length) := by
  rw [← amnrSpaceWord_append]
  have hh := hT (w ++ η) (by simp only [List.length_append]; omega)
  apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [List.length_append]
  calc
    _ ≤ M * (η.length.factorial * (2 : ℝ) ^ η.length * w.length.factorial *
        2 ^ w.length) * L ^ (w.length + η.length) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (slowFactor_shift_factorial_le _ _) hM) (by positivity)
    _ = _ := by rw [pow_add, mul_pow, mul_pow]; ring

end AVenhance.Infra.Section5
