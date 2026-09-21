/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Strict parameters for the cube good-`lambda` iteration

The local comparison coefficient is fixed before the cube, solution, and
datum.  This file chooses the amplification and datum parameters which make
the weighted layer-cake self coefficient strictly smaller than one.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

namespace INTERNAL

private theorem rpow_product_goodLambda_factor
    {p r M : ℝ} (hM : 0 < M) :
    (M / 2) ^ (2 - r) * (2 * M) ^ (p - 2) =
      (2 : ℝ) ^ (p + r - 4) * M ^ (p - r) := by
  rw [Real.div_rpow hM.le (by norm_num : (0 : ℝ) ≤ 2),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hM.le]
  have hMprod : M ^ (2 - r) * M ^ (p - 2) = M ^ (p - r) := by
    rw [← Real.rpow_add hM]
    congr 1
    ring
  have htwoquot : (2 : ℝ) ^ (p - 2) / (2 : ℝ) ^ (2 - r) =
      (2 : ℝ) ^ (p + r - 4) := by
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    (M ^ (2 - r) / (2 : ℝ) ^ (2 - r)) *
        ((2 : ℝ) ^ (p - 2) * M ^ (p - 2)) =
        ((2 : ℝ) ^ (p - 2) / (2 : ℝ) ^ (2 - r)) *
          (M ^ (2 - r) * M ^ (p - 2)) := by
          field_simp [Real.rpow_pos_of_pos hM]
    _ = _ := by rw [htwoquot, hMprod]

/-- Fixed parameters which make the one-level good-`lambda` self coefficient
strictly smaller than one.  The result is deliberately stated in `ENNReal`,
matching the layer-cake integration theorem. -/
theorem exists_strict_goodLambda_parameters
    {p r : ℝ} {C : ℝ≥0∞} (hC : C ≠ ∞) (_hp : 2 < p) (hpr : p < r) :
    ∃ M eps : ℝ, 1 < M ∧ 0 < eps ∧ eps ≤ 1 ∧
      C * (ENNReal.ofReal ((M / 2) ^ (2 - r)) +
          ENNReal.ofReal (eps ^ (2 : ℕ))) *
        ENNReal.ofReal ((2 * M) ^ (p - 2)) < 1 := by
  let c : ℝ := C.toReal
  let a : ℝ := max c 1
  let delta : ℝ := r - p
  let A : ℝ := 4 * a * (2 : ℝ) ^ (p + r - 4)
  let M : ℝ := 2 + A ^ delta⁻¹
  let D : ℝ := a * (2 * M) ^ (p - 2)
  let eps : ℝ := (4 * (1 + D))⁻¹
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have ha_one : 1 ≤ a := by
    exact le_max_right _ _
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha_one
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  have hpow_two : 0 < (2 : ℝ) ^ (p + r - 4) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hM : 2 < M := by
    dsimp only [M]
    have : 0 < A ^ delta⁻¹ := Real.rpow_pos_of_pos hA _
    linarith
  have hMpos : 0 < M := by linarith
  have hMhalf : 0 < M / 2 := by positivity
  have hMpow : A < M ^ delta := by
    have hlt : A ^ delta⁻¹ < M := by
      dsimp only [M]
      linarith
    have := Real.rpow_lt_rpow (Real.rpow_nonneg hA.le _) hlt hdelta
    rw [Real.rpow_inv_rpow hA.le hdelta.ne'] at this
    exact this
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have heps : 0 < eps := by
    dsimp only [eps]
    positivity
  have heps_one : eps ≤ 1 := by
    dsimp only [eps]
    have hdenom : 1 ≤ 4 * (1 + D) := by nlinarith [hD]
    exact inv_le_one_of_one_le₀ hdenom
  have hfirst :
      c * (M / 2) ^ (2 - r) * (2 * M) ^ (p - 2) < 1 / 4 := by
    calc
      c * (M / 2) ^ (2 - r) * (2 * M) ^ (p - 2) =
          c * ((M / 2) ^ (2 - r) * (2 * M) ^ (p - 2)) := by ring
      _ = c * ((2 : ℝ) ^ (p + r - 4) * M ^ (p - r)) := by
        rw [rpow_product_goodLambda_factor hMpos]
      _ = c * (2 ^ (p + r - 4) * M ^ (p - r)) := rfl
      _ < 1 / 4 := by
        have hMneg : M ^ (p - r) < A⁻¹ := by
          rw [show p - r = -delta by dsimp only [delta]; ring,
            Real.rpow_neg hMpos.le]
          exact (inv_lt_inv₀ (Real.rpow_pos_of_pos hMpos _) hA).2 hMpow
        have hc_le_a : c ≤ a := le_max_left _ _
        have hleft : c * 2 ^ (p + r - 4) ≤ A / 4 := by
          dsimp only [A]
          nlinarith [mul_le_mul_of_nonneg_right hc_le_a hpow_two.le]
        calc
          c * (2 ^ (p + r - 4) * M ^ (p - r)) =
              (c * 2 ^ (p + r - 4)) * M ^ (p - r) := by ring
          _ ≤ (A / 4) * M ^ (p - r) :=
            mul_le_mul_of_nonneg_right hleft (Real.rpow_nonneg hMpos.le _)
          _ < (A / 4) * A⁻¹ :=
            mul_lt_mul_of_pos_left hMneg (by positivity)
          _ = 1 / 4 := by
            field_simp [hA.ne']
  have hsecond : c * (eps ^ (2 : ℕ)) * (2 * M) ^ (p - 2) < 1 / 4 := by
    have hc_le_a : c ≤ a := le_max_left _ _
    have hbase : c * (2 * M) ^ (p - 2) ≤ D := by
      dsimp only [D]
      exact mul_le_mul_of_nonneg_right hc_le_a (Real.rpow_nonneg (by positivity) _)
    have heps_sq : eps ^ (2 : ℕ) < (4 * (1 + D))⁻¹ := by
      dsimp only [eps]
      have heps_lt_one : eps < 1 := by
        exact inv_lt_one_of_one_lt₀ (by nlinarith [hD])
      calc
        eps ^ (2 : ℕ) < eps := by
          rw [pow_two]
          nlinarith [heps, heps_lt_one]
        _ = (4 * (1 + D))⁻¹ := rfl
    have hD_eps : D * (eps ^ (2 : ℕ)) < 1 / 4 := by
      calc
        D * (eps ^ (2 : ℕ)) < D * (4 * (1 + D))⁻¹ :=
          mul_lt_mul_of_pos_left heps_sq hD
        _ < 1 / 4 := by
          rw [← div_eq_mul_inv]
          apply (div_lt_iff₀ (by positivity : 0 < 4 * (1 + D))).2
          nlinarith [hD]
    calc
      c * eps ^ (2 : ℕ) * (2 * M) ^ (p - 2) =
          (c * (2 * M) ^ (p - 2)) * eps ^ (2 : ℕ) := by ring
      _ ≤ D * eps ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right hbase (sq_nonneg eps)
      _ < 1 / 4 := hD_eps
  refine ⟨M, eps, ?_, heps, heps_one, ?_⟩
  · linarith
  have hterm_one : 0 ≤ (M / 2) ^ (2 - r) := Real.rpow_nonneg hMhalf.le _
  have hterm_two : 0 ≤ eps ^ (2 : ℕ) := sq_nonneg eps
  have hreal :
      c * ((M / 2) ^ (2 - r) + eps ^ (2 : ℕ)) *
        (2 * M) ^ (p - 2) < 1 := by
    calc
      c * ((M / 2) ^ (2 - r) + eps ^ (2 : ℕ)) * (2 * M) ^ (p - 2) =
          c * (M / 2) ^ (2 - r) * (2 * M) ^ (p - 2) +
            c * eps ^ (2 : ℕ) * (2 * M) ^ (p - 2) := by ring
      _ < 1 / 4 + 1 / 4 := add_lt_add hfirst hsecond
      _ < 1 := by norm_num
  have hCeq : C = ENNReal.ofReal c := by
    dsimp only [c]
    exact (ENNReal.ofReal_toReal hC).symm
  rw [hCeq, ← ENNReal.ofReal_add hterm_one hterm_two,
    ← ENNReal.ofReal_mul hc,
    ← ENNReal.ofReal_mul (mul_nonneg hc (add_nonneg hterm_one hterm_two))]
  exact ENNReal.ofReal_lt_one.mpr hreal

end INTERNAL

end CubeCalderonZygmund

end

end Homogenization
