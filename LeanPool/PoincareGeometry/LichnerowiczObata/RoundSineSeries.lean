/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.CPolynomialDef
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Smooth radial sine coordinates through a power series in squared radius -/

@[expose] public noncomputable section
open scoped Topology ContDiff
namespace LichnerowiczObata

def roundSineCoefficient (n : ℕ) : ℝ := (-1) ^ n / (2 * n + 1).factorial

def roundSineSeries : ℝ → ℝ := FormalMultilinearSeries.ofScalarsSum roundSineCoefficient

@[simp] theorem roundSineSeries_zero : roundSineSeries 0 = 1 := by
  simp [roundSineSeries, roundSineCoefficient]

theorem analyticAt_roundSineSeries_zero : AnalyticAt ℝ roundSineSeries 0 := by
  let p := FormalMultilinearSeries.ofScalars ℝ roundSineCoefficient
  have hr : (1 : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_bound (r := 1) 1
    intro n
    have hf : (1 : ℝ) ≤ (2 * n + 1).factorial := by
      exact_mod_cast Nat.factorial_pos (2 * n + 1)
    simpa [p, FormalMultilinearSeries.ofScalars_norm, roundSineCoefficient,
      norm_div, norm_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (2 * n + 1).factorial)] using (one_div_le_one_div_of_le (by norm_num) hf)
  exact (p.hasFPowerSeriesOnBall (lt_of_lt_of_le (by norm_num) hr)).analyticAt

theorem roundSineSeries_sq (x : ℝ) : roundSineSeries (x ^ 2) = Real.sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [Real.sinc_of_ne_zero hx]
  have hs := (Real.hasSum_sin x).div_const x
  rw [roundSineSeries, FormalMultilinearSeries.ofScalars_sum_eq]
  convert hs.tsum_eq using 1
  congr 1
  funext n
  simp only [roundSineCoefficient, smul_eq_mul, pow_mul, pow_add, pow_one]
  field_simp

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

def roundPoleSine (R : ℝ) (z : P) : P :=
  roundSineSeries (‖z‖ ^ 2 / R ^ 2) • z

@[simp] theorem roundPoleSine_zero (R : ℝ) : roundPoleSine (P := P) R 0 = 0 := by
  simp [roundPoleSine]

theorem roundPoleSine_eq (R : ℝ) (z : P) :
    roundPoleSine R z = Real.sinc (‖z‖ / R) • z := by
  rw [roundPoleSine, ← div_pow, roundSineSeries_sq]

theorem contDiffAt_roundPoleSine_zero (R : ℝ) :
    ContDiffAt ℝ ∞ (roundPoleSine (P := P) R) 0 := by
  have hq : ContDiffAt ℝ ∞ (fun z : P => ‖z‖ ^ 2 / R ^ 2) 0 :=
    (contDiff_norm_sq ℝ).contDiffAt.div_const _
  have hs : ContDiffAt ℝ ∞ roundSineSeries (‖(0 : P)‖ ^ 2 / R ^ 2) := by
    simpa using analyticAt_roundSineSeries_zero.contDiffAt
  exact (hs.comp 0 hq).smul contDiffAt_id

end LichnerowiczObata
