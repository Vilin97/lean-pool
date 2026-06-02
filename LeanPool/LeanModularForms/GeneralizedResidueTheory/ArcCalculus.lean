/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Tactic.Common
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Homotopy.Basic

/-!
# Arc Calculus

General-purpose API for unit circle arc parameterizations and their properties.
Used for computing winding numbers, distances, and derivatives along circular arcs.

## Main definitions

* `unitArc` - parameterization of a unit circle arc from angle θ₁ to θ₂

## Main results

* `unitArc_norm` - points on the arc have norm 1
* `unitArc_hasDerivAt` - derivative formula for the arc
* `exp_sub_norm_sq` - distance formula between arc points via cosine
* `sin_pos_of_mem_Ioo_zero_pi` - sin is positive on (0, π)
-/

open Complex Real Set

namespace ArcCalculus

/-- Unit circle arc from angle θ₁ to θ₂, linearly parameterized on [a,b]. -/
noncomputable def unitArc (θ₁ θ₂ a b : ℝ) (t : ℝ) : ℂ :=
  exp (↑(θ₁ + (t - a) / (b - a) * (θ₂ - θ₁)) * I)

/-- Points on the unit arc have norm 1. -/
theorem unitArc_norm (θ₁ θ₂ a b t : ℝ) : ‖unitArc θ₁ θ₂ a b t‖ = 1 := by
  simp only [unitArc, Complex.norm_exp_ofReal_mul_I]

/-- The arc starts at exp(iθ₁). -/
theorem unitArc_at_start (θ₁ θ₂ a b : ℝ) :
    unitArc θ₁ θ₂ a b a = exp (↑θ₁ * I) := by
  simp only [unitArc, sub_self, zero_div, zero_mul, add_zero]

/-- The arc ends at exp(iθ₂). -/
theorem unitArc_at_end (θ₁ θ₂ a b : ℝ) (hab : a ≠ b) :
    unitArc θ₁ θ₂ a b b = exp (↑θ₂ * I) := by
  simp only [unitArc]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  congr 1
  push_cast
  have : (↑b - ↑a) / (↑b - ↑a) = (1 : ℂ) := by
    apply div_self; exact_mod_cast hba
  rw [this, one_mul]
  ring

/-- The unit arc is continuous. -/
theorem unitArc_continuous (θ₁ θ₂ a b : ℝ) : Continuous (unitArc θ₁ θ₂ a b) := by
  unfold unitArc
  apply Complex.continuous_exp.comp
  apply Continuous.mul
  · apply continuous_ofReal.comp
    fun_prop
  · exact continuous_const

/-- Helper: the angle function for the unit arc has a specific derivative. -/
private lemma unitArc_angle_hasDerivAt (θ₁ θ₂ a b t : ℝ) (hab : b - a ≠ 0) :
    HasDerivAt (fun s => θ₁ + (s - a) / (b - a) * (θ₂ - θ₁))
      ((θ₂ - θ₁) / (b - a)) t := by
  have hd : HasDerivAt (fun s => (s - a) / (b - a)) (1 / (b - a)) t := by
    simpa using ((hasDerivAt_id t).sub_const a).div_const (b - a)
  have h1 : HasDerivAt (fun s => (s - a) / (b - a) * (θ₂ - θ₁))
      ((θ₂ - θ₁) / (b - a)) t := by
    have hmul := hd.mul_const (θ₂ - θ₁)
    convert hmul using 1
    field_simp
  simpa using h1.const_add θ₁

/-- Derivative of the unit arc. -/
theorem unitArc_hasDerivAt (θ₁ θ₂ a b t : ℝ) (hab : a < b) :
    HasDerivAt (unitArc θ₁ θ₂ a b)
      (unitArc θ₁ θ₂ a b t * (↑((θ₂ - θ₁) / (b - a)) * I)) t := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hangle := unitArc_angle_hasDerivAt θ₁ θ₂ a b t hba
  -- Lift angle derivative to ℂ
  have hlift : HasDerivAt (fun s => (↑(θ₁ + (s - a) / (b - a) * (θ₂ - θ₁)) : ℂ))
      (↑((θ₂ - θ₁) / (b - a))) t :=
    hangle.ofReal_comp
  -- Multiply by I
  have hc : HasDerivAt (fun s => (↑(θ₁ + (s - a) / (b - a) * (θ₂ - θ₁)) : ℂ) * I)
      (↑((θ₂ - θ₁) / (b - a)) * I) t :=
    hlift.mul_const I
  -- Apply chain rule for cexp
  have hexp := hc.cexp
  simp only [unitArc]
  convert hexp using 1

/-- Key distance formula: squared norm of difference of two points on the unit circle. -/
theorem exp_sub_norm_sq (θ₁ θ₂ : ℝ) :
    ‖exp (↑θ₁ * I) - exp (↑θ₂ * I)‖ ^ 2 = 2 - 2 * Real.cos (θ₁ - θ₂) := by
  rw [← Complex.normSq_eq_norm_sq]
  -- Expand using exp(iθ) = cos θ + i sin θ
  simp only [Complex.normSq_apply, Complex.exp_mul_I, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.I_im, mul_one, sub_zero, Complex.add_im,
    Complex.mul_im, zero_add,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  have hc1 := Real.sin_sq_add_cos_sq θ₁
  have hc2 := Real.sin_sq_add_cos_sq θ₂
  rw [Real.cos_sub]
  nlinarith [sq_nonneg (Real.cos θ₁ - Real.cos θ₂),
             sq_nonneg (Real.sin θ₁ - Real.sin θ₂)]

/-- sin is positive on the open interval (0, π). -/
theorem sin_pos_of_mem_Ioo_zero_pi {θ : ℝ} (hθ : θ ∈ Ioo 0 π) : 0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2

/-- |cos θ| ≤ 1/2 for θ ∈ [π/3, 2π/3]. -/
theorem abs_cos_le_half_of_mem_Icc {θ : ℝ} (hθ : θ ∈ Icc (π / 3) (2 * π / 3)) :
    |Real.cos θ| ≤ 1 / 2 := by
  have hpi := Real.pi_pos
  have h1 : π / 3 ≤ θ := hθ.1
  have h2 : θ ≤ 2 * π / 3 := hθ.2
  rw [abs_le]; constructor
  · have : Real.cos (2 * π / 3) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h2
    rw [show (2 * π / 3 : ℝ) = π - π / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at this
    linarith
  · have : Real.cos θ ≤ Real.cos (π / 3) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) h1
    rw [Real.cos_pi_div_three] at this
    linarith

end ArcCalculus
