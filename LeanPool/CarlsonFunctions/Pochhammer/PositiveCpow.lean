/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Pochhammer.Gamma
public import LeanPool.CarlsonFunctions.Pochhammer.ComplexPowMeasurable
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Complex powers on the positive half-line

This scalar calculus has no simplex dependency. The historical `DirichletTransform`
namespace is retained for compatibility.
-/

open Complex Set Filter
open scoped Topology

@[expose] public noncomputable section

namespace DirichletTransform

/-- A complex power on the positive half-line, extended by zero. -/
def positiveCpow (a : ℂ) (x : ℝ) : ℂ :=
  if 0 < x then (x : ℂ) ^ a else 0

theorem continuous_positiveCpow {a : ℂ} (ha : 0 < a.re) :
    Continuous (positiveCpow a) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have heq : positiveCpow a = fun x : ℝ => ((max x 0 : ℝ) : ℂ) ^ a := by
    funext x
    by_cases hx : 0 < x
    · simp [positiveCpow, hx, max_eq_left hx.le]
    · simp [positiveCpow, hx, max_eq_right (le_of_not_gt hx), zero_cpow ha0]
  rw [heq]
  exact (continuous_ofReal_cpow_const ha).comp (continuous_id.max continuous_const)

theorem hasDerivAt_positiveCpow {a : ℂ} (ha : 1 < a.re) (x : ℝ) :
    HasDerivAt (positiveCpow a) (a * positiveCpow (a - 1) x) x := by
  have ha0 : a ≠ 0 := by intro h; norm_num [h] at ha
  have ham : 0 < (a - 1).re := by simp only [sub_re, one_re]; linarith
  have ham0 : a - 1 ≠ 0 := by intro h; simp [h] at ham
  rcases lt_trichotomy 0 x with hx | rfl | hx
  · rw [show positiveCpow (a - 1) x = (x : ℂ) ^ (a - 1) by simp [positiveCpow, hx]]
    apply (hasDerivAt_ofReal_cpow_const hx.ne' ha0).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp [positiveCpow, hy]
  · rw [show a * positiveCpow (a - 1) 0 = 0 by simp [positiveCpow]]
    rw [hasDerivAt_iff_tendsto_slope_left_right]
    constructor
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : x < 0 := hx
      simp [slope, positiveCpow, not_lt.mpr hx'.le]
    · have hlim := ((continuous_ofReal_cpow_const ham).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rw [ofReal_zero, zero_cpow ham0] at hlim
      apply hlim.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : 0 < x := hx
      have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx')
      simp only [slope, vsub_eq_sub, sub_zero, positiveCpow, hx', ite_true,
        lt_self_iff_false, ite_false, sub_zero, Complex.real_smul, ofReal_inv]
      rw [cpow_sub _ _ hx0, cpow_one]
      ring
  · rw [show a * positiveCpow (a - 1) x = 0 by
      simp [positiveCpow, not_lt.mpr hx.le]]
    apply (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    simp [positiveCpow, not_lt.mpr hy.le]

/-- The normalized positive power; differentiation lowers the parameter by one. -/
def positiveGammaPower (a : ℂ) (x : ℝ) : ℂ :=
  positiveCpow (a - 1) x / Gamma a

theorem continuous_positiveGammaPower {a : ℂ} (ha : 1 < a.re) :
    Continuous (positiveGammaPower a) :=
  (continuous_positiveCpow (by simp only [sub_re, one_re]; linarith)).div_const _

theorem hasDerivAt_positiveGammaPower {a : ℂ} (ha : 2 < a.re) (x : ℝ) :
    HasDerivAt (positiveGammaPower a) (positiveGammaPower (a - 1) x) x := by
  have ham : 0 < (a - 1).re := by simp only [sub_re, one_re]; linarith
  have ham0 : a - 1 ≠ 0 := by intro h; simp [h] at ham
  have hg : Gamma a = (a - 1) * Gamma (a - 1) := by
    simpa using Gamma_add_one (a - 1) ham0
  convert! (hasDerivAt_positiveCpow (a := a - 1)
    (by simp only [sub_re, one_re]; linarith) x).div_const (Gamma a) using 1
  change positiveCpow (a - 1 - 1) x / Gamma (a - 1) = _
  rw [hg]
  field_simp [ham0]

end DirichletTransform

end
