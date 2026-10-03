/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.Interpolation

/-! # Transport from a power integral to the Lp seminorm

The scalar conversion requires measurability of only the two actual
functions. A finite input seminorm then gives a finite output seminorm.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Endgame

/-- A power-integral estimate gives the corresponding scalar Lp seminorm
estimate for two actual a.e. strongly measurable functions. -/
theorem eLpNorm_bound_of_absE_power_bound
    {f g : Vec3 → ℝ} {C p : ℝ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hp : 0 < p)
    (hbound : (∫⁻ x, absE g x ^ p) ≤ ENNReal.ofReal C * ∫⁻ x, absE f x ^ p) :
    eLpNorm g (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal C) ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  rw [eLpNorm_eq_eLpNorm' hpne ENNReal.ofReal_ne_top hg,
    eLpNorm_eq_eLpNorm' hpne ENNReal.ofReal_ne_top hf]
  have hpow : eLpNorm' g p volume ^ p ≤ ENNReal.ofReal C * eLpNorm' f p volume ^ p := by
    rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp]
    simpa only [absE, Real.enorm_eq_ofReal_abs] using hbound
  have hnorm : eLpNorm' g p volume ≤
      (ENNReal.ofReal C) ^ (1 / p) * eLpNorm' f p volume := by
    calc
      eLpNorm' g p volume = (eLpNorm' g p volume ^ p) ^ (1 / p) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]
      _ ≤ (ENNReal.ofReal C * eLpNorm' f p volume ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hpow (one_div_nonneg.mpr hp.le)
      _ = (ENNReal.ofReal C) ^ (1 / p) * eLpNorm' f p volume := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le),
          ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]
  simpa only [ENNReal.toReal_ofReal hp.le] using hnorm

/-- A power-integral estimate transports finite Lp membership to its
actual output function. -/
theorem memLp_of_absE_power_bound
    {f g : Vec3 → ℝ} {C p : ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) (hg : AEStronglyMeasurable g volume)
    (hp : 0 < p)
    (hbound : (∫⁻ x, absE g x ^ p) ≤ ENNReal.ofReal C * ∫⁻ x, absE f x ^ p) :
    MemLp g (ENNReal.ofReal p) volume := by
  exact (eLpNorm_bound_of_absE_power_bound hf.aestronglyMeasurable hg hp hbound).trans_lt
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hp.le) ENNReal.ofReal_ne_top)
      hf.eLpNorm_lt_top)

end CKN.Core.Endgame
