/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodMaximalLp
import LeanPool.QuadraticCarleson.QuadraticCarleson.IntervalMaximalComparison

/-!
# Strong bounds for the interval maximal averages in the sparse argument

This file combines the arbitrary-interval comparison with the genuine
Hardy--Littlewood `L^q` theorem. It supplies the analytic maximal-function
factor used in Lemma `l:weak11sparse` of the paper.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson


/-- The interval `L^p` maximal average has the expected strong `L^r` bound
whenever `1 < r / p`. The constant is explicit and uniform in the input. -/
theorem intervalMaximalAverage_rpow_lintegral_le
    (p r : ℝ) (hp : 0 < p) (hpr : p < r) (f : L0Infinity) :
    (∫⁻ x, intervalMaximalAverage p f x ^ r) ≤
      (4 : ℝ≥0∞) ^ (r / p) *
        ENNReal.ofReal (centeredHardyLittlewoodRpowConstant (r / p)) *
          ∫⁻ x, ‖f x‖ₑ ^ r := by
  let h : ℝ → ℝ≥0∞ := fun y ↦ ‖f y‖ₑ ^ p
  let M : ℝ → ℝ≥0∞ := centeredHardyLittlewoodMaximal h
  have hr : 0 < r := hp.trans hpr
  have hq : 1 < r / p := (lt_div_iff₀ hp).2 (by simpa [one_mul] using hpr)
  have hq0 : 0 < r / p := zero_lt_one.trans hq
  have hh : Measurable h :=
    ENNReal.continuous_rpow_const.measurable.comp f.measurable_toFun.enorm
  have hhfinite (y : ℝ) : h y ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hp.le enorm_ne_top
  have hpoint (x : ℝ) : intervalMaximalAverage p f x ^ r ≤
      (4 : ℝ≥0∞) ^ (r / p) * M x ^ (r / p) := by
    have hbase := intervalMaximalAverage_le_centeredHardyLittlewoodMaximal_rpow
      p hp f x
    apply (ENNReal.rpow_le_rpow hbase hr.le).trans_eq
    rw [← ENNReal.rpow_mul]
    have hexp : 1 / p * r = r / p := by field_simp
    rw [hexp, ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
  calc
    (∫⁻ x, intervalMaximalAverage p f x ^ r) ≤
        ∫⁻ x, (4 : ℝ≥0∞) ^ (r / p) * M x ^ (r / p) :=
      lintegral_mono hpoint
    _ = (4 : ℝ≥0∞) ^ (r / p) * ∫⁻ x, M x ^ (r / p) := by
      rw [lintegral_const_mul' _ _
        (ENNReal.rpow_ne_top_of_nonneg hq0.le (by norm_num))]
    _ ≤ (4 : ℝ≥0∞) ^ (r / p) *
        (ENNReal.ofReal (centeredHardyLittlewoodRpowConstant (r / p)) *
          ∫⁻ x, h x ^ (r / p)) := by
      gcongr
      exact centeredHardyLittlewoodMaximal_rpow_lintegral_le
        hh hhfinite hq
    _ = (4 : ℝ≥0∞) ^ (r / p) *
        ENNReal.ofReal (centeredHardyLittlewoodRpowConstant (r / p)) *
          ∫⁻ x, ‖f x‖ₑ ^ r := by
      have hpow (x : ℝ) : h x ^ (r / p) = ‖f x‖ₑ ^ r := by
        dsimp only [h]
        rw [← ENNReal.rpow_mul]
        congr 1
        field_simp
      simp_rw [hpow]
      ring

/-- The measurable centered maximal-function majorant for arbitrary interval
`L^p` averages. -/
noncomputable def intervalAverageMajorant (p : ℝ) (f : L0Infinity) (x : ℝ) : ℝ≥0∞ :=
  (4 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ ^ p) x) ^ (1 / p)

theorem measurable_intervalAverageMajorant (p : ℝ) (f : L0Infinity) :
    Measurable (intervalAverageMajorant p f) := by
  apply ENNReal.continuous_rpow_const.measurable.comp
  exact measurable_const.mul (measurable_centeredHardyLittlewoodMaximal
    (ENNReal.continuous_rpow_const.measurable.comp f.measurable_toFun.enorm))

theorem intervalMaximalAverage_le_intervalAverageMajorant
    {p : ℝ} (hp : 0 < p) (f : L0Infinity) (x : ℝ) :
    intervalMaximalAverage p f x ≤ intervalAverageMajorant p f x :=
  intervalMaximalAverage_le_centeredHardyLittlewoodMaximal_rpow p hp f x

/-- Strong moment bound for the measurable majorant itself. -/
theorem intervalAverageMajorant_rpow_lintegral_le
    (p r : ℝ) (hp : 0 < p) (hpr : p < r) (f : L0Infinity) :
    (∫⁻ x, intervalAverageMajorant p f x ^ r) ≤
      (4 : ℝ≥0∞) ^ (r / p) *
        ENNReal.ofReal (centeredHardyLittlewoodRpowConstant (r / p)) *
          ∫⁻ x, ‖f x‖ₑ ^ r := by
  let h : ℝ → ℝ≥0∞ := fun y ↦ ‖f y‖ₑ ^ p
  let M : ℝ → ℝ≥0∞ := centeredHardyLittlewoodMaximal h
  have hq : 1 < r / p := (lt_div_iff₀ hp).2 (by simpa using hpr)
  have hh : Measurable h :=
    ENNReal.continuous_rpow_const.measurable.comp f.measurable_toFun.enorm
  have hhfinite (y : ℝ) : h y ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hp.le enorm_ne_top
  have hpoint (x : ℝ) : intervalAverageMajorant p f x ^ r =
      (4 : ℝ≥0∞) ^ (r / p) * M x ^ (r / p) := by
    rw [intervalAverageMajorant, ← ENNReal.rpow_mul]
    have hexp : 1 / p * r = r / p := by field_simp
    rw [hexp, ENNReal.mul_rpow_of_nonneg _ _ (zero_lt_one.trans hq).le]
  simp_rw [hpoint]
  rw [lintegral_const_mul' _ _
    (ENNReal.rpow_ne_top_of_nonneg (zero_lt_one.trans hq).le (by norm_num))]
  rw [mul_assoc]
  apply mul_le_mul' le_rfl
  apply (centeredHardyLittlewoodMaximal_rpow_lintegral_le hh hhfinite hq).trans_eq
  congr 2
  funext x
  dsimp only [h]
  rw [← ENNReal.rpow_mul]
  congr 1
  field_simp

/-- Hölder embedding of a sparse form into the two measurable maximal
majorants. This is the analytic middle line of Lemma `l:weak11sparse`. -/
theorem sparseForm_le_lintegral_majorants_holder
    {p r η : ℝ} {S : Set RealInterval} (hS : IsSparse η S)
    (hp : 0 < p) (hr : 1 < r) (f g : L0Infinity) :
    sparseForm p f g S ≤ ENNReal.ofReal η⁻¹ *
      ((∫⁻ x, intervalAverageMajorant 1 f x ^ holderConjugate r) ^
          (1 / holderConjugate r) *
        (∫⁻ x, intervalAverageMajorant p g x ^ r) ^ (1 / r)) := by
  apply (sparseForm_le_lintegral_intervalMaximalAverage hS f g).trans
  apply mul_le_mul' le_rfl
  apply (lintegral_mono (fun x ↦ mul_le_mul'
    (intervalMaximalAverage_le_intervalAverageMajorant zero_lt_one f x)
    (intervalMaximalAverage_le_intervalAverageMajorant hp g x))).trans
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    (holderConjugate_spec hr).symm
    (measurable_intervalAverageMajorant 1 f).aemeasurable
    (measurable_intervalAverageMajorant p g).aemeasurable

theorem one_lt_holderConjugate_of_one_lt {r : ℝ} (hr : 1 < r) :
    1 < holderConjugate r := by
  unfold holderConjugate
  rw [lt_div_iff₀ (sub_pos.mpr hr)]
  linarith

/-- The fully quantified global sparse-form estimate obtained by combining
the maximal-function comparison, Hölder, and both strong maximal bounds. -/
theorem sparseForm_le_strong_maximal_factors
    {p r η : ℝ} {S : Set RealInterval} (hS : IsSparse η S)
    (hp : 0 < p) (hr : 1 < r) (hpr : p < r) (f g : L0Infinity) :
    sparseForm p f g S ≤ ENNReal.ofReal η⁻¹ *
      (((4 : ℝ≥0∞) ^ holderConjugate r *
          ENNReal.ofReal
            (centeredHardyLittlewoodRpowConstant (holderConjugate r)) *
          ∫⁻ x, ‖f x‖ₑ ^ holderConjugate r) ^
            (1 / holderConjugate r) *
        ((4 : ℝ≥0∞) ^ (r / p) *
          ENNReal.ofReal (centeredHardyLittlewoodRpowConstant (r / p)) *
          ∫⁻ x, ‖g x‖ₑ ^ r) ^ (1 / r)) := by
  let q := holderConjugate r
  have hq : 1 < q := one_lt_holderConjugate_of_one_lt hr
  have hf : (∫⁻ x, intervalAverageMajorant 1 f x ^ holderConjugate r) ≤
      (4 : ℝ≥0∞) ^ holderConjugate r *
        ENNReal.ofReal
          (centeredHardyLittlewoodRpowConstant (holderConjugate r)) *
          ∫⁻ x, ‖f x‖ₑ ^ holderConjugate r := by
    simpa [q] using intervalAverageMajorant_rpow_lintegral_le
      1 q zero_lt_one hq f
  have hg := intervalAverageMajorant_rpow_lintegral_le p r hp hpr g
  have hbase := sparseForm_le_lintegral_majorants_holder hS hp hr f g
  apply hbase.trans
  apply mul_le_mul' le_rfl
  apply mul_le_mul'
  · exact ENNReal.rpow_le_rpow hf (one_div_nonneg.mpr (zero_lt_one.trans hq).le)
  · exact ENNReal.rpow_le_rpow hg (one_div_nonneg.mpr (zero_lt_one.trans hr).le)

end QuadraticCarleson
