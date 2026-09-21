/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteSparseMaximal
import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodMaximal

/-!
# Comparing interval averages with the measurable centered maximal operator

The sparse-form argument is naturally stated using arbitrary intervals,
whereas the measurable Hardy--Littlewood maximal operator uses centered balls
of positive rational radius.  Every interval containing `x` lies in such a
ball with radius less than twice the interval length.  This file records the
resulting pointwise comparison.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace QuadraticCarleson


theorem RealInterval.carrier_subset_closedBall_of_mem
    (I : RealInterval) {x : ℝ} (hx : x ∈ I.carrier) {r : ℝ}
    (hr : I.length ≤ r) : I.carrier ⊆ closedBall x r := by
  intro y hy
  rw [mem_closedBall, Real.dist_eq]
  simp only [RealInterval.carrier, mem_Ioc] at hx hy
  have hlength : I.length = I.right - I.left := rfl
  rw [abs_le]
  constructor <;> linarith

theorem exists_positive_rational_radius_for_interval (I : RealInterval) :
    ∃ q : PositiveRational, I.length < (q : ℝ) ∧ (q : ℝ) < 2 * I.length := by
  have hlt : I.length < 2 * I.length := by linarith [I.length_pos]
  obtain ⟨q, hIq, hqI⟩ := exists_rat_btwn hlt
  refine ⟨⟨q, ?_⟩, hIq, hqI⟩
  exact_mod_cast I.length_pos.trans hIq

theorem ofReal_localAverage_one_eq
    (f : ℝ → ℂ) (I : RealInterval) (hf : IntegrableOn f I.carrier) :
    ENNReal.ofReal (localAverage 1 f I) =
      (∫⁻ y in I.carrier, ‖f y‖ₑ) / ENNReal.ofReal I.length := by
  have hnorm := hf.norm
  have hnonneg : 0 ≤ᵐ[volume.restrict I.carrier] fun y ↦ ‖f y‖ :=
    Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _)
  rw [localAverage]
  simp only [one_div, inv_one, Real.rpow_one]
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr I.length_pos.le)]
  rw [ofReal_integral_eq_lintegral_ofReal hnorm hnonneg]
  rw [ENNReal.ofReal_inv_of_pos I.length_pos]
  simp only [ofReal_norm]
  rw [ENNReal.div_eq_inv_mul]

/-- An arbitrary interval `L¹` average is at most four times the centered
rational-radius maximal function at every point of that interval. -/
theorem ofReal_localAverage_one_le_centeredHardyLittlewoodMaximal
    (f : ℝ → ℂ) (I : RealInterval) (hf : IntegrableOn f I.carrier)
    {x : ℝ} (hx : x ∈ I.carrier) :
    ENNReal.ofReal (localAverage 1 f I) ≤
      4 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  obtain ⟨q, hIq, hqI⟩ := exists_positive_rational_radius_for_interval I
  have hsubset : I.carrier ⊆ closedBall x (q : ℝ) :=
    I.carrier_subset_closedBall_of_mem hx hIq.le
  have hmass : (∫⁻ y in I.carrier, ‖f y‖ₑ) ≤
      ∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ :=
    lintegral_mono_set hsubset
  have hlength : ENNReal.ofReal I.length ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr I.length_pos
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.property
  have hqden : ENNReal.ofReal (2 * (q : ℝ)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (mul_pos (by norm_num) hqpos)
  have hqtop : ENNReal.ofReal (2 * (q : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdenominator : ENNReal.ofReal (2 * (q : ℝ)) ≤
      4 * ENNReal.ofReal I.length := by
    rw [← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [ofReal_localAverage_one_eq f I hf]
  calc
    (∫⁻ y in I.carrier, ‖f y‖ₑ) / ENNReal.ofReal I.length ≤
        (∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ) /
          ENNReal.ofReal I.length := ENNReal.div_le_div_right hmass _
    _ ≤ 4 * ((∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ) /
          ENNReal.ofReal (2 * (q : ℝ))) := by
      apply (ENNReal.div_le_iff hlength ENNReal.ofReal_ne_top).2
      calc
        (∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ) =
            ((∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ) /
              ENNReal.ofReal (2 * (q : ℝ))) *
                ENNReal.ofReal (2 * (q : ℝ)) := by
          exact (ENNReal.div_mul_cancel hqden hqtop).symm
        _ ≤ ((∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ) /
              ENNReal.ofReal (2 * (q : ℝ))) *
                (4 * ENNReal.ofReal I.length) :=
          mul_le_mul' le_rfl hdenominator
        _ = 4 * ((∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ) /
              ENNReal.ofReal (2 * (q : ℝ))) * ENNReal.ofReal I.length := by
          ac_rfl
    _ ≤ 4 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
      apply mul_le_mul' le_rfl
      exact le_iSup (fun q' : PositiveRational ↦
        centeredAverage (q' : ℝ) (fun y ↦ ‖f y‖ₑ) x) q

theorem L0Infinity.integrableOn_realInterval (f : L0Infinity) (I : RealInterval) :
    IntegrableOn f I.carrier := by
  rcases f.bounded_toFun with ⟨C, hC⟩
  apply IntegrableOn.of_bound (by simp)
    f.measurable_toFun.aestronglyMeasurable.restrict C
  exact Filter.Eventually.of_forall hC

/-- The uncentered interval maximal average used by the sparse form at
exponent one is controlled by the measurable centered maximal function. -/
theorem intervalMaximalAverage_one_le_centeredHardyLittlewoodMaximal
    (f : L0Infinity) (x : ℝ) :
    intervalMaximalAverage 1 f x ≤
      4 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  apply iSup_le
  intro I
  apply iSup_le
  intro hx
  exact ofReal_localAverage_one_le_centeredHardyLittlewoodMaximal
    f I (f.integrableOn_realInterval I) hx

theorem L0Infinity.integrableOn_norm_rpow (f : L0Infinity) (I : RealInterval)
    {p : ℝ} (hp : 0 ≤ p) : IntegrableOn (fun y ↦ ‖f y‖ ^ p) I.carrier := by
  rcases f.bounded_toFun with ⟨C, hC⟩
  let D := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hbound (x : ℝ) : ‖f x‖ ≤ D := (hC x).trans (le_max_left _ _)
  have hmeas : Measurable (fun y ↦ ‖f y‖ ^ p) :=
    (Real.continuous_rpow_const hp).measurable.comp f.measurable_toFun.norm
  apply IntegrableOn.of_bound (by simp) hmeas.aestronglyMeasurable.restrict (D ^ p)
  exact Filter.Eventually.of_forall (fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (hbound x) hp)

theorem ofReal_localAverage_eq_rpow_lintegral
    (p : ℝ) (hp : 0 < p) (f : ℝ → ℂ) (I : RealInterval)
    (hpow : IntegrableOn (fun y ↦ ‖f y‖ ^ p) I.carrier) :
    ENNReal.ofReal (localAverage p f I) =
      (((∫⁻ y in I.carrier, ‖f y‖ₑ ^ p) / ENNReal.ofReal I.length) ^ (1 / p)) := by
  have hnonneg : 0 ≤ᵐ[volume.restrict I.carrier] fun y ↦ ‖f y‖ ^ p :=
    Filter.Eventually.of_forall (fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
  rw [localAverage]
  rw [← ENNReal.ofReal_rpow_of_nonneg
    (mul_nonneg (inv_nonneg.mpr I.length_pos.le) (integral_nonneg_of_ae hnonneg))
    (one_div_nonneg.mpr hp.le)]
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr I.length_pos.le)]
  rw [ofReal_integral_eq_lintegral_ofReal hpow hnonneg]
  rw [ENNReal.ofReal_inv_of_pos I.length_pos]
  simp_rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le, ofReal_norm]
  rw [ENNReal.div_eq_inv_mul]

/-- Arbitrary-interval `Lᵖ` averages are controlled by the rational centered
maximal operator applied to `|f|^p`. -/
theorem ofReal_localAverage_le_centeredHardyLittlewoodMaximal_rpow
    (p : ℝ) (hp : 0 < p) (f : ℝ → ℂ) (I : RealInterval)
    (hpow : IntegrableOn (fun y ↦ ‖f y‖ ^ p) I.carrier)
    {x : ℝ} (hx : x ∈ I.carrier) :
    ENNReal.ofReal (localAverage p f I) ≤
      (4 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ ^ p) x) ^ (1 / p) := by
  obtain ⟨q, hIq, hqI⟩ := exists_positive_rational_radius_for_interval I
  have hsubset : I.carrier ⊆ closedBall x (q : ℝ) :=
    I.carrier_subset_closedBall_of_mem hx hIq.le
  have hmass : (∫⁻ y in I.carrier, ‖f y‖ₑ ^ p) ≤
      ∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ ^ p :=
    lintegral_mono_set hsubset
  have hlength : ENNReal.ofReal I.length ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr I.length_pos
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.property
  have hqden : ENNReal.ofReal (2 * (q : ℝ)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (mul_pos (by norm_num) hqpos)
  have hqtop : ENNReal.ofReal (2 * (q : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hdenominator : ENNReal.ofReal (2 * (q : ℝ)) ≤
      4 * ENNReal.ofReal I.length := by
    rw [← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [ofReal_localAverage_eq_rpow_lintegral p hp f I hpow]
  apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hp.le)
  calc
    (∫⁻ y in I.carrier, ‖f y‖ₑ ^ p) / ENNReal.ofReal I.length ≤
        (∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ ^ p) /
          ENNReal.ofReal I.length := ENNReal.div_le_div_right hmass _
    _ ≤ 4 * ((∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ ^ p) /
          ENNReal.ofReal (2 * (q : ℝ))) := by
      apply (ENNReal.div_le_iff hlength ENNReal.ofReal_ne_top).2
      calc
        (∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ ^ p) =
            ((∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ ^ p) /
              ENNReal.ofReal (2 * (q : ℝ))) *
                ENNReal.ofReal (2 * (q : ℝ)) := by
          exact (ENNReal.div_mul_cancel hqden hqtop).symm
        _ ≤ ((∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ ^ p) /
              ENNReal.ofReal (2 * (q : ℝ))) *
                (4 * ENNReal.ofReal I.length) :=
          mul_le_mul' le_rfl hdenominator
        _ = 4 * ((∫⁻ y in closedBall x (q : ℝ), ‖f y‖ₑ ^ p) /
              ENNReal.ofReal (2 * (q : ℝ))) * ENNReal.ofReal I.length := by
          ac_rfl
    _ ≤ 4 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ ^ p) x := by
      apply mul_le_mul' le_rfl
      exact le_iSup (fun q' : PositiveRational ↦
        centeredAverage (q' : ℝ) (fun y ↦ ‖f y‖ₑ ^ p) x) q

/-- Pointwise comparison for the complete interval maximal average at a
positive exponent. -/
theorem intervalMaximalAverage_le_centeredHardyLittlewoodMaximal_rpow
    (p : ℝ) (hp : 0 < p) (f : L0Infinity) (x : ℝ) :
    intervalMaximalAverage p f x ≤
      (4 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ ^ p) x) ^ (1 / p) := by
  apply iSup_le
  intro I
  apply iSup_le
  intro hx
  exact ofReal_localAverage_le_centeredHardyLittlewoodMaximal_rpow
    p hp f I (f.integrableOn_norm_rpow I hp.le) hx

end QuadraticCarleson
