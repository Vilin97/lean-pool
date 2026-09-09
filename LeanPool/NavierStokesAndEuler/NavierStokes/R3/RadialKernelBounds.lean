/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# The radial majorant of the cutoff commutator

The cancellation factor `min (‖z‖ / R) 1` makes the singular kernel belong to
`L^(4/3)` in three dimensions. The proof uses the layer-cake formula and the
volume of balls, so no principal-value integral occurs in this module.
-/

@[expose] public section



noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The positive radial majorant after inserting the cutoff difference. -/
def radialCommutatorKernel (R : ℝ) (z : Space) : ℝ :=
  ‖z‖ ^ (-3 : ℝ) * min (‖z‖ / R) 1

theorem radialCommutatorKernel_nonneg {R : ℝ} (hR : 0 < R) (z : Space) :
    0 ≤ radialCommutatorKernel R z := by
  unfold radialCommutatorKernel
  positivity

theorem radialCommutatorKernel_measurable (R : ℝ) :
    Measurable (radialCommutatorKernel R) := by
  unfold radialCommutatorKernel
  fun_prop

@[simp] theorem radialCommutatorKernel_zero (R : ℝ) :
    radialCommutatorKernel R 0 = 0 := by
  simp [radialCommutatorKernel]

private theorem kernel_one_le_cube (z : Space) :
    radialCommutatorKernel 1 z ≤ ‖z‖ ^ (-3 : ℝ) := by
  unfold radialCommutatorKernel
  exact mul_le_of_le_one_right (Real.rpow_nonneg (norm_nonneg _) _) (min_le_right _ _)

private theorem kernel_one_le_square (z : Space) :
    radialCommutatorKernel 1 z ≤ ‖z‖ ^ (-2 : ℝ) := by
  by_cases hz : z = 0
  · simp [hz]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  calc
    radialCommutatorKernel 1 z ≤ ‖z‖ ^ (-3 : ℝ) * ‖z‖ := by
      unfold radialCommutatorKernel
      gcongr
      simp
    _ = ‖z‖ ^ (-2 : ℝ) := by
      calc
        _ = ‖z‖ ^ (-3 : ℝ) * ‖z‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hn]; norm_num

private theorem kernel_one_power_le_four (z : Space) :
    radialCommutatorKernel 1 z ^ (4 / 3 : ℝ) ≤ ‖z‖ ^ (-4 : ℝ) := by
  calc
    _ ≤ (‖z‖ ^ (-3 : ℝ)) ^ (4 / 3 : ℝ) :=
      Real.rpow_le_rpow (radialCommutatorKernel_nonneg (by norm_num) z)
        (kernel_one_le_cube z) (by norm_num)
    _ = _ := by rw [← Real.rpow_mul (norm_nonneg _)]; norm_num

private theorem kernel_one_power_le_eight_thirds (z : Space) :
    radialCommutatorKernel 1 z ^ (4 / 3 : ℝ) ≤ ‖z‖ ^ (-(8 / 3) : ℝ) := by
  calc
    _ ≤ (‖z‖ ^ (-2 : ℝ)) ^ (4 / 3 : ℝ) :=
      Real.rpow_le_rpow (radialCommutatorKernel_nonneg (by norm_num) z)
        (kernel_one_le_square z) (by norm_num)
    _ = _ := by rw [← Real.rpow_mul (norm_nonneg _)]; norm_num

private theorem levelset_measure_le_ball {f : Space → ℝ} {q t : ℝ}
    (hq : q < 0) (ht : 0 < t) (hf : ∀ z, f z ≤ ‖z‖ ^ q) :
    volume {z | t ≤ f z} ≤ volume (Metric.closedBall (0 : Space) (t ^ q⁻¹)) := by
  apply measure_mono
  intro z hz
  have hn : 0 < ‖z‖ := by
    by_contra hn
    have hnz : ‖z‖ = 0 := le_antisymm (not_lt.mp hn) (norm_nonneg _)
    have := hz.trans (hf z)
    rw [hnz, Real.zero_rpow hq.ne] at this
    exact (not_le_of_gt ht) this
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (Real.le_rpow_inv_iff_of_neg hn ht hq).mpr (hz.trans (hf z))

private theorem ball_measure_power (t q : ℝ) (ht : 0 < t) :
    volume (Metric.closedBall (0 : Space) (t ^ q)) =
      ENNReal.ofReal (t ^ (q * 3)) * volume (Metric.ball (0 : Space) 1) := by
  rw [Measure.addHaar_closedBall volume (0 : Space) (Real.rpow_nonneg ht.le _)]
  congr 2
  simp only [Space, NavierStokes.ProblemStatement.Space, finrank_euclideanSpace,
    Fintype.card_fin]
  rw [Real.rpow_mul ht.le]
  exact (Real.rpow_natCast (t ^ q) 3).symm

private theorem kernel_one_power_integrable :
    Integrable (fun z : Space => radialCommutatorKernel 1 z ^ (4 / 3 : ℝ)) := by
  let f : Space → ℝ := fun z => radialCommutatorKernel 1 z ^ (4 / 3 : ℝ)
  have hm : Measurable f := (radialCommutatorKernel_measurable 1).pow_const _
  have hn : ∀ z, 0 ≤ f z := fun z =>
    Real.rpow_nonneg (radialCommutatorKernel_nonneg (by norm_num) z) _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  change HasFiniteIntegral f volume
  rw [hasFiniteIntegral_iff_enorm, lintegral_enorm_of_nonneg hn,
    lintegral_eq_lintegral_meas_le volume (Filter.Eventually.of_forall hn) hm.aemeasurable]
  calc
    (∫⁻ t in Ioi (0 : ℝ), volume {z | t ≤ f z}) ≤
        ∫⁻ t in Ioc (0 : ℝ) 1 ∪ Ioi 1, volume {z | t ≤ f z} :=
      lintegral_mono_set Ioi_subset_Ioc_union_Ioi
    _ ≤ (∫⁻ t in Ioc (0 : ℝ) 1, volume {z | t ≤ f z}) +
        ∫⁻ t in Ioi (1 : ℝ), volume {z | t ≤ f z} := lintegral_union_le _ _ _
    _ < ∞ := by
      apply ENNReal.add_lt_top.mpr
      constructor
      · calc
          (∫⁻ t in Ioc (0 : ℝ) 1, volume {z | t ≤ f z}) ≤
              ∫⁻ t in Ioc (0 : ℝ) 1,
                ENNReal.ofReal (t ^ (-(3 / 4) : ℝ)) *
                  volume (Metric.ball (0 : Space) 1) := by
            apply setLIntegral_mono' measurableSet_Ioc
            intro t ht
            calc
              volume {z | t ≤ f z} ≤
                  volume (Metric.closedBall (0 : Space) (t ^ ((-4 : ℝ)⁻¹))) :=
                levelset_measure_le_ball (by norm_num) ht.1 kernel_one_power_le_four
              _ = _ := by
                rw [ball_measure_power t _ ht.1]
                norm_num
          _ < ∞ := by
            rw [lintegral_mul_const' _ _ measure_ball_lt_top.ne]
            apply ENNReal.mul_lt_top _ measure_ball_lt_top
            apply IntegrableOn.setLIntegral_lt_top
            rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
            exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
      · calc
          (∫⁻ t in Ioi (1 : ℝ), volume {z | t ≤ f z}) ≤
              ∫⁻ t in Ioi (1 : ℝ),
                ENNReal.ofReal (t ^ (-(9 / 8) : ℝ)) *
                  volume (Metric.ball (0 : Space) 1) := by
            apply setLIntegral_mono' measurableSet_Ioi
            intro t ht
            have ht0 : 0 < t := zero_lt_one.trans ht
            calc
              volume {z | t ≤ f z} ≤
                  volume (Metric.closedBall (0 : Space) (t ^ ((-(8 / 3) : ℝ)⁻¹))) :=
                levelset_measure_le_ball (by norm_num) ht0 kernel_one_power_le_eight_thirds
              _ = _ := by
                rw [ball_measure_power t _ ht0]
                norm_num
          _ < ∞ := by
            rw [lintegral_mul_const' _ _ measure_ball_lt_top.ne]
            exact ENNReal.mul_lt_top
              (IntegrableOn.setLIntegral_lt_top
                (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one))
              measure_ball_lt_top

/-- Dilation of the cutoff kernel. -/
theorem radialCommutatorKernel_scale {R : ℝ} (hR : 0 < R) (z : Space) :
    radialCommutatorKernel R z =
      R ^ (-3 : ℝ) * radialCommutatorKernel 1 (R⁻¹ • z) := by
  simp only [radialCommutatorKernel, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR), div_one]
  rw [Real.mul_rpow (inv_nonneg.mpr hR.le) (norm_nonneg z), Real.inv_rpow hR.le]
  have hpow : R ^ (-3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hR _).ne'
  simp only [div_eq_mul_inv, mul_comm R⁻¹ ‖z‖]
  field_simp

private theorem kernel_power_scale {R : ℝ} (hR : 0 < R) (z : Space) :
    radialCommutatorKernel R z ^ (4 / 3 : ℝ) =
      R ^ (-4 : ℝ) * radialCommutatorKernel 1 (R⁻¹ • z) ^ (4 / 3 : ℝ) := by
  rw [radialCommutatorKernel_scale hR, Real.mul_rpow (Real.rpow_nonneg hR.le _)
    (radialCommutatorKernel_nonneg (by norm_num) _), ← Real.rpow_mul hR.le]
  norm_num

/-- The `4/3` power of the radial kernel is integrable. -/
theorem radialCommutatorKernel_power_integrable {R : ℝ} (hR : 0 < R) :
    Integrable (fun z : Space => radialCommutatorKernel R z ^ (4 / 3 : ℝ)) := by
  have h := (kernel_one_power_integrable.comp_smul (inv_ne_zero hR.ne')).const_mul
    (R ^ (-4 : ℝ))
  simpa only [kernel_power_scale hR] using h

/-- The actual cancellation kernel belongs to `L^(4/3)`. -/
theorem radialCommutatorKernel_memLp {R : ℝ} (hR : 0 < R) :
    MemLp (radialCommutatorKernel R) (4 / 3 : ℝ≥0∞) volume := by
  apply (integrable_norm_rpow_iff
    (radialCommutatorKernel_measurable R).aestronglyMeasurable
    (by norm_num : (4 / 3 : ℝ≥0∞) ≠ 0)
    (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, Real.norm_eq_abs,
    abs_of_nonneg (radialCommutatorKernel_nonneg hR _)] using
    radialCommutatorKernel_power_integrable hR

private theorem kernel_power_integral_scale {R : ℝ} (hR : 0 < R) :
    (∫ z : Space, radialCommutatorKernel R z ^ (4 / 3 : ℝ)) =
      R ^ (-1 : ℝ) * ∫ z : Space, radialCommutatorKernel 1 z ^ (4 / 3 : ℝ) := by
  have hpow : R ^ (-4 : ℝ) * R ^ (3 : ℕ) = R ^ (-1 : ℝ) := by
    calc
      _ = R ^ (-4 : ℝ) * R ^ (3 : ℝ) := by
        exact congrArg (fun a => R ^ (-4 : ℝ) * a) (Real.rpow_natCast R 3).symm
      _ = R ^ ((-4 : ℝ) + 3) := (Real.rpow_add hR _ _).symm
      _ = _ := by norm_num
  simp_rw [kernel_power_scale hR]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun z : Space => radialCommutatorKernel 1 z ^ (4 / 3 : ℝ)) hR.le]
  simp only [Space, NavierStokes.ProblemStatement.Space, finrank_euclideanSpace,
    Fintype.card_fin, smul_eq_mul, ← mul_assoc, hpow]

private theorem kernel_lpNorm_formula {R : ℝ} (hR : 0 < R) :
    comparisonLpNorm (4 / 3) (radialCommutatorKernel R) =
      (∫ z : Space, radialCommutatorKernel R z ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
  unfold comparisonLpNorm
  rw [(radialCommutatorKernel_memLp hR).eLpNorm_eq_integral_rpow_norm
    (by norm_num) (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne]
  have hp : (4 / 3 : ℝ≥0∞).toReal = (4 / 3 : ℝ) := by norm_num
  rw [hp]
  have hinv : (4 / 3 : ℝ)⁻¹ = (3 / 4 : ℝ) := by norm_num
  rw [hinv]
  have hnorm : (fun z : Space => ‖radialCommutatorKernel R z‖ ^ (4 / 3 : ℝ)) =
      (fun z : Space => radialCommutatorKernel R z ^ (4 / 3 : ℝ)) := by
    funext z
    rw [Real.norm_eq_abs, abs_of_nonneg (radialCommutatorKernel_nonneg hR z)]
  have hi : 0 ≤ ∫ z : Space, radialCommutatorKernel R z ^ (4 / 3 : ℝ) :=
    integral_nonneg fun z => Real.rpow_nonneg (radialCommutatorKernel_nonneg hR z) _
  rw [hnorm, ENNReal.toReal_ofReal (Real.rpow_nonneg hi _)]

/-- The norm has exactly the scale required by the cutoff commutator. -/
theorem radialCommutatorKernel_lpNorm_scale {R : ℝ} (hR : 0 < R) :
    comparisonLpNorm (4 / 3) (radialCommutatorKernel R) =
      comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) * R ^ (-(3 / 4) : ℝ) := by
  have hi : 0 ≤ ∫ z : Space, radialCommutatorKernel 1 z ^ (4 / 3 : ℝ) :=
    integral_nonneg fun z =>
      Real.rpow_nonneg (radialCommutatorKernel_nonneg zero_lt_one z) _
  rw [kernel_lpNorm_formula hR, kernel_lpNorm_formula zero_lt_one,
    kernel_power_integral_scale hR,
    Real.mul_rpow (Real.rpow_nonneg hR.le _) hi, ← Real.rpow_mul hR.le]
  norm_num; ring

/-- A single finite constant bounds the kernel norm at every positive radius. -/
theorem radialCommutatorKernel_lpNorm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R > 0,
      comparisonLpNorm (4 / 3) (radialCommutatorKernel R) ≤ C * R ^ (-(3 / 4) : ℝ) := by
  refine ⟨comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) + 1, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one
  · intro R hR
    rw [radialCommutatorKernel_lpNorm_scale hR]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (Real.rpow_nonneg hR.le _)

end NavierStokesR3.Comparison
