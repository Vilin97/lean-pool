/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveHighHeightEstimate
import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightL2Stability
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# The paper's strict high-height tail

The height parametrization `B + n + 1` is exactly `r > B`. The maximal tail
is bounded by a measurable sum of the actual fixed-height maximal functions,
whose L² norms form a geometric series with ratio `2^(-1/10)`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveHighHeightEstimate

theorem highHeight_iff_exists (B r : ℕ) : B < r ↔ ∃ n : ℕ, r = B + n + 1 := by
  constructor
  · intro h
    exact ⟨r - B - 1, by omega⟩
  · rintro ⟨n, rfl⟩
    omega

theorem highHeight_oscillatoryScaleIndex_eq (lam : ℝ) (hlam : lam ≠ 0) (B n : ℕ) :
    oscillatoryScaleIndex lam (B + n + 1) hlam =
      oscillatoryScaleIndex lam 0 hlam + (B : ℤ) + (n : ℤ) + 1 := by
  rw [oscillatoryScaleIndex_eq_add]
  push_cast
  ring

/-- Countable Minkowski in L² for measurable extended nonnegative functions.
No summability assumption is needed: an infinite right side remains valid. -/
theorem eLpNorm_tsum_two_le {ι : Type*} [Countable ι]
    (F : ι → ℝ → ℝ≥0∞) (hF : ∀ i, Measurable (F i)) :
    eLpNorm (fun x ↦ ∑' i, F i x) 2 ≤ ∑' i, eLpNorm (F i) 2 := by
  classical
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  rw [ENNReal.rpow_two, ENNReal.rpow_two,
    eLpNorm_two_sq_lintegral _ (Measurable.tsum hF).aestronglyMeasurable]
  simp only [enorm_eq_self]
  simp_rw [ENNReal.tsum_eq_iSup_sum, ENNReal.iSup_pow]
  rw [lintegral_iSup_directed_of_measurable]
  · apply iSup_le
    intro s
    apply le_iSup_of_le s
    have hs := eLpNorm_sum_le (μ := volume) (s := s) (f := F)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hp := pow_le_pow_left₀ bot_le hs 2
    rw [eLpNorm_two_sq_lintegral _
      (Finset.aestronglyMeasurable_sum s (fun i _ ↦ (hF i).aestronglyMeasurable))] at hp
    simpa only [Finset.sum_apply, enorm_eq_self] using hp
  · intro s
    exact (Finset.measurable_fun_sum s (fun i _ ↦ hF i)).pow_const 2
  · intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro x
      exact pow_le_pow_left₀ bot_le
        (Finset.sum_le_sum_of_subset (f := fun i ↦ F i x) Finset.subset_union_left) 2
    · intro x
      exact pow_le_pow_left₀ bot_le
        (Finset.sum_le_sum_of_subset (f := fun i ↦ F i x) Finset.subset_union_right) 2

/-- The geometric decay ratio in the high-height L² estimate. -/
noncomputable def highHeightDecayRatio : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (-(1 : ℝ) / 10))

theorem highHeightDecayRatio_lt_one : highHeightDecayRatio < 1 := by
  rw [highHeightDecayRatio, ENNReal.ofReal_lt_one]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- The constant obtained by summing the geometric fixed-height L² bounds. -/
noncomputable def highHeightTailConstant : ℝ≥0∞ :=
  ENNReal.ofReal fixedHeightL2DecayConstant * highHeightDecayRatio *
    (1 - highHeightDecayRatio)⁻¹

theorem highHeightTailConstant_lt_top : highHeightTailConstant < ∞ := by
  unfold highHeightTailConstant
  apply ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by finiteness) (highHeightDecayRatio_lt_one.trans (by simp)))
  exact ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr highHeightDecayRatio_lt_one)

theorem fixedHeightDecay_highHeight_factor (B n : ℕ) :
    ENNReal.ofReal (fixedHeightL2DecayConstant * (2 : ℝ) ^ (-((B + n + 1 : ℕ) : ℝ) / 10)) =
      ENNReal.ofReal fixedHeightL2DecayConstant *
        ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 10)) * highHeightDecayRatio ^ (n + 1) := by
  have hp : (2 : ℝ) ^ (-((B + n + 1 : ℕ) : ℝ) / 10) =
      (2 : ℝ) ^ (-(B : ℝ) / 10) * ((2 : ℝ) ^ (-(1 : ℝ) / 10)) ^ (n + 1) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  rw [hp, ENNReal.ofReal_mul fixedHeightL2DecayConstant_pos.le,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
  simp only [highHeightDecayRatio, mul_assoc]

theorem tsum_fixedHeightDecay_highHeight (B : ℕ) :
    (∑' n : ℕ, ENNReal.ofReal (fixedHeightL2DecayConstant *
      (2 : ℝ) ^ (-((B + n + 1 : ℕ) : ℝ) / 10))) =
      highHeightTailConstant * ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 10)) := by
  simp_rw [fixedHeightDecay_highHeight_factor]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
  unfold highHeightTailConstant
  ring

/-- The sum of fixed-height quadratic maxima strictly above the cutoff height. -/
noncomputable def highHeightMajorant (B : ℕ) (b : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, paperFixedHeightQuadraticMaximal (B + n + 1) b x

theorem measurable_highHeightMajorant (B : ℕ) {b : ℝ → ℂ} (hb : MemLp b 2) :
    Measurable (highHeightMajorant B b) :=
  Measurable.tsum (fun _ ↦ measurable_paperFixedHeightQuadraticMaximal _ hb)

-- Elaborating the countable Minkowski specialization unfolds the concrete
-- real-modulation supremum and its height-dependent kernel several times.
theorem highHeightMajorant_eLpNorm_le (B : ℕ) {b : ℝ → ℂ} (hb : MemLp b 2) :
    eLpNorm (highHeightMajorant B b) 2 ≤ highHeightTailConstant *
      ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 10)) * eLpNorm b 2 := by
  have hp (n : ℕ) : eLpNorm (paperFixedHeightQuadraticMaximal (B + n + 1) b) 2 ≤
      ENNReal.ofReal (fixedHeightL2DecayConstant *
        (2 : ℝ) ^ (-((B + n + 1 : ℕ) : ℝ) / 10)) * eLpNorm b 2 :=
    paperFixedHeightQuadraticMaximal_eLpNorm_decay (B + n + 1) hb
  have hs := ENNReal.tsum_le_tsum hp
  rw [ENNReal.tsum_mul_right, tsum_fixedHeightDecay_highHeight] at hs
  exact (eLpNorm_tsum_two_le
    (fun n : ℕ ↦ paperFixedHeightQuadraticMaximal (B + n + 1) b)
    (fun n ↦ measurable_paperFixedHeightQuadraticMaximal (B + n + 1) hb)).trans hs

/-! ## Continuity of the actual infinite tail

For each fixed modulation, Hölder bounds the convolution at every observation point by
an interval-supported kernel's L² norm. Its radius doubles at each height, so these uniform
bounds form a geometric series with ratio `2^(-1/2)`. This proves continuity before taking
the unrestricted real-modulation supremum.
-/

private theorem tailKernel_eLpNorm_bound (lam : ℝ) (h : ℕ) (hlam : lam ≠ 0) :
    eLpNorm (fixedHeightQuadraticKernel lam h hlam) 2 ≤
      ENNReal.ofReal ((2 * positiveDyadicAmplitudeBound / fixedHeightRadius lam h hlam) *
        (2 * fixedHeightRadius lam h hlam) ^ (1 / (2 : ℝ))) := by
  let R := fixedHeightRadius lam h hlam
  let D := 2 * positiveDyadicAmplitudeBound
  have hR : 0 < R := fixedHeightRadius_pos lam h hlam
  have hD : 0 ≤ D := mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg
  have hc : AEStronglyMeasurable (fixedHeightQuadraticKernel lam h hlam) volume :=
    (continuous_fixedHeightQuadraticKernel lam h hlam).aestronglyMeasurable
  calc
    _ ≤ eLpNorm ((Icc (-R) R).indicator (fun _ : ℝ ↦ D / R)) 2 := by
      apply eLpNorm_mono_real hc
      intro t
      by_cases ht : t ∈ Icc (-R) R
      · rw [indicator_of_mem ht]
        exact norm_fixedHeightQuadraticKernel_le lam h hlam t
      · rw [indicator_of_notMem ht]
        have hz := fixedHeightQuadraticKernel_eq_zero_of_radius_lt lam h hlam t
          (lt_of_not_ge (fun ha ↦ ht (abs_le.mp ha)))
        simp [hz]
    _ = ENNReal.ofReal ((D / R) * (2 * R) ^ (1 / (2 : ℝ))) := by
      rw [eLpNorm_indicator_const measurableSet_Icc.nullMeasurableSet (by norm_num)
        (by norm_num), Real.volume_Icc]
      simp only [ENNReal.toReal_ofNat, sub_neg_eq_add, ← two_mul, ← ofReal_norm,
        Real.norm_eq_abs, abs_of_nonneg (div_nonneg hD hR.le)]
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
        ENNReal.ofReal_mul (div_nonneg hD hR.le)]

private theorem tailConvolution_bound (lam : ℝ) (h : ℕ) (hlam : lam ≠ 0)
    {b : ℝ → ℂ} (hb : MemLp b 2) (x : ℝ) :
    ‖∫ t, b t * fixedHeightQuadraticKernel lam h hlam (x - t)‖ ≤
      (‖ContinuousLinearMap.mul ℂ ℂ‖ * (eLpNorm b 2).toReal) *
        ((2 * positiveDyadicAmplitudeBound / fixedHeightRadius lam h hlam) *
          (2 * fixedHeightRadius lam h hlam) ^ (1 / (2 : ℝ))) := by
  have hc : AEStronglyMeasurable (fixedHeightQuadraticKernel lam h hlam) volume :=
    (continuous_fixedHeightQuadraticKernel lam h hlam).aestronglyMeasurable
  have hy := enorm_convolution_le (L := ContinuousLinearMap.mul ℂ ℂ)
    (p := 2) (q := 2) hb.aestronglyMeasurable hc x
  have hbound := hy.trans (mul_le_mul' le_rfl (tailKernel_eLpNorm_bound lam h hlam))
  have hfin : ‖ContinuousLinearMap.mul ℂ ℂ‖ₑ * eLpNorm b 2 *
      ENNReal.ofReal ((2 * positiveDyadicAmplitudeBound / fixedHeightRadius lam h hlam) *
        (2 * fixedHeightRadius lam h hlam) ^ (1 / (2 : ℝ))) ≠ ∞ := by
    finiteness
  have ht := ENNReal.toReal_mono hfin hbound
  have hn : 0 ≤ (2 * positiveDyadicAmplitudeBound / fixedHeightRadius lam h hlam) *
        (2 * fixedHeightRadius lam h hlam) ^ (1 / (2 : ℝ)) := by
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
      (fixedHeightRadius_pos lam h hlam).le) (Real.rpow_nonneg (mul_nonneg (by
        norm_num) (fixedHeightRadius_pos lam h hlam).le) _)
  simpa only [convolution, ContinuousLinearMap.mul_apply', ENNReal.toReal_mul,
    toReal_enorm, ENNReal.toReal_ofReal hn] using ht


private theorem tailRadius_factor (R D : ℝ) (hR : 0 < R) (n : ℕ) :
    (D / (R * 2 ^ n)) * (2 * (R * 2 ^ n)) ^ (1 / (2 : ℝ)) =
      (D / R * (2 * R) ^ (1 / (2 : ℝ))) * ((2 : ℝ) ^ (-(1 / (2 : ℝ)))) ^ n := by
  have hr : (2 : ℝ) ^ (1 / (2 : ℝ)) / 2 = (2 : ℝ) ^ (-(1 / (2 : ℝ))) := by
    calc
      _ = (2 : ℝ) ^ (1 / (2 : ℝ)) / (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (2 : ℝ) ^ (1 / (2 : ℝ) - 1) := (Real.rpow_sub (by norm_num) _ _).symm
      _ = _ := by norm_num
  rw [show (2 : ℝ) * (R * 2 ^ n) = (2 * R) * 2 ^ n by ring,
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
    mul_comm (n : ℝ), Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← hr, div_pow]
  ring


private theorem tailRadius_scale (lam : ℝ) (hlam : lam ≠ 0) (B n : ℕ) :
    fixedHeightRadius lam (B + n) hlam =
      fixedHeightRadius lam B hlam * (2 : ℝ) ^ n := by
  unfold fixedHeightRadius
  rw [oscillatoryScaleIndex_eq_add lam (B + n) hlam,
    oscillatoryScaleIndex_eq_add lam B hlam]
  rw [show oscillatoryScaleIndex lam 0 hlam + ((B + n : ℕ) : ℤ) - 1 =
    (oscillatoryScaleIndex lam 0 hlam + (B : ℤ) - 1) + (n : ℤ) by omega,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]

/-- The fixed-modulation convolution series from any starting height is continuous
for every L² input; the geometric bound is uniform in the observation point. -/
theorem continuous_fixedHeightConvolution_tsum (lam : ℝ) (hlam : lam ≠ 0) (B : ℕ)
    {b : ℝ → ℂ} (hb : MemLp b 2) :
    Continuous (fun x ↦ ∑' n : ℕ, ∫ t,
      b t * fixedHeightQuadraticKernel lam (B + n) hlam (x - t)) := by
  let R := fixedHeightRadius lam B hlam
  let q := (2 : ℝ) ^ (-(1 / (2 : ℝ)))
  let C := (‖ContinuousLinearMap.mul ℂ ℂ‖ * (eLpNorm b 2).toReal) *
    (2 * positiveDyadicAmplitudeBound / R * (2 * R) ^ (1 / (2 : ℝ)))
  have hq : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  apply continuous_tsum (u := fun n : ℕ ↦ C * q ^ n)
  · intro n
    have hc := (hasCompactSupport_fixedHeightQuadraticKernel lam (B + n)
      hlam).continuous_convolution_right
      (ContinuousLinearMap.mul ℂ ℂ) (hb.locallyIntegrable (by norm_num))
      (continuous_fixedHeightQuadraticKernel lam (B + n) hlam)
    change Continuous (fun x ↦ ∫ t,
      b t * fixedHeightQuadraticKernel lam (B + n) hlam (x - t)) at hc
    exact hc
  · exact (summable_geometric_of_lt_one hq hq1).mul_left C
  · intro n x
    have h := tailConvolution_bound lam (B + n) hlam hb x
    rw [tailRadius_scale, tailRadius_factor _ _ (fixedHeightRadius_pos lam B hlam)] at h
    simpa only [C, R, q, mul_assoc] using h

/-- The actual maximal complex tail, not the sum of the separate maximal
operators. Its heights are exactly the strict high range. -/
noncomputable def paperHighHeightTail (B : ℕ) (b : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ lam : {lam : ℝ // lam ≠ 0}, ‖∑' n : ℕ,
    ∫ t, b (x - t) *
      (dyadicPsi (oscillatoryScaleIndex lam.val (B + n + 1) lam.property) t : ℂ) *
        phase (lam.val * t ^ 2)‖ₑ

/-- The unrestricted modulation supremum is measurable because every modulated tail
is continuous in the observation point. -/
theorem measurable_paperHighHeightTail (B : ℕ) {b : ℝ → ℂ} (hb : MemLp b 2) :
    Measurable (paperHighHeightTail B b) := by
  apply LowerSemicontinuous.measurable
  unfold paperHighHeightTail
  apply lowerSemicontinuous_iSup
  intro lam
  have hc : Continuous (fun x ↦ ∑' n : ℕ,
      ∫ t, b (x - t) *
        (dyadicPsi (oscillatoryScaleIndex lam.val (B + n + 1) lam.property) t : ℂ) *
          phase (lam.val * t ^ 2)) := by
    convert continuous_fixedHeightConvolution_tsum lam.val lam.property (B + 1) hb using 1
    funext x
    apply tsum_congr
    intro n
    rw [show B + n + 1 = (B + 1) + n by omega,
      ← fixedHeightQuadraticKernel_integral_eq_paper]
    apply integral_congr_ae
    filter_upwards [] with t
    exact mul_comm _ _
  exact hc.enorm.lowerSemicontinuous

theorem paperHighHeightTail_le_majorant (B : ℕ) (b : ℝ → ℂ) (x : ℝ) :
    paperHighHeightTail B b x ≤ highHeightMajorant B b x := by
  apply iSup_le
  intro lam
  apply enorm_tsum_le_tsum_enorm.trans
  apply ENNReal.tsum_le_tsum
  intro n
  exact le_iSup (fun μ : {μ : ℝ // μ ≠ 0} ↦ ‖∫ t, b (x - t) *
    (dyadicPsi (oscillatoryScaleIndex μ.val (B + n + 1) μ.property) t : ℂ) *
      phase (μ.val * t ^ 2)‖ₑ) lam

theorem paperHighHeightTail_eLpNorm_le (B : ℕ) {b : ℝ → ℂ} (hb : MemLp b 2) :
    eLpNorm (paperHighHeightTail B b) 2 ≤ highHeightTailConstant *
      ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 10)) * eLpNorm b 2 := by
  apply (eLpNorm_mono_enorm (f := paperHighHeightTail B b) (g := highHeightMajorant B b)
    (measurable_paperHighHeightTail B hb).aestronglyMeasurable
    (fun x ↦ by simpa only [enorm_eq_self] using paperHighHeightTail_le_majorant B b x)).trans
  exact highHeightMajorant_eLpNorm_le B hb

end PositiveHighHeightEstimate
end QuadraticCarleson
