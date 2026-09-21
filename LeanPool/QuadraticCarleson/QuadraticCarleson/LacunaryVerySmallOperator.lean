/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryLowSupport
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryVerySmallRange
import LeanPool.QuadraticCarleson.QuadraticCarleson.CanonicalScaleAtoms
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleRangeSummation
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveLowFullEndpoint

/-!
# The genuine lacunary very-small low-kernel contribution

This file combines the cancellation estimate for an actual magnitude-level
atom with the compact support of the paper's telescoped low kernel.  It is the
analytic step which produces the factor
`2^(B + m/2) * length(I)` before the geometric summation in
`LacunaryVerySmallRange`.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace LacunaryVerySmallOperator

open CalderonZygmundLevelAtoms LacunaryLowSupport
open LowKernelLevelSummation LacunaryVerySmallRange
open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CanonicalScaleAtoms
open PositiveLowFullEstimate
open PositiveHighHeightEstimate
open PositiveEndpointOptimization


/-- The outer spatial radius of the low kernel at modulation `2^m`. -/
noncomputable def lowSupportRadius (B : ℕ) (m : ℤ) : ℝ :=
  (2 : ℝ) ^ B / Real.sqrt (dyadicModulation m)

theorem lowSupportRadius_pos (B : ℕ) (m : ℤ) :
    0 < lowSupportRadius B m := by
  unfold lowSupportRadius
  exact div_pos (by positivity) (Real.sqrt_pos.2 (dyadicModulation_pos m))

/-- The square root of the dyadic modulation is its half-integer real power. -/
theorem sqrt_dyadicModulation (m : ℤ) :
    Real.sqrt (dyadicModulation m) = (2 : ℝ) ^ ((m : ℝ) / 2) := by
  rw [dyadicModulation, Real.sqrt_eq_rpow, ← Real.rpow_intCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- Multiplication by `2^m` converts the support radius into the square-root
frequency factor occurring in the paper. -/
theorem dyadicModulation_mul_lowSupportRadius (B : ℕ) (m : ℤ) :
    dyadicModulation m * lowSupportRadius B m =
      (2 : ℝ) ^ ((B : ℝ) + (m : ℝ) / 2) := by
  have hs : 0 < Real.sqrt (dyadicModulation m) :=
    Real.sqrt_pos.2 (dyadicModulation_pos m)
  have hquot : dyadicModulation m / Real.sqrt (dyadicModulation m) =
      Real.sqrt (dyadicModulation m) := by
    apply (div_eq_iff hs.ne').2
    rw [← pow_two, Real.sq_sqrt (dyadicModulation_pos m).le]
  unfold lowSupportRadius
  calc
    dyadicModulation m * ((2 : ℝ) ^ B / Real.sqrt (dyadicModulation m)) =
        (2 : ℝ) ^ B *
          (dyadicModulation m / Real.sqrt (dyadicModulation m)) := by ring
    _ = (2 : ℝ) ^ B * Real.sqrt (dyadicModulation m) := by rw [hquot]
    _ = (2 : ℝ) ^ (B : ℝ) * (2 : ℝ) ^ ((m : ℝ) / 2) := by
      rw [sqrt_dyadicModulation, Real.rpow_natCast]
    _ = (2 : ℝ) ^ ((B : ℝ) + (m : ℝ) / 2) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-- In the paper's very-small range, an atom is shorter than the outer
support radius of the low kernel. -/
theorem atomLength_lt_lowSupportRadius_of_mem_L
    {c B : ℕ} (hB : 0 < B) {m j : ℤ} (hj : j ∈ LacunaryMiddleRange.L B c m)
    {R : ℝ} (hscale : (2 : ℝ) ^ j ≤ R ∧ R < (2 : ℝ) ^ (j + 1)) :
    R < lowSupportRadius B m := by
  have hR : 0 < R := (zpow_pos (by norm_num) j).trans_le hscale.1
  have hR2 : R ^ 2 < ((2 : ℝ) ^ (j + 1)) ^ 2 :=
    (sq_lt_sq₀ hR.le (zpow_nonneg (by norm_num) (j + 1))).2 hscale.2
  have hmpos : 0 < dyadicModulation m := dyadicModulation_pos m
  have hmul : dyadicModulation m * R ^ 2 <
      dyadicModulation m * ((2 : ℝ) ^ (j + 1)) ^ 2 :=
    mul_lt_mul_of_pos_left hR2 hmpos
  have hexp : dyadicModulation m * ((2 : ℝ) ^ (j + 1)) ^ 2 =
      (2 : ℝ) ^ (m + 2 * j + 2) := by
    rw [dyadicModulation, pow_two,
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  have hBexp : ((2 : ℝ) ^ B) ^ 2 = (2 : ℝ) ^ (2 * (B : ℤ)) := by
    rw [pow_two, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  have hexplt : m + 2 * j + 2 < 2 * (B : ℤ) := by
    rw [LacunaryMiddleRange.mem_L] at hj
    omega
  have hpow : (2 : ℝ) ^ (m + 2 * j + 2) < (2 : ℝ) ^ (2 * (B : ℤ)) :=
    (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2 hexplt
  have hsquare : (R * Real.sqrt (dyadicModulation m)) ^ 2 < ((2 : ℝ) ^ B) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (dyadicModulation_pos m).le, hBexp]
    simpa only [mul_comm] using (hmul.trans_eq hexp).trans hpow
  have hsqrt : 0 < Real.sqrt (dyadicModulation m) :=
    Real.sqrt_pos.2 (dyadicModulation_pos m)
  have hmain : R * Real.sqrt (dyadicModulation m) < (2 : ℝ) ^ B :=
    (sq_lt_sq₀ (mul_nonneg hR.le hsqrt.le) (by positivity)).1 hsquare
  exact (lt_div_iff₀ hsqrt).2 hmain

/-- The expanded support interval has length at most three outer radii in
the very-small range. -/
theorem expandedLength_le_three_mul_lowSupportRadius
    {c B : ℕ} (hB : 0 < B) {m j : ℤ} (hj : j ∈ LacunaryMiddleRange.L B c m)
    {R : ℝ} (hscale : (2 : ℝ) ^ j ≤ R ∧ R < (2 : ℝ) ^ (j + 1)) :
    2 * lowSupportRadius B m + R ≤ 3 * lowSupportRadius B m := by
  linarith [atomLength_lt_lowSupportRadius_of_mem_L hB hj hscale]

/-- The product of the cancellation size and the support length is exactly
controlled by the paper's very-small weight. -/
theorem verySmallCancellationCoefficient_le
    {c B : ℕ} (hB : 0 < B) {m j : ℤ} (hj : j ∈ LacunaryMiddleRange.L B c m)
    {R : ℝ} (hscale : (2 : ℝ) ^ j ≤ R ∧ R < (2 : ℝ) ^ (j + 1)) :
    (lowKernelDerivativeConstant * dyadicModulation m * (R / 2)) *
        (2 * lowSupportRadius B m + R) ≤
      3 * lowKernelDerivativeConstant * verySmallWeight B m j := by
  have hR : 0 ≤ R :=
    (zpow_nonneg (by norm_num) j).trans hscale.1
  have hC : 0 ≤ lowKernelDerivativeConstant * dyadicModulation m * (R / 2) :=
    mul_nonneg
      (mul_nonneg lowKernelDerivativeConstant_nonneg (dyadicModulation_pos m).le)
      (div_nonneg hR (by norm_num))
  have hfactor : 0 ≤ (3 / 2 : ℝ) * lowKernelDerivativeConstant := by
    exact mul_nonneg (by norm_num) lowKernelDerivativeConstant_nonneg
  have hscale' : () ∈ dyadicAtomScaleClass (fun _ : Unit ↦ R) j := hscale
  calc
    (lowKernelDerivativeConstant * dyadicModulation m * (R / 2)) *
        (2 * lowSupportRadius B m + R) ≤
        (lowKernelDerivativeConstant * dyadicModulation m * (R / 2)) *
          (3 * lowSupportRadius B m) :=
      mul_le_mul_of_nonneg_left
        (expandedLength_le_three_mul_lowSupportRadius hB hj hscale) hC
    _ = ((3 / 2 : ℝ) * lowKernelDerivativeConstant) *
        ((dyadicModulation m * lowSupportRadius B m) * R) := by ring
    _ = ((3 / 2 : ℝ) * lowKernelDerivativeConstant) *
        ((2 : ℝ) ^ ((B : ℝ) + (m : ℝ) / 2) * R) := by
      rw [dyadicModulation_mul_lowSupportRadius]
    _ ≤ ((3 / 2 : ℝ) * lowKernelDerivativeConstant) *
        (2 * verySmallWeight B m j) :=
      mul_le_mul_of_nonneg_left
        (modulationWeight_mul_atomLength_le_two_mul_verySmallWeight
          hscale' B m) hfactor
    _ = 3 * lowKernelDerivativeConstant * verySmallWeight B m j := by ring

/-- If `x` lies outside the interval obtained by adding an outer radius `D`
to both sides of `I`, then it is more than `D` from every point of `I`.
The half-open convention supplies the required strict inequality at both
endpoints. -/
theorem radius_lt_distance_of_not_mem_expanded
    {z R D x y : ℝ} (hR : 0 < R) (hD : 0 < D)
    (hx : x ∉ centeredInterval z (2 * D + R))
    (hy : y ∈ centeredInterval z R) :
    D < |x - y| := by
  rw [centeredInterval] at hx hy
  simp only [mem_Ico, not_and_or] at hx
  rcases hx with hx | hx
  · have hxy : x - y < 0 := by linarith [hy.1]
    rw [abs_of_neg hxy]
    linarith [hy.1]
  · have hxy : 0 < x - y := by linarith [hy.2]
    rw [abs_of_pos hxy]
    linarith [hy.2]

/-- Outside the expanded interval, the actual low kernel is identically zero
on the atom interval. -/
theorem paperLowCZKernel_eq_zero_of_not_mem_expanded
    (B : ℕ) (m : ℤ) {z R x y : ℝ} (hR : 0 < R)
    (hx : x ∉ centeredInterval z (2 * lowSupportRadius B m + R))
    (hy : y ∈ centeredInterval z R) :
    paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y = 0 := by
  by_contra hne
  have ht : x - y ∈ support (paperLowOscillatoryKernel
      (dyadicModulation m) (dyadicModulation_pos m).ne' B) := by
    simpa only [paperLowCZKernel, mem_support] using hne
  have hs := (paperLowOscillatoryKernel_support_normalized
    (dyadicModulation m) (dyadicModulation_pos m).ne' B ht).2
  rw [abs_of_pos (dyadicModulation_pos m)] at hs
  have hd : lowSupportRadius B m < |x - y| :=
    radius_lt_distance_of_not_mem_expanded hR (lowSupportRadius_pos B m) hx hy
  have hsqrt : 0 < Real.sqrt (dyadicModulation m) :=
    Real.sqrt_pos.2 (dyadicModulation_pos m)
  have hmul := mul_lt_mul_of_pos_right hd hsqrt
  unfold lowSupportRadius at hmul
  rw [div_mul_cancel₀ _ hsqrt.ne'] at hmul
  exact (not_lt_of_ge hmul.le) hs

/-- Hence the genuine low-kernel action on one level atom is supported in
the explicitly expanded interval. -/
theorem integral_paperLowCZKernel_levelAtom_eq_zero_of_not_mem_expanded
    {A : ℕ → ℝ} {f : ℝ → ℂ} (k B : ℕ) (m : ℤ)
    {z R x : ℝ} (hR : 0 < R)
    (hx : x ∉ centeredInterval z (2 * lowSupportRadius B m + R)) :
    (∫ y in centeredInterval z R,
      paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
        levelAtom A f k z R y) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
  simp only [paperLowCZKernel_eq_zero_of_not_mem_expanded B m hR hx hy,
    zero_mul, Pi.zero_apply]

/-- Raw integrated very-small estimate.  The first factor is exactly the
pointwise cancellation bound, and the second is the length of the only
interval on which the output can be nonzero. -/
theorem lintegral_enorm_paperLowCZKernel_levelAtom_compl_fivefold_le
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k B : ℕ} (hAk : 0 ≤ A k) (m : ℤ)
    {z R : ℝ} (hR : 0 < R) :
    (∫⁻ x in (centeredInterval z (5 * R))ᶜ,
      ‖∫ y in centeredInterval z R,
        paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
          levelAtom A f k z R y‖ₑ) ≤
      ENNReal.ofReal
          ((lowKernelDerivativeConstant * dyadicModulation m * (R / 2)) *
            ∫ y in centeredInterval z R, ‖levelAtom A f k z R y‖) *
        ENNReal.ofReal (2 * lowSupportRadius B m + R) := by
  let C : ℝ := (lowKernelDerivativeConstant * dyadicModulation m * (R / 2)) *
    ∫ y in centeredInterval z R, ‖levelAtom A f k z R y‖
  let E : Set ℝ := centeredInterval z (2 * lowSupportRadius B m + R)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg lowKernelDerivativeConstant_nonneg (dyadicModulation_pos m).le)
        (by linarith))
      (integral_nonneg fun _ ↦ norm_nonneg _)
  have hpoint : ∀ᵐ x ∂volume.restrict (centeredInterval z (5 * R))ᶜ,
      ‖∫ y in centeredInterval z R,
        paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
          levelAtom A f k z R y‖ₑ ≤ E.indicator (fun _ ↦ ENNReal.ofReal C) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ico.compl] with x hx
    by_cases hxE : x ∈ E
    · rw [indicator_of_mem hxE]
      simpa only [C, ofReal_norm] using ENNReal.ofReal_le_ofReal
        (norm_setIntegral_paperLowCZKernel_levelAtom_le_dyadic
          hf hAk m hR hx)
    · rw [indicator_of_notMem hxE,
        integral_paperLowCZKernel_levelAtom_eq_zero_of_not_mem_expanded
          k B m hR hxE, enorm_zero]
  calc
    (∫⁻ x in (centeredInterval z (5 * R))ᶜ,
      ‖∫ y in centeredInterval z R,
        paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
          levelAtom A f k z R y‖ₑ) ≤
        ∫⁻ x in (centeredInterval z (5 * R))ᶜ,
          E.indicator (fun _ ↦ ENNReal.ofReal C) x := lintegral_mono_ae hpoint
    _ ≤ ∫⁻ x, E.indicator (fun _ ↦ ENNReal.ofReal C) x :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal C * volume E :=
      lintegral_indicator_const measurableSet_Ico _
    _ = ENNReal.ofReal C * ENNReal.ofReal (2 * lowSupportRadius B m + R) := by
      rw [volume_centeredInterval]
    _ = _ := rfl

/-- Paper-facing atomwise estimate in the very-small range, now expressed
with the exact summable weight `2^(B+m/2+j)`. -/
theorem lintegral_enorm_paperLowCZKernel_levelAtom_verySmall_le
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k c B : ℕ} (hAk : 0 ≤ A k) (hB : 0 < B) {m j : ℤ}
    (hj : j ∈ LacunaryMiddleRange.L B c m)
    {z R : ℝ} (hR : 0 < R)
    (hscale : (2 : ℝ) ^ j ≤ R ∧ R < (2 : ℝ) ^ (j + 1)) :
    (∫⁻ x in (centeredInterval z (5 * R))ᶜ,
      ‖∫ y in centeredInterval z R,
        paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
          levelAtom A f k z R y‖ₑ) ≤
      ENNReal.ofReal (3 * lowKernelDerivativeConstant * verySmallWeight B m j) *
        ENNReal.ofReal
          (∫ y in centeredInterval z R, ‖levelAtom A f k z R y‖) := by
  let M : ℝ := ∫ y in centeredInterval z R, ‖levelAtom A f k z R y‖
  let C : ℝ := lowKernelDerivativeConstant * dyadicModulation m * (R / 2)
  let D : ℝ := 2 * lowSupportRadius B m + R
  have hM : 0 ≤ M := integral_nonneg fun _ ↦ norm_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg lowKernelDerivativeConstant_nonneg (dyadicModulation_pos m).le)
      (by linarith)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg
      (mul_nonneg (by norm_num) (lowSupportRadius_pos B m).le) hR.le
  have hcoef : C * D ≤
      3 * lowKernelDerivativeConstant * verySmallWeight B m j := by
    exact verySmallCancellationCoefficient_le hB hj hscale
  calc
    (∫⁻ x in (centeredInterval z (5 * R))ᶜ,
      ‖∫ y in centeredInterval z R,
        paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
          levelAtom A f k z R y‖ₑ) ≤
        ENNReal.ofReal (C * M) * ENNReal.ofReal D := by
      exact lintegral_enorm_paperLowCZKernel_levelAtom_compl_fivefold_le
        hf hAk m hR
    _ = ENNReal.ofReal ((C * D) * M) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hC hM)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal
        ((3 * lowKernelDerivativeConstant * verySmallWeight B m j) * M) := by
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoef hM)
    _ = ENNReal.ofReal (3 * lowKernelDerivativeConstant * verySmallWeight B m j) *
        ENNReal.ofReal M := by
      rw [ENNReal.ofReal_mul]
      exact mul_nonneg
        (mul_nonneg (by norm_num) lowKernelDerivativeConstant_nonneg)
        (verySmallWeight_pos B m j).le

/-- Strong fixed-scale family form, retaining the actual atom mass rather
than replacing it by the whole magnitude-level mass. -/
theorem tsum_lintegral_enorm_paperLowCZKernel_levelAtom_verySmall_le_atomMass
    {ι : Type*} [Countable ι]
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k c B : ℕ} (hAk : 0 ≤ A k) (hB : 0 < B) {m j : ℤ}
    (hj : j ∈ LacunaryMiddleRange.L B c m)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hscale : ∀ i, (2 : ℝ) ^ j ≤ R i ∧ R i < (2 : ℝ) ^ (j + 1)) :
    (∑' i : ι, ∫⁻ x in (centeredInterval (z i) (5 * R i))ᶜ,
      ‖∫ y in centeredInterval (z i) (R i),
        paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
          levelAtom A f k (z i) (R i) y‖ₑ) ≤
      ENNReal.ofReal (3 * lowKernelDerivativeConstant * verySmallWeight B m j) *
        ∑' i : ι, ENNReal.ofReal
          (∫ y, ‖levelAtom A f k (z i) (R i) y‖) := by
  have hlocal : ∀ i : ι,
      (∫⁻ x in (centeredInterval (z i) (5 * R i))ᶜ,
        ‖∫ y in centeredInterval (z i) (R i),
          paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
            levelAtom A f k (z i) (R i) y‖ₑ) ≤
        ENNReal.ofReal (3 * lowKernelDerivativeConstant * verySmallWeight B m j) *
          ENNReal.ofReal (∫ y, ‖levelAtom A f k (z i) (R i) y‖) := by
    intro i
    rw [← setIntegral_norm_levelAtom_eq_integral k (z i) (R i)]
    exact lintegral_enorm_paperLowCZKernel_levelAtom_verySmall_le
      hf hAk hB hj (hR i) (hscale i)
  have hsum := ENNReal.tsum_le_tsum hlocal
  rwa [ENNReal.tsum_mul_left] at hsum

/-- Summing the very-small estimate over a disjoint family of atoms in one
fixed spatial scale costs only the standard factor two from centering the
atoms. -/
theorem tsum_lintegral_enorm_paperLowCZKernel_levelAtom_verySmall_le
    {ι : Type*} [Countable ι]
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k c B : ℕ} (hAk : 0 ≤ A k) (hB : 0 < B) {m j : ℤ}
    (hj : j ∈ LacunaryMiddleRange.L B c m)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hscale : ∀ i, (2 : ℝ) ^ j ≤ R i ∧ R i < (2 : ℝ) ^ (j + 1))
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∑' i : ι, ∫⁻ x in (centeredInterval (z i) (5 * R i))ᶜ,
      ‖∫ y in centeredInterval (z i) (R i),
        paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
          levelAtom A f k (z i) (R i) y‖ₑ) ≤
      ENNReal.ofReal (6 * lowKernelDerivativeConstant * verySmallWeight B m j) *
        ∫⁻ x in PositiveLevelIntegration.magnitudeLevelSet A f k,
          ENNReal.ofReal ‖f x‖ := by
  let C : ENNReal :=
    ENNReal.ofReal (3 * lowKernelDerivativeConstant * verySmallWeight B m j)
  have hlocal : ∀ i : ι,
      (∫⁻ x in (centeredInterval (z i) (5 * R i))ᶜ,
        ‖∫ y in centeredInterval (z i) (R i),
          paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
            levelAtom A f k (z i) (R i) y‖ₑ) ≤
        C * ENNReal.ofReal
          (∫ y, ‖levelAtom A f k (z i) (R i) y‖) := by
    intro i
    rw [← setIntegral_norm_levelAtom_eq_integral k (z i) (R i)]
    exact lintegral_enorm_paperLowCZKernel_levelAtom_verySmall_le
      hf hAk hB hj (hR i) (hscale i)
  have hsum := ENNReal.tsum_le_tsum hlocal
  rw [ENNReal.tsum_mul_left] at hsum
  have hmass := tsum_atomL1Mass_le_two_mul_global_level_mass
    hf hAk z R hdisj
  have hcoefNonneg :
      0 ≤ 3 * lowKernelDerivativeConstant * verySmallWeight B m j :=
    mul_nonneg (mul_nonneg (by norm_num) lowKernelDerivativeConstant_nonneg)
      (verySmallWeight_pos B m j).le
  calc
    (∑' i : ι, ∫⁻ x in (centeredInterval (z i) (5 * R i))ᶜ,
      ‖∫ y in centeredInterval (z i) (R i),
        paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
          levelAtom A f k (z i) (R i) y‖ₑ) ≤
        C * ∑' i : ι, ENNReal.ofReal
          (∫ y, ‖levelAtom A f k (z i) (R i) y‖) := hsum
    _ ≤ C * (2 * PositiveLevelIntegration.magnitudeLevelL1Mass volume A f k) :=
      mul_le_mul' le_rfl hmass
    _ = ENNReal.ofReal
          (6 * lowKernelDerivativeConstant * verySmallWeight B m j) *
        PositiveLevelIntegration.magnitudeLevelL1Mass volume A f k := by
      have hcoef : C * (2 : ENNReal) = ENNReal.ofReal
          (6 * lowKernelDerivativeConstant * verySmallWeight B m j) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul hcoefNonneg]
        congr 1
        ring
      rw [← mul_assoc, hcoef]
    _ = _ := rfl

/-- The preceding estimate applied to the actual canonical stopping cells in
one exact dyadic scale class.  No auxiliary interval family is assumed. -/
theorem tsum_canonicalScaleCells_verySmall_le
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k c B : ℕ} (hAk : 0 ≤ A k) (hB : 0 < B) {m j : ℤ}
    (hj : j ∈ LacunaryMiddleRange.L B c m) :
    (∑' I : {I : stoppingCell f //
        I ∈ dyadicAtomScaleClass (stoppingLength (f := f)) j},
      ∫⁻ x in
        (centeredInterval (stoppingCenter I.1) (5 * stoppingLength I.1))ᶜ,
        ‖∫ y in centeredInterval (stoppingCenter I.1) (stoppingLength I.1),
          paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
            levelAtom A f k (stoppingCenter I.1) (stoppingLength I.1) y‖ₑ) ≤
      ENNReal.ofReal (6 * lowKernelDerivativeConstant * verySmallWeight B m j) *
        ∫⁻ x in PositiveLevelIntegration.magnitudeLevelSet A f k,
          ENNReal.ofReal ‖f x‖ := by
  refine tsum_lintegral_enorm_paperLowCZKernel_levelAtom_verySmall_le
    (ι := {I : stoppingCell f //
      I ∈ dyadicAtomScaleClass (stoppingLength (f := f)) j})
    (A := A) (f := f) (k := k) (c := c) (B := B) (m := m) (j := j)
    hf hAk hB hj
    (fun I ↦ stoppingCenter I.1) (fun I ↦ stoppingLength I.1)
    (fun I ↦ stoppingLength_pos I.1) (fun I ↦ I.2) ?_
  intro I J hIJ
  apply centeredStoppingIntervals_pairwiseDisjoint
  intro hcoe
  exact hIJ (Subtype.ext hcoe)

noncomputable def canonicalScaleVerySmallOutputMass
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B : ℕ) (m j : ℤ) : ENNReal :=
  ∑' I : {I : stoppingCell f //
      I ∈ dyadicAtomScaleClass (stoppingLength (f := f)) j},
    ∫⁻ x in (centeredInterval (stoppingCenter I.1) (5 * stoppingLength I.1))ᶜ,
      ‖∫ y in centeredInterval (stoppingCenter I.1) (stoppingLength I.1),
        paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
          levelAtom A f k (stoppingCenter I.1) (stoppingLength I.1) y‖ₑ

/-- The canonical scale slice is literally the disjoint atom sum indexed by
the stopping cells in that exact scale class. -/
theorem stoppingScaleLevelBadPart_eq_scaleDisjointLevelAtomSum
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (j : ℤ) (x : ℝ) :
    stoppingScaleLevelBadPart A f j k x =
      disjointLevelAtomSum A f k
        (fun I : {I : stoppingCell f //
          I ∈ dyadicAtomScaleClass (stoppingLength (f := f)) j} ↦
            stoppingCenter I.1)
        (fun I : {I : stoppingCell f //
          I ∈ dyadicAtomScaleClass (stoppingLength (f := f)) j} ↦
            stoppingLength I.1) x := by
  unfold stoppingScaleLevelBadPart disjointLevelAtomSum
  rw [← tsum_subtype
    (dyadicAtomScaleClass (stoppingLength (f := f)) j)
    (fun I : stoppingCell f ↦
      levelAtom A f k (stoppingCenter I) (stoppingLength I) x)]

/-- The low-kernel action on one canonical scale is exactly the sum of its
genuine atom actions. -/
theorem integral_paperLowCZKernel_stoppingScaleLevelBadPart_eq_tsum_cells
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k B : ℕ} (hAk : 0 ≤ A k) (m j : ℤ) (x : ℝ) :
    (∫ y, paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
      stoppingScaleLevelBadPart A f j k y) =
      ∑' I : {I : stoppingCell f //
          I ∈ dyadicAtomScaleClass (stoppingLength (f := f)) j},
        ∫ y in centeredInterval (stoppingCenter I.1) (stoppingLength I.1),
          paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
            levelAtom A f k (stoppingCenter I.1) (stoppingLength I.1) y := by
  have hs : stoppingScaleLevelBadPart A f j k =
      disjointLevelAtomSum A f k
        (fun I : {I : stoppingCell f //
          I ∈ dyadicAtomScaleClass (stoppingLength (f := f)) j} ↦
            stoppingCenter I.1)
        (fun I : {I : stoppingCell f //
          I ∈ dyadicAtomScaleClass (stoppingLength (f := f)) j} ↦
            stoppingLength I.1) := by
    funext y
    exact stoppingScaleLevelBadPart_eq_scaleDisjointLevelAtomSum A f k j y
  rw [hs]
  apply integral_paperLowCZKernel_mul_disjointLevelAtomSum
    (dyadicModulation_pos m).ne' B hf hfi hAk
  intro I J hIJ
  apply centeredStoppingIntervals_pairwiseDisjoint
  intro hcoe
  exact hIJ (Subtype.ext hcoe)

/-- Pointwise norm of the genuine low-kernel action on the canonical
scale-sliced bad part `b_{j,k}`. -/
noncomputable def canonicalScaleLowActionEnorm
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B : ℕ) (m j : ℤ) (x : ℝ) : ENNReal :=
    ‖∫ y, paperLowCZKernel
        (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
      stoppingScaleLevelBadPart A f j k y‖ₑ

theorem measurable_canonicalScaleLowActionEnorm
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    (k B : ℕ) (m j : ℤ) :
    Measurable (canonicalScaleLowActionEnorm A f k B m j) := by
  have hjoint : Measurable (fun p : ℝ × ℝ ↦
      paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B p.1 p.2 *
        stoppingScaleLevelBadPart A f j k p.2) := by
    have hK : Measurable (fun p : ℝ × ℝ ↦
        paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B p.1 p.2) :=
      (continuous_paperLowOscillatoryKernel (dyadicModulation_pos m).ne' B).measurable.comp
        (measurable_fst.sub measurable_snd)
    exact hK.mul ((measurable_stoppingScaleLevelBadPart hf j k).comp measurable_snd)
  have hs : StronglyMeasurable (fun x : ℝ ↦
      ∫ y, paperLowCZKernel
          (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
        stoppingScaleLevelBadPart A f j k y) :=
    hjoint.stronglyMeasurable.integral_prod_right
  change Measurable (fun x : ℝ ↦
    ‖∫ y, paperLowCZKernel
        (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
      stoppingScaleLevelBadPart A f j k y‖ₑ)
  simpa only [ofReal_norm] using hs.norm.measurable.ennreal_ofReal

/-- The genuine low-kernel output of `b_{j,k}`, integrated outside the one
global fivefold Calderón--Zygmund exceptional set. -/
noncomputable def canonicalScaleLowActionMass
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B : ℕ) (m j : ℤ) : ENNReal :=
  ∫⁻ x in (fivefoldExceptionalSet
      (stoppingCenter (f := f)) stoppingLength)ᶜ,
    canonicalScaleLowActionEnorm A f k B m j x

/-- Passing from individual atom complements to the global exceptional-set
complement and summing the exact atom identity bounds the actual scale
output by `canonicalScaleVerySmallOutputMass`. -/
theorem canonicalScaleLowActionMass_le_outputMass
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k B : ℕ} (hAk : 0 ≤ A k) (m j : ℤ) :
    canonicalScaleLowActionMass A f k B m j ≤
      canonicalScaleVerySmallOutputMass A f k B m j := by
  let S : Set (stoppingCell f) :=
    dyadicAtomScaleClass (stoppingLength (f := f)) j
  let E : Set ℝ := fivefoldExceptionalSet
    (stoppingCenter (f := f)) stoppingLength
  let F : {I : stoppingCell f // I ∈ S} → ℝ → ℂ := fun I x ↦
    ∫ y in centeredInterval (stoppingCenter I.1) (stoppingLength I.1),
      paperLowCZKernel (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
        levelAtom A f k (stoppingCenter I.1) (stoppingLength I.1) y
  have hmeas (I : {I : stoppingCell f // I ∈ S}) :
      AEMeasurable (fun x ↦ ‖F I x‖ₑ) (volume.restrict Eᶜ) := by
    have h := aestronglyMeasurable_norm_setIntegral_paperLowCZKernel_levelAtom
      (A := A) (dyadicModulation_pos m).ne' B hf k
      (stoppingCenter I.1) (stoppingLength I.1)
    simpa only [F, ofReal_norm] using h.aemeasurable.ennreal_ofReal.restrict
  have hsub (I : {I : stoppingCell f // I ∈ S}) :
      Eᶜ ⊆ (centeredInterval
        (stoppingCenter I.1) (5 * stoppingLength I.1))ᶜ := by
    intro x hxE hxI
    apply hxE
    exact mem_iUnion.mpr ⟨I.1, hxI⟩
  calc
    canonicalScaleLowActionMass A f k B m j =
        ∫⁻ x in Eᶜ, ‖∑' I : {I : stoppingCell f // I ∈ S}, F I x‖ₑ := by
      unfold canonicalScaleLowActionMass
      change (∫⁻ x in Eᶜ,
        ‖∫ y, paperLowCZKernel
            (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
          stoppingScaleLevelBadPart A f j k y‖ₑ) = _
      apply lintegral_congr
      intro x
      rw [integral_paperLowCZKernel_stoppingScaleLevelBadPart_eq_tsum_cells
        hf hfi hAk]
    _ ≤ ∫⁻ x in Eᶜ,
        ∑' I : {I : stoppingCell f // I ∈ S}, ‖F I x‖ₑ := by
      apply lintegral_mono
      intro x
      exact enorm_tsum_le_tsum_enorm
    _ = ∑' I : {I : stoppingCell f // I ∈ S},
        ∫⁻ x in Eᶜ, ‖F I x‖ₑ := by
      rw [lintegral_tsum hmeas]
    _ ≤ ∑' I : {I : stoppingCell f // I ∈ S},
        ∫⁻ x in (centeredInterval
          (stoppingCenter I.1) (5 * stoppingLength I.1))ᶜ,
          ‖F I x‖ₑ := by
      apply ENNReal.tsum_le_tsum
      intro I
      exact lintegral_mono_set (hsub I)
    _ = canonicalScaleVerySmallOutputMass A f k B m j := by
      rfl

/-- Actual `L¹` mass of the canonical level atoms in spatial scale `j`. -/
noncomputable def canonicalScaleAtomL1Mass
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (j : ℤ) : ENNReal :=
  LacunaryMiddleRangeSummation.atomScaleMass (stoppingLength (f := f))
    (fun I ↦ ENNReal.ofReal
      (∫ x, ‖levelAtom A f k (stoppingCenter I) (stoppingLength I) x‖)) j

/-- The fixed `(m,j)` canonical output is bounded by the paper's weight times
the mass actually present at scale `j`. -/
theorem canonicalScaleVerySmallOutputMass_le
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k c B : ℕ} (hAk : 0 ≤ A k) (hB : 0 < B) {m j : ℤ}
    (hj : j ∈ LacunaryMiddleRange.L B c m) :
    canonicalScaleVerySmallOutputMass A f k B m j ≤
      ENNReal.ofReal (3 * lowKernelDerivativeConstant * verySmallWeight B m j) *
        canonicalScaleAtomL1Mass A f k j := by
  have h := tsum_lintegral_enorm_paperLowCZKernel_levelAtom_verySmall_le_atomMass
    (ι := {I : stoppingCell f //
      I ∈ dyadicAtomScaleClass (stoppingLength (f := f)) j})
    (A := A) (f := f) (k := k) (c := c) (B := B) (m := m) (j := j)
    hf hAk hB hj
    (fun I ↦ stoppingCenter I.1) (fun I ↦ stoppingLength I.1)
    (fun I ↦ stoppingLength_pos I.1) (fun I ↦ I.2)
  change canonicalScaleVerySmallOutputMass A f k B m j ≤ _
  refine h.trans_eq ?_
  congr 1
  unfold canonicalScaleAtomL1Mass LacunaryMiddleRangeSummation.atomScaleMass
  rw [← tsum_subtype
    (dyadicAtomScaleClass (stoppingLength (f := f)) j)
    (fun I : stoppingCell f ↦ ENNReal.ofReal
      (∫ x, ‖levelAtom A f k (stoppingCenter I) (stoppingLength I) x‖))]

/-- The genuine canonical output, restricted to the paper's very-small
indices. -/
noncomputable def restrictedCanonicalVerySmallOutputMass
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (m j : ℤ) : ENNReal :=
  (LacunaryMiddleRange.L B c m).indicator
    (fun j ↦ canonicalScaleVerySmallOutputMass A f k B m j) j

/-- Termwise comparison with the nonnegative weight used by the already
verified geometric Tonelli lemma. -/
theorem restrictedCanonicalVerySmallOutputMass_le
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k c B : ℕ} (hAk : 0 ≤ A k) (hB : 0 < B) (m j : ℤ) :
    restrictedCanonicalVerySmallOutputMass A f k B c m j ≤
      ENNReal.ofReal (3 * lowKernelDerivativeConstant) *
        ENNReal.ofReal (restrictedVerySmallWeight B c j m) *
          canonicalScaleAtomL1Mass A f k j := by
  by_cases hj : j ∈ LacunaryMiddleRange.L B c m
  · have hm : m ∈ verySmallModulations B c j := hj
    rw [restrictedCanonicalVerySmallOutputMass, indicator_of_mem hj,
      restrictedVerySmallWeight, indicator_of_mem hm]
    apply (canonicalScaleVerySmallOutputMass_le hf hAk hB hj).trans_eq
    rw [← ENNReal.ofReal_mul
      (mul_nonneg (by norm_num) lowKernelDerivativeConstant_nonneg)]
  · have hm : m ∉ verySmallModulations B c j := hj
    simp [restrictedCanonicalVerySmallOutputMass, restrictedVerySmallWeight, hj, hm]

/-- Summation over all lacunary modulations and all atom scales.  This is the
paper's complete very-small double sum for one magnitude level. -/
theorem tsum_tsum_restrictedCanonicalVerySmallOutputMass_le
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k c B : ℕ} (hAk : 0 ≤ A k) (hB : 0 < B) :
    (∑' m : ℤ, ∑' j : ℤ,
      restrictedCanonicalVerySmallOutputMass A f k B c m j) ≤
      ENNReal.ofReal (3 * lowKernelDerivativeConstant) *
        ENNReal.ofReal verySmallGeometricConstant *
          ∑' j : ℤ, canonicalScaleAtomL1Mass A f k j := by
  have hterm : ∀ m j : ℤ,
      restrictedCanonicalVerySmallOutputMass A f k B c m j ≤
        ENNReal.ofReal (3 * lowKernelDerivativeConstant) *
          (ENNReal.ofReal (restrictedVerySmallWeight B c j m) *
            canonicalScaleAtomL1Mass A f k j) := by
    intro m j
    simpa only [mul_assoc] using
      restrictedCanonicalVerySmallOutputMass_le hf hAk hB m j
  calc
    (∑' m : ℤ, ∑' j : ℤ,
      restrictedCanonicalVerySmallOutputMass A f k B c m j) ≤
        ∑' m : ℤ, ∑' j : ℤ,
          ENNReal.ofReal (3 * lowKernelDerivativeConstant) *
            (ENNReal.ofReal (restrictedVerySmallWeight B c j m) *
              canonicalScaleAtomL1Mass A f k j) :=
      ENNReal.tsum_le_tsum (fun m ↦ ENNReal.tsum_le_tsum (hterm m))
    _ = ENNReal.ofReal (3 * lowKernelDerivativeConstant) *
        (∑' m : ℤ, ∑' j : ℤ,
          ENNReal.ofReal (restrictedVerySmallWeight B c j m) *
            canonicalScaleAtomL1Mass A f k j) := by
      simp_rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (3 * lowKernelDerivativeConstant) *
        (ENNReal.ofReal verySmallGeometricConstant *
          ∑' j : ℤ, canonicalScaleAtomL1Mass A f k j) := by
      gcongr
      exact tsum_tsum_verySmall_le B c (canonicalScaleAtomL1Mass A f k)
    _ = _ := by rw [mul_assoc]

/-- The exact half-open scale partition loses no atom mass; only the standard
factor two from subtracting the atom average remains. -/
theorem tsum_canonicalScaleAtomL1Mass_le
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k) :
    (∑' j : ℤ, canonicalScaleAtomL1Mass A f k j) ≤
      2 * PositiveLevelIntegration.magnitudeLevelL1Mass volume A f k := by
  unfold canonicalScaleAtomL1Mass
  rw [LacunaryMiddleRangeSummation.tsum_atomScaleMass_eq
    (stoppingLength (f := f)) stoppingLength_pos]
  exact tsum_atomL1Mass_le_two_mul_global_level_mass hf hAk
    _ _ centeredStoppingIntervals_pairwiseDisjoint

/-- Final geometric summation of the genuine very-small contribution for one
magnitude level, expressed directly in terms of that level's `L¹` mass. -/
theorem tsum_tsum_restrictedCanonicalVerySmallOutputMass_le_levelMass
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k c B : ℕ} (hAk : 0 ≤ A k) (hB : 0 < B) :
    (∑' m : ℤ, ∑' j : ℤ,
      restrictedCanonicalVerySmallOutputMass A f k B c m j) ≤
      ENNReal.ofReal (6 * lowKernelDerivativeConstant * verySmallGeometricConstant) *
        PositiveLevelIntegration.magnitudeLevelL1Mass volume A f k := by
  calc
    (∑' m : ℤ, ∑' j : ℤ,
      restrictedCanonicalVerySmallOutputMass A f k B c m j) ≤
        ENNReal.ofReal (3 * lowKernelDerivativeConstant) *
          ENNReal.ofReal verySmallGeometricConstant *
            ∑' j : ℤ, canonicalScaleAtomL1Mass A f k j :=
      tsum_tsum_restrictedCanonicalVerySmallOutputMass_le hf hAk hB
    _ ≤ ENNReal.ofReal (3 * lowKernelDerivativeConstant) *
          ENNReal.ofReal verySmallGeometricConstant *
            (2 * PositiveLevelIntegration.magnitudeLevelL1Mass volume A f k) := by
      gcongr
      exact tsum_canonicalScaleAtomL1Mass_le hf hAk
    _ = ENNReal.ofReal
          (6 * lowKernelDerivativeConstant * verySmallGeometricConstant) *
        PositiveLevelIntegration.magnitudeLevelL1Mass volume A f k := by
      have hC : 0 ≤ 3 * lowKernelDerivativeConstant :=
        mul_nonneg (by norm_num) lowKernelDerivativeConstant_nonneg
      have hG : 0 ≤ verySmallGeometricConstant :=
        verySmallGeometricConstant_nonneg
      have hcoef : ENNReal.ofReal (3 * lowKernelDerivativeConstant) *
          ENNReal.ofReal verySmallGeometricConstant * 2 =
          ENNReal.ofReal
            (6 * lowKernelDerivativeConstant * verySmallGeometricConstant) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul hC,
          ← ENNReal.ofReal_mul (mul_nonneg hC hG)]
        congr 1
        ring
      rw [← mul_assoc, hcoef]

/-- The actual scale-output mass, retained exactly on the paper's
very-small index relation. -/
noncomputable def restrictedCanonicalScaleLowActionMass
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (m j : ℤ) : ENNReal :=
  (LacunaryMiddleRange.L B c m).indicator
    (fun j ↦ canonicalScaleLowActionMass A f k B m j) j

theorem restrictedCanonicalScaleLowActionMass_le_outputMass
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k B c : ℕ} (hAk : 0 ≤ A k) (m j : ℤ) :
    restrictedCanonicalScaleLowActionMass A f k B c m j ≤
      restrictedCanonicalVerySmallOutputMass A f k B c m j := by
  by_cases hj : j ∈ LacunaryMiddleRange.L B c m
  · simp only [restrictedCanonicalScaleLowActionMass,
      restrictedCanonicalVerySmallOutputMass, indicator_of_mem hj]
    exact canonicalScaleLowActionMass_le_outputMass hf hfi hAk m j
  · simp [restrictedCanonicalScaleLowActionMass,
      restrictedCanonicalVerySmallOutputMass, hj]

/-- The paper's full very-small double sum now controls the genuine
low-kernel scale outputs outside the global exceptional set. -/
theorem tsum_tsum_restrictedCanonicalScaleLowActionMass_le_levelMass
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k c B : ℕ} (hAk : 0 ≤ A k) (hB : 0 < B) :
    (∑' m : ℤ, ∑' j : ℤ,
      restrictedCanonicalScaleLowActionMass A f k B c m j) ≤
      ENNReal.ofReal (6 * lowKernelDerivativeConstant * verySmallGeometricConstant) *
        PositiveLevelIntegration.magnitudeLevelL1Mass volume A f k := by
  calc
    (∑' m : ℤ, ∑' j : ℤ,
      restrictedCanonicalScaleLowActionMass A f k B c m j) ≤
        ∑' m : ℤ, ∑' j : ℤ,
          restrictedCanonicalVerySmallOutputMass A f k B c m j := by
      apply ENNReal.tsum_le_tsum
      intro m
      apply ENNReal.tsum_le_tsum
      intro j
      exact restrictedCanonicalScaleLowActionMass_le_outputMass hf hfi hAk m j
    _ ≤ _ := tsum_tsum_restrictedCanonicalVerySmallOutputMass_le_levelMass
      hf hAk hB

/-- Pointwise genuine scale action restricted to the very-small relation. -/
noncomputable def restrictedCanonicalScaleLowActionEnorm
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (m j : ℤ) (x : ℝ) : ENNReal :=
  (LacunaryMiddleRange.L B c m).indicator
    (fun j ↦ canonicalScaleLowActionEnorm A f k B m j x) j

theorem measurable_restrictedCanonicalScaleLowActionEnorm
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    (k B c : ℕ) (m j : ℤ) :
    Measurable (restrictedCanonicalScaleLowActionEnorm A f k B c m j) := by
  unfold restrictedCanonicalScaleLowActionEnorm
  by_cases hj : j ∈ LacunaryMiddleRange.L B c m
  · simp only [indicator_of_mem hj]
    exact measurable_canonicalScaleLowActionEnorm (A := A) hf k B m j
  · simp only [indicator_of_notMem hj]
    exact measurable_const

theorem lintegral_restrictedCanonicalScaleLowActionEnorm_compl
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (m j : ℤ) :
    (∫⁻ x in (fivefoldExceptionalSet
        (stoppingCenter (f := f)) stoppingLength)ᶜ,
      restrictedCanonicalScaleLowActionEnorm A f k B c m j x) =
      restrictedCanonicalScaleLowActionMass A f k B c m j := by
  by_cases hj : j ∈ LacunaryMiddleRange.L B c m
  · simp [restrictedCanonicalScaleLowActionEnorm,
      restrictedCanonicalScaleLowActionMass, canonicalScaleLowActionMass, hj]
  · simp [restrictedCanonicalScaleLowActionEnorm,
      restrictedCanonicalScaleLowActionMass, hj]

/-- The paper's very-small triangle majorant at one magnitude level.  Every
term is the actual low-kernel action on the genuine canonical `b_{j,k}`. -/
noncomputable def verySmallLowContributionAtLevel
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (x : ℝ) : ENNReal :=
  ∑' m : ℤ, ∑' j : ℤ,
    restrictedCanonicalScaleLowActionEnorm A f k B c m j x

theorem measurable_verySmallLowContributionAtLevel
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    (k B c : ℕ) : Measurable (verySmallLowContributionAtLevel A f k B c) :=
  Measurable.tsum (fun m ↦ Measurable.tsum fun j ↦
    measurable_restrictedCanonicalScaleLowActionEnorm hf k B c m j)

theorem lintegral_verySmallLowContributionAtLevel_compl_eq
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    (k B c : ℕ) :
    (∫⁻ x in (fivefoldExceptionalSet
        (stoppingCenter (f := f)) stoppingLength)ᶜ,
      verySmallLowContributionAtLevel A f k B c x) =
      ∑' m : ℤ, ∑' j : ℤ,
        restrictedCanonicalScaleLowActionMass A f k B c m j := by
  unfold verySmallLowContributionAtLevel
  rw [lintegral_tsum (fun m ↦
    (Measurable.tsum fun j ↦
      measurable_restrictedCanonicalScaleLowActionEnorm hf k B c m j).aemeasurable.restrict)]
  apply tsum_congr
  intro m
  rw [lintegral_tsum (fun j ↦
    (measurable_restrictedCanonicalScaleLowActionEnorm hf k B c m j).aemeasurable.restrict)]
  exact tsum_congr fun j ↦
    lintegral_restrictedCanonicalScaleLowActionEnorm_compl A f k B c m j

theorem lintegral_verySmallLowContributionAtLevel_compl_le
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k c B : ℕ} (hAk : 0 ≤ A k) (hB : 0 < B) :
    (∫⁻ x in (fivefoldExceptionalSet
        (stoppingCenter (f := f)) stoppingLength)ᶜ,
      verySmallLowContributionAtLevel A f k B c x) ≤
      ENNReal.ofReal (6 * lowKernelDerivativeConstant * verySmallGeometricConstant) *
        PositiveLevelIntegration.magnitudeLevelL1Mass volume A f k := by
  rw [lintegral_verySmallLowContributionAtLevel_compl_eq hf]
  exact tsum_tsum_restrictedCanonicalScaleLowActionMass_le_levelMass
    hf hfi hAk hB

/-- The genuine lacunary very-small contribution, summed over all magnitude
levels with the paper's level-dependent low-height cutoffs. -/
noncomputable def lacunaryVerySmallLowContribution
    (f : ℝ → ℂ) (B : ℕ → ℕ) (c : ℕ) (x : ℝ) : ENNReal :=
  ∑' k : ℕ,
    verySmallLowContributionAtLevel lacunaryAmplitude f k (B k) c x

theorem measurable_lacunaryVerySmallLowContribution
    {f : ℝ → ℂ} (hf : Measurable f) (B : ℕ → ℕ) (c : ℕ) :
    Measurable (lacunaryVerySmallLowContribution f B c) :=
  Measurable.tsum fun k ↦
    measurable_verySmallLowContributionAtLevel hf k (B k) c

/-- Complete `L¹` estimate for the actual very-small lacunary contribution
outside the global fivefold exceptional set.  The bound is uniform in the
positive cutoff sequence `B_k`. -/
theorem lintegral_lacunaryVerySmallLowContribution_compl_le
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} (hB : ∀ k, 0 < B k) (c : ℕ) :
    (∫⁻ x in (fivefoldExceptionalSet
        (stoppingCenter (f := f)) stoppingLength)ᶜ,
      lacunaryVerySmallLowContribution f B c x) ≤
      ENNReal.ofReal (6 * lowKernelDerivativeConstant * verySmallGeometricConstant) *
        ∫⁻ x, ‖f x‖ₑ := by
  unfold lacunaryVerySmallLowContribution
  rw [lintegral_tsum (fun k ↦
    (measurable_verySmallLowContributionAtLevel hf k (B k) c).aemeasurable.restrict)]
  have hm : (∑' k : ℕ,
      PositiveLevelIntegration.magnitudeLevelL1Mass
        volume lacunaryAmplitude f k) = ∫⁻ x, ‖f x‖ₑ := by
    unfold PositiveLevelIntegration.magnitudeLevelL1Mass
    rw [← lintegral_iUnion
      (fun k ↦ PositiveLevelIntegration.measurableSet_magnitudeLevelSet hf k)
      (fun k l hkl ↦ PositiveLevelIntegration.magnitudeLevelSet_disjoint
        PositiveLevelIntegration.strictMono_lacunaryAmplitude f hkl),
      PositiveLevelIntegration.iUnion_magnitudeLevelSet_eq_univ
        (lacunaryAmplitude_pos 0).le
        PositiveLevelIntegration.strictMono_lacunaryAmplitude
        PositiveLevelIntegration.lacunaryAmplitude_cofinal f]
    simp only [Measure.restrict_univ, ofReal_norm]
  calc
    (∑' k : ℕ, ∫⁻ x in (fivefoldExceptionalSet
        (stoppingCenter (f := f)) stoppingLength)ᶜ,
      verySmallLowContributionAtLevel lacunaryAmplitude f k (B k) c x) ≤
        ∑' k : ℕ,
          ENNReal.ofReal
              (6 * lowKernelDerivativeConstant * verySmallGeometricConstant) *
            PositiveLevelIntegration.magnitudeLevelL1Mass
              volume lacunaryAmplitude f k := by
      apply ENNReal.tsum_le_tsum
      intro k
      exact lintegral_verySmallLowContributionAtLevel_compl_le
        hf hfi (lacunaryAmplitude_pos k).le (hB k)
    _ = ENNReal.ofReal
          (6 * lowKernelDerivativeConstant * verySmallGeometricConstant) *
        ∑' k : ℕ, PositiveLevelIntegration.magnitudeLevelL1Mass
          volume lacunaryAmplitude f k := by
      rw [ENNReal.tsum_mul_left]
    _ = _ := by rw [hm]


end LacunaryVerySmallOperator
end QuadraticCarleson
