/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LowKernelBadAtomSharp
import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundLevelAtoms
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Summing the sharp low-kernel estimate over a magnitude level

This file applies the sharp atomwise `O(B + 1)` low-kernel estimate to an
arbitrary countable pairwise-disjoint family of centered intervals.  The
atom `L¹` masses are then summed using the exact magnitude-level result from
`CalderonZygmundLevelAtoms`.  Each output is integrated on the complement of
the atom's triple interval; this is stronger than the paper's required
complement of `5I` after restriction.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators Function

namespace QuadraticCarleson
namespace LowKernelLevelSummation

open CalderonZygmundLevelAtoms
open PositiveEndpointOptimization PositiveLevelIntegration


noncomputable section

theorem continuous_paperLowOscillatoryKernel
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ) :
    Continuous (paperLowOscillatoryKernel lam hlam B) := by
  unfold paperLowOscillatoryKernel lowOscillatoryKernel
  apply continuous_finsetSum
  intro r hr
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp (dyadicPsi_smooth _).continuous
  · unfold phase
    fun_prop

/-- A level atom has zero set integral on its defining interval. -/
theorem setIntegral_levelAtom_eq_zero
    {A : ℕ → ℝ} {f : ℝ → ℂ} (k : ℕ) (z R : ℝ) :
    ∫ y in centeredInterval z R, levelAtom A f k z R y = 0 := by
  rw [← MeasureTheory.integral_indicator
    (show MeasurableSet (centeredInterval z R) from measurableSet_Ico)]
  have hind : (centeredInterval z R).indicator (levelAtom A f k z R) =
      levelAtom A f k z R := by
    funext y
    by_cases hy : y ∈ centeredInterval z R
    · simp [hy]
    · simp [hy, levelAtom_eq_zero_of_not_mem hy]
  rw [hind, integral_levelAtom_eq_zero]

/-- Since a level atom is supported on its defining interval, its set and
global `L¹` masses agree. -/
theorem setIntegral_norm_levelAtom_eq_integral
    {A : ℕ → ℝ} {f : ℝ → ℂ} (k : ℕ) (z R : ℝ) :
    (∫ y in centeredInterval z R, ‖levelAtom A f k z R y‖) =
      ∫ y, ‖levelAtom A f k z R y‖ := by
  rw [← MeasureTheory.integral_indicator
    (show MeasurableSet (centeredInterval z R) from measurableSet_Ico)]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ centeredInterval z R
  · simp [hy]
  · simp [hy, levelAtom_eq_zero_of_not_mem hy]

/-- Off the triple interval, multiplication by the low kernel preserves
integrability of a level atom on its supporting interval. -/
theorem integrableOn_paperLowCZKernel_mul_levelAtom
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k) {z R x : ℝ} (hR : 0 < R)
    (hx : x ∉ tripleCenteredInterval z R) :
    IntegrableOn
      (fun y ↦ paperLowCZKernel lam hlam B x y * levelAtom A f k z R y)
      (centeredInterval z R) := by
  let b := levelAtom A f k z R
  have hb : IntegrableOn b (centeredInterval z R) :=
    (integrable_levelAtom hf hAk z R).integrableOn
  have hxz : 0 < |x - z| := by
    have := not_mem_tripleCenteredInterval_abs hx
    linarith
  have hmajorant : IntegrableOn
      (fun y ↦ (2 / |x - z|) * ‖b y‖) (centeredInterval z R) :=
    hb.norm.const_mul (2 / |x - z|)
  have hmeas : AEStronglyMeasurable
      (fun y ↦ paperLowCZKernel lam hlam B x y * b y)
      (volume.restrict (centeredInterval z R)) := by
    have hK : Continuous (fun y ↦ paperLowCZKernel lam hlam B x y) :=
      (continuous_paperLowOscillatoryKernel hlam B).comp
        (continuous_const.sub continuous_id)
    exact (hK.measurable.mul (measurable_levelAtom hf k z R)).aestronglyMeasurable.restrict
  apply Integrable.mono' hmajorant hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
  have hdist : |x - z| / 2 ≤ |x - y| :=
    half_center_distance_le_distance hR.le hx hy
  have hxy : 0 < |x - y| := lt_of_lt_of_le (half_pos hxz) hdist
  have hkernel : ‖paperLowCZKernel lam hlam B x y‖ ≤ 2 / |x - z| := by
    calc
      ‖paperLowCZKernel lam hlam B x y‖ ≤ 1 / |x - y| := by
        exact paperLowOscillatoryKernel_norm_le_inv_abs hlam B
          (sub_ne_zero.mpr (by
            intro h
            rw [h] at hxy
            simp at hxy))
      _ ≤ 1 / (|x - z| / 2) :=
        one_div_le_one_div_of_le (half_pos hxz) hdist
      _ = 2 / |x - z| := by field_simp [ne_of_gt hxz]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hkernel (norm_nonneg (b y))

/-- The norm of the parameterized level-atom output is measurable. -/
theorem aestronglyMeasurable_norm_setIntegral_paperLowCZKernel_levelAtom
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    (k : ℕ) (z R : ℝ) :
    AEStronglyMeasurable
      (fun x ↦ ‖∫ y in centeredInterval z R,
        paperLowCZKernel lam hlam B x y * levelAtom A f k z R y‖) := by
  have hjoint : Measurable (fun p : ℝ × ℝ ↦
      paperLowCZKernel lam hlam B p.1 p.2 * levelAtom A f k z R p.2) := by
    have hK : Measurable (fun p : ℝ × ℝ ↦
        paperLowCZKernel lam hlam B p.1 p.2) :=
      (continuous_paperLowOscillatoryKernel hlam B).measurable.comp
        (measurable_fst.sub measurable_snd)
    exact hK.mul ((measurable_levelAtom hf k z R).comp measurable_snd)
  exact (hjoint.stronglyMeasurable.integral_prod_right
    (ν := volume.restrict (centeredInterval z R))).norm.aestronglyMeasurable

/-- Paper-facing levelwise low-kernel estimate for an arbitrary countable
pairwise-disjoint family of centered intervals. -/
theorem tsum_integral_norm_paperLowCZKernel_levelAtom_le
    {ι : Type*} [Countable ι]
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∑' i : ι, ENNReal.ofReal
      (∫ x in (tripleCenteredInterval (z i) (R i))ᶜ,
        ‖∫ y in centeredInterval (z i) (R i),
          paperLowCZKernel lam hlam B x y *
            levelAtom A f k (z i) (R i) y‖)) ≤
      ENNReal.ofReal
          (8 * (B + 1 : ℝ) * lowKernelBadAtomConstant) *
        ∫⁻ x in magnitudeLevelSet A f k, ENNReal.ofReal ‖f x‖ := by
  let C : ℝ := 4 * (B + 1 : ℝ) * lowKernelBadAtomConstant
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by positivity)) lowKernelBadAtomConstant_nonneg
  have hlocal : ∀ i : ι,
      ENNReal.ofReal
        (∫ x in (tripleCenteredInterval (z i) (R i))ᶜ,
          ‖∫ y in centeredInterval (z i) (R i),
            paperLowCZKernel lam hlam B x y *
              levelAtom A f k (z i) (R i) y‖) ≤
        ENNReal.ofReal C *
          ENNReal.ofReal
            (∫ y, ‖levelAtom A f k (z i) (R i) y‖) := by
    intro i
    have hatom := integrable_levelAtom hf hAk (z i) (R i)
    have hsharp := integral_norm_paperLowCZKernel_le_sharp
      hlam B (levelAtom A f k (z i) (R i)) (z i) (R i)
      (hR i) hatom.integrableOn
      (setIntegral_levelAtom_eq_zero k (z i) (R i))
      (fun x hx ↦ integrableOn_paperLowCZKernel_mul_levelAtom
        hlam B hf hAk (hR i) hx)
      ((aestronglyMeasurable_norm_setIntegral_paperLowCZKernel_levelAtom
        hlam B hf k (z i) (R i)).restrict)
    rw [setIntegral_norm_levelAtom_eq_integral k (z i) (R i)] at hsharp
    calc
      ENNReal.ofReal
          (∫ x in (tripleCenteredInterval (z i) (R i))ᶜ,
            ‖∫ y in centeredInterval (z i) (R i),
              paperLowCZKernel lam hlam B x y *
                levelAtom A f k (z i) (R i) y‖) ≤
          ENNReal.ofReal
            (C * ∫ y, ‖levelAtom A f k (z i) (R i) y‖) := by
        apply ENNReal.ofReal_le_ofReal
        simpa only [C, mul_assoc] using hsharp
      _ = ENNReal.ofReal C * ENNReal.ofReal
          (∫ y, ‖levelAtom A f k (z i) (R i) y‖) := by
        rw [ENNReal.ofReal_mul hC]
  calc
    (∑' i : ι, ENNReal.ofReal
      (∫ x in (tripleCenteredInterval (z i) (R i))ᶜ,
        ‖∫ y in centeredInterval (z i) (R i),
          paperLowCZKernel lam hlam B x y *
            levelAtom A f k (z i) (R i) y‖)) ≤
        ∑' i : ι, ENNReal.ofReal C * ENNReal.ofReal
          (∫ y, ‖levelAtom A f k (z i) (R i) y‖) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ENNReal.ofReal C *
        ∑' i : ι, ENNReal.ofReal
          (∫ y, ‖levelAtom A f k (z i) (R i) y‖) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal C *
        (2 * ∫⁻ x in magnitudeLevelSet A f k, ENNReal.ofReal ‖f x‖) := by
      gcongr
      exact tsum_atomL1Mass_le_two_mul_global_level_mass hf hAk z R hdisj
    _ = ENNReal.ofReal
          (8 * (B + 1 : ℝ) * lowKernelBadAtomConstant) *
        ∫⁻ x in magnitudeLevelSet A f k, ENNReal.ofReal ‖f x‖ := by
      let G := ∫⁻ x in magnitudeLevelSet A f k, ENNReal.ofReal ‖f x‖
      have hcoef : ENNReal.ofReal C * (2 : ENNReal) =
          ENNReal.ofReal (8 * (B + 1 : ℝ) * lowKernelBadAtomConstant) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul hC]
        congr 1
        dsimp [C]
        ring
      change ENNReal.ofReal C * (2 * G) = _ * G
      rw [← mul_assoc, hcoef]

/-! ### Full and lacunary magnitude levels -/

theorem tsum_integral_norm_paperLowCZKernel_fullLevelAtom_le
    {ι : Type*} [Countable ι]
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    {f : ℝ → ℂ} (hf : Measurable f) (k : ℕ)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∑' i : ι, ENNReal.ofReal
      (∫ x in (tripleCenteredInterval (z i) (R i))ᶜ,
        ‖∫ y in centeredInterval (z i) (R i),
          paperLowCZKernel lam hlam B x y *
            fullLevelAtom f k (z i) (R i) y‖)) ≤
      ENNReal.ofReal
          (8 * (B + 1 : ℝ) * lowKernelBadAtomConstant) *
        ∫⁻ x in fullMagnitudeLevelSet f k, ENNReal.ofReal ‖f x‖ := by
  simpa [fullMagnitudeLevelSet] using
    tsum_integral_norm_paperLowCZKernel_levelAtom_le
      hlam B hf (fullAmplitude_pos k).le z R hR hdisj

theorem tsum_integral_norm_paperLowCZKernel_lacunaryLevelAtom_le
    {ι : Type*} [Countable ι]
    {lam : ℝ} (hlam : lam ≠ 0) (B : ℕ)
    {f : ℝ → ℂ} (hf : Measurable f) (k : ℕ)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∑' i : ι, ENNReal.ofReal
      (∫ x in (tripleCenteredInterval (z i) (R i))ᶜ,
        ‖∫ y in centeredInterval (z i) (R i),
          paperLowCZKernel lam hlam B x y *
            lacunaryLevelAtom f k (z i) (R i) y‖)) ≤
      ENNReal.ofReal
          (8 * (B + 1 : ℝ) * lowKernelBadAtomConstant) *
        ∫⁻ x in lacunaryMagnitudeLevelSet f k, ENNReal.ofReal ‖f x‖ := by
  simpa [lacunaryMagnitudeLevelSet] using
    tsum_integral_norm_paperLowCZKernel_levelAtom_le
      hlam B hf (lacunaryAmplitude_pos k).le z R hR hdisj

end
end LowKernelLevelSummation
end QuadraticCarleson
