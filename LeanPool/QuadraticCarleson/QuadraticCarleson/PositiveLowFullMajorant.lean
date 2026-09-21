/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LowKernelRealMaximal
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveHighHeightFullEndpoint

/-!
# A common measurable majorant for the full low contribution

The atomwise majorant is cut off on the complement of the triple interval.
Its countable sum is measurable, unlike an arbitrary uncountable supremum.
The paper's exceptional set uses the larger fivefold intervals.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveLowFullEstimate

open CalderonZygmundLevelAtoms LowKernelLevelSummation
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate

/-- The decaying low-frequency atom bound outside the tripled supporting interval. -/
noncomputable def lowAtomMajorant (B : ℕ) (b : ℝ → ℂ) (z R x : ℝ) : ℝ≥0∞ :=
  (tripleCenteredInterval z R)ᶜ.indicator (fun x ↦
    ENNReal.ofReal (lowKernelBadAtomConstant * ∫ y, ‖b y‖) *
      ENNReal.ofReal (lowDecayMajorant ((2 : ℝ) ^ (2 * B)) (3 * R / 2) z x)) x

theorem measurable_lowAtomMajorant (B : ℕ) (b : ℝ → ℂ) (z R : ℝ) :
    Measurable (lowAtomMajorant B b z R) := by
  unfold lowAtomMajorant lowDecayMajorant tripleCenteredInterval
  apply Measurable.indicator _ measurableSet_Icc.compl
  fun_prop

theorem lintegral_lowAtomMajorant_le (B : ℕ) (b : ℝ → ℂ) (z R : ℝ) (hR : 0 < R) :
    (∫⁻ x, lowAtomMajorant B b z R x) ≤
      ENNReal.ofReal (4 * (B + 1 : ℝ) * lowKernelBadAtomConstant) *
        ENNReal.ofReal (∫ y, ‖b y‖) := by
  have hC := lowKernelBadAtomConstant_nonneg
  have hlen : 0 < 3 * R / 2 := by positivity
  have hD : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * B) := one_le_pow₀ (by norm_num)
  have hi := integrableOn_lowDecayMajorant_compl
    ((2 : ℝ) ^ (2 * B)) (3 * R / 2) z hD hlen
  have hn : ∀ x, 0 ≤ lowDecayMajorant ((2 : ℝ) ^ (2 * B)) (3 * R / 2) z x := by
    intro x
    unfold lowDecayMajorant
    positivity
  unfold lowAtomMajorant
  rw [lintegral_indicator (show MeasurableSet (tripleCenteredInterval z R)ᶜ from
    measurableSet_Icc.compl), lintegral_const_mul' _ _ (by finiteness)]
  have hdec : (∫⁻ x in (tripleCenteredInterval z R)ᶜ,
      ENNReal.ofReal (lowDecayMajorant ((2 : ℝ) ^ (2 * B)) (3 * R / 2) z x)) ≤
      ENNReal.ofReal (4 * (B + 1 : ℝ)) := by
    unfold tripleCenteredInterval
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)]
    exact ENNReal.ofReal_le_ofReal (integral_lowDecayMajorant_two_pow_le B (3 * R / 2) z hlen)
  apply (mul_le_mul' le_rfl hdec).trans_eq
  rw [← ENNReal.ofReal_mul (mul_nonneg lowKernelBadAtomConstant_nonneg
    (integral_nonneg fun _ ↦ norm_nonneg _)),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * (B + 1 : ℝ) * lowKernelBadAtomConstant)]
  congr 1
  ring

theorem paperLowBadAtomMaximal_levelAtom_le_majorant
    (B : ℕ) {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k) {z R x : ℝ} (hR : 0 < R)
    (hx : x ∉ tripleCenteredInterval z R) :
    paperLowBadAtomMaximal B (levelAtom A f k z R) z R x ≤
      lowAtomMajorant B (levelAtom A f k z R) z R x := by
  have hp := paperLowBadAtomMaximal_le_lowDecayMajorant B (levelAtom A f k z R)
    hR hx (integrable_levelAtom hf hAk z R).integrableOn
    (fun lam ↦ integrableOn_paperLowCZKernel_mul_levelAtom lam.2 B hf hAk hR hx)
    (setIntegral_levelAtom_eq_zero k z R)
  rw [setIntegral_norm_levelAtom_eq_integral k z R] at hp
  rw [lowAtomMajorant, indicator_of_mem hx,
    ← ENNReal.ofReal_mul (mul_nonneg lowKernelBadAtomConstant_nonneg
      (integral_nonneg fun _ ↦ norm_nonneg _))]
  apply hp.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (lowDecayMajorant_mono_length (by positivity) (by linarith : R ≤ 3 * R / 2))
    (mul_nonneg lowKernelBadAtomConstant_nonneg (integral_nonneg fun _ ↦ norm_nonneg _))

/-- The sum of low-frequency atom majorants at a fixed magnitude level. -/
noncomputable def lowLevelMajorant {ι : Type*} (B : ℕ) (A : ℕ → ℝ) (f : ℝ → ℂ)
    (k : ℕ) (z R : ι → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑' i, lowAtomMajorant B (levelAtom A f k (z i) (R i)) (z i) (R i) x

theorem measurable_lowLevelMajorant {ι : Type*} [Countable ι]
    (B : ℕ) (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (z R : ι → ℝ) :
    Measurable (lowLevelMajorant B A f k z R) :=
  Measurable.tsum (fun i ↦ measurable_lowAtomMajorant B _ (z i) (R i))

theorem lintegral_lowLevelMajorant_le {ι : Type*} [Countable ι]
    (B : ℕ) {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k) (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∫⁻ x, lowLevelMajorant B A f k z R x) ≤
      ENNReal.ofReal (8 * (B + 1 : ℝ) * lowKernelBadAtomConstant) *
        magnitudeLevelL1Mass volume A f k := by
  have hC := lowKernelBadAtomConstant_nonneg
  unfold lowLevelMajorant
  rw [lintegral_tsum (fun i ↦ (measurable_lowAtomMajorant B _ (z i) (R i)).aemeasurable)]
  have hs := ENNReal.tsum_le_tsum
    (fun i ↦ lintegral_lowAtomMajorant_le B (levelAtom A f k (z i) (R i)) (z i) (R i) (hR i))
  rw [ENNReal.tsum_mul_left] at hs
  apply hs.trans
  apply (mul_le_mul' le_rfl
    (tsum_atomL1Mass_le_two_mul_global_level_mass hf hAk z R hdisj)).trans_eq
  rw [← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * (B + 1 : ℝ) * lowKernelBadAtomConstant)]
  congr 1
  ring

/-- The sum of the low-frequency level majorants with the full endpoint cutoffs. -/
noncomputable def fullLowMajorant {ι : Type*} (f : ℝ → ℂ) (z R : ι → ℝ)
    (x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, lowLevelMajorant (fullHighCutoff k) fullAmplitude f k z R x

theorem measurable_fullLowMajorant {ι : Type*} [Countable ι]
    (f : ℝ → ℂ) (z R : ι → ℝ) : Measurable (fullLowMajorant f z R) :=
  Measurable.tsum (fun k ↦ measurable_lowLevelMajorant (fullHighCutoff k) _ _ k z R)

/-- The explicit constant for the full low-frequency endpoint estimate. -/
noncomputable def fullLowEndpointConstant : ℝ≥0∞ :=
  ENNReal.ofReal (1280 * lowKernelBadAtomConstant)

theorem fullLowEndpointConstant_lt_top : fullLowEndpointConstant < ∞ := by
  exact ENNReal.ofReal_lt_top

theorem lintegral_fullLowMajorant_le_orlicz {ι : Type*} [Countable ι]
    {f : ℝ → ℂ} (hf : Measurable f) (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∫⁻ x, fullLowMajorant f z R x) ≤ fullLowEndpointConstant *
      ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  have hC := lowKernelBadAtomConstant_nonneg
  unfold fullLowMajorant
  rw [lintegral_tsum (fun k ↦
    (measurable_lowLevelMajorant (fullHighCutoff k) _ _ k z R).aemeasurable)]
  have hp (k : ℕ) : (∫⁻ x, lowLevelMajorant (fullHighCutoff k) fullAmplitude f k z R x) ≤
      ENNReal.ofReal (16 * lowKernelBadAtomConstant) *
        (ENNReal.ofReal (fullCutoff 20 k) * magnitudeLevelL1Mass volume fullAmplitude f k) := by
    apply (lintegral_lowLevelMajorant_le (fullHighCutoff k) hf
      (fullAmplitude_pos k).le z R hR hdisj).trans
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * lowKernelBadAtomConstant)]
    apply mul_le_mul' ?_ le_rfl
    apply ENNReal.ofReal_le_ofReal
    rw [← cast_fullHighCutoff]
    have hB : (1 : ℝ) ≤ fullHighCutoff k := by exact_mod_cast fullHighCutoff_pos k
    nlinarith [lowKernelBadAtomConstant_nonneg]
  have hs := ENNReal.tsum_le_tsum hp
  rw [ENNReal.tsum_mul_left] at hs
  have hw := tsum_full_weight_mul_levelMass_le_orlicz volume (C := 20) (by norm_num) hf
  norm_num only [show (4 : ℝ) * 20 = 80 by norm_num] at hw
  simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 80)] at hw
  rw [lintegral_const_mul' _ _ (by finiteness)] at hw
  apply hs.trans
  apply (mul_le_mul' le_rfl hw).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * lowKernelBadAtomConstant)]
  congr 1
  unfold fullLowEndpointConstant
  congr 1
  ring

end PositiveLowFullEstimate
end QuadraticCarleson
