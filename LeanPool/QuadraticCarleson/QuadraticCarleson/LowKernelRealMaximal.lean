/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LowKernelLevelSummation

/-!
# The genuine real-modulation supremum for a low-kernel bad atom

The pointwise estimate in `LowKernelBadAtomSharp` has a right-hand side that
is independent of the nonzero real modulation parameter. Consequently it
controls the supremum over *all* such parameters directly. This file takes
that supremum in `ℝ≥0∞`, where its outer integral is meaningful without first
having to prove measurability of an uncountable supremum.

This is the form needed in the low-oscillation part of the positive endpoint
proof. In particular, it does not replace the real supremum by a countable
or rational one.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators Function

namespace QuadraticCarleson


noncomputable
section

/-- The low-kernel output of one atom, maximized over every nonzero real
quadratic modulation parameter. -/
def paperLowBadAtomMaximal (B : ℕ) (f : ℝ → ℂ) (z R x : ℝ) : ℝ≥0∞ :=
  ⨆ lam : {lam : ℝ // lam ≠ 0},
    ENNReal.ofReal ‖∫ y in centeredInterval z R,
      paperLowCZKernel lam.1 lam.2 B x y * f y‖

/-- The sharp bad-atom majorant controls the genuine supremum over all
nonzero real modulations pointwise off the triple interval. -/
theorem paperLowBadAtomMaximal_le_lowDecayMajorant
    (B : ℕ) (f : ℝ → ℂ) {z R x : ℝ}
    (hR : 0 < R)
    (hx : x ∉ tripleCenteredInterval z R)
    (hf : IntegrableOn f (centeredInterval z R))
    (hKf : ∀ lam : {lam : ℝ // lam ≠ 0},
      IntegrableOn
        (fun y ↦ paperLowCZKernel lam.1 lam.2 B x y * f y)
        (centeredInterval z R))
    (hmean : ∫ y in centeredInterval z R, f y = 0) :
    paperLowBadAtomMaximal B f z R x ≤
      ENNReal.ofReal
        (lowKernelBadAtomConstant *
          (∫ y in centeredInterval z R, ‖f y‖) *
          lowDecayMajorant ((2 : ℝ) ^ (2 * B)) R z x) := by
  apply iSup_le
  intro lam
  exact ENNReal.ofReal_le_ofReal
    (norm_setIntegral_paperLowCZKernel_le_lowDecayMajorant
      lam.2 B f hR hx hf (hKf lam) hmean)

/-- Integrated `O(B + 1)` bound for the genuine real-modulation supremum of
one cancellative bad atom. No measurability assumption on the supremum is
needed: the Lebesgue outer integral is bounded by the common measurable
majorant. -/
theorem lintegral_paperLowBadAtomMaximal_le_sharp
    (B : ℕ) (f : ℝ → ℂ) (z R : ℝ)
    (hR : 0 < R)
    (hf : IntegrableOn f (centeredInterval z R))
    (hmean : ∫ y in centeredInterval z R, f y = 0)
    (hKf : ∀ (lam : {lam : ℝ // lam ≠ 0})
        (x : ℝ), x ∉ tripleCenteredInterval z R →
      IntegrableOn
        (fun y ↦ paperLowCZKernel lam.1 lam.2 B x y * f y)
        (centeredInterval z R)) :
    (∫⁻ x in (tripleCenteredInterval z R)ᶜ,
        paperLowBadAtomMaximal B f z R x) ≤
      ENNReal.ofReal
        (4 * (B + 1 : ℝ) *
          (lowKernelBadAtomConstant *
            ∫ y in centeredInterval z R, ‖f y‖)) := by
  let A : ℝ := ∫ y in centeredInterval z R, ‖f y‖
  let C : ℝ := lowKernelBadAtomConstant * A
  let ell : ℝ := 3 * R / 2
  have hA : 0 ≤ A := integral_nonneg fun _ ↦ norm_nonneg _
  have hC : 0 ≤ C := mul_nonneg lowKernelBadAtomConstant_nonneg hA
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hD : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * B) := one_le_pow₀ (by norm_num)
  have hlowNonneg : ∀ x : ℝ,
      0 ≤ lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ell z x := by
    intro x
    unfold lowDecayMajorant
    apply le_min
    · exact one_div_nonneg.mpr (abs_nonneg _)
    · exact div_nonneg (mul_nonneg (by positivity) hell.le) (sq_nonneg _)
  have hdecay : IntegrableOn
      (fun x ↦ lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ell z x)
      (tripleCenteredInterval z R)ᶜ := by
    simpa only [ell, tripleCenteredInterval] using
      integrableOn_lowDecayMajorant_compl
        ((2 : ℝ) ^ (2 * B)) ell z hD hell
  have hmajorantInt : IntegrableOn
      (fun x ↦ C * lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ell z x)
      (tripleCenteredInterval z R)ᶜ := hdecay.const_mul C
  have hmajorantNonneg : ∀ᵐ x ∂volume.restrict
      (tripleCenteredInterval z R)ᶜ,
      0 ≤ C * lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ell z x := by
    filter_upwards with x
    exact mul_nonneg hC (hlowNonneg x)
  calc
    (∫⁻ x in (tripleCenteredInterval z R)ᶜ,
        paperLowBadAtomMaximal B f z R x) ≤
        ∫⁻ x in (tripleCenteredInterval z R)ᶜ,
          ENNReal.ofReal
            (C * lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ell z x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
      have hpoint := paperLowBadAtomMaximal_le_lowDecayMajorant
        B f hR (by simpa only [mem_compl_iff] using hx) hf
        (fun lam ↦ hKf lam x (by simpa only [mem_compl_iff] using hx)) hmean
      have hmono : lowDecayMajorant ((2 : ℝ) ^ (2 * B)) R z x ≤
          lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ell z x :=
        lowDecayMajorant_mono_length (by positivity) (by dsimp [ell]; linarith)
      exact hpoint.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hmono hC))
    _ = ENNReal.ofReal
        (∫ x in (tripleCenteredInterval z R)ᶜ,
          C * lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ell z x) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal
        hmajorantInt hmajorantNonneg
    _ ≤ ENNReal.ofReal (4 * (B + 1 : ℝ) * C) := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [ell, tripleCenteredInterval] using
        integral_le_four_mul_succ_of_le_lowDecayMajorant
          (fun x ↦ C * lowDecayMajorant ((2 : ℝ) ^ (2 * B)) ell z x)
          C ell z B hC hell
          hmajorantInt.1
          (fun x _ ↦ mul_nonneg hC (hlowNonneg x))
          (fun _ _ ↦ le_rfl)
    _ = ENNReal.ofReal
        (4 * (B + 1 : ℝ) *
          (lowKernelBadAtomConstant *
            ∫ y in centeredInterval z R, ‖f y‖)) := by
      rfl

/-! ## Countable Calderón--Zygmund level families -/

open CalderonZygmundLevelAtoms
open PositiveEndpointOptimization PositiveLevelIntegration

/-- The genuine real-modulation maximal estimate for one magnitude-level
atom, with its mass written as a global `L¹` mass. -/
theorem lintegral_paperLowBadAtomMaximal_levelAtom_le
    (B : ℕ) {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k) (z R : ℝ) (hR : 0 < R) :
    (∫⁻ x in (tripleCenteredInterval z R)ᶜ,
        paperLowBadAtomMaximal B (levelAtom A f k z R) z R x) ≤
      ENNReal.ofReal
          (4 * (B + 1 : ℝ) * lowKernelBadAtomConstant) *
        ENNReal.ofReal (∫ y, ‖levelAtom A f k z R y‖) := by
  have hatom := integrable_levelAtom hf hAk z R
  have hmain := lintegral_paperLowBadAtomMaximal_le_sharp
    B (levelAtom A f k z R) z R hR hatom.integrableOn
    (LowKernelLevelSummation.setIntegral_levelAtom_eq_zero k z R)
    (fun lam x hx ↦
      LowKernelLevelSummation.integrableOn_paperLowCZKernel_mul_levelAtom
        lam.2 B hf hAk hR hx)
  rw [LowKernelLevelSummation.setIntegral_norm_levelAtom_eq_integral k z R] at hmain
  calc
    (∫⁻ x in (tripleCenteredInterval z R)ᶜ,
        paperLowBadAtomMaximal B (levelAtom A f k z R) z R x) ≤
      ENNReal.ofReal
        (4 * (B + 1 : ℝ) *
          (lowKernelBadAtomConstant *
            ∫ y, ‖levelAtom A f k z R y‖)) := hmain
    _ = ENNReal.ofReal
          (4 * (B + 1 : ℝ) * lowKernelBadAtomConstant) *
        ENNReal.ofReal (∫ y, ‖levelAtom A f k z R y‖) := by
      have hcoef : 0 ≤ 4 * (B + 1 : ℝ) * lowKernelBadAtomConstant :=
        mul_nonneg (mul_nonneg (by norm_num) (by positivity))
          lowKernelBadAtomConstant_nonneg
      rw [← ENNReal.ofReal_mul hcoef]
      congr 1
      ring

/-- Summing over a countable disjoint family gives the exact levelwise
`O(B + 1)` estimate for the genuine real-modulation suprema. -/
theorem tsum_lintegral_paperLowBadAtomMaximal_levelAtom_le
    {ι : Type*} [Countable ι]
    (B : ℕ) {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∑' i : ι,
      ∫⁻ x in (tripleCenteredInterval (z i) (R i))ᶜ,
        paperLowBadAtomMaximal B
          (levelAtom A f k (z i) (R i)) (z i) (R i) x) ≤
      ENNReal.ofReal
          (8 * (B + 1 : ℝ) * lowKernelBadAtomConstant) *
        ∫⁻ x in magnitudeLevelSet A f k, ENNReal.ofReal ‖f x‖ := by
  let C : ℝ := 4 * (B + 1 : ℝ) * lowKernelBadAtomConstant
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      lowKernelBadAtomConstant_nonneg
  calc
    (∑' i : ι,
      ∫⁻ x in (tripleCenteredInterval (z i) (R i))ᶜ,
        paperLowBadAtomMaximal B
          (levelAtom A f k (z i) (R i)) (z i) (R i) x) ≤
        ∑' i : ι, ENNReal.ofReal C *
          ENNReal.ofReal (∫ y, ‖levelAtom A f k (z i) (R i) y‖) := by
      apply ENNReal.tsum_le_tsum
      intro i
      simpa only [C] using
        lintegral_paperLowBadAtomMaximal_levelAtom_le
          B hf hAk (z i) (R i) (hR i)
    _ = ENNReal.ofReal C *
        ∑' i : ι, ENNReal.ofReal
          (∫ y, ‖levelAtom A f k (z i) (R i) y‖) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal C *
        (2 * ∫⁻ x in magnitudeLevelSet A f k,
          ENNReal.ofReal ‖f x‖) := by
      gcongr
      exact tsum_atomL1Mass_le_two_mul_global_level_mass hf hAk z R hdisj
    _ = ENNReal.ofReal
          (8 * (B + 1 : ℝ) * lowKernelBadAtomConstant) *
        ∫⁻ x in magnitudeLevelSet A f k, ENNReal.ofReal ‖f x‖ := by
      let G := ∫⁻ x in magnitudeLevelSet A f k, ENNReal.ofReal ‖f x‖
      have hcoef : ENNReal.ofReal C * (2 : ℝ≥0∞) =
          ENNReal.ofReal
            (8 * (B + 1 : ℝ) * lowKernelBadAtomConstant) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul hC]
        congr 1
        dsimp [C]
        ring
      change ENNReal.ofReal C * (2 * G) = _ * G
      rw [← mul_assoc, hcoef]

theorem tsum_lintegral_paperLowBadAtomMaximal_fullLevelAtom_le
    {ι : Type*} [Countable ι]
    (B : ℕ) {f : ℝ → ℂ} (hf : Measurable f) (k : ℕ)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∑' i : ι,
      ∫⁻ x in (tripleCenteredInterval (z i) (R i))ᶜ,
        paperLowBadAtomMaximal B
          (fullLevelAtom f k (z i) (R i)) (z i) (R i) x) ≤
      ENNReal.ofReal
          (8 * (B + 1 : ℝ) * lowKernelBadAtomConstant) *
        ∫⁻ x in fullMagnitudeLevelSet f k, ENNReal.ofReal ‖f x‖ := by
  simpa [fullMagnitudeLevelSet] using
    tsum_lintegral_paperLowBadAtomMaximal_levelAtom_le
      B hf (fullAmplitude_pos k).le z R hR hdisj

theorem tsum_lintegral_paperLowBadAtomMaximal_lacunaryLevelAtom_le
    {ι : Type*} [Countable ι]
    (B : ℕ) {f : ℝ → ℂ} (hf : Measurable f) (k : ℕ)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∑' i : ι,
      ∫⁻ x in (tripleCenteredInterval (z i) (R i))ᶜ,
        paperLowBadAtomMaximal B
          (lacunaryLevelAtom f k (z i) (R i)) (z i) (R i) x) ≤
      ENNReal.ofReal
          (8 * (B + 1 : ℝ) * lowKernelBadAtomConstant) *
        ∫⁻ x in lacunaryMagnitudeLevelSet f k, ENNReal.ofReal ‖f x‖ := by
  simpa [lacunaryMagnitudeLevelSet] using
    tsum_lintegral_paperLowBadAtomMaximal_levelAtom_le
      B hf (lacunaryAmplitude_pos k).le z R hR hdisj

end

end QuadraticCarleson
