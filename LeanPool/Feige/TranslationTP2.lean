/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.ConvolutionLogConcave
import LeanPool.Feige.LikelihoodRatio

/-!
# Translation TP2 and convolution

This file proves the one-dimensional total-positivity statement behind
preservation of log-concavity under convolution.  It is adapted to the
existing `LikelihoodRatio.densityConvolution` definition.
-/

open scoped ENNReal
open MeasureTheory

namespace Feige
namespace LikelihoodRatio

noncomputable section

/-- Total positivity of order two for the translation kernel of `f`. -/
def TranslationTP2 (f : ℝ → ℝ≥0∞) : Prop :=
  ∀ ⦃x₁ x₂ z₁ z₂ : ℝ⦄, x₁ ≤ x₂ → z₁ ≤ z₂ →
    f (x₁ - z₂) * f (x₂ - z₁) ≤
      f (x₁ - z₁) * f (x₂ - z₂)

private lemma ennreal_mul_rearrangement
    {a b c d : ℝ≥0∞} (hba : b ≤ a) (hdc : d ≤ c)
    (ha : a ≠ ∞) (hc : c ≠ ∞) :
    a * d + b * c ≤ a * c + b * d := by
  have hb : b ≠ ∞ := ne_top_of_le_ne_top ha hba
  have hd : d ≠ ∞ := ne_top_of_le_ne_top hc hdc
  have hba' : b.toNNReal ≤ a.toNNReal :=
    ENNReal.toNNReal_mono ha hba
  have hdc' : d.toNNReal ≤ c.toNNReal :=
    ENNReal.toNNReal_mono hc hdc
  rw [← ENNReal.coe_toNNReal ha, ← ENNReal.coe_toNNReal hb,
    ← ENNReal.coe_toNNReal hc, ← ENNReal.coe_toNNReal hd]
  exact_mod_cast mul_add_mul_le_mul_add_mul' hba' hdc'

/-- Composition of two nonnegative translation kernels. -/
def translationKernelComposition
    (f g : ℝ → ℝ≥0∞) (x y : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, f (x - z) * g (z - y)

lemma measurable_translationKernelComposition
    {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p : ℝ × ℝ ↦
      translationKernelComposition f g p.1 p.2 := by
  have hjoint : Measurable fun p : (ℝ × ℝ) × ℝ ↦
      f (p.1.1 - p.2) * g (p.2 - p.1.2) := by
    fun_prop
  simpa only [translationKernelComposition] using
    hjoint.lintegral_prod_right' (ν := volume)

private lemma translationKernelComposition_mul
    {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (x₁ y₁ x₂ y₂ : ℝ) :
    translationKernelComposition f g x₁ y₁ *
        translationKernelComposition f g x₂ y₂ =
      ∫⁻ z₁, ∫⁻ z₂,
        (f (x₁ - z₁) * g (z₁ - y₁)) *
          (f (x₂ - z₂) * g (z₂ - y₂)) := by
  have h₁ : Measurable fun z : ℝ ↦
      f (x₁ - z) * g (z - y₁) := by fun_prop
  have h₂ : Measurable fun z : ℝ ↦
      f (x₂ - z) * g (z - y₂) := by fun_prop
  unfold translationKernelComposition
  calc
    (∫⁻ z, f (x₁ - z) * g (z - y₁)) *
          (∫⁻ z, f (x₂ - z) * g (z - y₂)) =
        ∫⁻ z₁, (f (x₁ - z₁) * g (z₁ - y₁)) *
          (∫⁻ z₂, f (x₂ - z₂) * g (z₂ - y₂)) := by
      rw [lintegral_mul_const]
      exact h₁
    _ = ∫⁻ z₁, ∫⁻ z₂,
        (f (x₁ - z₁) * g (z₁ - y₁)) *
          (f (x₂ - z₂) * g (z₂ - y₂)) := by
      apply lintegral_congr
      intro z₁
      rw [lintegral_const_mul]
      exact h₂

/-- Composition of finite-valued measurable translation-TP2 kernels is
again TP2. -/
theorem TranslationTP2.kernelComposition
    {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfFinite : ∀ x, f x ≠ ∞) (hgFinite : ∀ x, g x ≠ ∞)
    (hfTP2 : TranslationTP2 f) (hgTP2 : TranslationTP2 g) :
    ∀ ⦃x₁ x₂ y₁ y₂ : ℝ⦄, x₁ ≤ x₂ → y₁ ≤ y₂ →
      translationKernelComposition f g x₁ y₂ *
          translationKernelComposition f g x₂ y₁ ≤
        translationKernelComposition f g x₁ y₁ *
          translationKernelComposition f g x₂ y₂ := by
  intro x₁ x₂ y₁ y₂ hx hy
  let L : ℝ → ℝ → ℝ≥0∞ := fun z₁ z₂ ↦
    (f (x₁ - z₁) * g (z₁ - y₁)) *
      (f (x₂ - z₂) * g (z₂ - y₂))
  let R : ℝ → ℝ → ℝ≥0∞ := fun z₁ z₂ ↦
    (f (x₁ - z₁) * g (z₁ - y₂)) *
      (f (x₂ - z₂) * g (z₂ - y₁))
  have hLmeas : Measurable (Function.uncurry L) := by
    dsimp only [L, Function.uncurry]
    fun_prop
  have hRmeas : Measurable (Function.uncurry R) := by
    dsimp only [R, Function.uncurry]
    fun_prop
  have hpoint : ∀ z₁ z₂, R z₁ z₂ + R z₂ z₁ ≤
      L z₁ z₂ + L z₂ z₁ := by
    intro z₁ z₂
    rcases le_total z₁ z₂ with hz | hz
    · have hF := hfTP2 hx hz
      have hG := hgTP2 hz hy
      have h := ennreal_mul_rearrangement hF hG
        (ENNReal.mul_ne_top (hfFinite _) (hfFinite _))
        (ENNReal.mul_ne_top (hgFinite _) (hgFinite _))
      dsimp only [L, R]
      simpa only [mul_assoc, mul_left_comm, mul_comm,
        add_comm, add_left_comm, add_assoc] using h
    · have hF := hfTP2 hx hz
      have hG := hgTP2 hz hy
      have h := ennreal_mul_rearrangement hF hG
        (ENNReal.mul_ne_top (hfFinite _) (hfFinite _))
        (ENNReal.mul_ne_top (hgFinite _) (hgFinite _))
      dsimp only [L, R]
      simpa only [mul_assoc, mul_left_comm, mul_comm,
        add_comm, add_left_comm, add_assoc] using h
  have hsum :
      (∫⁻ z₁, ∫⁻ z₂, R z₁ z₂) + (∫⁻ z₁, ∫⁻ z₂, R z₂ z₁) ≤
        (∫⁻ z₁, ∫⁻ z₂, L z₁ z₂) + (∫⁻ z₁, ∫⁻ z₂, L z₂ z₁) := by
    calc
      _ = ∫⁻ z₁, (∫⁻ z₂, R z₁ z₂) + (∫⁻ z₂, R z₂ z₁) := by
        rw [lintegral_add_left]
        exact hRmeas.lintegral_prod_right'
      _ = ∫⁻ z₁, ∫⁻ z₂, R z₁ z₂ + R z₂ z₁ := by
        apply lintegral_congr
        intro z₁
        rw [lintegral_add_left]
        dsimp only [R]
        fun_prop
      _ ≤ ∫⁻ z₁, ∫⁻ z₂, L z₁ z₂ + L z₂ z₁ := by
        apply lintegral_mono
        intro z₁
        apply lintegral_mono
        exact hpoint z₁
      _ = ∫⁻ z₁, (∫⁻ z₂, L z₁ z₂) + (∫⁻ z₂, L z₂ z₁) := by
        apply lintegral_congr
        intro z₁
        rw [lintegral_add_left]
        dsimp only [L]
        fun_prop
      _ = _ := by
        rw [lintegral_add_left]
        exact hLmeas.lintegral_prod_right'
  have hRswap : (∫⁻ z₁, ∫⁻ z₂, R z₂ z₁) =
      ∫⁻ z₁, ∫⁻ z₂, R z₁ z₂ :=
    (lintegral_lintegral_swap hRmeas.aemeasurable).symm
  have hLswap : (∫⁻ z₁, ∫⁻ z₂, L z₂ z₁) =
      ∫⁻ z₁, ∫⁻ z₂, L z₁ z₂ :=
    (lintegral_lintegral_swap hLmeas.aemeasurable).symm
  rw [hRswap, hLswap] at hsum
  have htwice :
      (2 : ℝ≥0∞) * (∫⁻ z₁, ∫⁻ z₂, R z₁ z₂) ≤
        (2 : ℝ≥0∞) * ∫⁻ z₁, ∫⁻ z₂, L z₁ z₂ := by
    simpa only [two_mul] using hsum
  have hRL :
      (∫⁻ z₁, ∫⁻ z₂, R z₁ z₂) ≤
        ∫⁻ z₁, ∫⁻ z₂, L z₁ z₂ := by
    calc
      _ = (2 : ℝ≥0∞)⁻¹ *
          (2 * (∫⁻ z₁, ∫⁻ z₂, R z₁ z₂)) := by
        symm
        exact ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)
      _ ≤ (2 : ℝ≥0∞)⁻¹ *
          (2 * (∫⁻ z₁, ∫⁻ z₂, L z₁ z₂)) :=
        mul_le_mul_right htwice _
      _ = _ := ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)
  rw [translationKernelComposition_mul hf hg,
    translationKernelComposition_mul hf hg]
  exact hRL

lemma translationKernelComposition_eq_densityConvolution_sub
    (f g : ℝ → ℝ≥0∞) (x y : ℝ) :
    translationKernelComposition f g x y =
      densityConvolution g f (x - y) := by
  let h : ℝ → ℝ≥0∞ := fun u ↦ f ((x - y) - u) * g u
  have hshift := lintegral_add_right_eq_self (μ := volume) h (-y)
  unfold translationKernelComposition
  calc
    (∫⁻ z, f (x - z) * g (z - y)) =
        ∫⁻ z, h (z + (-y)) := by
      apply lintegral_congr
      intro z
      dsimp only [h]
      congr 2
      ring
    _ = ∫⁻ u, h u := hshift
    _ = densityConvolution g f (x - y) := by
      rw [densityConvolution_apply]
      apply lintegral_congr
      intro u
      dsimp only [h]
      ac_rfl

/-- The current project's density convolution preserves translation TP2. -/
theorem TranslationTP2.convolution
    {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfFinite : ∀ x, f x ≠ ∞) (hgFinite : ∀ x, g x ≠ ∞)
    (hfTP2 : TranslationTP2 f) (hgTP2 : TranslationTP2 g) :
    TranslationTP2 (densityConvolution f g) := by
  intro x₁ x₂ z₁ z₂ hx hz
  rw [← translationKernelComposition_eq_densityConvolution_sub g f,
    ← translationKernelComposition_eq_densityConvolution_sub g f,
    ← translationKernelComposition_eq_densityConvolution_sub g f,
    ← translationKernelComposition_eq_densityConvolution_sub g f]
  exact hgTP2.kernelComposition hg hf hgFinite hfFinite hfTP2 hx hz

/-- Translation TP2 implies the existing general four-point
log-concavity predicate. -/
theorem TranslationTP2.fourPointLogConcave
    {f : ℝ → ℝ≥0∞} (hf : TranslationTP2 f) :
    FourPointLogConcave f := by
  intro r p q s hrp hpq hrs hsq hsum
  have hz : (0 : ℝ) ≤ p - r := sub_nonneg.mpr hrp
  have h := hf (x₁ := p) (x₂ := q)
    (z₁ := 0) (z₂ := p - r) hpq hz
  have hs : q - (p - r) = s := by linarith
  simpa [hs] using h

/-- The existing four-point predicate is equivalent to translation TP2. -/
theorem FourPointLogConcave.translationTP2
    {f : ℝ → ℝ≥0∞} (hf : FourPointLogConcave f) :
    TranslationTP2 f := by
  intro x₁ x₂ z₁ z₂ hx hz
  exact hf
    (r := x₁ - z₂) (p := x₁ - z₁)
    (q := x₂ - z₁) (s := x₂ - z₂)
    (by linarith) (by linarith) (by linarith) (by linarith) (by ring)

end
end LikelihoodRatio
end Feige
