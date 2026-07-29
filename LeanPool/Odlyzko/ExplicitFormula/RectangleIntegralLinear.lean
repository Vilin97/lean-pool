/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.FromPrimeNumberTheoremAnd.RectangleIntegral

/-!
# Rectangle Integral Linear

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex intervalIntegral MeasureTheory Real Set

namespace NumberField.Odlyzko

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
theorem rectangleBorderIntegrable_of_continuousAt_boundary
    {f : ℂ → E} {a b u v : ℝ} (hab : a ≤ b) (huv : u ≤ v)
    (hf : ∀ z ∈ Icc a b ×ℂ Icc u v,
      (z.re = a ∨ z.re = b ∨ z.im = u ∨ z.im = v) →
        ContinuousAt f z) :
    RectangleBorderIntegrable f (a + u * I) (b + v * I) := by
  simp only [RectangleBorderIntegrable, add_re, ofReal_re, mul_re,
    I_re, mul_zero, sub_self, add_zero, add_im, ofReal_im,
    mul_im, I_im, mul_one, zero_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hab] at hx
    apply ContinuousAt.continuousWithinAt
    have hout := hf (x + u * I) (by
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re,
          mul_zero, sub_self, add_zero, add_im, ofReal_im, mul_im,
          I_im, mul_one, zero_add]
        simp_all) (by simp)
    have hin : ContinuousAt (fun q : ℝ ↦ (q : ℂ) + u * I) x := by fun_prop
    simpa only [ContinuousAt, Function.comp_def] using
      Filter.Tendsto.comp hout hin
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hab] at hx
    apply ContinuousAt.continuousWithinAt
    have hout := hf (x + v * I) (by
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re,
          mul_zero, sub_self, add_zero, add_im, ofReal_im, mul_im,
          I_im, mul_one, zero_add]
        simp_all) (by simp)
    have hin : ContinuousAt (fun q : ℝ ↦ (q : ℂ) + v * I) x := by fun_prop
    simpa only [ContinuousAt, Function.comp_def] using
      Filter.Tendsto.comp hout hin
  · apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le huv] at hy
    apply ContinuousAt.continuousWithinAt
    have hout := hf (b + y * I) (by
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re,
          mul_zero, sub_self, add_zero, add_im, ofReal_im, mul_im,
          I_im, mul_one, zero_add]
        simp_all) (by simp)
    have hin : ContinuousAt (fun q : ℝ ↦ (b : ℂ) + q * I) y := by fun_prop
    simpa only [ContinuousAt, Function.comp_def] using
      Filter.Tendsto.comp hout hin
  · apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le huv] at hy
    apply ContinuousAt.continuousWithinAt
    have hout := hf (a + y * I) (by
        simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re,
          mul_zero, sub_self, add_zero, add_im, ofReal_im, mul_im,
          I_im, mul_one, zero_add]
        simp_all) (by simp)
    have hin : ContinuousAt (fun q : ℝ ↦ (a : ℂ) + q * I) y := by fun_prop
    simpa only [ContinuousAt, Function.comp_def] using
      Filter.Tendsto.comp hout hin

theorem rectangleIntegral_sub
    {f g : ℂ → E} {z w : ℂ}
    (hf : RectangleBorderIntegrable f z w)
    (hg : RectangleBorderIntegrable g z w) :
    rectangleIntegral (fun s ↦ f s - g s) z w =
      rectangleIntegral f z w - rectangleIntegral g z w := by
  rcases hf with ⟨hf₁, hf₂, hf₃, hf₄⟩
  rcases hg with ⟨hg₁, hg₂, hg₃, hg₄⟩
  unfold rectangleIntegral horizontalIntegral verticalSegmentIntegral
  rw [integral_sub hf₁ hg₁, integral_sub hf₂ hg₂,
    integral_sub hf₃ hg₃, integral_sub hf₄ hg₄]
  simp only [smul_sub]
  grind

end NumberField.Odlyzko
