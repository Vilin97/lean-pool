/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.FromPrimeNumberTheoremAnd.RectangleIntegral

/-!
# Rectangle Symmetry

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex intervalIntegral

namespace NumberField.Odlyzko

theorem verticalSegmentIntegral_one_sub_of_antiInvariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : ∀ z, f (1 - z) = -f z)
    (b T : ℝ) :
    verticalSegmentIntegral f (1 - b) (-T) T =
      -verticalSegmentIntegral f b (-T) T := by
  have hpoint (y : ℝ) :
      f (((1 - b : ℝ) : ℂ) + y * I) =
        -f ((b : ℂ) + (-y) * I) := by
    have harg :
        (((1 - b : ℝ) : ℂ) + y * I) =
          1 - ((b : ℂ) + (-y) * I) := by
      apply Complex.ext <;> simp
    simp_all
  simp only [verticalSegmentIntegral]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_neg]
  have heq :
      (fun x : ℝ ↦ f ((b : ℂ) + -(x : ℂ) * I)) =
        fun x : ℝ ↦ (fun y : ℝ ↦ f ((b : ℂ) + y * I)) (-x) := by simp
  rw [heq]
  have hcomp :
      (∫ x in -T..T, (fun y : ℝ ↦ f ((b : ℂ) + y * I)) (-x)) =
        ∫ x in -T..T, f ((b : ℂ) + x * I) := by
    simpa using
      (intervalIntegral.integral_comp_neg
        (f := fun y : ℝ ↦ f ((b : ℂ) + y * I))
        (a := -T) (b := T))
  simp_all

theorem rectangleIntegral_eq_horizontal_sub_add_two_vertical_of_antiInvariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : ∀ z, f (1 - z) = -f z)
    (b T : ℝ) :
    rectangleIntegral f ((1 - b : ℝ) + (-T) * I) (b + T * I) =
      horizontalIntegral f (1 - b) b (-T) -
        horizontalIntegral f (1 - b) b T +
          (2 : ℂ) • verticalSegmentIntegral f b (-T) T := by
  rw [rectangleIntegral]
  simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im,
    I_re, I_im, neg_re, neg_im, mul_zero, mul_one, zero_add,
    neg_zero, sub_self, add_zero]
  rw [verticalSegmentIntegral_one_sub_of_antiInvariant hf]
  simp only [two_smul]
  grind

theorem mul_antiInvariant_of_invariant_of_antiInvariant
    {h g : ℂ → ℂ}
    (hh : ∀ z, h (1 - z) = h z)
    (hg : ∀ z, g (1 - z) = -g z) :
    ∀ z, h (1 - z) * g (1 - z) = -(h z * g z) := by simp_all

end NumberField.Odlyzko
