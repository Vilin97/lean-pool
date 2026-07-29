/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.TestFunction.ComplexFourier

/-!
# Poitou Transform

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory

namespace NumberField.Odlyzko

/-- A poitou kernel used in the Odlyzko-bound argument. -/
noncomputable def poitouKernel (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x / Real.cosh (x / 2)

/-- A poitou transform integrand used in the Odlyzko-bound argument. -/
noncomputable def poitouTransformIntegrand
    (f : ℝ → ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  (poitouKernel f x : ℂ) * Complex.exp ((s - 1 / 2) * x)

/-- A poitou transform used in the Odlyzko-bound argument. -/
noncomputable def poitouTransform (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, poitouTransformIntegrand f s x

theorem poitouKernel_neg {f : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x) (x : ℝ) :
    poitouKernel f (-x) = poitouKernel f x := by
  rw [poitouKernel, poitouKernel, hf]
  rw [show -x / 2 = -(x / 2) by ring, Real.cosh_neg]

private theorem poitouTransformIntegrand_one_sub {f : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x) (s : ℂ) (x : ℝ) :
    poitouTransformIntegrand f (1 - s) x =
      poitouTransformIntegrand f s (-x) := by
  rw [poitouTransformIntegrand, poitouTransformIntegrand,
    poitouKernel_neg hf]
  push_cast
  ring_nf

theorem poitouTransform_one_sub {f : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x) (s : ℂ) :
    poitouTransform f (1 - s) = poitouTransform f s := by
  rw [poitouTransform]
  simp_rw [poitouTransformIntegrand_one_sub hf]
  exact integral_neg_eq_self (poitouTransformIntegrand f s) volume

theorem poitouTransform_reflection {f : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x) (s : ℂ) :
    poitouTransform f s = poitouTransform f (1 - s) :=
  (poitouTransform_one_sub hf s).symm

theorem re_poitouTransform_mul_I_eq_cosineTransform
    {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (t : ℝ)
    (hint : Integrable (poitouTransformIntegrand f (t * I))) :
    (poitouTransform f (t * I)).re = Poitou.cosineTransform f t := by
  let A : ℝ → ℝ := fun x ↦ (poitouTransformIntegrand f (t * I) x).re
  have hA : Integrable A := hint.re
  have hAneg : Integrable (fun x ↦ A (-x)) := hA.comp_neg
  have hneg : (∫ x : ℝ, A (-x)) = ∫ x : ℝ, A x :=
    integral_neg_eq_self A volume
  have hpoint (x : ℝ) :
      A x + A (-x) = 2 * (f x * Real.cos (t * x)) := by
    dsimp [A, poitouTransformIntegrand]
    rw [poitouKernel_neg hf]
    norm_num [Complex.exp_re]
    rw [poitouKernel, Real.cosh_eq]
    field_simp
    grind
  rw [poitouTransform]
  change RCLike.re (∫ x : ℝ, poitouTransformIntegrand f (t * I) x) =
    Poitou.cosineTransform f t
  rw [← integral_re hint]
  change (∫ x : ℝ, A x) = Poitou.cosineTransform f t
  have hadd := integral_add hA hAneg
  rw [hneg] at hadd
  have hpointIntegral :
      (∫ x : ℝ, A x + A (-x)) =
        ∫ x : ℝ, 2 * (f x * Real.cos (t * x)) := by simp_all
  rw [hadd] at hpointIntegral
  rw [integral_const_mul] at hpointIntegral
  unfold Poitou.cosineTransform
  linarith

theorem re_poitouTransform_mul_I_nonneg
    {f : ℝ → ℝ} (hf : Poitou.Admissible f) (t : ℝ)
    (hint : Integrable (poitouTransformIntegrand f (t * I))) :
    0 ≤ (poitouTransform f (t * I)).re := by
  rw [re_poitouTransform_mul_I_eq_cosineTransform hf.even t hint]
  exact hf.cosineTransform_nonnegative t

private theorem cosineTransform_neg {f : ℝ → ℝ} (t : ℝ) :
    Poitou.cosineTransform f (-t) = Poitou.cosineTransform f t := by
  unfold Poitou.cosineTransform
  simp

theorem re_poitouTransform_one_add_mul_I_nonneg
    {f : ℝ → ℝ} (hf : Poitou.Admissible f) (t : ℝ)
    (hint : Integrable
      (poitouTransformIntegrand f (((-t : ℝ) : ℂ) * I))) :
    0 ≤ (poitouTransform f (1 + t * I)).re := by
  rw [poitouTransform_reflection hf.even]
  have hreflect : 1 - (1 + (t : ℂ) * I) = ((-t : ℝ) : ℂ) * I := by simp
  rw [hreflect, re_poitouTransform_mul_I_eq_cosineTransform hf.even (-t) hint,
    cosineTransform_neg]
  exact hf.cosineTransform_nonnegative t

theorem poitouTransform_one_eq_integral
    {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x)
    (hint : Integrable (poitouTransformIntegrand f 0)) :
    poitouTransform f 1 = (∫ x : ℝ, f x) := by
  have hreflect := poitouTransform_reflection hf (0 : ℂ)
  simp only [sub_zero] at hreflect
  rw [← hreflect]
  apply Complex.ext
  · have hre :=
      re_poitouTransform_mul_I_eq_cosineTransform hf 0
        (by simpa using hint)
    simpa [Poitou.cosineTransform] using hre
  · rw [poitouTransform]
    change RCLike.im (∫ x : ℝ, poitouTransformIntegrand f 0 x) = 0
    rw [← integral_im hint]
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    simp [poitouTransformIntegrand, Complex.exp_im]

end NumberField.Odlyzko
