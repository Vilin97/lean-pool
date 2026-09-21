/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.Fourier.ExponentialAbs
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Fourier.HaagerupZsido.Defs
public import LeanPool.DavisKahan.ForTauCeti.Analysis.SpecialFunctions.Integral.RationalQuadratic
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Fourier.HaagerupZsido.Integrability

/-!
# The Haagerup--Zsidó kernel: the exterior Fourier identity

This file computes the oscillatory sine transform and proves the final exterior
Fourier identity: the reciprocal kernel represents `1 / x` on the whole exterior
region `1 ≤ |x|`.

This is a topic split of `ForTauCeti/Analysis/Fourier/HaagerupZsidoKernel.lean`;
declarations are moved verbatim and remain in the `TauCeti.HaagerupZsido`
namespace.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti` at Davis--Kahan
  commit `f35ffc0`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti
namespace HaagerupZsido

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators FourierTransform

noncomputable section

/-- The oscillatory sine transform against a symmetric exponential, from the
two-sided Laplace transform at the shifted frequencies `x ± 1`. -/
private theorem integral_sin_mul_cexp_neg_mul_abs_mul_cexp
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ,
        ((Real.sin t : ℝ) : ℂ) * Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
          Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
      Complex.I *
        (((y / (y ^ 2 + (x - 1) ^ 2) : ℝ) : ℂ) -
          ((y / (y ^ 2 + (x + 1) ^ 2) : ℝ) : ℂ)) := by
  have hplus := integral_cexp_neg_mul_abs_mul_cexp (x + 1) hy
  have hminus := integral_cexp_neg_mul_abs_mul_cexp (x - 1) hy
  have hintp := integrable_cexp_neg_mul_abs_mul_cexp (x + 1) hy
  have hintm := integrable_cexp_neg_mul_abs_mul_cexp (x - 1) hy
  have hexpsin (t : ℝ) :
      Complex.exp ((t : ℂ) * Complex.I) -
        Complex.exp (-(t : ℂ) * Complex.I) =
      2 * Complex.sin t * Complex.I := by
    rw [Complex.exp_mul_I,
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      show -(t : ℂ) * Complex.I = (-(t : ℂ)) * Complex.I by ring,
      Complex.exp_mul_I, Complex.sin_neg, Complex.cos_neg]
    ring
  have hsin (t : ℝ) : ((Real.sin t : ℝ) : ℂ) =
      (Complex.exp ((t : ℂ) * Complex.I) -
        Complex.exp (-(t : ℂ) * Complex.I)) / (2 * Complex.I) := by
    rw [Complex.ofReal_sin, hexpsin,
      eq_div_iff (by simp [Complex.I_ne_zero] : (2 : ℂ) * Complex.I ≠ 0)]
    ring
  have hphase1 (t : ℝ) : Complex.exp ((t : ℂ) * Complex.I) *
      Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) =
      Complex.exp ((((t * (x + 1) : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase2 (t : ℝ) : Complex.exp (-(t : ℂ) * Complex.I) *
      Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) =
      Complex.exp ((((t * (x - 1) : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpoint (t : ℝ) :
      ((Real.sin t : ℝ) : ℂ) * Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
          Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) =
        (1 / (2 * Complex.I)) *
          (Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
              Complex.exp ((((t * (x + 1) : ℝ) : ℂ) * Complex.I)) -
            Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
              Complex.exp ((((t * (x - 1) : ℝ) : ℂ) * Complex.I))) := by
    rw [← hphase1, ← hphase2, hsin]
    ring
  calc
    (∫ t : ℝ,
        ((Real.sin t : ℝ) : ℂ) * Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
          Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
        ∫ t : ℝ, (1 / (2 * Complex.I)) *
          (Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
              Complex.exp ((((t * (x + 1) : ℝ) : ℂ) * Complex.I)) -
            Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
              Complex.exp ((((t * (x - 1) : ℝ) : ℂ) * Complex.I))) := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact hpoint t
    _ = (1 / (2 * Complex.I)) *
        (((2 * (y : ℝ) / ((y : ℝ) ^ 2 + (x + 1) ^ 2) : ℝ) : ℂ) -
          ((2 * (y : ℝ) / ((y : ℝ) ^ 2 + (x - 1) ^ 2) : ℝ) : ℂ)) := by
      rw [integral_const_mul, integral_sub hintp hintm, hplus, hminus]
    _ = Complex.I *
        (((y / (y ^ 2 + (x - 1) ^ 2) : ℝ) : ℂ) -
          ((y / (y ^ 2 + (x + 1) ^ 2) : ℝ) : ℂ)) := by
      push_cast
      field_simp
      rw [Complex.I_sq]
      ring

/-- The unnormalized Fourier transform of the real kernel at exterior positive
frequencies.  The kernel unfolds to a double integral; the proved mass
certificate justifies Fubini, the oscillatory sine transform evaluates the
inner integral, and the telescoping integral collapses the outer one. -/
private theorem realKernel_fourier_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    (∫ t : ℝ, ((realKernel t : ℝ) : ℂ) *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
      Complex.I * ((1 / x : ℝ) : ℂ) := by
  let G : ℝ → ℝ → ℂ := fun y t =>
    (((Real.sin t / 2 : ℝ) : ℂ) *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) *
      ((weight y * Real.exp (-y * |t|) : ℝ) : ℂ)
  have hGcont : Continuous (Function.uncurry G) := by
    apply Continuous.mul
    · apply Continuous.mul
      · exact Complex.continuous_ofReal.comp
          ((Real.continuous_sin.comp continuous_snd).div_const 2)
      · exact Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp
            (continuous_snd.mul continuous_const)).mul continuous_const)
    · exact Complex.continuous_ofReal.comp
        ((continuous_weight.comp continuous_fst).mul
          (Real.continuous_exp.comp (continuous_fst.neg.mul continuous_snd.abs)))
  have hG : Integrable (Function.uncurry G)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    apply integrable_kernel_prod.mono hGcont.aestronglyMeasurable
    filter_upwards [] with p
    rcases p with ⟨y, t⟩
    simp only [Function.uncurry_apply_pair, G]
    simp only [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_eq_abs, abs_abs, abs_div, abs_two, abs_of_pos (Real.exp_pos _)]
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (weight y))
      (abs_nonneg (Real.sin t))) (Real.exp_pos (-y * |t|)).le]
  have hunfold (t : ℝ) :
      ((realKernel t : ℝ) : ℂ) *
          Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) =
        ∫ y in Set.Ioi (0 : ℝ), G y t := by
    calc
      ((realKernel t : ℝ) : ℂ) *
          Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) =
          (((Real.sin t / 2 : ℝ) : ℂ) *
              Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) *
            ((weightLaplaceTransform t : ℝ) : ℂ) := by
        rw [realKernel_def]
        push_cast
        ring
      _ = (((Real.sin t / 2 : ℝ) : ℂ) *
              Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) *
            ∫ y in Set.Ioi (0 : ℝ),
              ((weight y * Real.exp (-y * |t|) : ℝ) : ℂ) := by
        congr 1
        rw [weightLaplaceTransform_def, ← integral_complex_ofReal]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y _
        dsimp only
        rw [show -|t| * y = -y * |t| by ring]
      _ = ∫ y in Set.Ioi (0 : ℝ), G y t := (integral_const_mul _ _).symm
  have hswap := integral_integral_swap hG
  have hslice {y : ℝ} (hy : 0 < y) :
      (∫ t : ℝ, G y t) =
        ((weight y / 2 : ℝ) : ℂ) *
          (Complex.I *
            (((y / (y ^ 2 + (x - 1) ^ 2) : ℝ) : ℂ) -
              ((y / (y ^ 2 + (x + 1) ^ 2) : ℝ) : ℂ))) := by
    calc
      (∫ t : ℝ, G y t) =
          ∫ t : ℝ, ((weight y / 2 : ℝ) : ℂ) *
            (((Real.sin t : ℝ) : ℂ) * Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
              Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) := by
        apply integral_congr_ae
        filter_upwards [] with t
        simp only [G]
        rw [← Complex.ofReal_exp, show (-(y * |t|) : ℝ) = -y * |t| by ring]
        push_cast
        ring
      _ = ((weight y / 2 : ℝ) : ℂ) *
          ∫ t : ℝ, ((Real.sin t : ℝ) : ℂ) *
            Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
            Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) :=
        integral_const_mul _ _
      _ = ((weight y / 2 : ℝ) : ℂ) *
          (Complex.I *
            (((y / (y ^ 2 + (x - 1) ^ 2) : ℝ) : ℂ) -
              ((y / (y ^ 2 + (x + 1) ^ 2) : ℝ) : ℂ))) := by
        rw [integral_sin_mul_cexp_neg_mul_abs_mul_cexp x hy]
  have ha : (0 : ℝ) ≤ x - 1 := by linarith
  have hx0 : (x : ℂ) ≠ 0 := by
    exact_mod_cast (show (x : ℝ) ≠ 0 by linarith)
  calc
    (∫ t : ℝ, ((realKernel t : ℝ) : ℂ) *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
        ∫ t : ℝ, ∫ y in Set.Ioi (0 : ℝ), G y t := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact hunfold t
    _ = ∫ y in Set.Ioi (0 : ℝ), ∫ t : ℝ, G y t := hswap.symm
    _ = ∫ y in Set.Ioi (0 : ℝ), (Complex.I / 2) *
        ((weight y * y *
          ((y ^ 2 + (x - 1) ^ 2)⁻¹ - (y ^ 2 + (x - 1 + 2) ^ 2)⁻¹) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      have hy0 : (0 : ℝ) < y := hy
      dsimp only
      rw [hslice hy0]
      push_cast
      ring_nf
    _ = (Complex.I / 2) *
        ((∫ y in Set.Ioi (0 : ℝ), weight y * y *
          ((y ^ 2 + (x - 1) ^ 2)⁻¹ - (y ^ 2 + (x - 1 + 2) ^ 2)⁻¹) : ℝ) : ℂ) := by
      rw [integral_const_mul, ← integral_complex_ofReal]
    _ = (Complex.I / 2) * ((2 / (x - 1 + 1) : ℝ) : ℂ) := by
      rw [integral_weight_mul_reciprocal_difference ha]
    _ = Complex.I * ((1 / x : ℝ) : ℂ) := by
      push_cast
      field_simp
      rw [show (x : ℂ) - 1 + 1 = (x : ℂ) by ring]
      exact div_self hx0

/-- The reciprocal Fourier identity at exterior positive frequencies. -/
private theorem reciprocalKernel_fourier_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    (∫ t : ℝ, reciprocalKernel t *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
      1 / (x : ℂ) := by
  calc
    (∫ t : ℝ, reciprocalKernel t *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
        ∫ t : ℝ, -Complex.I * (((realKernel t : ℝ) : ℂ) *
          Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [reciprocalKernel_def]
      ring
    _ = -Complex.I * ∫ t : ℝ, ((realKernel t : ℝ) : ℂ) *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) :=
      integral_const_mul _ _
    _ = -Complex.I * (Complex.I * ((1 / x : ℝ) : ℂ)) := by
      rw [realKernel_fourier_of_one_le hx]
    _ = 1 / (x : ℂ) := by
      rw [show -Complex.I * (Complex.I * ((1 / x : ℝ) : ℂ)) =
        -(Complex.I * Complex.I) * ((1 / x : ℝ) : ℂ) by ring,
        Complex.I_mul_I]
      push_cast
      ring

/-- **Exterior Fourier identity.**  The reciprocal kernel represents `1 / x`
on the whole exterior region `1 ≤ |x|`; negative frequencies follow from the
positive ones by the oddness of the real kernel. -/
theorem reciprocalKernel_fourier (x : ℝ) (hx : 1 ≤ |x|) :
    (∫ t : ℝ, reciprocalKernel t *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
      1 / (x : ℂ) := by
  rcases le_abs.mp hx with h | h
  · exact reciprocalKernel_fourier_of_one_le h
  · have hpos := reciprocalKernel_fourier_of_one_le h
    have hflip :
        (∫ t : ℝ, reciprocalKernel t *
            Complex.exp ((((t * -x : ℝ) : ℂ) * Complex.I))) =
          -∫ t : ℝ, reciprocalKernel t *
            Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) := by
      rw [← integral_neg_eq_self (fun t : ℝ => reciprocalKernel t *
        Complex.exp ((((t * -x : ℝ) : ℂ) * Complex.I))) volume,
        ← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [reciprocalKernel_neg, show (-t * -x : ℝ) = t * x by ring]
      ring
    rw [hpos] at hflip
    have : (∫ t : ℝ, reciprocalKernel t *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
        -(1 / ((-x : ℝ) : ℂ)) := by
      linear_combination hflip
    rw [this]
    push_cast
    rw [div_neg, neg_neg]

end

end HaagerupZsido
end TauCeti
