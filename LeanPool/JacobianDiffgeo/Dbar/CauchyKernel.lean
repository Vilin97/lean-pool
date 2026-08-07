/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import LeanPool.JacobianDiffgeo.Dbar.Wirtinger

/-!
# The Cauchy kernel, the Cauchy transform, and Cauchy–Pompeiu (Forster 13.1)

Unit: dbar-solvability (`docs/design/dbar-solvability.md` §4.2, §5). Mathlib-only planar file.

`cauchyKernel w := (π w)⁻¹`; `cauchyTransform g := cauchyKernel ⋆[mul ℝ ℂ] g`. The pointwise
identity `dbar(cauchyKernel ⋆ g) = g` for compactly supported `C¹` `g` (`cauchyPompeiu`) is
proved by
polar coordinates + 1-D FTC in the radial and angular directions (design §5): the convolution
derivative package handles "differentiate under the integral", and the polar substitution makes
the kernel singularity cancel exactly.
-/

open MeasureTheory Metric Set Complex
open scoped Convolution ContDiff

noncomputable section

namespace RS

variable (g : ℂ → ℂ)

/-- The Cauchy kernel `1/(π w)`. -/
def cauchyKernel : ℂ → ℂ := fun w => (Real.pi * w)⁻¹

theorem measurable_cauchyKernel : Measurable cauchyKernel :=
  (measurable_id.const_mul _).inv

theorem aestronglyMeasurable_cauchyKernel : AEStronglyMeasurable cauchyKernel volume :=
  measurable_cauchyKernel.aestronglyMeasurable

theorem norm_cauchyKernel (w : ℂ) : ‖cauchyKernel w‖ = (Real.pi * ‖w‖)⁻¹ := by
  simp [cauchyKernel, norm_inv, Real.norm_of_nonneg Real.pi_pos.le]

/-- Step 1 of the design: `cauchyKernel` is integrable on every ball centred at `0`. -/
theorem integrableOn_cauchyKernel_ball (ρ : ℝ) :
    IntegrableOn cauchyKernel (ball (0 : ℂ) ρ) volume := by
  by_cases hρ0 : ρ ≤ 0
  · simp [ball_eq_empty.2 hρ0]
  push Not at hρ0
  have hρ : 0 < ρ := hρ0
  refine ⟨aestronglyMeasurable_cauchyKernel.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hind : (∫⁻ w in ball (0 : ℂ) ρ, ‖cauchyKernel w‖ₑ ∂volume) =
      ∫⁻ w, (ball (0 : ℂ) ρ).indicator (fun w => ‖cauchyKernel w‖ₑ) w ∂volume := by
    rw [lintegral_indicator measurableSet_ball]
  rw [hind, ← Complex.lintegral_comp_polarCoord_symm]
  -- pointwise bound, valid on the whole plane (both sides are `0` off the relevant boxes)
  have hbound : ∀ p : ℝ × ℝ,
      Complex.polarCoord.target.indicator
          (fun p => ENNReal.ofReal p.1 • (ball (0 : ℂ) ρ).indicator (fun w => ‖cauchyKernel w‖ₑ)
              (Complex.polarCoord.symm p)) p ≤
        (Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun _ => ENNReal.ofReal (Real.pi⁻¹)) p := by
    intro p
    by_cases hp : p ∈ Complex.polarCoord.target
    · rw [Set.indicator_of_mem hp]
      obtain ⟨r, θ⟩ := p
      have hr : 0 < r := hp.1
      by_cases hrρ : r < ρ
      · have hmem1 : (r, θ) ∈ Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi := ⟨⟨hr, hrρ⟩, hp.2⟩
        have hnorm : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
          rw [Complex.norm_polarCoord_symm]; exact abs_of_pos hr
        have hmem2 : Complex.polarCoord.symm (r, θ) ∈ ball (0 : ℂ) ρ := by
          rw [mem_ball_zero_iff, hnorm]; exact hrρ
        rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2, ← ofReal_norm,
          norm_cauchyKernel, hnorm, smul_eq_mul, ← ENNReal.ofReal_mul hr.le]
        have heq : r * (Real.pi * r)⁻¹ = Real.pi⁻¹ := by field_simp
        rw [heq]
      · push Not at hrρ
        have hnotmem_ball : Complex.polarCoord.symm (r, θ) ∉ ball (0 : ℂ) ρ := by
          rw [mem_ball_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hr]
          exact not_lt.2 hrρ
        rw [Set.indicator_of_notMem hnotmem_ball, smul_zero]
        exact (bot_le : (0 : ENNReal) ≤ _)
    · rw [Set.indicator_of_notMem hp]
      exact (bot_le : (0 : ENNReal) ≤ _)
  calc ∫⁻ p in Complex.polarCoord.target,
      ENNReal.ofReal p.1 • (ball (0 : ℂ) ρ).indicator (fun w => ‖cauchyKernel w‖ₑ)
          (Complex.polarCoord.symm p)
      = ∫⁻ p, Complex.polarCoord.target.indicator
          (fun p => ENNReal.ofReal p.1 • (ball (0 : ℂ) ρ).indicator (fun w => ‖cauchyKernel w‖ₑ)
              (Complex.polarCoord.symm p)) p :=
        (lintegral_indicator Complex.polarCoord.open_target.measurableSet _).symm
    _ ≤ ∫⁻ p, (Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun _ => ENNReal.ofReal (Real.pi⁻¹)) p := lintegral_mono hbound
    _ = ∫⁻ p in Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (Real.pi⁻¹) :=
        lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo) _
    _ < ⊤ := by
        rw [MeasureTheory.setLIntegral_const,
          show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
          Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

theorem locallyIntegrable_cauchyKernel : LocallyIntegrable cauchyKernel volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_ball (0 : ℂ)
  exact (integrableOn_cauchyKernel_ball ρ).mono_set hρ

/-! ## The Cauchy transform and its derivative (design §5, step 2) -/

/-- The Cauchy transform `cauchyKernel ⋆ g`. -/
noncomputable def cauchyTransform (g : ℂ → ℂ) : ℂ → ℂ :=
  cauchyKernel ⋆[ContinuousLinearMap.mul ℝ ℂ] g

theorem contDiff_cauchyTransform (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g) :
    ContDiff ℝ ∞ (cauchyTransform g) :=
  hcs.contDiff_convolution_right _ locallyIntegrable_cauchyKernel hg

/-- Step 2: differentiation under the integral, via the convolution-derivative package. -/
theorem wirtingerDbar_cauchyTransform (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g) (z : ℂ) :
    wirtingerDbar (cauchyTransform g) z = ∫ w : ℂ, cauchyKernel w * wirtingerDbar g (z - w) := by
  have hg1 : ContDiff ℝ (1 : ℕ∞) g := hg.of_le (by norm_num)
  have hfd : HasFDerivAt (cauchyTransform g)
      ((cauchyKernel ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR ℂ] fderiv ℝ g) z) z :=
    hcs.hasFDerivAt_convolution_right _ locallyIntegrable_cauchyKernel hg1 z
  have hcompv : ∀ v : ℂ,
      (cauchyKernel ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR ℂ] fderiv ℝ g) z v =
        ∫ w, cauchyKernel w * fderiv ℝ g (z - w) v := by
    intro v
    rw [convolution_precompR_apply _ locallyIntegrable_cauchyKernel (hcs.fderiv ℝ)
      (hg1.continuous_fderiv (by norm_num))]
    simp [convolution_def]
  have hInt1 : Integrable (fun w => cauchyKernel w * fderiv ℝ g (z - w) 1) :=
    (hcs.fderiv_apply ℝ (1 : ℂ)).convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
      locallyIntegrable_cauchyKernel
      ((hg1.continuous_fderiv (by norm_num)).clm_apply continuous_const) z
  have hIntI : Integrable (fun w => cauchyKernel w * fderiv ℝ g (z - w) Complex.I) :=
    (hcs.fderiv_apply ℝ Complex.I).convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
      locallyIntegrable_cauchyKernel
      ((hg1.continuous_fderiv (by norm_num)).clm_apply continuous_const) z
  have key : ∀ w, cauchyKernel w * wirtingerDbar g (z - w) =
      (cauchyKernel w * fderiv ℝ g (z - w) 1
        + Complex.I * (cauchyKernel w * fderiv ℝ g (z - w) Complex.I)) / 2 := by
    intro w; simp only [wirtingerDbar]; ring
  rw [wirtingerDbar, hfd.fderiv, hcompv 1, hcompv Complex.I]
  simp_rw [key]
  rw [integral_div, integral_add hInt1 (hIntI.const_mul _), integral_const_mul]

/-! ## Cauchy–Pompeiu (design §5, steps 0, 1, 3–8) -/

/-- `circleMap` computes `Complex.polarCoord.symm`. -/
private theorem polarCoord_symm_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, Complex.ofReal_cos,
    Complex.ofReal_sin]

private theorem hasDerivAt_circleMap_r (c : ℂ) (θ r : ℝ) :
    HasDerivAt (fun r : ℝ => circleMap c r θ) (Complex.exp (θ * Complex.I)) r := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const
    (Complex.exp (θ * Complex.I))).const_add c
  simpa [circleMap] using h

private theorem conj_exp_real_mul_I (x : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((x : ℂ) * Complex.I)) = Complex.exp (-(x : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- Fubini in the reversed order for a rectangle, on `IntegrableOn` (mathlib has no
`setIntegral_prod_symm` at the pin, design §5 fallback (ii)). -/
private theorem setIntegral_prod_symm {f : ℝ × ℝ → ℂ} {s t : Set ℝ}
    (hf : IntegrableOn f (s ×ˢ t) (volume.prod volume)) :
    ∫ x in s, ∫ y in t, f (x, y) ∂volume ∂volume =
      ∫ y in t, ∫ x in s, f (x, y) ∂volume ∂volume := by
  have hf' : Integrable (Function.uncurry (fun x y => f (x, y)))
      ((volume.restrict s).prod (volume.restrict t)) := by
    rw [Measure.prod_restrict]; exact hf
  exact integral_integral_swap hf'

/-- The polar-coordinate integrand of the Cauchy-Pompeiu reduction, rewritten through the radial
and angular derivative fields. Split out of `cauchyPompeiu` to keep that proof under the 200-line
size we hold ourselves to; the abbreviations are rebuilt here so the body reads as it did. -/
private theorem eqOn_polar_integrand {g : ℂ → ℂ} (hgdiff : Differentiable ℝ g) (z : ℂ) (R' : ℝ) :
    Set.EqOn
      (fun p : ℝ × ℝ => p.1 • ((fun w => cauchyKernel w * wirtingerDbar g (z - w))
        (Complex.polarCoord.symm p)))
      (fun p : ℝ × ℝ => (Real.pi : ℂ)⁻¹ * (((Complex.I * (p.1 : ℂ))⁻¹ *
          (-(fderiv ℝ g (z - circleMap 0 p.1 p.2))
            (Complex.I * p.1 * Complex.exp (p.2 * Complex.I))) -
          (-(fderiv ℝ g (z - circleMap 0 p.1 p.2)) (Complex.exp (p.2 * Complex.I)))) / 2))
      (Set.Ioc (0 : ℝ) R' ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  set h : ℂ → ℂ := wirtingerDbar g with hh_def
  set Gr : ℝ × ℝ → ℂ := fun p => -(fderiv ℝ g (z - circleMap 0 p.1 p.2))
    (Complex.exp (p.2 * Complex.I)) with hGr_def
  set Gθ : ℝ × ℝ → ℂ := fun p => -(fderiv ℝ g (z - circleMap 0 p.1 p.2))
    (Complex.I * p.1 * Complex.exp (p.2 * Complex.I)) with hGθ_def
  set T' : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) R' ×ˢ Set.Ioo (-Real.pi) Real.pi with hT'_def
  set F : ℂ → ℂ := fun w => cauchyKernel w * h (z - w) with hF_def
  change Set.EqOn (fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p))
    (fun p => (Real.pi : ℂ)⁻¹ * (((Complex.I * (p.1 : ℂ))⁻¹ * Gθ p - Gr p) / 2)) T'
  intro p hp
  have hp1 : 0 < p.1 := hp.1.1
  have hne : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp1.ne'
  have hexpne : Complex.exp ((p.2 : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hdec : DifferentiableAt ℝ g (z - circleMap 0 p.1 p.2) := hgdiff _
  have hv1 := fderiv_apply_eq_wirtinger g (z - circleMap 0 p.1 p.2) hdec
      (Complex.exp ((p.2 : ℂ) * Complex.I))
  have hv2 := fderiv_apply_eq_wirtinger g (z - circleMap 0 p.1 p.2) hdec
      (Complex.I * (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))
  rw [conj_exp_real_mul_I] at hv1
  have hconj2 : (starRingEnd ℂ) (Complex.I * (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) =
      -Complex.I * (p.1 : ℂ) * Complex.exp (-(p.2 : ℂ) * Complex.I) := by
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, conj_exp_real_mul_I]
  rw [hconj2] at hv2
  have hFval : F (Complex.polarCoord.symm p) =
      (Real.pi * (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))⁻¹ *
        h (z - circleMap 0 p.1 p.2) := by
    simp only [hF_def, polarCoord_symm_eq_circleMap, cauchyKernel, circleMap, zero_add,
      mul_assoc]
  change p.1 • F (Complex.polarCoord.symm p) =
      (Real.pi : ℂ)⁻¹ * (((Complex.I * (p.1 : ℂ))⁻¹ * Gθ p - Gr p) / 2)
  rw [hFval, Complex.real_smul]
  simp only [hGr_def, hGθ_def]
  rw [hv1, hv2, ← hh_def]
  have hexp_prod : Complex.exp ((p.2 : ℂ) * Complex.I) *
      Complex.exp (-((p.2 : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_add]; simp
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  linear_combination (-(2 * h (z - circleMap 0 p.1 p.2))) * hexp_prod

/-- The angular field, divided by `i r`, is bounded by the derivative bound. Split out of
`cauchyPompeiu` for the 200-line proof size we hold ourselves to. -/
private theorem norm_angular_ratio_le {g : ℂ → ℂ} {M : ℝ} (hM : ∀ w, ‖fderiv ℝ g w‖ ≤ M) (z : ℂ) :
    ∀ p : ℝ × ℝ, 0 < p.1 → ‖(Complex.I * (p.1 : ℂ))⁻¹ *
      (-(fderiv ℝ g (z - circleMap 0 p.1 p.2))
        (Complex.I * p.1 * Complex.exp (p.2 * Complex.I)))‖ ≤ M := by
  set Gθ : ℝ × ℝ → ℂ := fun p => -(fderiv ℝ g (z - circleMap 0 p.1 p.2))
    (Complex.I * p.1 * Complex.exp (p.2 * Complex.I)) with hGθ_def
  change ∀ p : ℝ × ℝ, 0 < p.1 → ‖(Complex.I * (p.1 : ℂ))⁻¹ * Gθ p‖ ≤ M
  intro p hp1
  have hnorm_Ir : ‖Complex.I * (p.1 : ℂ)‖ = p.1 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hp1.le]
  have hbound2 : ‖Gθ p‖ ≤ M * p.1 := by
    rw [hGθ_def, norm_neg]
    calc ‖(fderiv ℝ g (z - circleMap 0 p.1 p.2))
            (Complex.I * (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I))‖
        ≤ ‖fderiv ℝ g (z - circleMap 0 p.1 p.2)‖ *
            ‖Complex.I * (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)‖ :=
          (fderiv ℝ g (z - circleMap 0 p.1 p.2)).le_opNorm _
      _ = ‖fderiv ℝ g (z - circleMap 0 p.1 p.2)‖ * p.1 := by
          rw [norm_mul, hnorm_Ir, Complex.norm_exp_ofReal_mul_I, mul_one]
      _ ≤ M * p.1 := mul_le_mul_of_nonneg_right (hM _) hp1.le
  rw [norm_mul, norm_inv, hnorm_Ir]
  calc p.1⁻¹ * ‖Gθ p‖ ≤ p.1⁻¹ * (M * p.1) :=
        mul_le_mul_of_nonneg_left hbound2 (inv_nonneg.mpr hp1.le)
    _ = M := by field_simp

/-- The radial derivative of the shifted argument. Split out of `cauchyPompeiu` for the 200-line
proof size we hold ourselves to. -/
private theorem hasDerivAt_radial {g : ℂ → ℂ} (hgdiff : Differentiable ℝ g) (z : ℂ) :
    ∀ p : ℝ × ℝ, HasDerivAt (fun r => g (z - circleMap 0 r p.2))
      (-(fderiv ℝ g (z - circleMap 0 p.1 p.2)) (Complex.exp (p.2 * Complex.I))) p.1 := by
  set Gr : ℝ × ℝ → ℂ := fun p => -(fderiv ℝ g (z - circleMap 0 p.1 p.2))
    (Complex.exp (p.2 * Complex.I)) with hGr_def
  change ∀ p : ℝ × ℝ, HasDerivAt (fun r => g (z - circleMap 0 r p.2)) (Gr p) p.1
  intro p
  have h1 : HasDerivAt (fun r : ℝ => z - circleMap 0 r p.2)
      (-(Complex.exp (p.2 * Complex.I))) p.1 :=
    (hasDerivAt_circleMap_r 0 p.2 p.1).const_sub z
  have h3 : HasFDerivAt g (fderiv ℝ g (z - circleMap 0 p.1 p.2)) (z - circleMap 0 p.1 p.2) :=
    (hgdiff (z - circleMap 0 p.1 p.2)).hasFDerivAt
  have h4 := HasFDerivAt.comp_hasDerivAt_of_eq p.1 h3 h1 rfl
  simp only [map_neg] at h4
  exact h4

/-- Forster 13.1 / Cauchy–Pompeiu, proved by the polar-FTC computation of design §5. -/
theorem cauchyPompeiu (hg : ContDiff ℝ 1 g) (hcs : HasCompactSupport g) (z : ℂ) :
    ∫ w : ℂ, cauchyKernel w * wirtingerDbar g (z - w) = g z := by
  have hgdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hfc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  set h : ℂ → ℂ := wirtingerDbar g with hh_def
  have hhc : Continuous h := by
    have h1 : Continuous (fun w => fderiv ℝ g w 1) := hfc.clm_apply continuous_const
    have h2 : Continuous (fun w => fderiv ℝ g w Complex.I) := hfc.clm_apply continuous_const
    rw [hh_def]
    exact (h1.add (continuous_const.mul h2)).div_const 2
  -- R0, R'
  obtain ⟨R0', hR0'⟩ := hcs.isBounded.subset_closedBall (0 : ℂ)
  set R0 : ℝ := max R0' 0 with hR0_def
  have hR0nonneg : 0 ≤ R0 := le_max_right _ _
  have hR0 : tsupport g ⊆ Metric.closedBall (0 : ℂ) R0 :=
    hR0'.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  set R' : ℝ := ‖z‖ + R0 + 1 with hR'_def
  have hR'pos : 0 < R' := by positivity
  have hnotmem_tsupport : ∀ r θ : ℝ, R' ≤ r → z - circleMap 0 r θ ∉ tsupport g := by
    intro r θ hr hmem
    have h1 := hR0 hmem
    rw [mem_closedBall_zero_iff] at h1
    have h2 : ‖circleMap 0 r θ‖ = r := by
      rw [circleMap, zero_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (hR'pos.le.trans hr)]
    have h3 : ‖circleMap 0 r θ‖ - ‖z‖ ≤ ‖z - circleMap 0 r θ‖ := by
      have h4 := norm_sub_norm_le (circleMap 0 r θ) z
      rwa [norm_sub_rev] at h4
    rw [h2] at h3
    linarith
  have hvanish : ∀ r θ : ℝ, R' ≤ r → g (z - circleMap 0 r θ) = 0 := fun r θ hr =>
    image_eq_zero_of_notMem_tsupport (hnotmem_tsupport r θ hr)
  have hvanish_h_gen : ∀ x : ℂ, x ∉ tsupport g → h x = 0 := by
    intro x hx
    have hnhds : g =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    rw [hh_def, wirtingerDbar_congr_nhds g (fun _ => (0:ℂ)) x hnhds, wirtingerDbar_const]
  have hvanish_h : ∀ r θ : ℝ, R' ≤ r → h (z - circleMap 0 r θ) = 0 := fun r θ hr =>
    hvanish_h_gen _ (hnotmem_tsupport r θ hr)
  -- the derivative facts (design step 4)
  set Gr : ℝ × ℝ → ℂ := fun p => -(fderiv ℝ g (z - circleMap 0 p.1 p.2))
    (Complex.exp (p.2 * Complex.I)) with hGr_def
  set Gθ : ℝ × ℝ → ℂ := fun p => -(fderiv ℝ g (z - circleMap 0 p.1 p.2))
    (Complex.I * p.1 * Complex.exp (p.2 * Complex.I)) with hGθ_def
  have hGr_deriv := hasDerivAt_radial hgdiff z
  have hGθ_deriv : ∀ p : ℝ × ℝ, HasDerivAt (fun θ => g (z - circleMap 0 p.1 θ)) (Gθ p) p.2 := by
    intro p
    have h1 : HasDerivAt (fun θ : ℝ => z - circleMap 0 p.1 θ)
        (-(circleMap 0 p.1 p.2 * Complex.I)) p.2 :=
      (hasDerivAt_circleMap 0 p.1 p.2).const_sub z
    have h3 : HasFDerivAt g (fderiv ℝ g (z - circleMap 0 p.1 p.2)) (z - circleMap 0 p.1 p.2) :=
      (hgdiff (z - circleMap 0 p.1 p.2)).hasFDerivAt
    have h4 := HasFDerivAt.comp_hasDerivAt_of_eq p.2 h3 h1 rfl
    have heq : circleMap 0 p.1 p.2 * Complex.I = Complex.I * p.1 * Complex.exp (p.2 * Complex.I) :=
        by
      rw [circleMap]; ring
    rw [heq] at h4
    simp only [map_neg] at h4
    exact h4
  have hcirc_cont : Continuous (fun p : ℝ × ℝ => z - circleMap 0 p.1 p.2) := by
    unfold circleMap; fun_prop
  have hGr_cont : Continuous Gr := by
    have hc2 : Continuous (fun p : ℝ × ℝ => Complex.exp ((p.2 : ℂ) * Complex.I)) := by fun_prop
    exact ((hfc.comp hcirc_cont).clm_apply hc2).neg
  have hGθ_cont : Continuous Gθ := by
    have hc2 : Continuous (fun p : ℝ × ℝ =>
        Complex.I * (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) := by fun_prop
    exact ((hfc.comp hcirc_cont).clm_apply hc2).neg
  -- Step 5: a global bound on `fderiv ℝ g`, and the two boundedness facts
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ w, ‖fderiv ℝ g w‖ ≤ M := by
    have hcsfd : HasCompactSupport (fderiv ℝ g) := hcs.fderiv ℝ
    have hcsnorm : HasCompactSupport (fun w => ‖fderiv ℝ g w‖) := by
      apply hcsfd.mono'
      intro w hw
      simp only [Function.mem_support, ne_eq, norm_eq_zero] at hw
      exact subset_tsupport _ hw
    obtain ⟨x0, hx0⟩ := hfc.norm.exists_forall_ge_of_hasCompactSupport hcsnorm
    exact ⟨‖fderiv ℝ g x0‖, hx0⟩
  have hGr_bound : ∀ p : ℝ × ℝ, ‖Gr p‖ ≤ M := by
    intro p
    rw [hGr_def, norm_neg]
    calc ‖(fderiv ℝ g (z - circleMap 0 p.1 p.2)) (Complex.exp ((p.2 : ℂ) * Complex.I))‖
        ≤ ‖fderiv ℝ g (z - circleMap 0 p.1 p.2)‖ * ‖Complex.exp ((p.2 : ℂ) * Complex.I)‖ :=
          (fderiv ℝ g (z - circleMap 0 p.1 p.2)).le_opNorm _
      _ = ‖fderiv ℝ g (z - circleMap 0 p.1 p.2)‖ := by
          rw [Complex.norm_exp_ofReal_mul_I, mul_one]
      _ ≤ M := hM _
  have hGθ_ratio_bound := norm_angular_ratio_le hM z
  -- the bounded box `T'`
  set T' : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) R' ×ˢ Set.Ioo (-Real.pi) Real.pi with hT'_def
  have hT'sub : T' ⊆ Complex.polarCoord.target := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    exact ⟨hr.1, hθ⟩
  have hT'meas : MeasurableSet T' := measurableSet_Ioc.prod measurableSet_Ioo
  have hT'_finite : volume T' ≠ ⊤ := by
    rw [hT'_def, show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  -- Step 3: reduce the polar integral from the full target to the bounded box
  set F : ℂ → ℂ := fun w => cauchyKernel w * h (z - w) with hF_def
  have hreduce : ∫ p in Complex.polarCoord.target, p.1 • F (Complex.polarCoord.symm p) =
      ∫ p in T', p.1 • F (Complex.polarCoord.symm p) := by
    rw [show T' = Complex.polarCoord.target ∩ T' from
      (Set.inter_eq_self_of_subset_right hT'sub).symm,
      ← MeasureTheory.setIntegral_indicator hT'meas]
    apply MeasureTheory.setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
    intro p hp
    by_cases hpT : p ∈ T'
    · rw [Set.indicator_of_mem hpT]
    · rw [Set.indicator_of_notMem hpT]
      obtain ⟨r, θ⟩ := p
      have hr : 0 < r := hp.1
      have hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi := hp.2
      have hrR' : R' < r := by
        by_contra hle
        push Not at hle
        exact hpT ⟨⟨hr, hle⟩, hθ⟩
      have hzero : h (z - circleMap 0 r θ) = 0 := hvanish_h r θ hrR'.le
      change r • F (Complex.polarCoord.symm (r, θ)) = 0
      rw [polarCoord_symm_eq_circleMap, hF_def]
      simp [hzero]
  have step3 : ∫ w, F w = ∫ p in T', p.1 • F (Complex.polarCoord.symm p) :=
    (Complex.integral_comp_polarCoord_symm F).symm.trans hreduce
  -- Steps 3+4 combined: the pointwise Wirtinger-split identity on `T'`
  have hstep34 := eqOn_polar_integrand hgdiff z R'
  -- integrability of `Gr` and the ratio on `T'`
  have hGr_intOn : IntegrableOn Gr T' := by
    apply Integrable.mono' (integrableOn_const (C := M) hT'_finite)
      hGr_cont.aestronglyMeasurable.restrict
    filter_upwards with p using hGr_bound p
  have hratio_contOn : ContinuousOn (fun p : ℝ × ℝ => (Complex.I * (p.1 : ℂ))⁻¹ * Gθ p) T' := by
    apply ContinuousOn.mul
    · apply ContinuousOn.inv₀ (by fun_prop)
      intro p hp
      simp [Complex.I_ne_zero, hp.1.1.ne']
    · exact hGθ_cont.continuousOn
  have hratio_intOn : IntegrableOn (fun p : ℝ × ℝ => (Complex.I * (p.1 : ℂ))⁻¹ * Gθ p) T' := by
    apply Integrable.mono' (integrableOn_const (C := M) hT'_finite)
      (hratio_contOn.aestronglyMeasurable hT'meas)
    filter_upwards [MeasureTheory.ae_restrict_mem hT'meas] with p hp using
      hGθ_ratio_bound p hp.1.1
  have step8_pre : ∫ p in T', p.1 • F (Complex.polarCoord.symm p) =
      (Real.pi : ℂ)⁻¹ * ((∫ p in T', (Complex.I * (p.1 : ℂ))⁻¹ * Gθ p) - ∫ p in T', Gr p) / 2 := by
    rw [MeasureTheory.setIntegral_congr_fun hT'meas hstep34, integral_const_mul, integral_div,
      integral_sub hratio_intOn hGr_intOn]
    ring
  have hvol_eq : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
  -- Step 6: the θ-leg vanishes
  have stepA : ∫ p in T', (Complex.I * (p.1 : ℂ))⁻¹ * Gθ p = 0 := by
    rw [hT'_def, hvol_eq, MeasureTheory.setIntegral_prod _ (hvol_eq ▸ hT'_def ▸ hratio_intOn)]
    have hinner : ∀ r ∈ Set.Ioc (0 : ℝ) R', (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        (Complex.I * (r : ℂ))⁻¹ * Gθ (r, θ)) = 0 := by
      intro r hr
      rw [integral_const_mul]
      have hIoo_eq : ∫ θ in Set.Ioo (-Real.pi) Real.pi, Gθ (r, θ) ∂volume =
          ∫ θ in Set.Ioc (-Real.pi) Real.pi, Gθ (r, θ) ∂volume :=
        MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc
      rw [hIoo_eq,
        ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
      have hGθ_deriv' : ∀ θ' ∈ Set.uIcc (-Real.pi) Real.pi,
          HasDerivAt (fun t => g (z - circleMap 0 r t)) (Gθ (r, θ')) θ' :=
        fun θ' _ => hGθ_deriv (r, θ')
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hGθ_deriv'
        ((show Continuous (fun θ => Gθ (r, θ)) from
          hGθ_cont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)]
      have hcirc_eq : circleMap 0 r Real.pi = circleMap 0 r (-Real.pi) := by
        rw [circleMap, circleMap]
        congr 1
        rw [show ((-Real.pi : ℝ) : ℂ) = -(Real.pi : ℂ) by push_cast; ring, neg_mul,
          Complex.exp_neg, Complex.exp_pi_mul_I]
        norm_num
      rw [hcirc_eq, sub_self, mul_zero]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun r hr => by
      rw [hinner r hr]), integral_zero]
  -- Step 7: the r-leg telescopes
  have stepB : ∫ p in T', Gr p = -(2 * Real.pi) * g z := by
    have hswap : ∫ r in Set.Ioc (0 : ℝ) R', ∫ θ in Set.Ioo (-Real.pi) Real.pi, Gr (r, θ) ∂volume
          ∂volume =
        ∫ θ in Set.Ioo (-Real.pi) Real.pi, ∫ r in Set.Ioc (0 : ℝ) R', Gr (r, θ) ∂volume ∂volume :=
      setIntegral_prod_symm (hvol_eq ▸ hT'_def ▸ hGr_intOn)
    have hinner : ∀ θ ∈ Set.Ioo (-Real.pi) Real.pi,
        (∫ r in Set.Ioc (0 : ℝ) R', Gr (r, θ)) = -g z := by
      intro θ hθ
      rw [← intervalIntegral.integral_of_le hR'pos.le]
      have hGr_deriv' : ∀ r' ∈ Set.uIcc (0 : ℝ) R',
          HasDerivAt (fun t => g (z - circleMap 0 t θ)) (Gr (r', θ)) r' :=
        fun r' _ => hGr_deriv (r', θ)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hGr_deriv'
        ((show Continuous (fun r => Gr (r, θ)) from
          hGr_cont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)]
      have h1 : g (z - circleMap 0 R' θ) = 0 := hvanish R' θ le_rfl
      have h2 : circleMap 0 (0 : ℝ) θ = 0 := by simp [circleMap]
      rw [h1, h2, sub_zero]
      ring
    rw [hT'_def, hvol_eq, MeasureTheory.setIntegral_prod _ (hvol_eq ▸ hT'_def ▸ hGr_intOn), hswap,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => by
        rw [hinner θ hθ])]
    rw [MeasureTheory.integral_const, Measure.real, MeasureTheory.Measure.restrict_apply_univ,
      Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), Complex.real_smul]
    push_cast
    ring
  rw [step3, step8_pre, stepA, stepB]
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- Forster 13.1: `dbar` of the Cauchy transform recovers `g`. -/
theorem wirtingerDbar_cauchyTransform_eq (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g) :
    ∀ z, wirtingerDbar (cauchyTransform g) z = g z := by
  intro z
  rw [wirtingerDbar_cauchyTransform g hg hcs z]
  exact cauchyPompeiu g (hg.of_le (by norm_num)) hcs z

/-- Forster 13.1, existential form: `dbaru = g` is solvable for compactly supported smooth `g`. -/
theorem exists_dbar_solution_of_hasCompactSupport (hg : ContDiff ℝ ∞ g)
    (hcs : HasCompactSupport g) : ∃ u, ContDiff ℝ ∞ u ∧ ∀ z, wirtingerDbar u z = g z :=
  ⟨cauchyTransform g, contDiff_cauchyTransform g hg hcs, wirtingerDbar_cauchyTransform_eq g hg hcs⟩

end RS
