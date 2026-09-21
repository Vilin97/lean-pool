/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ContinuationRieszIntegral
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.Core
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Transport -/

open TauCeti.DavisKahan.Angle


/-!
# Quantitative Riesz continuation along affine operator paths

This module proves the analytic continuation estimate for one fixed
proof-carrying contour.  Its first part packages the parameterized length of a
finitely piecewise-`C1` contour and bounds a curve integral by a uniform
operator-norm bound times that length.

The second part applies the accepted affine-path resolvent estimate.  A common
positive spectral margin along a parameter set yields a quantitative
Lipschitz estimate for the normalized Riesz operator and hence norm continuity
on that set.

Spectral identification and projection-range transport are deliberately left
to later leaf modules.  The declarations here require only self-adjointness and
uniform contour separation along the path.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set
open MeasureTheory
open scoped InnerProductSpace Interval unitInterval

universe u v

namespace PiecewiseC1ClosedContour

/-- The constant identity one-form used to measure contour speed. -/
noncomputable def tangentOneForm : ℂ → ℂ →L[ℂ] ℂ :=
  fun _ ↦ (1 : ℂ →L[ℂ] ℂ)

/-- Evaluation of the identity one-form. -/
@[simp] theorem tangentOneForm_apply (z v : ℂ) :
    tangentOneForm z v = v := by
  simp [tangentOneForm]

/-- Speed of the extended contour parameterization, measured using the same
within-derivative convention as Mathlib's curve integral. -/
noncomputable def contourSpeed (Γ : PiecewiseC1ClosedContour) (t : ℝ) : ℝ :=
  ‖derivWithin Γ.path.extend (Set.Icc (0 : ℝ) 1) t‖

/-- Parameterized contour length. -/
noncomputable def contourLength (Γ : PiecewiseC1ClosedContour) : ℝ :=
  ∫ t in (0 : ℝ)..1, Γ.contourSpeed t

/-- The contour speed is interval integrable. -/
theorem intervalIntegrable_contourSpeed (Γ : PiecewiseC1ClosedContour) :
    IntervalIntegrable Γ.contourSpeed volume 0 1 := by
  have hcurve : CurveIntegrable tangentOneForm Γ.path :=
    Γ.curveIntegrable_of_continuousOn tangentOneForm continuousOn_const
  have hinterval :
      IntervalIntegrable (curveIntegralFun tangentOneForm Γ.path) volume 0 1 :=
    hcurve
  have hnorm := hinterval.norm
  refine hnorm.congr ?_
  intro t ht
  simp only [curveIntegralFun_def, tangentOneForm_apply, contourSpeed]

/-- A curve integral is bounded by a uniform one-form norm times the
parameterized contour length. -/
theorem norm_curveIntegral_le_mul_contourLength
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (Γ : PiecewiseC1ClosedContour) (ω : ℂ → ℂ →L[ℂ] F)
    {C : ℝ} (hbound : ∀ z ∈ Γ.image, ‖ω z‖ ≤ C) :
    ‖∫ᶜ z in Γ.path, ω z‖ ≤ C * Γ.contourLength := by
  rw [curveIntegral_def]
  have hspeed : IntervalIntegrable (fun t ↦ C * Γ.contourSpeed t) volume 0 1 := by
    have h := Γ.intervalIntegrable_contourSpeed.smul C
    refine h.congr ?_
    intro t ht
    simp only [Pi.smul_apply, smul_eq_mul]
  have hpoint : ∀ᵐ t ∂volume,
      t ∈ Set.Ioc (0 : ℝ) 1 →
        ‖curveIntegralFun ω Γ.path t‖ ≤ C * Γ.contourSpeed t := by
    filter_upwards with t
    intro ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
    have himage : Γ.param t ∈ Γ.image := by
      refine ⟨(⟨t, htI⟩ : unitInterval), ?_⟩
      simpa only [image, param] using (Γ.path.extend_apply htI).symm
    calc
      ‖curveIntegralFun ω Γ.path t‖ =
          ‖ω (Γ.param t)
            (derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t)‖ := by
        simp only [curveIntegralFun_def, param]
      _ ≤ ‖ω (Γ.param t)‖ *
          ‖derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t‖ := by
        exact mul_le_mul_of_nonneg_right (hbound _ himage) (norm_nonneg _)
      _ = C * Γ.contourSpeed t := rfl
  calc
    ‖∫ t in (0 : ℝ)..1, curveIntegralFun ω Γ.path t‖ ≤
        ∫ t in (0 : ℝ)..1, C * Γ.contourSpeed t :=
      intervalIntegral.norm_integral_le_of_norm_le zero_le_one hpoint hspeed
    _ = C * Γ.contourLength := by
      simp only [contourLength, intervalIntegral.integral_const_mul]

end PiecewiseC1ClosedContour

section AffineRieszTransport

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The normalized Riesz operator of a bounded operator around one fixed
proof-carrying contour. -/
noncomputable def fixedContourRieszOperator
    (Γ : PiecewiseC1ClosedContour) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  rieszNormalization •
    ∫ᶜ z in Γ.path, resolventOneForm A z

/-- The fixed-contour definition agrees definitionally with the Riesz operator
attached to a full spectral-separation witness. -/
theorem fixedContourRieszOperator_eq_contourRieszProjection
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    fixedContourRieszOperator Γ.geometric A = Γ.contourRieszProjection :=
  rfl

/-- Uniform spectral separation makes the resolvent one-form continuous on a
fixed contour. -/
theorem continuousOn_resolventOneForm_of_contour_distance
    (Γ : PiecewiseC1ClosedContour) (A : H →L[ℂ] H)
    (hA : A.IsSymmetric) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ x : unitInterval, ∀ lam ∈ realSpectrum A,
      delta ≤ ‖Γ.path x - (lam : ℂ)‖) :
    ContinuousOn (resolventOneForm A) Γ.image := by
  have hsep_image : ∀ z ∈ Γ.image, ∀ lam ∈ realSpectrum A,
      delta ≤ ‖z - (lam : ℂ)‖ := by
    rintro z ⟨x, rfl⟩ lam hlam
    exact hsep x lam hlam
  have hres : ContinuousOn (resolventOperator A) Γ.image :=
    complex_continuousOn_resolventOperator_of_distance
      A hA Γ.image delta hdelta hsep_image
  let L : (H →L[ℂ] H) →L[ℂ] (ℂ →L[ℂ] (H →L[ℂ] H)) :=
    ContinuousLinearMap.smulRightL ℂ ℂ (H →L[ℂ] H)
      (1 : ℂ →L[ℂ] ℂ)
  have hcomp : ContinuousOn (fun z ↦ L (resolventOperator A z)) Γ.image :=
    L.continuous.continuousOn.comp hres (fun _ _ ↦ Set.mem_univ _)
  refine hcomp.congr ?_
  intro z hz
  change L (resolventOperator A z) = resolventOneForm A z
  rfl

/-- Uniform spectral separation gives curve integrability of the resolvent
one-form on a fixed contour. -/
theorem curveIntegrable_resolventOneForm_of_contour_distance
    (Γ : PiecewiseC1ClosedContour) (A : H →L[ℂ] H)
    (hA : A.IsSymmetric) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ x : unitInterval, ∀ lam ∈ realSpectrum A,
      delta ≤ ‖Γ.path x - (lam : ℂ)‖) :
    CurveIntegrable (resolventOneForm A) Γ.path :=
  Γ.curveIntegrable_of_continuousOn (resolventOneForm A)
    (continuousOn_resolventOneForm_of_contour_distance
      Γ A hA delta hdelta hsep)

/-- The difference of two resolvent one-forms has norm equal to the norm of the
underlying resolvent difference. -/
theorem norm_resolventOneForm_sub
    (A B : H →L[ℂ] H) (z : ℂ) :
    ‖resolventOneForm A z - resolventOneForm B z‖ =
      ‖resolventOperator A z - resolventOperator B z‖ := by
  have hform :
      resolventOneForm A z - resolventOneForm B z =
        ContinuousLinearMap.toSpanSingleton ℂ
          (resolventOperator A z - resolventOperator B z) := by
    ext v
    simp [resolventOneForm_apply]
  rw [hform, ContinuousLinearMap.norm_toSpanSingleton]

/-- Quantitative norm estimate for normalized Riesz operators along an affine
self-adjoint path with one common separating contour. -/
theorem norm_fixedContourRieszOperator_operatorPath_sub_le
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (parameterSet : Set ℝ) (delta : ℝ) (hdelta : 0 < delta)
    (hself : ∀ t ∈ parameterSet, (operatorPath A V t).IsSymmetric)
    (hsep : ∀ t ∈ parameterSet, ∀ x : unitInterval,
      ∀ lam ∈ realSpectrum (operatorPath A V t),
        delta ≤ ‖Γ.path x - (lam : ℂ)‖)
    {t u : ℝ} (ht : t ∈ parameterSet) (hu : u ∈ parameterSet) :
    ‖fixedContourRieszOperator Γ (operatorPath A V t) -
        fixedContourRieszOperator Γ (operatorPath A V u)‖ ≤
      ‖rieszNormalization‖ *
        (delta⁻¹ ^ 2 * ‖V‖ * Γ.contourLength) * ‖t - u‖ := by
  let At : H →L[ℂ] H := operatorPath A V t
  let Au : H →L[ℂ] H := operatorPath A V u
  have hAt : CurveIntegrable (resolventOneForm At) Γ.path :=
    curveIntegrable_resolventOneForm_of_contour_distance
      Γ At (hself t ht) delta hdelta (hsep t ht)
  have hAu : CurveIntegrable (resolventOneForm Au) Γ.path :=
    curveIntegrable_resolventOneForm_of_contour_distance
      Γ Au (hself u hu) delta hdelta (hsep u hu)
  let C : ℝ := delta⁻¹ ^ 2 * ‖V‖ * ‖t - u‖
  have honeForm : ∀ z ∈ Γ.image,
      ‖resolventOneForm At z - resolventOneForm Au z‖ ≤ C := by
    rintro z ⟨x, rfl⟩
    rw [norm_resolventOneForm_sub]
    exact norm_resolventOperator_operatorPath_sub_le_of_spectral_distance
      A V (Γ.path x) delta hdelta parameterSet hself
      (fun r hr lam hlam ↦ hsep r hr x lam hlam) ht hu
  have hintegral :
      ‖(∫ᶜ z in Γ.path, resolventOneForm At z) -
          ∫ᶜ z in Γ.path, resolventOneForm Au z‖ ≤
        C * Γ.contourLength := by
    rw [← curveIntegral_sub hAt hAu]
    exact Γ.norm_curveIntegral_le_mul_contourLength
      (resolventOneForm At - resolventOneForm Au) honeForm
  change ‖
      rieszNormalization •
          (∫ᶜ z in Γ.path, resolventOneForm At z) -
      rieszNormalization •
          ∫ᶜ z in Γ.path, resolventOneForm Au z‖ ≤ _
  rw [← smul_sub, norm_smul]
  calc
    ‖rieszNormalization‖ *
        ‖(∫ᶜ z in Γ.path, resolventOneForm At z) -
          ∫ᶜ z in Γ.path, resolventOneForm Au z‖ ≤
      ‖rieszNormalization‖ *
        (C * Γ.contourLength) := by
      exact mul_le_mul_of_nonneg_left hintegral (norm_nonneg _)
    _ = ‖rieszNormalization‖ *
        (delta⁻¹ ^ 2 * ‖V‖ * Γ.contourLength) * ‖t - u‖ := by
      dsimp [C]
      ring

/-- The fixed-contour Riesz operator is Lipschitz on every parameter set with
a common positive spectral margin. -/
theorem lipschitzOnWith_fixedContourRieszOperator_operatorPath
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (parameterSet : Set ℝ) (delta : ℝ) (hdelta : 0 < delta)
    (hself : ∀ t ∈ parameterSet, (operatorPath A V t).IsSymmetric)
    (hsep : ∀ t ∈ parameterSet, ∀ x : unitInterval,
      ∀ lam ∈ realSpectrum (operatorPath A V t),
        delta ≤ ‖Γ.path x - (lam : ℂ)‖) :
    LipschitzOnWith
      (Real.toNNReal
        |‖rieszNormalization‖ *
          (delta⁻¹ ^ 2 * ‖V‖ * Γ.contourLength)|)
      (fun t ↦ fixedContourRieszOperator Γ (operatorPath A V t)) parameterSet := by
  let K : ℝ := ‖rieszNormalization‖ *
    (delta⁻¹ ^ 2 * ‖V‖ * Γ.contourLength)
  change LipschitzOnWith (Real.toNNReal |K|)
    (fun t ↦ fixedContourRieszOperator Γ (operatorPath A V t)) parameterSet
  refine LipschitzOnWith.of_dist_le' (K := |K|) ?_
  intro t ht u hu
  have hmain := norm_fixedContourRieszOperator_operatorPath_sub_le
    Γ A V parameterSet delta hdelta hself hsep ht hu
  calc
    dist (fixedContourRieszOperator Γ (operatorPath A V t))
        (fixedContourRieszOperator Γ (operatorPath A V u)) =
      ‖fixedContourRieszOperator Γ (operatorPath A V t) -
        fixedContourRieszOperator Γ (operatorPath A V u)‖ := by
      rw [dist_eq_norm]
    _ ≤ K * ‖t - u‖ := by
      simpa only [K] using hmain
    _ ≤ |K| * ‖t - u‖ := by
      exact mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _)
    _ = |K| * dist t u := by
      rw [Real.dist_eq, Real.norm_eq_abs]

/-- Norm continuity of the fixed-contour Riesz operator path. -/
theorem continuousOn_fixedContourRieszOperator_operatorPath
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (parameterSet : Set ℝ) (delta : ℝ) (hdelta : 0 < delta)
    (hself : ∀ t ∈ parameterSet, (operatorPath A V t).IsSymmetric)
    (hsep : ∀ t ∈ parameterSet, ∀ x : unitInterval,
      ∀ lam ∈ realSpectrum (operatorPath A V t),
        delta ≤ ‖Γ.path x - (lam : ℂ)‖) :
    ContinuousOn
      (fun t ↦ fixedContourRieszOperator Γ (operatorPath A V t)) parameterSet :=
  (lipschitzOnWith_fixedContourRieszOperator_operatorPath
    Γ A V parameterSet delta hdelta hself hsep).continuousOn

end AffineRieszTransport

end DavisKahanExt
end TauCeti
