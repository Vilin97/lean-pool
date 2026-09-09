/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceFixedInverse
public import LeanPool.NavierStokesAndEuler.Euler.MeanTranslatedGevrey
public import LeanPool.NavierStokesAndEuler.Euler.MeanScaledBoundaryGevrey

@[expose] public section

/-!
# The actual source mean coordinate inverse has Gevrey spatial bounds

The spatial lower bound, operator smoothness, cutoff derivatives, fixed-space
transport, and inverse recurrence are all supplied by proved constructions.
The remaining quantitative inputs are literal spatial derivatives of the given
matrix coefficients and the actual translation derivatives of the forcing.
-/

noncomputable section

namespace EulerMeanSourceGevrey

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic EulerMeanSourceInverse
  EulerMeanVariationalInverse EulerMeanFixedSpaceInverse EulerMeanSourceFixedInverse
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTranslatedGevrey
  EulerTimeLp EulerCoerciveProjection EulerGevrey EulerOperatorGevreyCalculus
open scoped NNReal ContDiff

/-- True spatial coefficient bounds become bounds for the conjugated operator path. -/
theorem translatedPath_bound (T : ℝ)
    (F : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbound : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C*majorant
      R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b (operatorPath T F.field)) a‖ ≤
      C*majorant R 0 n := by
  simpa only [translatePath_operatorPath] using
    norm_iteratedFDeriv_operatorPathTranslation_le T F n (C*majorant R 0 n)
      (mul_nonneg hC (majorant_nonneg R hR 0 n)) (hbound n) a

/-- The initial matrix multiplier has the same literal spatial derivative bounds. -/
theorem translatedMultiplier_bound
    (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbound : ∀ n x, ‖iteratedFDeriv ℝ n (M0.field : Space → Space →L[ℝ] Space) x‖ ≤ C*majorant R 0
      n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => translateOperator b (multiplier M0.field)) a‖ ≤
      C*majorant R 0 n := by
  simpa only [translateOperator_multiplier] using
    norm_iteratedFDeriv_multiplierTranslation_le M0 n (C*majorant R 0 n)
      (mul_nonneg hC (majorant_nonneg R hR 0 n)) (hbound n) a

variable (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
  (F F₁ H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1*Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1/4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be*‖v‖^2 ≤ ⟪M0.field x v,v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc*‖v‖^2 ≤ ⟪M0.field x v,v⟫_ℝ)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (operatorPath T F.field t x) = x)
  (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (EulerVolterraConvolution.extendPath T hT (operatorPath T F.field))
      (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t x v, ⟪H.field t x v,v⟫_ℝ ≤ K*‖v‖^2)
  (hsmall : K*(T^2/2)+Be*T+boundaryLocalizationC2*Bc*r^3*T ≤ 1/2)

include hℓ1 in
/-- The source coordinate solver obeys all-order genuine spatial estimates.
Its coercivity and cutoff assumptions have already been discharged. -/
theorem sourceCoordinateSolver_translation_gevrey
    (f : TimeLp T L2) (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
    (Rc R M CF CF₁ CH CM Cf : ℝ) (hRc : 1024 ≤ Rc)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCf : 0 ≤ Cf)
    (hM : 1 ≤ M)
    (hMC : (sourceFixedCoercivity T F F₁ FInv)⁻¹*
      operatorAmplitude T CF CF₁ CH CM scaledBoundaryOperatorAmplitude L ≤ M)
    (hMD : (sourceFixedCoercivity T F F₁ FInv)⁻¹*forcingAmplitude T CF CF₁ Cf ≤ M)
    (hR : 2*M*(Rc+1) ≤ R)
    (hFb : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF*majorant Rc
      0 n)
    (hF₁b : ∀ n t x, ‖iteratedFDeriv ℝ n (F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF₁*majorant
      Rc 0 n)
    (hHb : ∀ n t x, ‖iteratedFDeriv ℝ n (H.field t : Space → Space →L[ℝ] Space) x‖ ≤ CH*majorant Rc
      0 n)
    (hMb : ∀ n x, ‖iteratedFDeriv ℝ n (M0.field : Space → Space →L[ℝ] Space) x‖ ≤ CM*majorant Rc 0
      n)
    (d : ℕ) (hfb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b f) a‖ ≤
      Cf*majorant R d n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b
      (sourceCoordinateSolver T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter
        hext hcore hInv hF K hK hF0 hH hsmall f)) a‖ ≤ majorant R (d+1) n := by
  have hRc0 : 0 ≤ Rc := (by norm_num : (0 : ℝ) ≤ 1024).trans hRc
  have hFr : ContDiff ℝ ∞ (fun b : Space => translatePath T b (operatorPath T F.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F
  have hF₁r : ContDiff ℝ ∞ (fun b : Space => translatePath T b (operatorPath T F₁.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F₁
  have hHr : ContDiff ℝ ∞ (fun b : Space => translatePath T b (operatorPath T H.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T H
  have hMr : ContDiff ℝ ∞ (fun b : Space => translateOperator b (multiplier M0.field)) := by
    simpa only [translateOperator_multiplier] using multiplierTranslation_contDiff M0
  have hAr : ContDiff ℝ ∞ (fun b : Space => translateOperator b (boundaryOperator (scaledCutoff ℓ
    hℓ))) := by
    simpa only [translateOperator_boundary] using scaledBoundaryOperator_contDiff ℓ hℓ
  have hAb (k b) : ‖iteratedFDeriv ℝ k
      (fun y : Space => translateOperator y (boundaryOperator (scaledCutoff ℓ hℓ))) b‖ ≤
      scaledBoundaryOperatorAmplitude*majorant Rc 0 k := by
    have h := scaledBoundaryOperator_gevrey ℓ hℓ hℓ1 k b
    apply (show ‖iteratedFDeriv ℝ k
      (fun y : Space => translateOperator y (boundaryOperator (scaledCutoff ℓ hℓ))) b‖ ≤
      scaledBoundaryOperatorAmplitude*majorant 1024 0 k by
        simpa only [translateOperator_boundary] using h).trans
    exact mul_le_mul_of_nonneg_left (majorant_radius_mono 1024 Rc (by norm_num) hRc 0 k)
      scaledBoundaryOperatorAmplitude_nonneg
  exact solution_translation_gevrey T hT (operatorPath T F.field) (operatorPath T F₁.field)
    (operatorPath T H.field) (multiplier M0.field) (boundaryOperator (scaledCutoff ℓ hℓ)) L
    (sourceFixedCoercivity T F F₁ FInv) (sourceFixedCoercivity_pos T hT F F₁ FInv)
    (sourceFixedForm_coercive T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter
      hext hcore hInv hF K hK hF0 hH hsmall)
    hFr hF₁r hHr hMr hAr f hf Rc R M CF CF₁ CH CM scaledBoundaryOperatorAmplitude Cf
    hRc0 hCF hCF₁ hCH hCM scaledBoundaryOperatorAmplitude_nonneg hCf hM hMC hMD hR
    (translatedPath_bound T F Rc CF hRc0 hCF hFb)
    (translatedPath_bound T F₁ Rc CF₁ hRc0 hCF₁ hF₁b)
    (translatedPath_bound T H Rc CH hRc0 hCH hHb)
    (translatedMultiplier_bound M0 Rc CM hRc0 hCM hMb) hAb d hfb n a

end EulerMeanSourceGevrey
