/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedSobolevGevrey
public import LeanPool.NavierStokesAndEuler.Euler.MeanScaledBoundaryGevrey
public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceFixedInverse
import LeanPool.NavierStokesAndEuler.Euler.BoundedCoefficientJets
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.Euler.MeanConcreteTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanSourceGevrey
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus

/-!
# The actual source mean inverse preserves fixed Sobolev word estimates

The input and output are literal ordered spatial derivative blocks of actual
L² translation orbits. Taking q=6 gives the fixed-H6 endpoint without spending
six additional factorial shifts. All constants are independent of the grade.
-/

@[expose] public section


noncomputable section

namespace EulerMeanSourceSobolev

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic EulerMeanSourceInverse
  EulerMeanVariationalInverse EulerMeanFixedSpaceInverse EulerMeanSourceFixedInverse
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTranslatedGevrey
  EulerTimeLp EulerCoerciveProjection EulerGevrey EulerOperatorGevreyCalculus
  EulerParameterWordGevrey EulerMeanSourceGevrey EulerMeanFixedSobolevGevrey
open scoped NNReal ContDiff

variable {ι : Type*} [Fintype ι]
  (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
  (F F₁ H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (operatorPath T F.field t x) = x)
  (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (EulerVolterraConvolution.extendPath T hT (operatorPath T F.field))
      (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t x v, ⟪H.field t x v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) + Be * T + boundaryLocalizationC2 * Bc * r ^ 3 * T ≤ 1 / 2)

include hd hℓ1 in
/-- Actual fixed-Hq source estimate, at one unchanged external radius and
with one shift. All form coercivity and cutoff bounds are already proved. -/
theorem sourceCoordinateSolver_translation_block_gevrey
    (f : TimeLp T L2) (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
    (Rc R M CF CF₁ CH CM Cf : ℝ) (hRc : 1024 ≤ Rc)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCf : 0 ≤ Cf)
    (hM : 1 ≤ M)
    (hMC : sobolevInverseCost (sourceFixedCoercivity T F F₁ FInv)⁻¹
      (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L) q *
      operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L ≤ M)
    (hMD : sobolevInverseCost (sourceFixedCoercivity T F F₁ FInv)⁻¹
      (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L) q *
      forcingBlockAmplitude ι q T Rc CF CF₁ Cf ≤ M)
    (hR : 2*M*(sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hFb : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF*majorant Rc
        0 n)
    (hF₁b : ∀ n t x, ‖iteratedFDeriv ℝ n (F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF₁*majorant
        Rc 0 n)
    (hHb : ∀ n t x, ‖iteratedFDeriv ℝ n (H.field t : Space → Space →L[ℝ] Space) x‖ ≤ CH*majorant Rc
        0 n)
    (hMb : ∀ n x, ‖iteratedFDeriv ℝ n (M0.field : Space → Space →L[ℝ] Space) x‖ ≤ CM*majorant Rc 0
        n)
    (d : ℕ) (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation T b f) n a ≤
        Cf*majorant R d n)
    (n : ℕ) (a : Space) :
    block directions q (fun b : Space => timeSolenoidalTranslation T b
      (sourceCoordinateSolver T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter
        hext hcore hInv hF K hK hF0 hH hsmall f)) n a ≤ majorant R (d+1) n := by
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
  exact solution_translation_block_gevrey directions hd q T hT (operatorPath T F.field)
      (operatorPath T F₁.field)
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

end EulerMeanSourceSobolev
