/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanTranslatedInverse
public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientGevrey
public import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveGevrey

@[expose] public section

/-!
# Genuine all-order spatial estimates for the translated mean inverse

The recurrence is proved for the actual coercive inverse. The translated
solution is identified with the real spatial translation orbit before its
iterated Fréchet derivatives are estimated. Coefficient and forcing amplitudes
enter through explicit polynomials, independently of derivative order.
-/

noncomputable section

namespace EulerMeanTranslatedGevrey

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal EulerTimeLp
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanFixedSpaceInverse
  EulerMeanFixedTranslation EulerMeanTranslatedInverse EulerMeanFixedCoefficientRegularity
  EulerMeanFixedCoefficientGevrey EulerHilbertCoerciveGevrey EulerCoerciveProjection
  EulerGevrey EulerOperatorGevreyCalculus EulerTransverseGramInverse
open scoped ContDiff

-- Reuse the nested Hilbert-space instances in the translated inverse estimates.
private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace) := inferInstance

/-- The proved polynomial amplitude for the actual fixed mean operator. -/
def operatorAmplitude (T CF CF₁ CH CM CA L : ℝ) : ℝ :=
  9*(T*CF₁+CF)^2*(1+(T^2/2)*CH+T*(CM+|L| * CA))

/-- The proved polynomial amplitude of the actual forcing pullback. -/
def forcingAmplitude (T CF CF₁ Cf : ℝ) : ℝ := 3*(T*(T*CF₁+CF))*Cf

theorem operatorAmplitude_nonneg (T CF CF₁ CH CM CA L : ℝ)
    (hT : 0 ≤ T) (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCA : 0 ≤ CA) :
    0 ≤ operatorAmplitude T CF CF₁ CH CM CA L := by unfold operatorAmplitude; positivity

theorem forcingAmplitude_nonneg (T CF CF₁ Cf : ℝ)
    (hT : 0 ≤ T) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf) :
    0 ≤ forcingAmplitude T CF CF₁ Cf := by unfold forcingAmplitude; positivity

variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L c : ℝ)
  (hc : 0 < c)
  (hcoercive : ∀ v, c*‖v‖^2 ≤ ⟪fixedMeanOperator T hT F F₁ H M0 A L v,v⟫_ℝ)

/-- Every actual spatial derivative of the solved mean field satisfies the
factorial bound, with no assumed solution-jet recurrence. -/
theorem solution_translation_gevrey
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hH : ContDiff ℝ ∞ (fun a : Space => translatePath T a H))
    (hM0 : ContDiff ℝ ∞ (fun a : Space => translateOperator a M0))
    (hA : ContDiff ℝ ∞ (fun a : Space => translateOperator a A))
    (f : TimeLp T L2) (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
    (Rc R M CF CF₁ CH CM CA Cf : ℝ)
    (hRc : 0 ≤ Rc) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCH : 0 ≤ CH)
    (hCM : 0 ≤ CM) (hCA : 0 ≤ CA) (hCf : 0 ≤ Cf)
    (hM : 1 ≤ M)
    (hMC : c⁻¹*operatorAmplitude T CF CF₁ CH CM CA L ≤ M)
    (hMD : c⁻¹*forcingAmplitude T CF CF₁ Cf ≤ M)
    (hR : 2*M*(Rc+1) ≤ R)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
      n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
      0 n)
    (hHb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b H) a‖ ≤ CH*majorant Rc 0
      n)
    (hMb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translateOperator b M0) a‖ ≤ CM*majorant Rc
      0 n)
    (hAb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translateOperator b A) a‖ ≤ CA*majorant Rc
      0 n)
    (d : ℕ) (hfb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b f) a‖ ≤
      Cf*majorant R d n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun a : Space => timeSolenoidalTranslation T a
      (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hcoercive
        (-(fixedMeanPrimitive T hT F F₁).adjoint f))) x‖ ≤ majorant R (d+1) n := by
  have hRcR : Rc ≤ R := by nlinarith
  have hR0 : 0 ≤ R := hRc.trans hRcR
  have hFbr (k a) : ‖iteratedFDeriv ℝ k (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant R 0
    k :=
    (hFb k a).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 k) hCF)
  have hF₁br (k a) : ‖iteratedFDeriv ℝ k (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant
    R 0 k :=
    (hF₁b k a).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 k) hCF₁)
  have hO : ContDiff ℝ ∞ (fun a : Space => translatedMeanOperator T hT a F F₁ H M0 A L) :=
    contDiff_fixedMeanOperator T hT (fun a => translatePath T a F) (fun a => translatePath T a F₁)
      (fun a => translatePath T a H) (fun a => translateOperator a M0) (fun a => translateOperator
        a A)
      L hF hF₁ hH hM0 hA
  have hJ : ContDiff ℝ ∞ (fun a : Space => translatedMeanPrimitive T hT a F F₁) :=
    contDiff_fixedMeanPrimitive T hT (fun a => translatePath T a F) (fun a => translatePath T a F₁)
      hF hF₁
  have hG : ContDiff ℝ ∞ (fun a : Space =>
      -(translatedMeanPrimitive T hT a F F₁).adjoint (timeTranslation T a f)) :=
    (((realAdjoint (U := TimeLp T solenoidalSpace) (E := TimeLp T L2)).contDiff.comp hJ).clm_apply
      hf).neg
  have hOb (j a) : ‖iteratedFDeriv ℝ (j+1)
      (fun b : Space => translatedMeanOperator T hT b F F₁ H M0 A L) a‖ ≤
      operatorAmplitude T CF CF₁ CH CM CA L*(Rc^(j+1)*((j+1).factorial : ℝ)^2) := by
    have h := fixedMeanOperator_bound T hT (fun a => translatePath T a F)
      (fun a => translatePath T a F₁) (fun a => translatePath T a H)
      (fun a => translateOperator a M0) (fun a => translateOperator a A) L hF hF₁ hH hM0 hA
      Rc CF CF₁ CH CM CA hRc hCF hCF₁ hCH hCM hCA hFb hF₁b hHb hMb hAb (j+1) a
    simpa only [translatedMeanOperator, operatorAmplitude, majorant, Nat.add_zero] using h
  have hGb (k a) : ‖iteratedFDeriv ℝ k (fun b : Space =>
      -(translatedMeanPrimitive T hT b F F₁).adjoint (timeTranslation T b f)) a‖ ≤
      forcingAmplitude T CF CF₁ Cf*majorant R d k :=
    fixedMeanForcing_bound T hT (fun a => translatePath T a F) (fun a => translatePath T a F₁)
      (fun a => timeTranslation T a f) hF hF₁ hf R CF CF₁ Cf hR0 hCF hCF₁ hCf d hFbr hF₁br hfb k a
  have hout := coerciveSolution_gevrey_amplitudes
    (fun a : Space => translatedMeanOperator T hT a F F₁ H M0 A L) (fun _ => c) (fun _ => hc)
    (fun a => translatedMeanOperator_coercive T hT a F F₁ H M0 A L c hcoercive)
    (fun a : Space => -(translatedMeanPrimitive T hT a F F₁).adjoint (timeTranslation T a f)) hO hG
    c⁻¹ (operatorAmplitude T CF CF₁ CH CM CA L) (forcingAmplitude T CF CF₁ Cf) M Rc R
    (operatorAmplitude_nonneg T CF CF₁ CH CM CA L hT hCH hCM hCA)
    (forcingAmplitude_nonneg T CF CF₁ Cf hT hCF hCF₁ hCf) hM hMC hMD hRc hR (fun _ => le_rfl)
    hOb d hGb n x
  have heq : (fun a : Space => translatedMeanSolver T hT F F₁ H M0 A L c hc hcoercive a
    (timeTranslation T a f)) =
      (fun a : Space => timeSolenoidalTranslation T a
        (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hcoercive
          (-(fixedMeanPrimitive T hT F F₁).adjoint f))) :=
    funext (fun a => translatedMeanSolver_covariance T hT F F₁ H M0 A L c hc hcoercive a f)
  exact (congrArg (fun g : Space → TimeLp T solenoidalSpace => ‖iteratedFDeriv ℝ n g x‖)
    heq.symm).trans_le hout

end EulerMeanTranslatedGevrey
