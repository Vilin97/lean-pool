/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanTranslatedGevrey
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevGevrey
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevProductGevrey

@[expose] public section

/-!
# Genuine fixed-Hq bounds for the constructed mean inverse

The input and output use the same ordered spatial words, the same fixed base
Sobolev order, and the same radius. Only the known coefficient estimates are
converted from tensor bounds. Their finite Sobolev cost is paid once, before
applying the actual inverse recurrence.
-/

noncomputable section

namespace EulerMeanFixedSobolevGevrey

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal EulerTimeLp
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanFixedSpaceInverse
  EulerMeanFixedTranslation EulerMeanTranslatedInverse EulerMeanFixedCoefficientRegularity
  EulerMeanFixedCoefficientGevrey EulerMeanTranslatedGevrey EulerCoerciveProjection
  EulerGevrey EulerOperatorGevreyCalculus EulerTransverseGramInverse
  EulerParameterWordGevrey EulerTerminalTimePrimitive EulerTimeLpCoefficientGevrey
open scoped ContDiff

-- Reuse the nested Hilbert-space instances in the adjoint and inverse estimates.
private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace) := inferInstance

/-- Coefficient-only amplitude of the full mean form in a fixed base order. -/
def operatorBlockAmplitude (ι : Type*) [Fintype ι] (q : ℕ)
    (T Rc CF CF₁ CH CM CA L : ℝ) : ℝ :=
  sobolevCoefficientAmplitude ι q Rc (operatorAmplitude T CF CF₁ CH CM CA L)

/-- Pulling back the right side is a multiplication in the same Sobolev block. -/
def forcingBlockAmplitude (ι : Type*) [Fintype ι] (q : ℕ)
    (T Rc CF CF₁ Cf : ℝ) : ℝ :=
  3*sobolevCoefficientAmplitude ι q Rc (T*(T*CF₁+CF))*Cf

/-- Actual derivatives of the force-pullback operator, before applying it to
any forcing. No forcing derivative is converted to a tensor norm. -/
theorem forcingOperator_bound {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (T : ℝ) (hT : 0 ≤ T)
    (F F₁ : P → C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (hF : ContDiff ℝ ∞ F) (hF₁ : ContDiff ℝ ∞ F₁)
    (Rc CF CF₁ : ℝ) (hRc : 0 ≤ Rc) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁)
    (hFb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ CF*majorant Rc 0 n)
    (hF₁b : ∀ n x, ‖iteratedFDeriv ℝ n F₁ x‖ ≤ CF₁*majorant Rc 0 n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => -(fixedMeanPrimitive T hT (F y) (F₁ y)).adjoint) x‖ ≤
      (T*(T*CF₁+CF))*majorant Rc 0 n := by
  have hD := contDiff_fixedMeanDerivative T hT F F₁ hF hF₁
  have hJ := contDiff_fixedMeanPrimitive T hT F F₁ hF hF₁
  have hD0 : 0 ≤ T*CF₁+CF := by positivity
  have hJb (k : ℕ) (y : P) :
      ‖iteratedFDeriv ℝ k (fun z => fixedMeanPrimitive T hT (F z) (F₁ z)) y‖ ≤
        (T*(T*CF₁+CF))*majorant Rc 0 k := by
    have hb := clm_comp_const_left_bound (primitiveTimeLp (E := L2) T hT)
      (fun z => fixedMeanDerivative T hT (F z) (F₁ z)) hD Rc (T*CF₁+CF) hRc hD0 0
      (fixedMeanDerivative_bound T hT F F₁ hF hF₁ Rc CF CF₁ hRc hCF hCF₁ 0 hFb hF₁b) k y
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (primitive_norm_le_time (E := L2) T hT) hD0)
      (majorant_nonneg Rc hRc 0 k))
  exact neg_bound (fun y => (fixedMeanPrimitive T hT (F y) (F₁ y)).adjoint)
    Rc (T*(T*CF₁+CF)) 0
    (adjoint_bound (fun y => fixedMeanPrimitive T hT (F y) (F₁ y)) hJ
      Rc (T*(T*CF₁+CF)) hRc (by positivity) 0 hJb) n x

variable {ι : Type*} [Fintype ι]
  (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T)
  (F F₁ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L c : ℝ)
  (hc : 0 < c)
  (hcoercive : ∀ v, c*‖v‖^2 ≤ ⟪fixedMeanOperator T hT F F₁ H M0 A L v,v⟫_ℝ)

include hd in
/-- A genuine one-shift fixed-Hq estimate for the spatial orbit of the actual
mean solution, at the identical forcing radius and with grade-independent
constants. The fixed-Hq cost is computed from the original L² inverse. -/
theorem solution_translation_block_gevrey
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
    (hMC : sobolevInverseCost c⁻¹ (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM CA L) q*
      operatorBlockAmplitude ι q T Rc CF CF₁ CH CM CA L ≤ M)
    (hMD : sobolevInverseCost c⁻¹ (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM CA L) q*
      forcingBlockAmplitude ι q T Rc CF CF₁ Cf ≤ M)
    (hR : 2*M*(sobolevCoefficientRadius ι Rc+1) ≤ R)
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
    (d : ℕ) (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation T b f) n a ≤
      Cf*majorant R d n)
    (n : ℕ) (x : Space) :
    block directions q (fun a : Space => timeSolenoidalTranslation T a
      (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hcoercive
        (-(fixedMeanPrimitive T hT F F₁).adjoint f))) n x ≤ majorant R (d+1) n := by
  let O := fun a : Space => translatedMeanOperator T hT a F F₁ H M0 A L
  let J := fun a : Space => -(translatedMeanPrimitive T hT a F F₁).adjoint
  let u := fun a : Space => timeSolenoidalTranslation T a
    (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hcoercive
      (-(fixedMeanPrimitive T hT F F₁).adjoint f))
  let g := fun a : Space => J a (timeTranslation T a f)
  have hO : ContDiff ℝ ∞ O :=
    contDiff_fixedMeanOperator T hT (fun a => translatePath T a F) (fun a => translatePath T a F₁)
      (fun a => translatePath T a H) (fun a => translateOperator a M0) (fun a => translateOperator
        a A)
      L hF hF₁ hH hM0 hA
  have hJ0 : ContDiff ℝ ∞ (fun a : Space => translatedMeanPrimitive T hT a F F₁) :=
    contDiff_fixedMeanPrimitive T hT (fun a => translatePath T a F) (fun a => translatePath T a F₁)
      hF hF₁
  have hJ : ContDiff ℝ ∞ J :=
    ((realAdjoint (U := TimeLp T solenoidalSpace) (E := TimeLp T L2)).contDiff.comp hJ0).neg
  have hu : ContDiff ℝ ∞ u := solution_translation_contDiff T hT F F₁ H M0 A L c hc hcoercive f hO
    hJ0 hf
  have hg : ContDiff ℝ ∞ g := hJ.clm_apply hf
  have heq (a : Space) : O a (u a) = g a := by
    dsimp only [u]
    exact (congrArg (O a)
      (translatedMeanSolver_covariance T hT F F₁ H M0 A L c hc hcoercive a f).symm).trans
        (operator_inverse_apply (O a) c hc
          (translatedMeanOperator_coercive T hT a F F₁ H M0 A L c hcoercive) _)
  have hOb (k a) : ‖iteratedFDeriv ℝ k O a‖ ≤ operatorAmplitude T CF CF₁ CH CM CA L*majorant Rc 0 k
    :=
    fixedMeanOperator_bound T hT (fun a => translatePath T a F)
      (fun a => translatePath T a F₁) (fun a => translatePath T a H)
      (fun a => translateOperator a M0) (fun a => translateOperator a A) L hF hF₁ hH hM0 hA
      Rc CF CF₁ CH CM CA hRc hCF hCF₁ hCH hCM hCA hFb hF₁b hHb hMb hAb k a
  have hJb (k a) : ‖iteratedFDeriv ℝ k J a‖ ≤ (T*(T*CF₁+CF))*majorant Rc 0 k :=
    forcingOperator_bound T hT (fun a => translatePath T a F) (fun a => translatePath T a F₁)
      hF hF₁ Rc CF CF₁ hRc hCF hCF₁ hFb hF₁b k a
  have hO0 := operatorAmplitude_nonneg T CF CF₁ CH CM CA L hT hCH hCM hCA
  have hOA0 : 0 ≤ operatorBlockAmplitude ι q T Rc CF CF₁ CH CM CA L :=
    sobolevCoefficientAmplitude_nonneg q Rc _ hRc hO0
  have hJA0 : 0 ≤ sobolevCoefficientAmplitude ι q Rc (T*(T*CF₁+CF)) :=
    sobolevCoefficientAmplitude_nonneg q Rc _ hRc (by positivity)
  have hD0 : 0 ≤ forcingBlockAmplitude ι q T Rc CF CF₁ Cf := by
    unfold forcingBlockAmplitude
    positivity
  have hr₀ : 0 ≤ sobolevCoefficientRadius ι Rc := sobolevCoefficientRadius_nonneg Rc hRc
  have hrR : sobolevCoefficientRadius ι Rc ≤ R := by nlinarith
  have hbO (k a) := coefficientBlock_of_tensor_bound directions hd q O hO Rc _ hRc hO0 hOb k a
  have hbJ (k a) := coefficientBlock_of_tensor_bound directions hd q J hJ Rc _ hRc
    (show 0 ≤ T*(T*CF₁+CF) by positivity) hJb k a
  have hgb (k a) : block directions q g k a ≤ forcingBlockAmplitude ι q T Rc CF CF₁ Cf*majorant R d
    k :=
    block_clm_apply_gevrey directions q J (fun a => timeTranslation T a f) hJ hf
      (sobolevCoefficientRadius ι Rc) R _ Cf hr₀ hrR hJA0 hCf hbJ d hfb k a
  apply block_inverse_gevrey directions q O u g hO hu hg heq
    (translatedMeanInverse T hT F F₁ H M0 A L c hc hcoercive)
    (fun a v => inverse_operator_apply (O a) c hc
      (translatedMeanOperator_coercive T hT a F F₁ H M0 A L c hcoercive) v)
    c⁻¹ (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM CA L)
    (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM CA L)
    (forcingBlockAmplitude ι q T Rc CF CF₁ Cf) M (sobolevCoefficientRadius ι Rc) R
    hOA0 hD0 hM hMC hMD hr₀ hR
    (translatedMeanInverse_norm T hT F F₁ H M0 A L c hc hcoercive)
    (baseSize_of_tensor_bound directions hd q O hO Rc _ hRc hO0 hOb) _ d hgb n x
  intro j a
  simpa only [majorant, Nat.add_zero, operatorBlockAmplitude] using hbO (j+1) a

end EulerMeanFixedSobolevGevrey
