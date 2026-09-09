/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousAcceleration
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousAccelerationSobolev

@[expose] public section

/-!
# Actual spatial orbits of continuous mean acceleration

The ordinary solenoidal Gram inverse commutes with simultaneous translation
of its data. This identifies the parameterized continuous solve with the
genuine spatial orbit of the acceleration, including endpoint times.
-/

noncomputable section

namespace EulerMeanContinuousSobolev

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanVariationalInverse
  EulerMeanTimeContinuousTranslation EulerMeanCoordinatePath EulerMeanGramTranslation
  EulerMeanFixedCoefficientRegularity EulerMeanFixedCoefficientGevrey
  EulerContinuousGramAcceleration EulerContinuousAccelerationGevrey
  EulerTimeLpGramGevrey EulerGevrey EulerMeanContinuousAcceleration
  EulerParameterWordGevrey EulerTimeLpGramSobolev
open scoped ContDiff

private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance : NormedAddCommGroup (L2 →L[ℝ] L2) := inferInstance
private local instance : NormedSpace ℝ (L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,solenoidalSpace →L[ℝ] L2) :=
  inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,solenoidalSpace →L[ℝ] L2) :=
  inferInstance

variable (T : ℝ) (F F₁ : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2))
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
  (v : C(Icc (0 : ℝ) T,solenoidalSpace)) (f : C(Icc (0 : ℝ) T,L2))

theorem meanAccelerationPath_translation_block_gevrey
    {ι : Type*} [Fintype ι] (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation T a v))
    (hf : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a f))
    (Rc R CF CF₁ Cf Cv : ℝ) (hRc : 0 ≤ Rc) (hRcR : sobolevCoefficientRadius ι Rc ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv)
    (hstrong : 2*gramBlockCost ι q c Rc CF (accelerationBlockAmplitude ι q Rc CF CF₁ Cf
      Cv)*(sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
      n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
      0 n)
    (d : ℕ)
    (hfb : ∀ n a, block directions q (fun b : Space => pathTranslation T b f) n a ≤ Cf*majorant R d
      n)
    (hvb : ∀ n a, block directions q (fun b : Space => coordinatePathTranslation T b v) n a ≤
      Cv*majorant R d n)
    (n : ℕ) (a : Space) :
    block directions q (fun b : Space =>
      coordinatePathTranslation T b (meanAccelerationPath T F F₁ c hc hLower v f)) n a ≤
      majorant R (d+1) n := by
  have hs := EulerContinuousAccelerationSobolev.acceleration_block_bound directions hd q T
    (fun a : Space => solenoidalFrame T (translatePath T a F))
    (fun a : Space => solenoidalFrame T (translatePath T a F₁))
    c hc (translatedFrame_lower T F c hLower)
    (fun a : Space => coordinatePathTranslation T a v) (fun a : Space => pathTranslation T a f)
    (contDiff_solenoidalFrame T (fun a => translatePath T a F) hF)
    (contDiff_solenoidalFrame T (fun a => translatePath T a F₁) hF₁) hv hf
    Rc R CF CF₁ Cf Cv hRc hRcR hCF hCF₁ hCf hCv hstrong
    (solenoidalFrame_bound T (fun b => translatePath T b F) hF Rc CF hRc hCF 0 hFb)
    (solenoidalFrame_bound T (fun b => translatePath T b F₁) hF₁ Rc CF₁ hRc hCF₁ 0 hF₁b)
    d hfb hvb n a
  exact (congrArg (fun g : Space → C(Icc (0 : ℝ) T,solenoidalSpace) => block directions q g n a)
    (meanAccelerationPath_orbit_eq T F F₁ c hc hLower v f)).trans_le hs

end EulerMeanContinuousSobolev
