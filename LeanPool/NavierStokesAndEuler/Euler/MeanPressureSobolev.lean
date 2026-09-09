/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongSobolev
public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPressure
public import LeanPool.NavierStokesAndEuler.Euler.MeanTimeSobolev
public import LeanPool.NavierStokesAndEuler.Euler.MeanAccelerationSobolev
public import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalSpatialTime
public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongContinuousGevrey

@[expose] public section

/-!
# Fixed-Hq bounds for the actual physical mean pressure force

Starting with the proved weak inverse's one-shift coordinate bound, this
result gives the actual continuous physical field at shift d+2 and its true
within-time derivative at shift d+3. All use the identical external radius.
-/

noncomputable section

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanCoordinatePath EulerMeanContinuousAcceleration EulerMeanContinuousSobolev
  EulerMeanTimeSobolev EulerMeanAccelerationSobolev EulerMeanGramTranslation
  EulerMeanStrongGevrey EulerMeanStrongContinuousGevrey EulerTimeLp EulerVolterraConvolution
  EulerTimeLpGramSobolev EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- The true pressure force retains the same radius and the time-derivative grade d+3. -/
theorem pressure_time_block_bounds {ι : Type*} [Fintype ι]
    (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (hTpos : 0 < T) (c : ℝ) (hc : 0 < c)
    (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
    (fC : C(Icc (0 : ℝ) T,L2))
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC))
    (Rc R CF CF₁ Cf : ℝ) (hRc : 0 ≤ Rc) (hR : 1 ≤ R)
    (hRcR : sobolevCoefficientRadius ι Rc ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf)
    (hstrong : 2*gramBlockCost ι q c Rc CF (accelerationBlockAmplitude ι q Rc CF CF₁ Cf 1)*
      (sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hstrongC : 2*gramBlockCost ι q c Rc CF
      (accelerationBlockAmplitude ι q Rc CF CF₁ Cf (coordinateTraceCost T))*
      (sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
      n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
      0 n)
    (d : ℕ)
    (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation T b f) n a ≤ Cf*majorant R d
      n)
    (hfCb : ∀ n a, block directions q (fun b : Space => pathTranslation T b fC) n a ≤ Cf*majorant R
      d n)
    (hvb : ∀ n a, block directions q (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
      n a ≤ majorant R (d+1) n) :
    (ContDiff ℝ ∞ (fun a : Space => pathTranslation T a (s.pressurePath c hc hLower fC))) ∧
    (∀ n a, block directions q
      (fun b : Space => pathTranslation T b (s.pressurePath c hc hLower fC)) n a ≤
      (Cf+3*sobolevCoefficientAmplitude ι q Rc CF+
        6*sobolevCoefficientAmplitude ι q Rc CF₁*coordinateTraceCost T)*majorant R (d+3) n) := by
  have htrace : 0 ≤ coordinateTraceCost T := coordinateTraceCost_nonneg T hT
  have hf1 (n a) : block directions q (fun b : Space => timeTranslation T b f) n a ≤
      Cf*majorant R (d+1) n :=
    (hfb n a).trans (mul_le_mul_of_nonneg_left (majorant_shift_mono R hR d n) hCf)
  have hv1 (n a) : block directions q (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
    n a ≤
      1*majorant R (d+1) n := by simpa only [one_mul] using hvb n a
  have hat (n a) : block directions q (fun b : Space => timeSolenoidalTranslation T b
    s.acceleration) n a ≤
      majorant R (d+2) n := by
    refine (congrArg (fun v : TimeLp T solenoidalSpace =>
      block directions q (fun b : Space => timeSolenoidalTranslation T b v) n a)
      (s.acceleration_eq_meanAcceleration c hc hLower)).trans_le ?_
    simpa only [Nat.add_assoc] using meanAcceleration_translation_block_gevrey directions hd q
      T hT F F₁ c hc hLower s.velocityLp f hF hF₁ hv hf Rc R CF CF₁ Cf 1
      hRc hRcR hCF hCF₁ hCf zero_le_one hstrong hFb hF₁b (d+1) hf1 hv1 n a
  have ha := s.acceleration_orbit_contDiff c hc hLower hF hF₁ hv hf
  have hv2 (n a) : block directions q (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
    n a ≤
      1*majorant R (d+2) n := by
    simpa only [one_mul] using (hvb n a).trans (majorant_shift_mono R hR (d+1) n)
  have hat1 (n a) : block directions q (fun b : Space => timeSolenoidalTranslation T b
    s.acceleration) n a ≤
      1*majorant R (d+2) n := by simpa only [one_mul] using hat n a
  have hvc := s.coordinateVelocityPath_translation_contDiff hTpos hv ha
  have hvcb (n a) : block directions q (fun b : Space => coordinatePathTranslation T b
    s.coordinateVelocityPath) n a ≤
      coordinateTraceCost T*majorant R (d+2) n := by
    simpa only [mul_one, coordinateTraceCost] using
      s.coordinateVelocityPath_translation_block_gevrey directions q hTpos hv ha R 1 1 (d+2) hv2
        hat1 n a
  have hfc2 (n a) : block directions q (fun b : Space => pathTranslation T b fC) n a ≤
      Cf*majorant R (d+2) n :=
    (hfCb n a).trans (mul_le_mul_of_nonneg_left (majorant_mono_shift R hR d (d+2) n (by omega)) hCf)
  have hac (n a) : block directions q
      (fun b : Space => coordinatePathTranslation T b (s.classicalAcceleration c hc hLower fC)) n a
        ≤
        majorant R (d+3) n := by
    simpa only [Nat.add_assoc, meanAccelerationPath, classicalAcceleration] using
      meanAccelerationPath_translation_block_gevrey
      T F F₁ c hc hLower s.coordinateVelocityPath fC directions hd q hF hF₁ hvc hfC
      Rc R CF CF₁ Cf (coordinateTraceCost T) hRc hRcR hCF hCF₁ hCf htrace
      hstrongC hFb hF₁b (d+2) hfc2 hvcb n a
  have hacs := s.classicalAcceleration_translation_contDiff c hc hLower fC hF hF₁ hvc hfC
  have hvc3 (n a) : block directions q (fun b : Space => coordinatePathTranslation T b
    s.coordinateVelocityPath) n a ≤
      coordinateTraceCost T*majorant R (d+3) n :=
    (hvcb n a).trans (mul_le_mul_of_nonneg_left (majorant_shift_mono R hR (d+2) n) htrace)
  have hac1 (n a) : block directions q
      (fun b : Space => coordinatePathTranslation T b (s.classicalAcceleration c hc hLower fC)) n a
        ≤
        1*majorant R (d+3) n := by simpa only [one_mul] using hac n a
  have hfc3 (n a) : block directions q (fun b : Space => pathTranslation T b fC) n a ≤
      Cf*majorant R (d+3) n :=
    (hfCb n a).trans (mul_le_mul_of_nonneg_left (majorant_mono_shift R hR d (d+3) n (by omega)) hCf)
  refine ⟨s.pressurePath_translation_contDiff c hc hLower fC hF hF₁ hvc hacs hfC, ?_⟩
  intro n a
  simpa only [mul_one] using s.pressurePath_translation_block_gevrey c hc hLower fC
    directions hd q hF hF₁ hvc hacs hfC Rc R CF CF₁ Cf (coordinateTraceCost T) 1
    hRc hRcR hCF hCF₁ htrace zero_le_one (d+3) hFb hF₁b hfc3 hvc3 hac1 n a

end EulerMeanVariationalInverse.StrongMeanEvolution
