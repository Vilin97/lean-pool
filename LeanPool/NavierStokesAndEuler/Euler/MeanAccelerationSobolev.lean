/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanGramTranslation
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevAcceleration
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramSobolev
import LeanPool.NavierStokesAndEuler.Euler.MeanAccelerationGevrey
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientGevrey
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientRegularity
import LeanPool.NavierStokesAndEuler.Euler.TimeLpAccelerationSobolev

/-! The genuine mean acceleration estimate in fixed-Hq external word blocks. -/

@[expose] public section


noncomputable section

namespace EulerMeanAccelerationSobolev

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanTimeTranslation EulerMeanOperatorTranslation
  EulerMeanVariationalInverse EulerMeanGramTranslation EulerMeanAccelerationGevrey
  EulerTimeLp EulerVolterraConvolution EulerMeanFixedCoefficientRegularity
  EulerMeanFixedCoefficientGevrey EulerTimeLpGramSobolev EulerTimeLpAccelerationSobolev
  EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanAccelerationSobolev1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanAccelerationSobolev2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (solenoidalSpace →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanAccelerationSobolev3 : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (solenoidalSpace →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanAccelerationSobolev4 : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (L2 →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanAccelerationSobolev5 : NormedAddCommGroup (L2 →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ (L2 →L[ℝ] L2)` instance to shorten typeclass synthesis. -/
local instance instMeanAccelerationSobolev6 : NormedSpace ℝ (L2 →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanAccelerationSobolev7 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T, L2 →L[ℝ]
    L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanAccelerationSobolev8 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)
    := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2)` instance
to shorten typeclass synthesis. -/
local instance instMeanAccelerationSobolev9 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,
    solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2)` instance to
shorten typeclass synthesis. -/
local instance instMeanAccelerationSobolev10 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,
    solenoidalSpace →L[ℝ] L2) :=
    inferInstance


variable {ι : Type*} [Fintype ι]

/-- The actual acceleration of the constructed mean field spends one shift
relative to its input blocks, at the same fixed Sobolev order and radius. -/
theorem meanAcceleration_translation_block_gevrey
    (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (T : ℝ) (hT : 0 ≤ T) (F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (c : ℝ) (hc : 0 < c) (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T F t v‖ ^ 2)
    (v : TimeLp T solenoidalSpace) (f : TimeLp T L2)
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a v))
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
    (Rc R CF CF₁ Cf Cv : ℝ) (hRc : 0 ≤ Rc) (hRcR : sobolevCoefficientRadius ι Rc ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv)
    (hstrong : 2*gramBlockCost ι q c Rc CF (accelerationBlockAmplitude ι q Rc CF CF₁ Cf Cv) *
      (sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
        n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
        0 n)
    (d : ℕ)
    (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation T b f) n a ≤ Cf*majorant R d
        n)
    (hvb : ∀ n a, block directions q (fun b : Space => timeSolenoidalTranslation T b v) n a ≤
        Cv*majorant R d n)
    (n : ℕ) (a : Space) :
    block directions q (fun b : Space =>
      timeSolenoidalTranslation T b (meanAcceleration T hT F F₁ c hc hLower v f)) n a ≤
        majorant R (d+1) n := by
  let Q := fun b : Space => solenoidalFrame T (translatePath T b F)
  let Q₁ := fun b : Space => solenoidalFrame T (translatePath T b F₁)
  have hQ : ContDiff ℝ ∞ Q := contDiff_solenoidalFrame T (fun b => translatePath T b F) hF
  have hQ₁ : ContDiff ℝ ∞ Q₁ := contDiff_solenoidalFrame T (fun b => translatePath T b F₁) hF₁
  have hbQ : ∀ k b, ‖iteratedFDeriv ℝ k Q b‖ ≤ CF*majorant Rc 0 k :=
    solenoidalFrame_bound T (fun b => translatePath T b F) hF Rc CF hRc hCF 0 hFb
  have hbQ₁ : ∀ k b, ‖iteratedFDeriv ℝ k Q₁ b‖ ≤ CF₁*majorant Rc 0 k :=
    solenoidalFrame_bound T (fun b => translatePath T b F₁) hF₁ Rc CF₁ hRc hCF₁ 0 hF₁b
  have hs := solution_block_bound directions hd q T hT Q Q₁ c hc
    (translatedFrame_lower T F c hLower) (fun b => timeTranslation T b f)
    (fun b => timeSolenoidalTranslation T b v) hQ hQ₁ hf hv
    Rc R CF CF₁ Cf Cv hRc hRcR hCF hCF₁ hCf hCv hstrong hbQ hbQ₁ d hfb hvb n a
  exact (congrArg (fun g : Space → TimeLp T solenoidalSpace => block directions q g n a)
    (meanAcceleration_orbit_eq T hT F F₁ c hc hLower v f)).trans_le hs

end EulerMeanAccelerationSobolev
