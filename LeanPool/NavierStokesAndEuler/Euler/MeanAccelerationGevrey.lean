/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanGramTranslation
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpAccelerationForcing
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramGevrey
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientGevrey
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientRegularity
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus

/-!
# Genuine spatial estimates for mean acceleration

The coordinate acceleration is recovered through the actual coercive Gram
inverse. Covariance identifies its parameterized solve with spatial
translation of the original field. Consequently the estimates below concern
the real spatial orbit, with no assumed derivatives of the inverse.
-/

@[expose] public section


noncomputable section

namespace EulerMeanAccelerationGevrey

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanTimeTranslation EulerMeanOperatorTranslation
  EulerMeanVariationalInverse EulerMeanGramTranslation EulerTimeLp EulerVolterraConvolution
  EulerMeanFixedCoefficientRegularity EulerMeanFixedCoefficientGevrey
    EulerTimeLpGramInverse
  EulerTimeLpGramGevrey EulerOperatorGevreyCalculus EulerGevrey
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanAccelerationGevrey1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanAccelerationGevrey2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (solenoidalSpace →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanAccelerationGevrey3 : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (solenoidalSpace →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanAccelerationGevrey4 : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (L2 →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanAccelerationGevrey5 : NormedAddCommGroup (L2 →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ (L2 →L[ℝ] L2)` instance to shorten typeclass synthesis. -/
local instance instMeanAccelerationGevrey6 : NormedSpace ℝ (L2 →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanAccelerationGevrey7 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T, L2 →L[ℝ]
    L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanAccelerationGevrey8 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2)` instance
to shorten typeclass synthesis. -/
local instance instMeanAccelerationGevrey9 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,
    solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2)` instance to
shorten typeclass synthesis. -/
local instance instMeanAccelerationGevrey10 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,
    solenoidalSpace →L[ℝ] L2) :=
    inferInstance

variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T F t v‖ ^ 2)
  (v : TimeLp T solenoidalSpace) (f : TimeLp T L2)

/-- The actual acceleration orbit is the actual translated Gram solve. -/
theorem meanAcceleration_orbit_eq :
    (fun a : Space => timeSolenoidalTranslation T a (meanAcceleration T hT F F₁ c hc hLower v f)) =
    fun a : Space => gramSolver T hT (solenoidalFrame T (translatePath T a F)) c hc
      (translatedFrame_lower T F c hLower a)
      (EulerTimeLpAccelerationForcing.forcing T hT
        (fun b => solenoidalFrame T (translatePath T b F))
        (fun b => solenoidalFrame T (translatePath T b F₁))
        (fun b => timeTranslation T b f) (fun b => timeSolenoidalTranslation T b v) a) :=
  funext (fun a => (meanAcceleration_translate T hT a F F₁ c hc hLower v f).symm)

/-- Actual spatial smoothness passes from the solved coordinate velocity to
the acceleration through the proved Gram inverse. -/
theorem meanAcceleration_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ n (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a v))
    (hf : ContDiff ℝ n (fun a : Space => timeTranslation T a f)) :
    ContDiff ℝ n (fun a : Space =>
      timeSolenoidalTranslation T a (meanAcceleration T hT F F₁ c hc hLower v f)) := by
  let Q := fun a : Space => solenoidalFrame T (translatePath T a F)
  let Q₁ := fun a : Space => solenoidalFrame T (translatePath T a F₁)
  have hQ : ContDiff ℝ n Q := contDiff_solenoidalFrame T (fun a => translatePath T a F) hF
  have hQ₁ : ContDiff ℝ n Q₁ := contDiff_solenoidalFrame T (fun a => translatePath T a F₁) hF₁
  have hg := EulerTimeLpAccelerationForcing.forcing_contDiff T hT Q Q₁
    (fun a => timeTranslation T a f) (fun a => timeSolenoidalTranslation T a v) hQ hQ₁ hf hv
  have hs := gramSolution_contDiff T hT Q c hc (translatedFrame_lower T F c hLower)
    (EulerTimeLpAccelerationForcing.forcing T hT Q Q₁
      (fun a => timeTranslation T a f) (fun a => timeSolenoidalTranslation T a v)) hQ hg
  exact Eq.mpr (congrArg (fun g : Space → TimeLp T solenoidalSpace => ContDiff ℝ n g)
    (meanAcceleration_orbit_eq T hT F F₁ c hc hLower v f)) hs

/-- The genuine acceleration gains one factorial shift relative to its
velocity and forcing inputs, with an explicit polynomial radius condition. -/
theorem meanAcceleration_translation_gevrey
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a v))
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
    (Rc R CF CF₁ Cf Cv : ℝ) (hRc : 0 ≤ Rc) (hR : 0 ≤ R) (hRcR : Rc ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv)
    (hstrong : 2*gramCost c CF (3*CF*(Cf+6*CF₁*Cv))*(Rc+1) ≤ R)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
        n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
        0 n)
    (d : ℕ)
    (hfb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b f) a‖ ≤ Cf*majorant R d
        n)
    (hvb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b v) a‖ ≤
        Cv*majorant R d n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space =>
      timeSolenoidalTranslation T b (meanAcceleration T hT F F₁ c hc hLower v f)) a‖ ≤
        majorant R (d+1) n := by
  let Q := fun b : Space => solenoidalFrame T (translatePath T b F)
  let Q₁ := fun b : Space => solenoidalFrame T (translatePath T b F₁)
  have hQ : ContDiff ℝ ∞ Q := contDiff_solenoidalFrame T (fun b => translatePath T b F) hF
  have hQ₁ : ContDiff ℝ ∞ Q₁ := contDiff_solenoidalFrame T (fun b => translatePath T b F₁) hF₁
  have hbQ : ∀ k b, ‖iteratedFDeriv ℝ k Q b‖ ≤ CF*majorant Rc 0 k :=
    solenoidalFrame_bound T (fun b => translatePath T b F) hF Rc CF hRc hCF 0 hFb
  have hbQ₁ : ∀ k b, ‖iteratedFDeriv ℝ k Q₁ b‖ ≤ CF₁*majorant Rc 0 k :=
    solenoidalFrame_bound T (fun b => translatePath T b F₁) hF₁ Rc CF₁ hRc hCF₁ 0 hF₁b
  have hbQR (k b) : ‖iteratedFDeriv ℝ k Q b‖ ≤ CF*majorant R 0 k :=
    (hbQ k b).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 k) hCF)
  have hbQ₁R (k b) : ‖iteratedFDeriv ℝ k Q₁ b‖ ≤ CF₁*majorant R 0 k :=
    (hbQ₁ k b).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 k) hCF₁)
  let g := EulerTimeLpAccelerationForcing.forcing T hT Q Q₁
    (fun b => timeTranslation T b f) (fun b => timeSolenoidalTranslation T b v)
  have hg : ContDiff ℝ ∞ g := EulerTimeLpAccelerationForcing.forcing_contDiff T hT Q Q₁
    (fun b => timeTranslation T b f) (fun b => timeSolenoidalTranslation T b v) hQ hQ₁ hf hv
  have hgb : ∀ k b, ‖iteratedFDeriv ℝ k g b‖ ≤ (3*CF*(Cf+6*CF₁*Cv))*majorant R d k :=
    EulerTimeLpAccelerationForcing.forcing_bound T hT Q Q₁
      (fun b => timeTranslation T b f) (fun b => timeSolenoidalTranslation T b v)
      hQ hQ₁ hf hv R CF CF₁ Cf Cv hR hCF hCF₁ hCf hCv d hbQR hbQ₁R hfb hvb
  have hs := gramSolution_gevrey T hT Q c hc (translatedFrame_lower T F c hLower) hQ
    Rc CF hRc hCF hbQ g hg (3*CF*(Cf+6*CF₁*Cv)) R (by positivity) hstrong d hgb n a
  exact (congrArg (fun g : Space → TimeLp T solenoidalSpace => ‖iteratedFDeriv ℝ n g a‖)
    (meanAcceleration_orbit_eq T hT F F₁ c hc hLower v f)).trans_le hs

end EulerMeanAccelerationGevrey
