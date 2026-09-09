/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPointwiseGramTranslation
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoordinatePath
public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientGevrey
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousAccelerationGevrey

@[expose] public section

/-!
# Actual spatial orbits of continuous mean acceleration

The ordinary solenoidal Gram inverse commutes with simultaneous translation
of its data. This identifies the parameterized continuous solve with the
genuine spatial orbit of the acceleration, including endpoint times.
-/

noncomputable section

namespace EulerMeanContinuousAcceleration

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanVariationalInverse
  EulerMeanTimeContinuousTranslation EulerMeanCoordinatePath EulerMeanGramTranslation
  EulerMeanFixedCoefficientRegularity EulerMeanFixedCoefficientGevrey
  EulerContinuousGramAcceleration EulerContinuousAccelerationGevrey
  EulerTimeLpGramGevrey EulerGevrey
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

/-- The continuous mean acceleration constructed at each actual time. -/
def meanAccelerationPath : C(Icc (0 : ℝ) T,solenoidalSpace) :=
  accelerationPath T (solenoidalFrame T F) (solenoidalFrame T F₁) c hc hLower v f

/-- The genuine spatial orbit equals the actual solve with translated data. -/
theorem meanAccelerationPath_orbit_eq :
    (fun a : Space => coordinatePathTranslation T a (meanAccelerationPath T F F₁ c hc hLower v f)) =
      fun a : Space => accelerationPath T (solenoidalFrame T (translatePath T a F))
        (solenoidalFrame T (translatePath T a F₁)) c hc (translatedFrame_lower T F c hLower a)
        (coordinatePathTranslation T a v) (pathTranslation T a f) := by
  funext a
  apply ContinuousMap.ext
  intro t
  exact (EulerMeanPointwiseGramTranslation.acceleration_translation a (F t) (F₁ t)
    c hc (hLower t) (v t) (f t)).symm

/-- Smooth coefficient and data orbits give the actual continuous acceleration orbit. -/
theorem meanAccelerationPath_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ n (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ n (fun a : Space => coordinatePathTranslation T a v))
    (hf : ContDiff ℝ n (fun a : Space => pathTranslation T a f)) :
    ContDiff ℝ n (fun a : Space =>
      coordinatePathTranslation T a (meanAccelerationPath T F F₁ c hc hLower v f)) := by
  have hs := acceleration_contDiff T
    (fun a : Space => solenoidalFrame T (translatePath T a F))
    (fun a : Space => solenoidalFrame T (translatePath T a F₁))
    c hc (translatedFrame_lower T F c hLower)
    (fun a : Space => coordinatePathTranslation T a v) (fun a : Space => pathTranslation T a f)
    (contDiff_solenoidalFrame T (fun a => translatePath T a F) hF)
    (contDiff_solenoidalFrame T (fun a => translatePath T a F₁) hF₁) hv hf
  exact Eq.mpr (congrArg (fun g : Space → C(Icc (0 : ℝ) T,solenoidalSpace) => ContDiff ℝ n g)
    (meanAccelerationPath_orbit_eq T F F₁ c hc hLower v f)) hs

/-- All actual spatial acceleration derivatives have a uniform-time bound
with one factorial shift and an explicit polynomial radius condition. -/
theorem meanAccelerationPath_translation_gevrey
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation T a v))
    (hf : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a f))
    (Rc R CF CF₁ Cf Cv : ℝ) (hRc : 0 ≤ Rc) (hR : 0 ≤ R) (hRcR : Rc ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv)
    (hstrong : 2*gramCost c CF (3*CF*(Cf+6*CF₁*Cv))*(Rc+1) ≤ R)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
      n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
      0 n)
    (d : ℕ)
    (hfb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => pathTranslation T b f) a‖ ≤ Cf*majorant R d
      n)
    (hvb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => coordinatePathTranslation T b v) a‖ ≤
      Cv*majorant R d n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space =>
      coordinatePathTranslation T b (meanAccelerationPath T F F₁ c hc hLower v f)) a‖ ≤
      majorant R (d+1) n := by
  have hs := acceleration_gevrey T
    (fun a : Space => solenoidalFrame T (translatePath T a F))
    (fun a : Space => solenoidalFrame T (translatePath T a F₁))
    c hc (translatedFrame_lower T F c hLower)
    (fun a : Space => coordinatePathTranslation T a v) (fun a : Space => pathTranslation T a f)
    (contDiff_solenoidalFrame T (fun a => translatePath T a F) hF)
    (contDiff_solenoidalFrame T (fun a => translatePath T a F₁) hF₁) hv hf
    Rc R CF CF₁ Cf Cv hRc hR hRcR hCF hCF₁ hCf hCv hstrong
    (solenoidalFrame_bound T (fun b => translatePath T b F) hF Rc CF hRc hCF 0 hFb)
    (solenoidalFrame_bound T (fun b => translatePath T b F₁) hF₁ Rc CF₁ hRc hCF₁ 0 hF₁b)
    d hfb hvb n a
  exact (congrArg (fun g : Space → C(Icc (0 : ℝ) T,solenoidalSpace) => ‖iteratedFDeriv ℝ n g a‖)
    (meanAccelerationPath_orbit_eq T F F₁ c hc hLower v f)).trans_le hs

end EulerMeanContinuousAcceleration
