/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoordinatePath
public import LeanPool.NavierStokesAndEuler.Euler.MeanOperatorTranslation
public import LeanPool.NavierStokesAndEuler.Euler.MeanTimeContinuousTranslation
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousAcceleration
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientGevrey
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientRegularity
import LeanPool.NavierStokesAndEuler.Euler.MeanPointwiseGramTranslation
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Uniform-time spatial calculus for the actual physical mean derivative

Multiplication by the actual mean frame commutes with spatial translation.
The continuous physical derivative is the sum of the two actual frame
products, so its smoothness and bounds follow without a new regularity
assumption on the solution.
-/

@[expose] public section


noncomputable section

namespace EulerMeanContinuousPhysical

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanOperatorTranslation EulerMeanVariationalInverse
  EulerMeanTimeContinuousTranslation EulerMeanCoordinatePath
  EulerMeanFixedCoefficientRegularity EulerMeanFixedCoefficientGevrey
  EulerContinuousTimeIntegral EulerContinuousPathCalculus EulerGevrey
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanContinuousPhysical1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanContinuousPhysical2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (solenoidalSpace →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanContinuousPhysical3 : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (solenoidalSpace →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanContinuousPhysical4 : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanContinuousPhysical5 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,L2 →L[ℝ]
    L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanContinuousPhysical6 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,L2 →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,solenoidalSpace →L[ℝ] L2)` instance
to shorten typeclass synthesis. -/
local instance instMeanContinuousPhysical7 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ)
    T,solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,solenoidalSpace →L[ℝ] L2)` instance to
shorten typeclass synthesis. -/
local instance instMeanContinuousPhysical8 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,solenoidalSpace
    →L[ℝ] L2) :=
    inferInstance

variable (T : ℝ) (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (v : C(Icc (0 : ℝ) T, solenoidalSpace))

/-- The actual continuous frame product has the exact translated product orbit. -/
theorem framePathApply_orbit_eq :
    (fun a : Space => pathTranslation T a (multiplier (solenoidalFrame T F) v)) =
      fun a : Space => multiplier (solenoidalFrame T (translatePath T a F))
        (coordinatePathTranslation T a v) := by
  funext a
  apply ContinuousMap.ext
  intro t
  exact (EulerMeanPointwiseGramTranslation.frame_translation a (F t) (v t)).symm

theorem framePathApply_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hv : ContDiff ℝ n (fun a : Space => coordinatePathTranslation T a v)) :
    ContDiff ℝ n (fun a : Space => pathTranslation T a (multiplier (solenoidalFrame T F) v)) :=
  Eq.mpr (congrArg (fun g : Space → C(Icc (0 : ℝ) T,L2) => ContDiff ℝ n g)
    (framePathApply_orbit_eq T F v))
    (contDiff_apply (fun a => solenoidalFrame T (translatePath T a F))
      (fun a => coordinatePathTranslation T a v)
      (contDiff_solenoidalFrame T (fun a => translatePath T a F) hF) hv)

theorem framePathApply_translation_gevrey
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hv : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation T a v))
    (R CF Cv : ℝ) (hR : 0 ≤ R) (hCF : 0 ≤ CF) (hCv : 0 ≤ Cv) (d : ℕ)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant R 0 n)
    (hvb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => coordinatePathTranslation T b v) a‖ ≤
        Cv*majorant R d n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => pathTranslation T b (multiplier (solenoidalFrame T F) v))
        a‖ ≤
      (3*CF*Cv)*majorant R d n := by
  have h := apply_bound (fun b : Space => solenoidalFrame T (translatePath T b F))
    (fun b : Space => coordinatePathTranslation T b v)
    (contDiff_solenoidalFrame T (fun b => translatePath T b F) hF) hv
    R CF Cv hR hCF hCv 0 d
    (solenoidalFrame_bound T (fun b => translatePath T b F) hF R CF hR hCF 0 hFb) hvb n a
  exact (congrArg (fun g : Space → C(Icc (0 : ℝ) T,L2) => ‖iteratedFDeriv ℝ n g a‖)
    (framePathApply_orbit_eq T F v)).trans_le (by simpa only [Nat.zero_add] using h)

end EulerMeanContinuousPhysical

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation EulerMeanCoordinatePath
  EulerMeanContinuousPhysical EulerMeanContinuousAcceleration EulerContinuousTimeIntegral
  EulerOperatorGevreyCalculus EulerTimeLp EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T F t v‖ ^ 2)
  (fC : C(Icc (0 : ℝ) T, L2))

/-- The original continuous physical derivative is exactly its two frame products. -/
theorem classicalPhysicalDerivative_eq_products :
    s.classicalPhysicalDerivative c hc hLower fC =
      multiplier (solenoidalFrame T F₁) s.coordinateVelocityPath +
      multiplier (solenoidalFrame T F) (s.classicalAcceleration c hc hLower fC) := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- The actual continuous coordinate acceleration has a smooth spatial orbit. -/
theorem classicalAcceleration_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ n (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ n (fun a : Space => coordinatePathTranslation T a s.coordinateVelocityPath))
    (hf : ContDiff ℝ n (fun a : Space => pathTranslation T a fC)) :
    ContDiff ℝ n (fun a : Space => coordinatePathTranslation T a (s.classicalAcceleration c hc
        hLower fC)) :=
  meanAccelerationPath_translation_contDiff T F F₁ c hc hLower s.coordinateVelocityPath fC hF hF₁
      hv hf

/-- The actual continuous B_t has a smooth spatial orbit, derived from the constructed acceleration.
-/
theorem classicalPhysicalDerivative_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ n (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ n (fun a : Space => coordinatePathTranslation T a s.coordinateVelocityPath))
    (hf : ContDiff ℝ n (fun a : Space => pathTranslation T a fC)) :
    ContDiff ℝ n (fun a : Space => pathTranslation T a (s.classicalPhysicalDerivative c hc hLower
        fC)) := by
  have he : (fun a : Space => pathTranslation T a (s.classicalPhysicalDerivative c hc hLower fC)) =
      fun a : Space =>
        pathTranslation T a (multiplier (solenoidalFrame T F₁) s.coordinateVelocityPath) +
        pathTranslation T a (multiplier (solenoidalFrame T F) (s.classicalAcceleration c hc hLower
            fC)) := by
    funext a
    exact (congrArg (pathTranslation T a) (s.classicalPhysicalDerivative_eq_products c hc hLower
        fC)).trans
      ((pathTranslation T a).map_add _ _)
  exact Eq.mpr (congrArg (fun g : Space → C(Icc (0 : ℝ) T,L2) => ContDiff ℝ n g) he)
    ((framePathApply_translation_contDiff T F₁ s.coordinateVelocityPath hF₁ hv).add
      (framePathApply_translation_contDiff T F (s.classicalAcceleration c hc hLower fC) hF
        (s.classicalAcceleration_translation_contDiff c hc hLower fC hF hF₁ hv hf)))

/-- Uniform-time derivative estimates pay only the two actual frame-product factors. -/
theorem classicalPhysicalDerivative_translation_gevrey
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation T a s.coordinateVelocityPath))
    (ha : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation T a (s.classicalAcceleration c
        hc hLower fC)))
    (R CF CF₁ Cv Ca : ℝ) (hR : 0 ≤ R) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁)
    (hCv : 0 ≤ Cv) (hCa : 0 ≤ Ca) (d : ℕ)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant R 0 n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant R
        0 n)
    (hvb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => coordinatePathTranslation T b
        s.coordinateVelocityPath) a‖ ≤ Cv*majorant R d n)
    (hab : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => coordinatePathTranslation T b
        (s.classicalAcceleration c hc hLower fC)) a‖ ≤ Ca*majorant R d n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => pathTranslation T b (s.classicalPhysicalDerivative c hc
        hLower fC)) a‖ ≤
      (3*(CF₁*Cv+CF*Ca))*majorant R d n := by
  have he : (fun b : Space => pathTranslation T b (s.classicalPhysicalDerivative c hc hLower fC)) =
      fun b : Space =>
        pathTranslation T b (multiplier (solenoidalFrame T F₁) s.coordinateVelocityPath) +
        pathTranslation T b (multiplier (solenoidalFrame T F) (s.classicalAcceleration c hc hLower
            fC)) := by
    funext b
    exact (congrArg (pathTranslation T b) (s.classicalPhysicalDerivative_eq_products c hc hLower
        fC)).trans
      ((pathTranslation T b).map_add _ _)
  have hb := add_bound
    (fun b : Space => pathTranslation T b (multiplier (solenoidalFrame T F₁)
        s.coordinateVelocityPath))
    (fun b : Space => pathTranslation T b (multiplier (solenoidalFrame T F)
        (s.classicalAcceleration c hc hLower fC)))
    (framePathApply_translation_contDiff T F₁ s.coordinateVelocityPath hF₁ hv)
    (framePathApply_translation_contDiff T F (s.classicalAcceleration c hc hLower fC) hF ha)
    R (3*CF₁*Cv) (3*CF*Ca) d
    (framePathApply_translation_gevrey T F₁ s.coordinateVelocityPath hF₁ hv R CF₁ Cv hR hCF₁ hCv d
        hF₁b hvb)
    (framePathApply_translation_gevrey T F (s.classicalAcceleration c hc hLower fC) hF ha R CF Ca
        hR hCF hCa d hFb hab) n a
  have hcst : 3*CF₁*Cv+3*CF*Ca = 3*(CF₁*Cv+CF*Ca) := by ring
  exact (congrArg (fun g : Space → C(Icc (0 : ℝ) T,L2) => ‖iteratedFDeriv ℝ n g a‖) he).trans_le
    (by simpa only [hcst] using hb)

end EulerMeanVariationalInverse.StrongMeanEvolution
