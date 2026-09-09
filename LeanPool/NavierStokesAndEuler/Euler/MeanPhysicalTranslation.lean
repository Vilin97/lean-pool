/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanOperatorTranslation
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import LeanPool.NavierStokesAndEuler.Euler.MeanVelocityPressure
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientGevrey
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientRegularity
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientGevrey
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Spatial orbit estimates for the actual physical mean fields

Frame multiplication preserves genuine translation regularity and factorial
bounds. These identities apply to the physical velocity, its actual time
derivative, and the pressure residual constructed by the strong mean solve.
-/

@[expose] public section


noncomputable section

namespace EulerMeanPhysicalTranslation

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanTimeTranslation EulerMeanOperatorTranslation
  EulerMeanVariationalInverse EulerTimeLp EulerVolterraConvolution
  EulerMeanFixedCoefficientRegularity EulerMeanFixedCoefficientGevrey
  EulerTimeLpCoefficientMap EulerTimeLpCoefficientGevrey EulerOperatorGevreyCalculus EulerGevrey
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanPhysicalTranslation1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanPhysicalTranslation2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (solenoidalSpace →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanPhysicalTranslation3 : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (solenoidalSpace →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanPhysicalTranslation4 : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (L2 →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanPhysicalTranslation5 : NormedAddCommGroup (L2 →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ (L2 →L[ℝ] L2)` instance to shorten typeclass synthesis. -/
local instance instMeanPhysicalTranslation6 : NormedSpace ℝ (L2 →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanPhysicalTranslation7 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T, L2 →L[ℝ]
    L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanPhysicalTranslation8 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)
    := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2)` instance
to shorten typeclass synthesis. -/
local instance instMeanPhysicalTranslation9 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,
    solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2)` instance to
shorten typeclass synthesis. -/
local instance instMeanPhysicalTranslation10 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,
    solenoidalSpace →L[ℝ] L2) :=
    inferInstance

variable (T : ℝ) (hT : 0 ≤ T)

/-- The actual spatial orbit of a frame product. -/
theorem frameApply_orbit_eq (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (v : TimeLp T solenoidalSpace) :
    (fun a : Space => timeTranslation T a (timeMultiplier T hT (solenoidalFrame T F) v)) =
      fun a : Space => timeMultiplier T hT (solenoidalFrame T (translatePath T a F))
        (timeSolenoidalTranslation T a v) :=
  funext (fun a => (frameMultiplier_translate T hT a F v).symm)

/-- Genuine spatial regularity survives multiplication by the actual frame. -/
theorem frameApply_translation_contDiff (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (v : TimeLp T solenoidalSpace) {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hv : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a v)) :
    ContDiff ℝ n (fun a : Space =>
      timeTranslation T a (timeMultiplier T hT (solenoidalFrame T F) v)) := by
  have hQ := contDiff_solenoidalFrame T (fun a : Space => translatePath T a F) hF
  have hp := (contDiff_timeMultiplier T hT
    (fun a : Space => solenoidalFrame T (translatePath T a F)) hQ).clm_apply hv
  exact Eq.mpr (congrArg (fun g : Space → TimeLp T L2 => ContDiff ℝ n g)
    (frameApply_orbit_eq T hT F v)) hp

/-- Frame multiplication has one fixed factorial amplitude, independent of order. -/
theorem frameApply_translation_gevrey (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (v : TimeLp T solenoidalSpace)
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a v))
    (R CF Cv : ℝ) (hR : 0 ≤ R) (hCF : 0 ≤ CF) (hCv : 0 ≤ Cv) (d : ℕ)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant R 0 n)
    (hvb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b v) a‖ ≤
        Cv*majorant R d n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space =>
      timeTranslation T b (timeMultiplier T hT (solenoidalFrame T F) v)) a‖ ≤
        (3*CF*Cv)*majorant R d n := by
  let Q := fun b : Space => solenoidalFrame T (translatePath T b F)
  have hQ : ContDiff ℝ ∞ Q := contDiff_solenoidalFrame T (fun b => translatePath T b F) hF
  have hbQ : ∀ k b, ‖iteratedFDeriv ℝ k Q b‖ ≤ CF*majorant R 0 k :=
    solenoidalFrame_bound T (fun b => translatePath T b F) hF R CF hR hCF 0 hFb
  have hp := clm_apply_bound (fun b => timeMultiplier T hT (Q b))
    (fun b => timeSolenoidalTranslation T b v) (contDiff_timeMultiplier T hT Q hQ) hv
    R CF Cv hR hCF hCv 0 d (timeMultiplier_bound T hT Q hQ R CF hR hCF 0 hbQ) hvb n a
  have hp' : ‖iteratedFDeriv ℝ n (fun b : Space =>
      timeMultiplier T hT (Q b) (timeSolenoidalTranslation T b v)) a‖ ≤
      (3*CF*Cv)*majorant R d n := by simpa only [Nat.zero_add] using hp
  exact (congrArg (fun g : Space → TimeLp T L2 => ‖iteratedFDeriv ℝ n g a‖)
    (frameApply_orbit_eq T hT F v)).trans_le hp'

end EulerMeanPhysicalTranslation

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanPhysicalTranslation
  EulerTimeLp EulerVolterraConvolution EulerOperatorGevreyCalculus EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

theorem velocityDerivative_orbit_eq :
    (fun a : Space => timeTranslation T a s.velocityDerivative) =
      fun a : Space => timeTranslation T a (timeMultiplier T hT (solenoidalFrame T F₁)
          s.velocityLp) +
        timeTranslation T a (timeMultiplier T hT (solenoidalFrame T F) s.acceleration) :=
  funext (fun a => (timeTranslation T a).map_add _ _)

theorem pressureResidual_orbit_eq :
    (fun a : Space => timeTranslation T a s.pressureResidual) =
      fun a : Space => timeTranslation T a f -
        timeTranslation T a (timeMultiplier T hT (solenoidalFrame T F) s.acceleration) -
        (2 : ℝ) • timeTranslation T a (timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp) :=
            by
  funext a
  change timeTranslation T a (f-timeMultiplier T hT (solenoidalFrame T F) s.acceleration -
    (2 : ℝ) • timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp) = _
  exact ((timeTranslation T a).map_sub _ _).trans
    (congrArg₂ (fun x y : TimeLp T L2 => x-y)
      ((timeTranslation T a).map_sub _ _)
      ((timeTranslation T a).map_smul (2 : ℝ) _))

/-- The physical velocity has the genuine spatial regularity of the coordinate velocity. -/
theorem velocityField_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hv : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a s.velocityLp)) :
    ContDiff ℝ n (fun a : Space => timeTranslation T a s.velocityField) :=
  frameApply_translation_contDiff T hT F s.velocityLp hF hv

/-- This is spatial regularity of the actual time derivative B_t. -/
theorem velocityDerivative_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ n (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (ha : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a s.acceleration)) :
    ContDiff ℝ n (fun a : Space => timeTranslation T a s.velocityDerivative) :=
  Eq.mpr (congrArg (fun g : Space → TimeLp T L2 => ContDiff ℝ n g) s.velocityDerivative_orbit_eq)
    ((frameApply_translation_contDiff T hT F₁ s.velocityLp hF₁ hv).add
      (frameApply_translation_contDiff T hT F s.acceleration hF ha))

/-- The actual gradient residual inherits the spatial regularity of the solved fields. -/
theorem pressureResidual_translation_contDiff {n : ℕ∞ω}
    (hF : ContDiff ℝ n (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ n (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (ha : ContDiff ℝ n (fun a : Space => timeSolenoidalTranslation T a s.acceleration))
    (hf : ContDiff ℝ n (fun a : Space => timeTranslation T a f)) :
    ContDiff ℝ n (fun a : Space => timeTranslation T a s.pressureResidual) :=
  Eq.mpr (congrArg (fun g : Space → TimeLp T L2 => ContDiff ℝ n g) s.pressureResidual_orbit_eq)
    ((hf.sub (frameApply_translation_contDiff T hT F s.acceleration hF ha)).sub
      ((frameApply_translation_contDiff T hT F₁ s.velocityLp hF₁ hv).const_smul (2 : ℝ)))

/-- A genuine all-order bound for the physical mean velocity. -/
theorem velocityField_translation_gevrey
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (R CF Cv : ℝ) (hR : 0 ≤ R) (hCF : 0 ≤ CF) (hCv : 0 ≤ Cv) (d : ℕ)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant R 0 n)
    (hvb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
        a‖ ≤ Cv*majorant R d n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b s.velocityField) a‖ ≤
      (3*CF*Cv)*majorant R d n :=
  frameApply_translation_gevrey T hT F s.velocityLp hF hv R CF Cv hR hCF hCv d hFb hvb n a

/-- The actual B_t has a fixed polynomial factorial amplitude. -/
theorem velocityDerivative_translation_gevrey
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (ha : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.acceleration))
    (R CF CF₁ Cv Ca : ℝ) (hR : 0 ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCv : 0 ≤ Cv) (hCa : 0 ≤ Ca) (d : ℕ)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant R 0 n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant R
        0 n)
    (hvb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
        a‖ ≤ Cv*majorant R d n)
    (hab : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b
        s.acceleration) a‖ ≤ Ca*majorant R d n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b s.velocityDerivative) a‖ ≤
      (3*(CF₁*Cv+CF*Ca))*majorant R d n := by
  have hvreg := frameApply_translation_contDiff T hT F₁ s.velocityLp hF₁ hv
  have hareg := frameApply_translation_contDiff T hT F s.acceleration hF ha
  have hvb' := frameApply_translation_gevrey T hT F₁ s.velocityLp hF₁ hv
    R CF₁ Cv hR hCF₁ hCv d hF₁b hvb
  have hab' := frameApply_translation_gevrey T hT F s.acceleration hF ha
    R CF Ca hR hCF hCa d hFb hab
  have hs := add_bound
    (fun b : Space => timeTranslation T b (timeMultiplier T hT (solenoidalFrame T F₁) s.velocityLp))
    (fun b : Space => timeTranslation T b (timeMultiplier T hT (solenoidalFrame T F)
        s.acceleration))
    hvreg hareg R (3*CF₁*Cv) (3*CF*Ca) d hvb' hab' n a
  exact ((congrArg (fun g : Space → TimeLp T L2 => ‖iteratedFDeriv ℝ n g a‖)
    s.velocityDerivative_orbit_eq).trans_le hs).trans_eq (by ring)

end EulerMeanVariationalInverse.StrongMeanEvolution
