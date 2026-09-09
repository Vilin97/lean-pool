/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPhysical
public import LeanPool.NavierStokesAndEuler.Euler.MeanPathTimeDerivative

@[expose] public section

/-!
# Classical spatial representatives of the actual mean time evolution

The actual continuous velocity and continuous time derivative have smooth
spatial translation orbits. The bounded time-integral identity commutes
with those spatial derivatives, giving genuine jointly continuous spatial
representatives and their pointwise classical time derivative.
-/

noncomputable section

namespace EulerMeanClassicalSpatialTime

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeContinuousTranslation EulerMeanSmoothRepresentative EulerVolterraConvolution
open scoped ContDiff

/-- Actual smooth representatives of a continuous L² path and its genuine
continuous derivative, with no separate mixed-derivative hypothesis. -/
theorem exists_classical_pair (T : ℝ) (hT : 0 ≤ T)
    (p q : C(Icc (0 : ℝ) T,L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (hq : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a q))
    (hder : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t) :
    ∃ B Bt : Icc (0 : ℝ) T → Space → Space,
      Continuous (fun z : Icc (0 : ℝ) T × Space => B z.1 z.2) ∧
      Continuous (fun z : Icc (0 : ℝ) T × Space => Bt z.1 z.2) ∧
      (∀ t, ContDiff ℝ ∞ (B t)) ∧ (∀ t, ContDiff ℝ ∞ (Bt t)) ∧
      (∀ t, (p t : Space → Space) =ᵐ[volume] B t) ∧
      (∀ t, (q t : Space → Space) =ᵐ[volume] Bt t) ∧
      ∀ t : Icc (0 : ℝ) T, ∀ x : Space,
        HasDerivWithinAt (fun r => B (projIcc 0 T hT r) x) (Bt t x) (Icc (0 : ℝ) T) t := by
  let B := fun t : Icc (0 : ℝ) T =>
    representative (p t) (pathTranslation_evaluation_contDiff T p hp t)
  let Bt := fun t : Icc (0 : ℝ) T =>
    representative (q t) (pathTranslation_evaluation_contDiff T q hq t)
  refine ⟨B, Bt, path_representative_joint_continuous T p hp,
    path_representative_joint_continuous T q hq,
    path_representative_smooth T p hp, path_representative_smooth T q hq,
    path_representative_ae T p hp, path_representative_ae T q hq, ?_⟩
  intro t x
  exact EulerMeanPathTimeDerivative.representative_hasDerivWithinAt T hT p q hder hp hq t x

end EulerMeanClassicalSpatialTime

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanCoordinatePath EulerMeanClassicalSpatialTime EulerVolterraConvolution EulerTimeLp
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c*‖v‖^2 ≤ ‖solenoidalFrame T F t v‖^2)
  (fC : C(Icc (0 : ℝ) T,L2))

/-- The reconstructed velocity path has its actual continuous derivative
at every time, including within-interval endpoint derivatives. -/
theorem continuousVelocity_hasDerivWithinAt (hTpos : 0 < T)
    (hf : (f : ℝ → L2) =ᵐ[timeMeasure T] extendPath T hT fC)
    (hFTime : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT s.continuousVelocity)
      (s.classicalPhysicalDerivative c hc hLower fC t) (Icc (0 : ℝ) T) t := by
  apply (s.physical_hasDerivWithinAt c hc hLower fC hf hFTime t).congr_of_mem _ t.property
  intro r hr
  change s.continuousVelocity (projIcc 0 T hT r) = s.physicalPath r
  rw [projIcc_of_mem hT hr]
  exact s.continuousVelocity_eq_physicalPath hTpos hFTime ⟨r, hr⟩

/-- Genuine space-time classical mean fields are obtained from the actual
solved coordinate velocity and acceleration orbits. -/
theorem exists_classical_spatial_pair (hTpos : 0 < T)
    (hf : (f : ℝ → L2) =ᵐ[timeMeasure T] extendPath T hT fC)
    (hFTime : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (ha : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.acceleration))
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC)) :
    ∃ B Bt : Icc (0 : ℝ) T → Space → Space,
      Continuous (fun z : Icc (0 : ℝ) T × Space => B z.1 z.2) ∧
      Continuous (fun z : Icc (0 : ℝ) T × Space => Bt z.1 z.2) ∧
      (∀ t, ContDiff ℝ ∞ (B t)) ∧ (∀ t, ContDiff ℝ ∞ (Bt t)) ∧
      (∀ t : Icc (0 : ℝ) T, (s.physicalPath t : Space → Space) =ᵐ[volume] B t) ∧
      (∀ t, (s.classicalPhysicalDerivative c hc hLower fC t : Space → Space) =ᵐ[volume] Bt t) ∧
      ∀ t : Icc (0 : ℝ) T, ∀ x : Space,
        HasDerivWithinAt (fun r => B (projIcc 0 T hT r) x) (Bt t x) (Icc (0 : ℝ) T) t := by
  have hp := s.continuousVelocity_translation_contDiff
    (s.velocityField_translation_contDiff hF hv)
    (s.velocityDerivative_translation_contDiff hF hF₁ hv ha)
  have hvc := s.coordinateVelocityPath_translation_contDiff hTpos hv ha
  have hq := s.classicalPhysicalDerivative_translation_contDiff c hc hLower fC hF hF₁ hvc hfC
  obtain ⟨B, Bt, hBc, hBtc, hBs, hBts, hBa, hBta, hd⟩ :=
    exists_classical_pair T hT s.continuousVelocity (s.classicalPhysicalDerivative c hc hLower fC)
      hp hq (s.continuousVelocity_hasDerivWithinAt c hc hLower fC hTpos hf hFTime)
  refine ⟨B, Bt, hBc, hBtc, hBs, hBts, ?_, hBta, hd⟩
  intro t
  rw [← s.continuousVelocity_eq_physicalPath hTpos hFTime t]
  exact hBa t

end EulerMeanVariationalInverse.StrongMeanEvolution
