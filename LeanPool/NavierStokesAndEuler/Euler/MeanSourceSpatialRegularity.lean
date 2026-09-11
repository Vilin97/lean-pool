/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousVelocity
public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceFixedInverse
import LeanPool.NavierStokesAndEuler.Euler.MeanAccelerationGevrey
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.Euler.MeanConcreteTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanPhysicalTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanSmoothRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedFrameTransport
public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongEquation

/-!
# Spatial regularity of the actual source mean inverse

Every strong realization of the constructed source solver has the same fixed
coordinate velocity. Its spatial regularity is therefore supplied by the
actual variational inverse, then passed through the proved Gram inverse and
physical frame. No spatial regularity of the unknown fields is assumed.
-/

section

/-!
# Identification of the strong mean velocity with the fixed derivative variable

The actual AC label has its actual L² velocity as derivative and zero terminal
trace. Terminal-primitive uniqueness therefore identifies every strong
realization with the same fixed-coordinate derivative field. Spatial estimates
for the fixed inverse consequently apply to the constructed physical velocity.
-/

@[expose] public section

noncomputable section

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open MeasureTheory Set ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive
  EulerMeanSolenoidal EulerVolterraConvolution EulerTimeH1OperatorProduct

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- The actual strong label is exactly the terminal primitive of its L² velocity. -/
theorem terminalPrimitive_velocityLp (t : Icc (0 : ℝ) T) :
    terminalPrimitive T hT s.velocityLp t = s.label t := by
  have hd : ∀ᵐ r ∂timeMeasure T, HasDerivAt s.label (s.velocityLp r) r := by
    filter_upwards [s.label_derivative, s.velocity_ae] with r hdr hvr
    exact hdr.congr_deriv hvr.symm
  exact (eq_realPrimitive_of_ac_hasDerivAt_ae T hT s.velocityLp s.label
    s.label_ac hd s.terminal t t.property).symm

/-- Differentiating the reconstructed displacement gives the original genuine
variational derivative field. -/
theorem productDerivative_velocityLp
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x) :
    productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F₁) s.velocityLp = u := by
  apply terminalPrimitive_injective T hT
  apply ContinuousMap.ext
  intro t
  have hp := terminalPrimitive_productDerivative T hT (solenoidalFrame T F)
    (solenoidalFrame T F₁) (solenoidalFrame_hasDerivWithinAt T hT F F₁ hF) s.velocityLp t
  have hlabel := (congrArg (F t) (s.label_eq t)).trans (hRight t (realPrimitive T u t))
  exact hp.trans ((congrArg (solenoidalFrame T F t) (s.terminalPrimitive_velocityLp t)).trans
      hlabel)

end EulerMeanVariationalInverse.StrongMeanEvolution

namespace EulerMeanVariationalInverse

open MeasureTheory Set ContinuousLinearMap EulerTimeLp EulerMeanSolenoidal EulerVolterraConvolution

/-- The strong velocity is exactly the canonical fixed-coordinate derivative,
not merely another solution of a similar equation. -/
theorem StrongMeanEvolution.velocityLp_eq_meanBackward
    (T : ℝ) (hT : 0 ≤ T) (FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (A : L2 →L[ℝ] L2) (L : ℝ) (u : meanDerivatives T hT FInv) (f : TimeLp T L2)
    (s : StrongMeanEvolution T hT FInv F F₁ A L (u : TimeLp T L2) f)
    (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x) :
    s.velocityLp = meanBackward T hT FInv F F₁ hInv u := by
  have hforward : meanTestMap T hT FInv F F₁ hF hInv s.velocityLp = u :=
    Subtype.ext (s.productDerivative_velocityLp hF hRight)
  exact (meanBackward_forward T hT FInv F F₁ hInv hF s.velocityLp).symm.trans
    (congrArg (meanBackward T hT FInv F F₁ hInv) hforward)

end EulerMeanVariationalInverse

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanSourceSpatialRegularity

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic EulerMeanSourceInverse
  EulerMeanVariationalInverse EulerMeanSourceFixedInverse
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanGramTranslation EulerMeanAccelerationGevrey EulerTimeLp EulerVolterraConvolution
open scoped NNReal ContDiff

variable (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ)
  (F F₁ H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (operatorPath T F.field t x) = x)
  (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT (operatorPath T F.field))
      (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
  (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), operatorPath T F.field t (FInv t x) = x)
  (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t x v, ⟪H.field t x v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) + Be * T + boundaryLocalizationC2 * Bc * r ^ 3 * T ≤ 1 / 2)
  (f : TimeLp T L2)
  (s : StrongMeanEvolution T hT FInv (operatorPath T F.field) (operatorPath T F₁.field)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L
    (sourceMeanSolver T hT ℓ hℓ M0.field M0.field.continuous.aestronglyMeasurable
      ‖M0.field‖₊ M0.field.norm_coe_le_norm Be Bc L r hBe hBc hL hr hrquarter hext hcore
      FInv (operatorPath T H.field) K hK hF0 (operatorPath_quadratic_upper T H.field K hH) hsmall
          f) f)

include hInv hF hRight

/-- The actual strong velocity is the constructed fixed-coordinate source solve. -/
theorem velocity_eq_sourceCoordinates :
    s.velocityLp = sourceCoordinateSolver T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
      hBe hBc hL hr hrquarter hext hcore hInv hF K hK hF0 hH hsmall f := by
  have hs := StrongMeanEvolution.velocityLp_eq_meanBackward T hT FInv
    (operatorPath T F.field) (operatorPath T F₁.field) (boundaryOperator (scaledCutoff ℓ hℓ)) L
    (sourceMeanSolver T hT ℓ hℓ M0.field M0.field.continuous.aestronglyMeasurable
      ‖M0.field‖₊ M0.field.norm_coe_le_norm Be Bc L r hBe hBc hL hr hrquarter hext hcore
      FInv (operatorPath T H.field) K hK hF0 (operatorPath_quadratic_upper T H.field K hH) hsmall f)
    f s hInv hF hRight
  exact hs.trans (sourceCoordinateSolver_eq_mean T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
    hBe hBc hL hr hrquarter hext hcore hInv hF K hK hF0 hH hsmall hRight f).symm

/-- Actual coordinate-velocity spatial regularity follows from the source assumptions. -/
theorem velocity_translation_contDiff
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f)) :
    ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp) := by
  have heq := velocity_eq_sourceCoordinates T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
    hBe hBc hL hr hrquarter hext hcore hInv hF hRight K hK hF0 hH hsmall f s
  have horbit : (fun a : Space => timeSolenoidalTranslation T a s.velocityLp) =
      fun a : Space => timeSolenoidalTranslation T a
        (sourceCoordinateSolver T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
          hBe hBc hL hr hrquarter hext hcore hInv hF K hK hF0 hH hsmall f) :=
    funext (fun a => congrArg (timeSolenoidalTranslation T a) heq)
  exact Eq.mpr (congrArg (fun g : Space → TimeLp T solenoidalSpace => ContDiff ℝ ∞ g) horbit)
    (sourceCoordinateSolver_translation_contDiff T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
      hBe hBc hL hr hrquarter hext hcore hInv hF K hK hF0 hH hsmall f hf)

/-- The actual acceleration has genuine spatial regularity, supplied by the
uniformly coercive translated Gram solve. -/
theorem acceleration_translation_contDiff
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f)) :
    ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.acceleration) := by
  have hFr : ContDiff ℝ ∞ (fun a : Space => translatePath T a (operatorPath T F.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F
  have hF₁r : ContDiff ℝ ∞ (fun a : Space => translatePath T a (operatorPath T F₁.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F₁
  have hv := velocity_translation_contDiff T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
    hBe hBc hL hr hrquarter hext hcore hInv hF hRight K hK hF0 hH hsmall f s hf
  have heq := s.acceleration_eq_meanAcceleration (meanFrameCoercivity T FInv)
    (meanFrameCoercivity_pos T FInv) (solenoidalFrame_lower T FInv (operatorPath T F.field) hInv)
  have horbit := congrArg (fun v : TimeLp T solenoidalSpace =>
    fun a : Space => timeSolenoidalTranslation T a v) heq
  exact Eq.mpr (congrArg (fun g : Space → TimeLp T solenoidalSpace => ContDiff ℝ ∞ g) horbit)
    (meanAcceleration_translation_contDiff T hT (operatorPath T F.field) (operatorPath T F₁.field)
      (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
      (solenoidalFrame_lower T FInv (operatorPath T F.field) hInv) s.velocityLp f hFr hF₁r hv hf)

/-- Both actual physical fields B and B_t, and their pressure residual, have
smooth spatial translation orbits. -/
theorem physical_translation_contDiff
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f)) :
    ContDiff ℝ ∞ (fun a : Space => timeTranslation T a s.velocityField) ∧
      ContDiff ℝ ∞ (fun a : Space => timeTranslation T a s.velocityDerivative) ∧
      ContDiff ℝ ∞ (fun a : Space => timeTranslation T a s.pressureResidual) := by
  have hFr : ContDiff ℝ ∞ (fun a : Space => translatePath T a (operatorPath T F.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F
  have hF₁r : ContDiff ℝ ∞ (fun a : Space => translatePath T a (operatorPath T F₁.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F₁
  have hv := velocity_translation_contDiff T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
    hBe hBc hL hr hrquarter hext hcore hInv hF hRight K hK hF0 hH hsmall f s hf
  have ha := acceleration_translation_contDiff T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
    hBe hBc hL hr hrquarter hext hcore hInv hF hRight K hK hF0 hH hsmall f s hf
  exact ⟨s.velocityField_translation_contDiff hFr hv,
    s.velocityDerivative_translation_contDiff hFr hF₁r hv ha,
    s.pressureResidual_translation_contDiff hFr hF₁r hv ha hf⟩

/-- The actual reconstructed velocity has a smooth spatial orbit uniformly in time. -/
theorem continuousVelocity_translation_contDiff
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f)) :
    ContDiff ℝ ∞ (fun a : Space => pathTranslation T a s.continuousVelocity) := by
  have hp := physical_translation_contDiff T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
    hBe hBc hL hr hrquarter hext hcore hInv hF hRight K hK hF0 hH hsmall f s hf
  exact s.continuousVelocity_translation_contDiff hp.1 hp.2.1

/-- Every actual time slice, including the initial slice, has a smooth spatial
translation orbit. -/
theorem physicalPath_translation_contDiff (hTpos : 0 < T)
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f)) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun a : Space => translation a (s.physicalPath t)) := by
  have hp := physical_translation_contDiff T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
    hBe hBc hL hr hrquarter hext hcore hInv hF hRight K hK hF0 hH hsmall f s hf
  exact s.physicalPath_translation_contDiff hTpos hF hp.1 hp.2.1 t

/-- Each physical time slice has a genuine smooth representative on ordinary R³. -/
theorem physicalPath_smooth_representative (hTpos : 0 < T)
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f)) (t : Icc (0 : ℝ) T) :
    ∃ b : Space → Space, ContDiff ℝ ∞ b ∧ (s.physicalPath t : Space → Space) =ᵐ[volume] b :=
  EulerMeanSmoothRepresentative.exists_smooth_representative (s.physicalPath t)
    (physicalPath_translation_contDiff T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
      hBe hBc hL hr hrquarter hext hcore hInv hF hRight K hK hF0 hH hsmall f s hTpos hf t)

end EulerMeanSourceSpatialRegularity
