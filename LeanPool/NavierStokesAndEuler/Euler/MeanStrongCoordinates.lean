/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongEstimates
public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedFrameTransport

@[expose] public section

/-!
# Identification of the strong mean velocity with the fixed derivative variable

The actual AC label has its actual L² velocity as derivative and zero terminal
trace. Terminal-primitive uniqueness therefore identifies every strong
realization with the same fixed-coordinate derivative field. Spatial estimates
for the fixed inverse consequently apply to the constructed physical velocity.
-/

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
