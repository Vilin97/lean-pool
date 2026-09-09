/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanFrameCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1FrameTransport

@[expose] public section

/-!
# A fixed Hilbert derivative space for the actual mean inverse

The fixed space is `TimeLp T solenoidalSpace`: the terminal condition is built
into its primitive and the initial value is free. Forward transport differentiates
F times that primitive; backward transport uses the constructed Gram left inverse.
These maps are proved inverse, so no parameter-dependent test space is hidden
when comparing translated or differentiated coefficients.
-/

noncomputable section


namespace EulerMeanVariationalInverse

open Set InnerProductSpace ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive
  EulerMeanSolenoidal EulerVolterraConvolution EulerTimeH1OperatorProduct
  EulerTimeH1FrameTransport EulerTransverseGramPath EulerTransverseCoordinateRegularity
  EulerTransverseStrongEstimates

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)

/-- Actual bounded derivative transport back to the fixed solenoidal Hilbert space. -/
def meanBackward : meanDerivatives T hT FInv →L[ℝ] TimeLp T solenoidalSpace :=
  (productDerivative T hT
    (frameLeftInversePath T (solenoidalFrame T F) (meanFrameCoercivity T FInv)
      (meanFrameCoercivity_pos T FInv) (solenoidalFrame_lower T FInv F hInv))
    (frameLeftInverseDerivativePath T (solenoidalFrame T F) (solenoidalFrame T F₁)
      (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
      (solenoidalFrame_lower T FInv F hInv))).comp (meanDerivatives T hT FInv).subtypeL

variable (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)

/-- Forward then backward transport recovers every fixed derivative field. -/
theorem meanBackward_forward (v : TimeLp T solenoidalSpace) :
    meanBackward T hT FInv F F₁ hInv (meanTestMap T hT FInv F F₁ hF hInv v) = v :=
  coordinateDerivative_productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F₁)
    (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
    (solenoidalFrame_lower T FInv F hInv) (solenoidalFrame_hasDerivWithinAt T hT F F₁ hF) v

/-- Backward then forward transport recovers every admissible mean derivative. -/
theorem meanForward_backward
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x)
    (u : meanDerivatives T hT FInv) :
    meanTestMap T hT FInv F F₁ hF hInv (meanBackward T hT FInv F F₁ hInv u) = u := by
  apply Subtype.ext
  exact coordinateDerivative_reconstruct_of_range T hT (solenoidalFrame T F) (solenoidalFrame T F₁)
    (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
    (solenoidalFrame_lower T FInv F hInv) (solenoidalFrame_hasDerivWithinAt T hT F F₁ hF)
    (u : TimeLp T L2) (meanPrimitive_in_frame_range T hT FInv F hRight u)

/-- A genuine continuous linear equivalence to a coefficient-independent mean space. -/
def meanTransportEquiv
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), F t (FInv t x) = x) :
    TimeLp T solenoidalSpace ≃L[ℝ] meanDerivatives T hT FInv where
  toLinearEquiv :=
    { toFun := meanTestMap T hT FInv F F₁ hF hInv
      invFun := meanBackward T hT FInv F F₁ hInv
      left_inv := meanBackward_forward T hT FInv F F₁ hInv hF
      right_inv := meanForward_backward T hT FInv F F₁ hInv hF hRight
      map_add' := map_add _
      map_smul' := map_smul _ }
  continuous_toFun := (meanTestMap T hT FInv F F₁ hF hInv).continuous
  continuous_invFun := (meanBackward T hT FInv F F₁ hInv).continuous

/-- Explicit polynomial transport cost for the mean fixed-space formulation. -/
def meanTransportCost : ℝ :=
  transportCost T (solenoidalFrame T F) (solenoidalFrame T F₁) (meanFrameCoercivity T FInv)

include hT in
/-- The actual transport cost is positive. -/
theorem meanTransportCost_pos : 0 < meanTransportCost T FInv F F₁ :=
  transportCost_pos T hT (solenoidalFrame T F) (solenoidalFrame T F₁)
    (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)

/-- The forward transport retains a quantitative lower kinetic bound. -/
theorem meanForward_norm_sq_lower (v : TimeLp T solenoidalSpace) :
    (meanTransportCost T FInv F F₁)⁻¹^2*‖v‖^2 ≤
      ‖meanTestMap T hT FInv F F₁ hF hInv v‖^2 :=
  productDerivative_norm_sq_lower T hT (solenoidalFrame T F) (solenoidalFrame T F₁)
    (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
    (solenoidalFrame_lower T FInv F hInv) (solenoidalFrame_hasDerivWithinAt T hT F F₁ hF) v

end EulerMeanVariationalInverse
