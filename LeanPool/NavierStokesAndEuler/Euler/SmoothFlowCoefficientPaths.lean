/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldFromPaths
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowTimeGevrey
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJoint
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowGevrey
import Mathlib.Algebra.Order.Star.Real

/-! The actual flow displacement and material velocity, with every spatial
jet in the uniform continuous-time bounded-field space. -/

@[expose] public section


noncomputable section


open scoped ContDiff BoundedContinuousFunction

namespace EulerSmoothBanachFlow

open Set EulerVolterraConvolution EulerContinuousTimeIntegral EulerSmoothFlowGevrey

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)
  (B R : ℝ)

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowCoefficientPaths1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instSmoothFlowCoefficientPaths2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowCoefficientPaths3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E))
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowCoefficientPaths4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E)) :=
    inferInstance

variable (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
  (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)

theorem displacementFamily_time_derivative (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (displacementFamily T hT A x))
      (velocityFamily T hT A x t) (Icc (0 : ℝ) T) t := by
  rw [displacementFamily_integral]
  exact integral_hasDerivWithinAt T hT _ t

include hB hR hsmall hb in
theorem displacementFamily_jet_bound (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => displacementFamily T hT A y t) x‖ ≤
      B*T*(4*R)^n*(n.factorial : ℝ)^2 := by
  have he : (fun y => displacementFamily T hT A y t) = displacement T hT A t := by
    funext y
    simp only [displacement, extendPath, projIcc_of_mem hT t.property]
  rw [he]
  apply (displacement_bound T hT A B R hB hR hsmall hb n t t.property x).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left t.property.2 hB)
      (pow_nonneg (by positivity) n)) (sq_nonneg _)

include hB hR hsmall hb in
theorem velocityFamily_jet_bound (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => velocityFamily T hT A y t) x‖ ≤
      B*(flowRadius B R T R)^n*(n.factorial : ℝ)^2 :=
  materialVelocity_bound T hT A B R hB hR hsmall hb n t x

/-- Displacement coefficient, constructed using `SmoothTimeField.ofPathFamily`. -/
def displacementCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E E :=
  SmoothTimeField.ofPathFamily T hT
    (displacementFamily T hT A) (velocityFamily T hT A)
    (displacementFamily_contDiff T hT A) (velocityFamily_contDiff T hT A)
    (displacementFamily_time_derivative T hT A)
    (fun n => B*T*(4*R)^n*(n.factorial : ℝ)^2)
    (fun n => B*(flowRadius B R T R)^n*(n.factorial : ℝ)^2)
    (displacementFamily_jet_bound T hT A B R hB hR hsmall hb)
    (velocityFamily_jet_bound T hT A B R hB hR hsmall hb)

@[simp] theorem displacementCoefficient_apply (t : Icc (0 : ℝ) T) (x : E) :
    (displacementCoefficient T hT A B R hB hR hsmall hb).field t x =
      (flowData T hT A).forward t x-x := rfl

theorem displacementCoefficient_jet_norm (n : ℕ) :
    ‖(displacementCoefficient T hT A B R hB hR hsmall hb).jet n‖ ≤
      B*T*(4*R)^n*(n.factorial : ℝ)^2 := by
  apply SmoothTimeField.ofPathFamily_jet_norm

variable (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)
  (htime : SmoothTimeField.TimeDerivative T hT A A₁)
  (B₁ R₁ : ℝ) (hB₁ : 0 ≤ B₁) (hR₁ : 0 ≤ R₁)
  (hb₁ : ∀ n, ‖A₁.jet n‖ ≤ B₁ * R₁ ^ n * (n.factorial : ℝ) ^ 2)

include hB hR hsmall hb hB₁ hR₁ hb₁ in
theorem accelerationFamily_jet_bound (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => accelerationFamily T hT A A₁ y t) x‖ ≤
      (B₁+3*B^2*R)*(flowRadius B R T (4*R+R₁))^n*(n.factorial : ℝ)^2 := by
  have he : (fun y => accelerationFamily T hT A A₁ y t) =
      materialAcceleration T hT A A₁ t := funext (fun y => accelerationFamily_apply T hT A A₁ y t)
  rw [he]
  exact materialAcceleration_bound T hT A A₁ B R B₁ R₁ hB hR hB₁ hR₁ hsmall hb hb₁ n t x

/-- Velocity coefficient, constructed using `SmoothTimeField.ofPathFamily`. -/
def velocityCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E E :=
  SmoothTimeField.ofPathFamily T hT
    (velocityFamily T hT A) (accelerationFamily T hT A A₁)
    (velocityFamily_contDiff T hT A) (accelerationFamily_contDiff T hT A A₁)
    (velocityFamily_time_derivative T hT A A₁ htime)
    (fun n => B*(flowRadius B R T R)^n*(n.factorial : ℝ)^2)
    (fun n => (B₁+3*B^2*R)*(flowRadius B R T (4*R+R₁))^n*(n.factorial : ℝ)^2)
    (velocityFamily_jet_bound T hT A B R hB hR hsmall hb)
    (accelerationFamily_jet_bound T hT A B R hB hR hsmall hb A₁ B₁ R₁ hB₁ hR₁ hb₁)

@[simp] theorem velocityCoefficient_apply (t : Icc (0 : ℝ) T) (x : E) :
    (velocityCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁).field t x =
      A.field t ((flowData T hT A).forward t x) := rfl

theorem velocityCoefficient_jet_norm (n : ℕ) :
    ‖(velocityCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁).jet n‖ ≤
      B*(flowRadius B R T R)^n*(n.factorial : ℝ)^2 := by
  apply SmoothTimeField.ofPathFamily_jet_norm

end EulerSmoothBanachFlow
