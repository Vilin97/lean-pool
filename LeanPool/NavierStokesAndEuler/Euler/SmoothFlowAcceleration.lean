/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJets
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
import LeanPool.NavierStokesAndEuler.Euler.SeparatingTimeDerivative
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! The actual acceleration of the constructed nonlinear flow is the
material derivative of its velocity, including the one-sided endpoint
identities. All coefficient time derivatives are literal hypotheses. -/

@[expose] public section


noncomputable section


open scoped ContDiff Topology

namespace EulerSmoothBanachFlow

open Set Filter EulerVolterraConvolution EulerContinuousTimeIntegral

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)

/-- Acceleration family, given by `A₁.superposition (pathFamily T hT A x) + multiplier
(A.derivative.superposition (pathFamily T hT A x)) (velocityFamily T hT A x)`. -/
def accelerationFamily (x : E) : C(Icc (0 : ℝ) T,E) :=
  A₁.superposition (pathFamily T hT A x) +
    multiplier (A.derivative.superposition (pathFamily T hT A x)) (velocityFamily T hT A x)

theorem accelerationFamily_apply (x : E) (t : Icc (0 : ℝ) T) :
    accelerationFamily T hT A A₁ x t =
      A₁.field t ((flowData T hT A).forward t x) +
        fderiv ℝ (A.field t : E → E) ((flowData T hT A).forward t x)
          (A.field t ((flowData T hT A).forward t x)) := by
  change A₁.field t ((flowData T hT A).forward t x) +
    A.derivativeField t ((flowData T hT A).forward t x)
      (A.field t ((flowData T hT A).forward t x)) = _
  rw [A.derivativeField_eq]

theorem pathFamily_time_derivative (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (pathFamily T hT A x))
      (velocityFamily T hT A x t) (Icc (0 : ℝ) T) t := by
  apply (pathFamily_hasDerivWithinAt T hT A x t).congr_of_mem _ t.property
  intro s hs
  simp only [extendPath, projIcc_of_mem hT hs, pathFamily_apply]

theorem velocityFamily_time_derivative_interior
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (x : E) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT (velocityFamily T hT A x))
      (accelerationFamily T hT A A₁ x ⟨t,ht.1.le,ht.2.le⟩) t := by
  have hf := (pathFamily_time_derivative T hT A x ⟨t,ht.1.le,ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  have hd := SmoothTimeField.realField_hasFDerivAt T hT A A₁ htime t ht
    (extendPath T hT (pathFamily T hT A x) t)
  have h := hd.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hf)
  convert h using 1
  · rfl
  · simp only [SmoothTimeField.jointDerivative, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    simp only [SmoothTimeField.realField, extendPath,
      projIcc_of_mem hT ⟨ht.1.le,ht.2.le⟩]
    rfl

theorem velocityFamily_time_derivative
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (velocityFamily T hT A x))
      (accelerationFamily T hT A A₁ x t) (Icc (0 : ℝ) T) t := by
  apply EulerSeparatingTimeDerivative.hasDerivWithinAt T hT
    (velocityFamily T hT A x) (accelerationFamily T hT A A₁ x)
    (fun _ : Unit => ContinuousLinearMap.id ℝ E)
  · intro u v h
    exact congrFun h ()
  · intro _ s hs
    exact velocityFamily_time_derivative_interior T hT A A₁ htime x s hs

theorem forward_second_time_derivative
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => deriv (fun r => (flowData T hT A).forward r x) s)
      (accelerationFamily T hT A A₁ x t) (Icc (0 : ℝ) T) t := by
  apply (velocityFamily_time_derivative T hT A A₁ htime x t).congr_of_mem _ t.property
  intro s hs
  rw [((flowData T hT A).forward_hasDerivAt s x).deriv]
  change (flowData T hT A).velocity s ((flowData T hT A).forward s x) =
    velocityFamily T hT A x (projIcc 0 T hT s)
  rw [projIcc_of_mem hT hs]
  exact EulerBoundedLipschitzFlow.ofTimeInterval_velocity T hT A.field
    ‖A.derivative.field‖₊ (velocity_lipschitz T A) ⟨s,hs⟩ _

end EulerSmoothBanachFlow
