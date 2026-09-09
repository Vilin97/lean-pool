/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowCoefficientPaths
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldComposition
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldBilinear
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldTimeJets
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldDerivativeBounds

@[expose] public section

/-! Actual deformation, first time derivative, and second time derivative
as smooth bounded coefficient paths. Every spatial jet is continuous in
the sup norm; no third time derivative is used for the acceleration. -/

noncomputable section


open scoped ContDiff BoundedContinuousFunction

namespace EulerSmoothBanachFlow

open Set EulerVolterraConvolution EulerSmoothFlowGevrey

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] E) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] E) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E)) := inferInstance
private local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] (E →L[ℝ] E)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] (E →L[ℝ] E)) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ] E))) :=
  inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ] E))) := inferInstance

variable (B R : ℝ) (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B*R*T ≤ 1/8)
  (hb : ∀ n, ‖A.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2)
  (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)

def accelerationCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E E :=
  (A₁.add (SmoothTimeField.bilinear (ContinuousLinearMap.id ℝ (E →L[ℝ] E)) A.derivative
    A)).compDisplacement
    (displacementCoefficient T hT A B R hB hR hsmall hb)

@[simp] theorem accelerationCoefficient_apply (t : Icc (0 : ℝ) T) (x : E) :
    (accelerationCoefficient T hT A B R hB hR hsmall hb A₁).field t x =
      accelerationFamily T hT A A₁ x t := by
  change A₁.field t (x+(displacementCoefficient T hT A B R hB hR hsmall hb).field t x) +
    A.derivative.field t (x+(displacementCoefficient T hT A B R hB hR hsmall hb).field t x)
      (A.field t (x+(displacementCoefficient T hT A B R hB hR hsmall hb).field t x)) = _
  rw [displacementCoefficient_apply]
  have he : x+((flowData T hT A).forward t x-x) = (flowData T hT A).forward t x := by abel
  rw [he]
  change A₁.field t ((flowData T hT A).forward t x) +
    A.derivativeField t ((flowData T hT A).forward t x)
      (A.field t ((flowData T hT A).forward t x)) = _
  rw [A.derivativeField_eq]
  exact (accelerationFamily_apply T hT A A₁ x t).symm

def deformationCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E (E →L[ℝ] E) :=
  (SmoothTimeField.boundConstant (ContinuousLinearMap.id ℝ E)).add
    (displacementCoefficient T hT A B R hB hR hsmall hb).derivative

@[simp] theorem deformationCoefficient_apply (t : Icc (0 : ℝ) T) (x : E) :
    (deformationCoefficient T hT A B R hB hR hsmall hb).field t x =
      fderiv ℝ (fun y => (flowData T hT A).forward t y) x := by
  change ContinuousLinearMap.id ℝ E+
    (displacementCoefficient T hT A B R hB hR hsmall hb).derivativeField t x = _
  rw [SmoothTimeField.derivativeField_eq]
  have he : ((displacementCoefficient T hT A B R hB hR hsmall hb).field t : E → E) =
      fun y => (flowData T hT A).forward t y-y :=
    funext (fun y => displacementCoefficient_apply T hT A B R hB hR hsmall hb t y)
  rw [he]
  have hd : fderiv ℝ (fun y => (flowData T hT A).forward t y-y) x =
      fderiv ℝ (fun y => (flowData T hT A).forward t y) x - ContinuousLinearMap.id ℝ E := by
    simpa only [Pi.sub_def, id_eq, fderiv_id] using
      (fderiv_sub (𝕜 := ℝ) (f := fun y => (flowData T hT A).forward t y) (g := id)
        ((forward_contDiff T hT A t).differentiable (by simp) x) differentiableAt_id)
  rw [hd]
  abel

variable (htime : SmoothTimeField.TimeDerivative T hT A A₁)
  (B₁ R₁ : ℝ) (hB₁ : 0 ≤ B₁) (hR₁ : 0 ≤ R₁)
  (hb₁ : ∀ n, ‖A₁.jet n‖ ≤ B₁*R₁^n*(n.factorial : ℝ)^2)

def deformationTimeCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E (E →L[ℝ] E) :=
  (velocityCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁).derivative

def deformationSecondCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E (E →L[ℝ] E) :=
  (accelerationCoefficient T hT A B R hB hR hsmall hb A₁).derivative

theorem displacementCoefficient_time : SmoothTimeField.TimeDerivative T hT
    (displacementCoefficient T hT A B R hB hR hsmall hb)
    (velocityCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁) := by
  intro t x
  exact displacementFamily_time_derivative T hT A x t

theorem velocityCoefficient_time : SmoothTimeField.TimeDerivative T hT
    (velocityCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁)
    (accelerationCoefficient T hT A B R hB hR hsmall hb A₁) := by
  intro t x
  rw [accelerationCoefficient_apply]
  exact velocityFamily_time_derivative T hT A A₁ htime x t

theorem deformationCoefficient_time : SmoothTimeField.TimeDerivative T hT
    (deformationCoefficient T hT A B R hB hR hsmall hb)
    (deformationTimeCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁) := by
  have hd := SmoothTimeField.TimeDerivative.derivative T hT _ _
    (displacementCoefficient_time T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁)
  intro t x
  exact (hd t x).const_add (ContinuousLinearMap.id ℝ E)

theorem deformationTimeCoefficient_time : SmoothTimeField.TimeDerivative T hT
    (deformationTimeCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁)
    (deformationSecondCoefficient T hT A B R hB hR hsmall hb A₁) :=
  SmoothTimeField.TimeDerivative.derivative T hT _ _
    (velocityCoefficient_time T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁)

end EulerSmoothBanachFlow
