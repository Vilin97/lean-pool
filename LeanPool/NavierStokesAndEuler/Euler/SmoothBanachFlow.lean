/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FiniteIntervalFlow
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeSuperposition
public import LeanPool.NavierStokesAndEuler.Euler.SmoothImplicitLift
public import LeanPool.NavierStokesAndEuler.Euler.LinearFundamentalPath
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelOperator

@[expose] public section

/-!
# Smooth dependence of the constructed flow on its initial position

The actual Picard flow is a continuous family of paths. Its integral
equation is inverted locally on the path Banach space: the derivative is
the genuine Volterra operator, whose two-sided inverse was constructed
from the linear ODE. This proves smooth label dependence at every order.
-/

noncomputable section


open scoped ContDiff BoundedContinuousFunction NNReal

namespace EulerSmoothBanachFlow

open Set EulerContinuousTimeIntegral
  EulerBoundedLipschitzFlow EulerLinearDuhamel

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)

omit [CompleteSpace E] in
theorem velocity_lipschitz (t : Icc (0 : ℝ) T) :
    LipschitzWith ‖A.derivative.field‖₊ (A.field t : E → E) := by
  apply lipschitzWith_of_nnnorm_fderiv_le ((A.smooth t).differentiable (by simp))
  intro x
  apply NNReal.coe_le_coe.mp
  change ‖fderiv ℝ (A.field t : E → E) x‖ ≤ ‖A.derivative.field‖
  rw [← A.derivativeField_eq]
  exact ((A.derivative.field t).norm_coe_le_norm x).trans
    (A.derivative.field.norm_coe_le_norm t)

def flowData : EulerBoundedLipschitzFlow.Data E :=
  ofTimeInterval T hT A.field ‖A.derivative.field‖₊ (velocity_lipschitz T A)

def pathFamily : C(E, C(Icc (0 : ℝ) T, E)) :=
  (⟨fun p : E × Icc (0 : ℝ) T => (flowData T hT A).forward p.2 p.1,
    (flowData T hT A).forward_joint_continuous.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)⟩ :
        C(E × Icc (0 : ℝ) T, E)).curry

@[simp] theorem pathFamily_apply (x : E) (t : Icc (0 : ℝ) T) :
    pathFamily T hT A x t = (flowData T hT A).forward t x := rfl

def pathOperator (u : C(Icc (0 : ℝ) T, E)) : C(Icc (0 : ℝ) T, E) :=
  u - EulerContinuousTimeIntegral.integral T hT (A.superposition u)

theorem pathOperator_contDiff : ContDiff ℝ ∞ (pathOperator T hT A) := by
  have hI := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) T, E)) (F := C(Icc (0 : ℝ) T, E))
    (EulerContinuousTimeIntegral.integral T hT)
  exact contDiff_id.sub (ContDiff.comp
    (g := EulerContinuousTimeIntegral.integral T hT) (f := A.superposition)
    hI A.superposition_contDiff)

theorem pathOperator_hasFDerivAt (u : C(Icc (0 : ℝ) T, E)) :
    HasFDerivAt (pathOperator T hT A)
      (volterraOperator T hT (A.derivative.superposition u)) u := by
  have hI : HasFDerivAt
      (EulerContinuousTimeIntegral.integral T hT :
        C(Icc (0 : ℝ) T, E) → C(Icc (0 : ℝ) T, E))
      (EulerContinuousTimeIntegral.integral T hT) (A.superposition u) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
      (E := C(Icc (0 : ℝ) T, E)) (F := C(Icc (0 : ℝ) T, E))
      (x := A.superposition u) (EulerContinuousTimeIntegral.integral (E := E) T hT)
  exact (hasFDerivAt_id u).sub (HasFDerivAt.comp
    (E := C(Icc (0 : ℝ) T, E)) (F := C(Icc (0 : ℝ) T, E))
    (G := C(Icc (0 : ℝ) T, E)) u hI (A.superposition_hasFDerivAt u))

theorem pathFamily_hasDerivWithinAt (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => (flowData T hT A).forward s x)
      (A.superposition (pathFamily T hT A x) t) (Icc (0 : ℝ) T) t := by
  have h := (flowData T hT A).forward_hasDerivAt t x
  have hv : (flowData T hT A).velocity t ((flowData T hT A).forward t x) =
      A.superposition (pathFamily T hT A x) t := by
    change (ofTimeInterval T hT A.field ‖A.derivative.field‖₊ (velocity_lipschitz T A)).velocity
      t ((flowData T hT A).forward t x) = _
    rw [ofTimeInterval_velocity]
    rfl
  rw [hv] at h
  exact h.hasDerivWithinAt

theorem pathFamily_integral (x : E) :
    pathFamily T hT A x = (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) x +
      EulerContinuousTimeIntegral.integral T hT (A.superposition (pathFamily T hT A x)) := by
  apply ContinuousMap.ext
  intro t
  have h := eq_initial_add_integral T hT (A.superposition (pathFamily T hT A x))
    (fun s => (flowData T hT A).forward s x) (pathFamily_hasDerivWithinAt T hT A x) t
  change (flowData T hT A).forward t x = x +
    EulerContinuousTimeIntegral.integral T hT (A.superposition (pathFamily T hT A x)) t
  simpa only [(flowData T hT A).forward_zero] using h

theorem pathOperator_pathFamily (x : E) :
    pathOperator T hT A (pathFamily T hT A x) =
      (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) x :=
  sub_eq_iff_eq_add.mpr (pathFamily_integral T hT A x)

/-- The actual nonlinear flow has smooth dependence on its initial point,
in the uniform path norm on the whole prescribed time interval. -/
theorem pathFamily_contDiff : ContDiff ℝ ∞ (pathFamily T hT A) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  let U := constructedEvolution T hT (A.derivative.superposition (pathFamily T hT A x))
  have hconst := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := E) (F := C(Icc (0 : ℝ) T, E))
    (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T))
  apply EulerSmoothImplicitLift.contDiffAt_of_identity
    (pathFamily T hT A) (pathOperator T hT A)
    (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) x ∞ (by simp)
    (pathFamily T hT A).continuous.continuousAt (pathOperator_contDiff T hT A).contDiffAt
    hconst.contDiffAt U.volterraEquiv
  · exact pathOperator_hasFDerivAt T hT A (pathFamily T hT A x)
  · exact pathOperator_pathFamily T hT A

theorem forward_contDiff (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun x => (flowData T hT A).forward t x) := by
  exact (ContinuousMap.evalCLM ℝ t).contDiff.comp (pathFamily_contDiff T hT A)

end EulerSmoothBanachFlow
