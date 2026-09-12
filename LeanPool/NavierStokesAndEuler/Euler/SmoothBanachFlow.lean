/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeSuperposition
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelOperator
import LeanPool.NavierStokesAndEuler.Euler.LinearFundamentalPath
import LeanPool.NavierStokesAndEuler.Euler.SmoothImplicitLift
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFlowContinuity
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Smooth dependence of the constructed flow on its initial position

The actual Picard flow is a continuous family of paths. Its integral
equation is inverted locally on the path Banach space: the derivative is
the genuine Volterra operator, whose two-sided inverse was constructed
from the linear ODE. This proves smooth label dependence at every order.
-/

section

/-! Construction of the flow and its continuous inverse from a genuine
bounded continuous velocity on the prescribed finite time interval.
Endpoint extension only defines the auxiliary velocity outside that
interval; all stated ODE identities use the original velocity. -/

@[expose] public section

noncomputable section

open Set Metric
open scoped Topology NNReal BoundedContinuousFunction

namespace EulerBoundedLipschitzFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Of time interval, bundling `velocity`, `continuous`, `lipschitzConstant`, `lipschitz` and
the required compatibility proofs. -/
def ofTimeInterval (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, E →ᵇ E)) (K : ℝ≥0)
    (hLip : ∀ t, LipschitzWith K (u t)) : Data E where
  velocity t x := u (projIcc 0 T hT t) x
  continuous := by fun_prop
  lipschitzConstant := K
  lipschitz t := hLip (projIcc 0 T hT t)
  speedBound := ‖u‖₊
  speed t x := ((u (projIcc 0 T hT t)).norm_coe_le_norm x).trans
    (u.norm_coe_le_norm (projIcc 0 T hT t))

omit [NormedSpace ℝ E] in
@[simp] theorem ofTimeInterval_velocity (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, E →ᵇ E)) (K : ℝ≥0)
    (hLip : ∀ t, LipschitzWith K (u t)) (t : Icc (0 : ℝ) T) (x : E) :
    (ofTimeInterval T hT u K hLip).velocity t x = u t x := by
  simp only [ofTimeInterval, projIcc_of_mem _ t.property]

variable [CompleteSpace E]

/-- The actual finite-time flow has an actual two-sided continuous inverse.
No flow map, inverse map or ODE solution is assumed. -/
theorem exists_flow_and_inverse (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, E →ᵇ E)) (K : ℝ≥0)
    (hLip : ∀ t, LipschitzWith K (u t)) :
    ∃ X Y : ℝ → E → E,
      (∀ x, X 0 x = x) ∧ (∀ x, Y 0 x = x) ∧
      Continuous (Function.uncurry X) ∧ Continuous (Function.uncurry Y) ∧
      (∀ t x, Y t (X t x) = x) ∧ (∀ t x, X t (Y t x) = x) ∧
      (∀ (t : Icc (0 : ℝ) T) x,
        HasDerivAt (fun s => X s x) (u t (X t x)) t) ∧
      (∀ (t : Icc (0 : ℝ) T) x, dist (X t x) x ≤ ‖u‖*|t.1|) := by
  let V := ofTimeInterval T hT u K hLip
  refine ⟨V.forward, V.backward, V.forward_zero, V.backward_zero,
    V.forward_joint_continuous, V.backward_joint_continuous,
    V.backward_forward, V.forward_backward, ?_, ?_⟩
  · intro t x
    have h := V.forward_hasDerivAt t x
    simpa only [V, ofTimeInterval_velocity] using h
  · intro t x
    exact V.forward_displacement t x

end EulerBoundedLipschitzFlow

end
end

end

@[expose] public section

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

/-- Flow data, given by `ofTimeInterval T hT A.field ‖A.derivative.field‖₊ (velocity_lipschitz T
A)`. -/
def flowData : EulerBoundedLipschitzFlow.Data E :=
  ofTimeInterval T hT A.field ‖A.derivative.field‖₊ (velocity_lipschitz T A)

/-- Path family as an element of `C(E, C(Icc (0 : ℝ) T, E))`. -/
def pathFamily : C(E, C(Icc (0 : ℝ) T, E)) :=
  (⟨fun p : E × Icc (0 : ℝ) T => (flowData T hT A).forward p.2 p.1,
    (flowData T hT A).forward_joint_continuous.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)⟩ :
        C(E × Icc (0 : ℝ) T, E)).curry

@[simp] theorem pathFamily_apply (x : E) (t : Icc (0 : ℝ) T) :
    pathFamily T hT A x t = (flowData T hT A).forward t x := rfl

/-- Path operator, given by `u - EulerContinuousTimeIntegral.integral T hT (A.superposition u)`. -/
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
