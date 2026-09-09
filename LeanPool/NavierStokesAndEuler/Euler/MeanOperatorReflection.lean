/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanTimeReflection
public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedSpaceInverse

@[expose] public section

/-!
# Reflection covariance of the full mean variational inverse

Every identity concerns the real time derivative, terminal primitive, initial
trace, and nonlocal boundary form. Uniqueness of the actual coercive inverse
then transports reflection without an assumed symmetry of a solution.
-/

noncomputable section

namespace EulerMeanFixedReflection

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerMeanSolenoidal
  EulerTimeLp EulerTerminalTimePrimitive EulerMeanTimeReflection EulerVolterraConvolution
  EulerMeanVariationalInverse EulerMeanFixedSpaceInverse EulerTimeH1OperatorProduct
  EulerCoerciveProjection

private local instance : NormedAddCommGroup L2 := inferInstance
private local instance : InnerProductSpace ℝ L2 := inferInstance
private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace) := inferInstance

def ReflectionInvariant (A : L2 →L[ℝ] L2) : Prop :=
  ∀ u, A (reflection u) = reflection (A u)

theorem timeMultiplier_reflection (T : ℝ) (hT : 0 ≤ T)
    (F : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)) (hF : ∀ t, ReflectionInvariant (F t))
    (u : TimeLp T L2) :
    timeMultiplier T hT F (timeReflection T u) = timeReflection T (timeMultiplier T hT F u) := by
  apply Lp.ext
  filter_upwards [timeMultiplier_ae T hT F (timeReflection T u), timeReflection_ae T u,
    timeReflection_ae T (timeMultiplier T hT F u), timeMultiplier_ae T hT F u]
    with t h₁ h₂ h₃ h₄
  exact (h₁.trans (congrArg (F (projIcc 0 T hT t)) h₂)).trans
    ((hF (projIcc 0 T hT t) (u t)).trans ((congrArg reflection h₄).symm.trans h₃.symm))

theorem frameMultiplier_reflection (T : ℝ) (hT : 0 ≤ T)
    (F : C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)) (hF : ∀ t, ReflectionInvariant (F t))
    (u : TimeLp T solenoidalSpace) :
    timeMultiplier T hT (solenoidalFrame T F) (timeSolenoidalReflection T u) =
      timeReflection T (timeMultiplier T hT (solenoidalFrame T F) u) := by
  apply Lp.ext
  filter_upwards [timeMultiplier_ae T hT (solenoidalFrame T F) (timeSolenoidalReflection T u),
    timeSolenoidalReflection_ae T u,
    timeReflection_ae T (timeMultiplier T hT (solenoidalFrame T F) u),
    timeMultiplier_ae T hT (solenoidalFrame T F) u] with t h₁ h₂ h₃ h₄
  have h₂' := congrArg (fun z : solenoidalSpace => (z : L2)) h₂
  change (timeSolenoidalReflection T u t : L2) = reflection (u t : L2) at h₂'
  exact (h₁.trans (congrArg (F (projIcc 0 T hT t)) h₂')).trans
    ((hF (projIcc 0 T hT t) (u t : L2)).trans ((congrArg reflection h₄).symm.trans h₃.symm))


end EulerMeanFixedReflection
