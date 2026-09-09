/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPeriodicFlow
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowVolume

@[expose] public section

/-! A smooth periodic divergence-free cover velocity constructs an actual
volume-preserving cylinder flow with continuous inverse. -/

noncomputable section

namespace EulerSmoothCylinderFlow

open Set MeasureTheory EulerLiftedGradientSpace EulerSmoothBanachFlow

private local instance : Measure.IsAddHaarMeasure (volume : Measure LiftTangent) := by
  change Measure.IsAddHaarMeasure ((volume : Measure Vector3).prod (volume : Measure ℝ))
  infer_instance

variable (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
  (A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
  (hA : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1,(c : ℝ)+z.2)=A.field t z)

include hA in
omit [Fact (0 < P)] in
theorem velocity_deck (c : AddSubgroup.zmultiples P) (t : ℝ) (z : LiftTangent) :
    (flowData T hT A).velocity t (z.1,(c : ℝ)+z.2)=(flowData T hT A).velocity t z :=
  hA c (projIcc 0 T hT t) z

def forward (t : ℝ) : LiftDomain P → LiftDomain P :=
  EulerCylinderPeriodicFlow.flow P (flowData T hT A) 0 t

def backward (t : ℝ) : LiftDomain P → LiftDomain P :=
  EulerCylinderPeriodicFlow.flow P (flowData T hT A) t 0

include hA in
theorem forward_cover (t : ℝ) (z : LiftTangent) :
    forward P T hT A t (coveringMap P z)=coveringMap P ((flowData T hT A).forward t z) :=
  EulerCylinderPeriodicFlow.flow_cover P (flowData T hT A) (velocity_deck P T hT A hA) 0 t z

include hA in
theorem backward_cover (t : ℝ) (z : LiftTangent) :
    backward P T hT A t (coveringMap P z)=coveringMap P ((flowData T hT A).backward t z) :=
  EulerCylinderPeriodicFlow.flow_cover P (flowData T hT A) (velocity_deck P T hT A hA) t 0 z

include hA in
theorem forward_joint_continuous : Continuous (Function.uncurry (forward P T hT A)) :=
  EulerCylinderPeriodicFlow.forward_joint_continuous P (flowData T hT A) (velocity_deck P T hT A hA)

include hA in
theorem backward_joint_continuous : Continuous (Function.uncurry (backward P T hT A)) :=
  EulerCylinderPeriodicFlow.backward_joint_continuous P (flowData T hT A) (velocity_deck P T hT A
    hA)

include hA in
theorem backward_forward (t : ℝ) : Function.LeftInverse (backward P T hT A t) (forward P T hT A t)
  :=
  EulerCylinderPeriodicFlow.flow_inverse P (flowData T hT A) (velocity_deck P T hT A hA) 0 t

include hA in
theorem forward_backward (t : ℝ) : Function.RightInverse (backward P T hT A t) (forward P T hT A t)
  :=
  EulerCylinderPeriodicFlow.flow_inverse P (flowData T hT A) (velocity_deck P T hT A hA) t 0

variable (hdiv : ∀ t x,
  LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent) x).toLinearMap=0)

include hA hdiv in
theorem forward_measurePreserving (t : Icc (0 : ℝ) T) :
    MeasurePreserving (forward P T hT A t) (liftMeasure P) (liftMeasure P) :=
  EulerCylinderPeriodicFlow.flow_measurePreserving P (flowData T hT A) (velocity_deck P T hT A hA)
    0 t
    (EulerSmoothBanachFlow.forward_measurePreserving T hT A hdiv volume t)

include hA hdiv in
theorem backward_measurePreserving (t : Icc (0 : ℝ) T) :
    MeasurePreserving (backward P T hT A t) (liftMeasure P) (liftMeasure P) :=
  EulerCylinderPeriodicFlow.flow_measurePreserving P (flowData T hT A) (velocity_deck P T hT A hA)
    t 0
    (EulerSmoothBanachFlow.backward_measurePreserving T hT A hdiv volume t)

end EulerSmoothCylinderFlow
