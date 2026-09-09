/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderCoverDescent
public import LeanPool.NavierStokesAndEuler.Euler.BoundedLipschitzFlow
import LeanPool.NavierStokesAndEuler.Euler.BoundedFlowContinuity
import LeanPool.NavierStokesAndEuler.Euler.BoundedFlowPeriodicity

/-! The actual flow of a periodic cover velocity descends to a genuine
continuous cylinder flow with two-sided inverse. -/

@[expose] public section


noncomputable section

namespace EulerCylinderPeriodicFlow

open Set Function MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent

variable (P : ℝ) [Fact (0 < P)] (V : EulerBoundedLipschitzFlow.Data LiftTangent)
  (hV : ∀ (c : AddSubgroup.zmultiples P) t z,
    V.velocity t (z.1, (c : ℝ) + z.2) = V.velocity t z)

include hV in
omit [Fact (0 < P)] in
theorem flow_deck (s t : ℝ) (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    V.flow s t (z.1,(c : ℝ)+z.2) = ((V.flow s t z).1,(c : ℝ)+(V.flow s t z).2) := by
  have shift (w : LiftTangent) : w+(0,(c : ℝ)) = (w.1,(c : ℝ)+w.2) := by
    apply Prod.ext <;> simp [add_comm]
  have hp : ∀ r w, V.velocity r (w+(0,(c : ℝ)))=V.velocity r w := by
    intro r w
    rw [shift]
    exact hV c r w
  simpa only [shift] using V.flow_add_eq (0,(c : ℝ)) hp s t z

/-- Flow, given by `descendMap P (V.flow s t)`. -/
def flow (s t : ℝ) : LiftDomain P → LiftDomain P := descendMap P (V.flow s t)

include hV in
theorem flow_cover (s t : ℝ) (z : LiftTangent) :
    flow P V s t (coveringMap P z) = coveringMap P (V.flow s t z) :=
  descendMap_cover P (V.flow s t) (flow_deck P V hV s t) z

include hV in
theorem flow_continuous (s t : ℝ) : Continuous (flow P V s t) :=
  descendMap_continuous P (V.flow s t) (flow_deck P V hV s t) (V.flowHomeomorph s t).continuous

include hV in
theorem flow_initial (s : ℝ) (q : LiftDomain P) : flow P V s s q=q := by
  obtain ⟨z,rfl⟩ := (coveringMap_isOpenQuotient P).surjective q
  rw [flow_cover P V hV,V.flow_initial]

include hV in
theorem flow_inverse (s t : ℝ) : Function.LeftInverse (flow P V t s) (flow P V s t) :=
  descendMap_leftInverse P (V.flow s t) (flow_deck P V hV s t)
    (V.flow t s) (flow_deck P V hV t s) (V.flow_inverse s t)

include hV in
theorem flow_cocycle (r s t : ℝ) (q : LiftDomain P) :
    flow P V s t (flow P V r s q)=flow P V r t q := by
  obtain ⟨z,rfl⟩ := (coveringMap_isOpenQuotient P).surjective q
  rw [flow_cover P V hV,flow_cover P V hV,flow_cover P V hV,V.flow_cocycle]

/-- Flow homeomorph, bundling `toFun`, `invFun`, `left_inv`, `right_inv` and the required
compatibility proofs. -/
def flowHomeomorph (s t : ℝ) : LiftDomain P ≃ₜ LiftDomain P where
  toFun := flow P V s t
  invFun := flow P V t s
  left_inv := flow_inverse P V hV s t
  right_inv := flow_inverse P V hV t s
  continuous_toFun := flow_continuous P V hV s t
  continuous_invFun := flow_continuous P V hV t s

include hV in
theorem forward_joint_continuous : Continuous (fun z : ℝ × LiftDomain P => flow P V 0 z.1 z.2) := by
  have hf : Continuous (fun z : ℝ × LiftTangent => coveringMap P (V.forward z.1 z.2)) :=
    (coveringMap_isOpenQuotient P).continuous.comp V.forward_joint_continuous
  exact descend_joint_continuous P (fun t z => coveringMap P (V.forward t z)) hf
    (fun t => map_fiber_constant P (V.flow 0 t) (flow_deck P V hV 0 t))

include hV in
theorem backward_joint_continuous : Continuous (fun z : ℝ × LiftDomain P => flow P V z.1 0 z.2) :=
    by
  have hf : Continuous (fun z : ℝ × LiftTangent => coveringMap P (V.backward z.1 z.2)) :=
    (coveringMap_isOpenQuotient P).continuous.comp V.backward_joint_continuous
  exact descend_joint_continuous P (fun t z => coveringMap P (V.backward t z)) hf
    (fun t => map_fiber_constant P (V.flow t 0) (flow_deck P V hV t 0))

include hV in
theorem flow_measurePreserving (s t : ℝ) (hf : MeasurePreserving (V.flow s t) volume volume) :
    MeasurePreserving (flow P V s t) (liftMeasure P) (liftMeasure P) :=
  descendMap_measurePreserving P (V.flow s t) (flow_deck P V hV s t) hf

end EulerCylinderPeriodicFlow
