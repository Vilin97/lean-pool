/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BoundedFlowContinuity
public import LeanPool.NavierStokesAndEuler.Euler.EulerProof

@[expose] public section

/-! A lifted flow tangent to the oscillating graph gives an actual
three-dimensional flow, with inverse and the projected differential
equation. Graph invariance follows from a conserved linear functional. -/

noncomputable section

namespace EulerGraphInvariantFlow

open Set InnerProductSpace ContinuousLinearMap EulerLiftedGradientSpace EulerMetricTransport

def graphLinear (k : ℝ) (m : Vector3) : Vector3 →L[ℝ] LiftTangent :=
  (ContinuousLinearMap.id ℝ Vector3).prod (k • toDual ℝ Vector3 m)

@[simp] theorem graphLinear_apply (k : ℝ) (m x : Vector3) :
    graphLinear k m x = (x,k*inner ℝ m x) := rfl

def graphConstraint (k : ℝ) (m : Vector3) : LiftTangent →L[ℝ] ℝ :=
  snd ℝ Vector3 ℝ - k • (toDual ℝ Vector3 m).comp (fst ℝ Vector3 ℝ)

@[simp] theorem graphConstraint_apply (k : ℝ) (m : Vector3) (z : LiftTangent) :
    graphConstraint k m z = z.2-k*inner ℝ m z.1 := rfl

@[simp] theorem graphConstraint_graph (k : ℝ) (m x : Vector3) :
    graphConstraint k m (graphLinear k m x)=0 := by simp

theorem graphConstraint_transport (k κ : ℝ) (hk : k*κ=1) (m v : Vector3) :
    graphConstraint k m (transportDirection κ m v)=0 := by
  change inner ℝ m v-k*inner ℝ m (κ • v)=0
  rw [inner_smul_right]
  simp only [← mul_assoc,hk,one_mul,sub_self]

variable (k : ℝ) (m : Vector3) (V : EulerBoundedLipschitzFlow.Data LiftTangent)
  (hV : ∀ t z, graphConstraint k m (V.velocity t z)=0)

include hV in
theorem graphConstraint_flow (s t : ℝ) (z : LiftTangent) :
    graphConstraint k m (V.flow s t z)=graphConstraint k m z := by
  have hd (r : ℝ) : HasDerivAt (fun q => graphConstraint k m (V.flow s q z)) 0 r := by
    have h := (graphConstraint k m).hasFDerivAt.comp_hasDerivAt r (V.flow_hasDerivAt s r z)
    rw [hV] at h
    convert! h using 1
  have he := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t s
  simpa only [V.flow_initial] using he

def graphFlow (s t : ℝ) (x : Vector3) : Vector3 := (V.flow s t (graphLinear k m x)).1

include hV in
theorem graphFlow_invariant (s t : ℝ) (x : Vector3) :
    V.flow s t (graphLinear k m x)=graphLinear k m (graphFlow k m V s t x) := by
  have he := graphConstraint_flow k m V hV s t (graphLinear k m x)
  rw [graphConstraint_graph,graphConstraint_apply,sub_eq_zero] at he
  apply Prod.ext
  · rfl
  · exact he

@[simp] theorem graphFlow_initial (s : ℝ) (x : Vector3) : graphFlow k m V s s x=x := by
  simp [graphFlow]

include hV in
theorem graphFlow_inverse (s t : ℝ) (x : Vector3) :
    graphFlow k m V t s (graphFlow k m V s t x)=x := by
  change (V.flow t s (graphLinear k m (graphFlow k m V s t x))).1=x
  rw [← graphFlow_invariant k m V hV,V.flow_inverse]
  rfl

include hV in
theorem graphFlow_hasDerivAt (s t : ℝ) (x : Vector3) :
    HasDerivAt (fun r => graphFlow k m V s r x)
      (V.velocity t (graphLinear k m (graphFlow k m V s t x))).1 t := by
  have hd := (V.flow_hasDerivAt s t (graphLinear k m x)).fst
  rwa [graphFlow_invariant k m V hV] at hd

theorem graphFlow_continuous (s t : ℝ) : Continuous (graphFlow k m V s t) :=
  continuous_fst.comp ((V.flowHomeomorph s t).continuous.comp (graphLinear k m).continuous)

theorem graphFlow_forward_joint_continuous :
    Continuous (fun r : ℝ × Vector3 => graphFlow k m V 0 r.1 r.2) :=
  continuous_fst.comp (V.forward_joint_continuous.comp
    (continuous_fst.prodMk ((graphLinear k m).continuous.comp continuous_snd)))

theorem graphFlow_backward_joint_continuous :
    Continuous (fun r : ℝ × Vector3 => graphFlow k m V r.1 0 r.2) :=
  continuous_fst.comp (V.backward_joint_continuous.comp
    (continuous_fst.prodMk ((graphLinear k m).continuous.comp continuous_snd)))

end EulerGraphInvariantFlow
