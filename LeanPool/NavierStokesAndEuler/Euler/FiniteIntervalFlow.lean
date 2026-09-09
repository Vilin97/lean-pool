/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BoundedFlowContinuity
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

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
