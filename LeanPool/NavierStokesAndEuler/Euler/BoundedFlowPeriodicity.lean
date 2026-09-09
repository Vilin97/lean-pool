/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BoundedLipschitzFlow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-! Periodicity of the prescribed velocity gives exact translation
equivariance of the constructed global flow, by ODE uniqueness. -/

@[expose] public section


noncomputable section

namespace EulerBoundedLipschitzFlow.Data

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (V : EulerBoundedLipschitzFlow.Data E)

theorem flow_add_eq (c : E) (hc : ∀ t x, V.velocity t (x + c) = V.velocity t x)
    (s t : ℝ) (x : E) : V.flow s t (x+c)=V.flow s t x+c := by
  have h := V.flow_unique s (x+c) (fun r => V.flow s r x+c)
    (fun r => by simpa only [hc] using (V.flow_hasDerivAt s r x).add_const c)
    (by rw [V.flow_initial])
  exact (congrFun h t).symm

end EulerBoundedLipschitzFlow.Data
