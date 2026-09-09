/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothBanachFlow
public import Mathlib.Algebra.Group.EvenFunction

@[expose] public section

/-! Odd prescribed velocity gives an odd actual Picard flow and inverse.
The symmetry is proved by uniqueness of the genuine ODE solution. -/

noncomputable section

namespace EulerBoundedLipschitzFlow.Data

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (V : EulerBoundedLipschitzFlow.Data E)

theorem flow_odd (ho : ∀ t, Function.Odd (V.velocity t)) (s t : ℝ) : Function.Odd (V.flow s t) := by
  intro x
  have he := V.flow_unique s (-x) (fun r => -V.flow s r x)
    (fun r => by
      rw [ho r]
      exact (V.flow_hasDerivAt s r x).neg)
    (by rw [V.flow_initial])
  exact (congrFun he t).symm

theorem forward_odd (ho : ∀ t, Function.Odd (V.velocity t)) (t : ℝ) :
    Function.Odd (V.forward t) := V.flow_odd ho 0 t

theorem backward_odd (ho : ∀ t, Function.Odd (V.velocity t)) (t : ℝ) :
    Function.Odd (V.backward t) := V.flow_odd ho t 0

end EulerBoundedLipschitzFlow.Data

namespace EulerSmoothBanachFlow

open Set

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)

theorem forward_odd (ho : ∀ t, Function.Odd (A.field t : E → E)) (t : ℝ) :
    Function.Odd ((flowData T hT A).forward t) :=
  (flowData T hT A).forward_odd (fun r => ho (projIcc 0 T hT r)) t

theorem backward_odd (ho : ∀ t, Function.Odd (A.field t : E → E)) (t : ℝ) :
    Function.Odd ((flowData T hT A).backward t) :=
  (flowData T hT A).backward_odd (fun r => ho (projIcc 0 T hT r)) t

end EulerSmoothBanachFlow
