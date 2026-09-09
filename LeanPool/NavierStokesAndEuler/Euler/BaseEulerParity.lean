/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerParent
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketParity
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowParity

/-! Oddness of the genuine base velocity propagates through its actual
flow to the base parent, using ODE uniqueness. -/

@[expose] public section


noncomputable section

namespace EulerBaseEulerParent.Input

open Set EulerSmoothLimit EulerSmoothBanachFlow EulerParentPacketFrames

variable (I : Input)

theorem oddData (hodd : ∀ t, Function.Odd (I.field.field t : Space → Space))
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) : OddData (I.parent ell hell hell1) := by
  have hd (t : Icc (0 : ℝ) I.T) : Function.Odd (I.displacement.field t : Space → Space) := by
    intro x
    rw [I.displacement_apply,I.displacement_apply,forward_odd I.T I.T_pos.le I.field hodd t]
    abel
  exact { displacement := hd }

end EulerBaseEulerParent.Input
