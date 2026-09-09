/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerState
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketParity

@[expose] public section

/-! The physical velocity and pressure force inherit the genuine
particle symmetry, so their values vanish at the fixed origin. -/

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set EulerSmoothLimit

variable {A : Parent} (E : Evolution A) (O : OddData A)

include O

theorem velocity_odd (t : Icc (0 : ℝ) A.T) : Function.Odd (fun x => E.velocity (t,x)) := by
  intro x
  change E.velocity (t,-x)= -E.velocity (t,x)
  rw [E.velocity_pullback,E.velocity_pullback,E.inverse.odd O t x,O.velocity t]

theorem force_odd (t : Icc (0 : ℝ) A.T) : Function.Odd (E.force t) := by
  intro x
  rw [E.force_pullback,E.force_pullback,E.inverse.odd O t x,O.acceleration t]

theorem velocity_zero (t : Icc (0 : ℝ) A.T) : E.velocity (t,0)=0 := by
  ext i
  have hi : Function.Odd (fun x : Space => (E.velocity (t,x)) i) :=
    fun x => congrArg (fun v : Space => v i) (E.velocity_odd O t x)
  exact hi.map_zero

theorem force_zero (t : Icc (0 : ℝ) A.T) : E.force t 0=0 := by
  ext i
  have hi : Function.Odd (fun x : Space => (E.force t x) i) :=
    fun x => congrArg (fun v : Space => v i) (E.force_odd O t x)
  exact hi.map_zero

theorem strain_origin (t : Icc (0 : ℝ) A.T) :
    A.strain.field t 0=fderiv ℝ (fun y => E.velocity (t,y)) 0 := by
  rw [E.strain_eq,smul_zero,O.position_zero]

theorem curvature_origin (t : Icc (0 : ℝ) A.T) :
    A.curvature.field t 0=fderiv ℝ (E.force t) 0 := by
  rw [E.curvature_eq,smul_zero,O.position_zero]

end EulerParentPacketFrames.Evolution
