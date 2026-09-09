/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerContinuation

@[expose] public section

/-! The genuine zero Euler solution rules out zero initial data for a
positive finite maximal lifespan. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal

private theorem zeroField_toLp : (zeroField : SmoothL2Field Space).toLp=0 := by
  apply Lp.ext
  filter_upwards [(zeroField : SmoothL2Field Space).toLp_ae,
    Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hx hz
  exact hx.trans hz.symm

/-- The identically zero unforced incompressible Euler solution on any
nonnegative closed time interval, with identically zero pressure force. -/
def zeroEvolution (T : ℝ) (hT : 0 ≤ T) : Evolution T hT where
  velocity _ := zeroField
  pressureForce _ := zeroField
  velocity_continuous _ := continuous_const
  pressure_continuous _ := continuous_const
  solenoidal _ := by
    rw [zeroField_toLp]
    exact solenoidalSpace.zero_mem
  gradient _ := by
    rw [zeroField_toLp]
    exact gradientSpace.zero_mem
  time_law t _ht x := by
    change HasDerivAt (fun _r : ℝ => (0 : Space))
      (-fderiv ℝ (fun _y : Space => (0 : Space)) x 0-0) t
    simpa only [fderiv_const_apply,zero_apply,neg_zero,sub_zero] using
      hasDerivAt_const t (0 : Space)

theorem zero_has_euler (T : ℝ) (hT : 0 < T) :
    HasEulerEvolution (zeroField : SmoothL2Field Space) T :=
  ⟨hT,zeroEvolution T hT.le,rfl⟩

namespace FiniteLifespan

variable {A : SmoothL2Field Space}

/-- A finite maximal lifespan cannot have identically zero initial data. -/
theorem initial_nonzero (L : FiniteLifespan A) : A.field ≠ (0 : Space → Space) := by
  intro hz
  apply L.no_endpoint
  refine ⟨L.duration_pos,zeroEvolution L.duration L.duration_pos.le,?_⟩
  apply field_ext
  exact hz.symm

end FiniteLifespan
end EulerOrdinarySobolev
