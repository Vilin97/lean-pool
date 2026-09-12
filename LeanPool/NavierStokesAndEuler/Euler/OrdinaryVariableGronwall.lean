/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerL2Stability

/-! A variable-coefficient Gronwall estimate from a genuine one-sided
time derivative.  The integrating factor uses the actual time integral. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set EulerVolterraConvolution EulerContinuousTimeIntegral
open scoped Topology

theorem variable_linear_stability (T : ℝ) (hT : 0 ≤ T)
    (X X' : ℝ → ℝ) (C : ℝ) (K : C(Icc (0 : ℝ) T, ℝ))
    (hcont : ContinuousOn X (Icc 0 T))
    (hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt X (X' t) (Icc 0 T) t)
    (hineq : ∀ t ∈ Ico 0 T, X' t ≤ C * extendPath T hT K t * X t)
    (t : Icc (0 : ℝ) T) :
    X t ≤ X 0*Real.exp (C*realIntegral T hT K t) := by
  let I := realIntegral T hT K
  let Y := fun r => X r*Real.exp (-C*I r)
  let Y' := fun r => Real.exp (-C*I r)*(X' r-C*extendPath T hT K r*X r)
  have hI (r : ℝ) : HasDerivAt I (extendPath T hT K r) r :=
    realIntegral_hasDerivAt T hT K r
  have hcI : Continuous I := (show Differentiable ℝ I from
    fun r => (hI r).differentiableAt).continuous
  have hcY : ContinuousOn Y (Icc 0 T) :=
    hcont.mul ((Real.continuous_exp.comp (hcI.const_mul (-C))).continuousOn)
  have hdY (r : ℝ) (hr : r ∈ Ico 0 T) : HasDerivWithinAt Y (Y' r) (Icc 0 T) r := by
    have h := (hder r hr).mul (((hI r).const_mul (-C)).exp.hasDerivWithinAt)
    have he : Y' r = X' r*Real.exp (-C*I r) +
        X r*(Real.exp (-C*I r)*(-C*extendPath T hT K r)) := by
      dsimp [Y']
      ring
    rw [he]
    exact h
  have hbY (r : ℝ) (hr : r ∈ Ico 0 T) : Y' r ≤ 0*Y r := by
    dsimp [Y']
    rw [zero_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (sub_nonpos.mpr (hineq r hr))
  have hy := linear_stability_within Y Y' 0 T hcY hdY hbY t t.property
  have hI0 : I 0=0 := intervalIntegral.integral_same
  have hY0 : Y 0=X 0 := by simp only [Y,hI0,mul_zero,Real.exp_zero,mul_one]
  simp only [hY0,zero_mul,Real.exp_zero,mul_one] at hy
  have he : (X 0*Real.exp (C*I t))*Real.exp (-C*I t)=X 0 := by
    rw [mul_assoc,← Real.exp_add]
    simp only [show C*I t+-C*I t=0 by ring,Real.exp_zero,mul_one]
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (-C*I t))).mp
  change Y t ≤ (X 0*Real.exp (C*I t))*Real.exp (-C*I t)
  rw [he]
  exact hy

end EulerOrdinarySobolev
