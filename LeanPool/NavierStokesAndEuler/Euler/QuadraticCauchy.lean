/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-! Strong Cauchy convergence from a quadratic norm estimate in complete-space arguments. -/

@[expose] public section


namespace EulerQuadraticCauchy

open scoped Topology

/-- Replacing three vectors by equal vectors preserves a quadratic norm estimate. -/
theorem transport_quadratic_bound {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    (a b : ℝ) (x x' : X) (y y' : Y) (z z' : Z)
    (hx : x = x') (hy : y = y') (hz : z = z')
    (h : ‖x‖ ^ 2 ≤ a * ‖y‖ ^ 2 + b * ‖z‖ ^ 2) : ‖x'‖^2 ≤ a*‖y'‖^2+b*‖z'‖^2 := by
  subst x'; subst y'; subst z'; exact h

/-- A quadratic norm estimate passes to actual strong limits in three normed spaces. -/
theorem limit_quadratic_bound {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    (U : ℕ → X) (F : ℕ → Y) (V : ℕ → Z) (u : X) (f : Y) (v : Z) (a b : ℝ)
    (hu : Filter.Tendsto U Filter.atTop (𝓝 u))
    (hf : Filter.Tendsto F Filter.atTop (𝓝 f))
    (hv : Filter.Tendsto V Filter.atTop (𝓝 v))
    (hb : ∀ n, ‖V n‖ ^ 2 ≤ a * ‖U n‖ ^ 2 + b * ‖F n‖ ^ 2) : ‖v‖^2 ≤ a*‖u‖^2+b*‖f‖^2 := by
  exact le_of_tendsto_of_tendsto' (hv.norm.pow 2)
    (((hu.norm.pow 2).const_mul a).add ((hf.norm.pow 2).const_mul b)) hb

/-- A sequence whose squared differences are bounded by two Cauchy-sequence differences is Cauchy.
-/
theorem cauchy_of_quadratic_bound {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    (U : ℕ → X) (F : ℕ → Y) (V : ℕ → Z) (a b : ℝ)
    (hu : CauchySeq U) (hf : CauchySeq F)
    (hb : ∀ n m, ‖V n - V m‖ ^ 2 ≤ a * ‖U n - U m‖ ^ 2 + b * ‖F n - F m‖ ^ 2) : CauchySeq V := by
  have hU : Filter.Tendsto (fun p : ℕ×ℕ => ‖U p.1-U p.2‖) Filter.atTop (𝓝 0) := by
    simpa only [dist_eq_norm] using cauchySeq_iff_tendsto_dist_atTop_0.mp hu
  have hF : Filter.Tendsto (fun p : ℕ×ℕ => ‖F p.1-F p.2‖) Filter.atTop (𝓝 0) := by
    simpa only [dist_eq_norm] using cauchySeq_iff_tendsto_dist_atTop_0.mp hf
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  simp only [dist_eq_norm]
  apply squeeze_zero (fun p : ℕ×ℕ => norm_nonneg (V p.1-V p.2)) (fun p : ℕ×ℕ =>
      Real.le_sqrt_of_sq_le (hb p.1 p.2))
  have hlim := ((hU.pow 2).const_mul a).add ((hF.pow 2).const_mul b)
  simpa only [zero_pow (by
      norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, Real.sqrt_zero] using hlim.sqrt

end EulerQuadraticCauchy
