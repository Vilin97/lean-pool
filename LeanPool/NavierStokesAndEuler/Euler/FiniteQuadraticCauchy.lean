/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.QuadraticCauchy

@[expose] public section

/-! Strong Cauchy convergence controlled by finitely many genuine norm observations. -/

namespace EulerQuadraticCauchy

open scoped Topology

/-- A finite family of Cauchy observations controlling squared differences forces a sequence to be Cauchy. -/
theorem cauchy_of_finite_quadratic_bound {X Y Z I : Type*} [Fintype I]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    (U : ℕ → X) (F : I → ℕ → Y) (V : ℕ → Z)
    (hu : CauchySeq U) (hf : ∀ i, CauchySeq (F i))
    (hb : ∀ n m, ‖V n-V m‖^2 ≤ ‖U n-U m‖^2 + ∑ i, ‖F i n-F i m‖^2) : CauchySeq V := by
  have hU : Filter.Tendsto (fun p : ℕ×ℕ => ‖U p.1-U p.2‖^2) Filter.atTop (𝓝 0) := by
    have h := (cauchySeq_iff_tendsto_dist_atTop_0.mp hu).pow 2
    simpa only [dist_eq_norm, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have hF : ∀ i, Filter.Tendsto (fun p : ℕ×ℕ => ‖F i p.1-F i p.2‖^2) Filter.atTop (𝓝 0) := by
    intro i
    have h := (cauchySeq_iff_tendsto_dist_atTop_0.mp (hf i)).pow 2
    simpa only [dist_eq_norm, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have hsum : Filter.Tendsto (fun p : ℕ×ℕ => ∑ i, ‖F i p.1-F i p.2‖^2) Filter.atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hF i)
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  simp only [dist_eq_norm]
  apply squeeze_zero (fun p : ℕ×ℕ => norm_nonneg (V p.1-V p.2))
    (fun p : ℕ×ℕ => Real.le_sqrt_of_sq_le (hb p.1 p.2))
  simpa only [add_zero, Real.sqrt_zero] using (hU.add hsum).sqrt

end EulerQuadraticCauchy
