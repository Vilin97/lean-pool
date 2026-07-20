/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.NesterovScheme

/-!
# Motion Error Step 1: Gradient Bound from L-Smoothness

Since π(x'_n) ∈ M and ∇f(π(x'_n)) = 0, L-smoothness gives:
  ‖g_n‖ = ‖∇f(x'_n) - ∇f(π(x'_n))‖ ≤ L · ‖x'_n - π(x'_n)‖ = L · ‖e_n‖

Combined with ‖e_n‖² ≤ C_coer/μ' · L_n from coercivity:
  ‖g_n‖ ≤ L · √(C_coer/μ') · √L_n =: C_g · √L_n
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped NNReal

/-- If gradient is L-Lipschitz on V and ∇f(y) = 0, then ‖∇f(x)‖ ≤ L·‖x - y‖. -/
theorem gradient_bound_from_lipschitz {d : ℕ}
    (f : E d → ℝ) (L : ℝ≥0)
    {V : Set (E d)}
    (hf_lip : LipschitzOnWith L (gradient f) V)
    (x y : E d) (hx_V : x ∈ V) (hy_V : y ∈ V)
    (hzero : gradient f y = 0) :
    ‖gradient f x‖ ≤ (L : ℝ) * ‖x - y‖ := by
  have h := hf_lip.dist_le_mul x hx_V y hy_V
  rw [dist_eq_norm, dist_eq_norm] at h
  simp_all

/-- Velocity bound: ‖v_{n+1}‖ = ‖ρ(v_n - √η g_n)‖ ≤ |ρ|(‖v_n‖ + √η ‖g_n‖). -/
theorem velocity_bound_from_step (v g : E d) (ρ sqrtη : ℝ) :
    ‖ρ • (v - sqrtη • g)‖ ≤ |ρ| * (‖v‖ + |sqrtη| * ‖g‖) := by
  calc ‖ρ • (v - sqrtη • g)‖
      = |ρ| * ‖v - sqrtη • g‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |ρ| * (‖v‖ + ‖sqrtη • g‖) := by
        apply mul_le_mul_of_nonneg_left (norm_sub_le v (sqrtη • g))
        exact abs_nonneg ρ
    _ = |ρ| * (‖v‖ + |sqrtη| * ‖g‖) := by rw [norm_smul, Real.norm_eq_abs]

/-- Step bound: h_n = √η v_{n+1} - η g_n, so ‖h_n‖ ≤ √η‖v_{n+1}‖ + η‖g_n‖. -/
theorem step_bound (v_next g : E d) (sqrtη η : ℝ) :
    ‖sqrtη • v_next - η • g‖ ≤ |sqrtη| * ‖v_next‖ + |η| * ‖g‖ := by
  calc ‖sqrtη • v_next - η • g‖
      ≤ ‖sqrtη • v_next‖ + ‖η • g‖ := norm_sub_le _ _
    _ = |sqrtη| * ‖v_next‖ + |η| * ‖g‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

end PLAcceleratedNesterovLean
