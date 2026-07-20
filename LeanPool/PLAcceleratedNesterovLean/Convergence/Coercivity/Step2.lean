/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.NesterovScheme

/-!
# Coercivity Step 2: Resolve Coupled Bounds on A_n and B_n

Given:
  A ≤ C₁ + B           (from triangle inequality on u_n)
  B ≤ C₂ + a(A + T)    (from quadratic growth + triangle inequality)
  0 ≤ a < 1

We substitute the first into the second to get:
  B ≤ C₂ + a(C₁ + B + T)
  (1 - a)B ≤ C₂ + a·C₁ + a·T
  B ≤ (C₂ + a·C₁ + a·T) / (1 - a)

Then A ≤ C₁ + B gives a bound on A.

Finally:
  A² + B² + T² ≤ C_coer · L_n

Also: Ψ(x_n) ≤ C_Ψ · L_n follows from dist(x_n, M) ≤ √η‖v_n‖ + ‖e_n‖.
-/

noncomputable section

namespace PLAcceleratedNesterovLean

/-- Resolve coupled system: A ≤ c₁ + B, B ≤ c₂ + a*(A + T), with 0 ≤ a < 1.
    Gives B ≤ (c₂ + a*c₁ + a*T)/(1-a). -/
theorem resolve_coupled_bounds (A B T c₁ c₂ a : ℝ)
    (ha_nn : 0 ≤ a) (ha_lt : a < 1)
    (hA : A ≤ c₁ + B)
    (hB : B ≤ c₂ + a * (A + T))
    (_hc₁ : 0 ≤ c₁) (_hc₂ : 0 ≤ c₂) (_hT : 0 ≤ T) :
    B ≤ (c₂ + a * c₁ + a * T) / (1 - a) := by
  have h1 : B ≤ c₂ + a * (c₁ + B + T) := by nlinarith
  have h2 : (1 - a) * B ≤ c₂ + a * c₁ + a * T := by nlinarith
  have h3 : (0 : ℝ) < 1 - a := by linarith
  rw [le_div_iff₀ h3]
  nlinarith

/-- After resolving the coupled system, get a bound on A. -/
theorem resolve_coupled_A_bound (A B c₁ c₂_prime : ℝ)
    (hA : A ≤ c₁ + B)
    (hB : B ≤ c₂_prime)
    (_hc₁ : 0 ≤ c₁) :
    A ≤ c₁ + c₂_prime := by
  linarith

/-- For Ψ: dist(x, M)² ≤ 2(η‖v‖² + ‖e‖²) from (a+b)² ≤ 2(a²+b²). -/
theorem dist_bound_from_v_e (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

end PLAcceleratedNesterovLean
