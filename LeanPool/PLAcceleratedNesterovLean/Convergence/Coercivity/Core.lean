/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.Coercivity.Step2

/-!
# Coercivity Core Bound

Proves that `(1 - a)² * (V² + μ' * E²) ≤ 60 * Ln` by resolving coupled
norm inequalities from the Nesterov accelerated gradient descent analysis.
-/

noncomputable section

namespace PLAcceleratedNesterovLean


theorem coercivity_core_bound
    (T A U E D V s r a μ' Ln : ℝ)
    (ha_nn : 0 ≤ a) (ha_lt1 : a < 1) (_hμ' : 0 < μ')
    (hs_nn : 0 ≤ s) (_hr_nn : 0 ≤ r)
    (hs_sq : s ^ 2 = μ') (hsr : s * r = a)
    (hE_nn : 0 ≤ E) (hU_nn : 0 ≤ U) (hT_nn : 0 ≤ T)
    (hA_nn : 0 ≤ A) (hD_nn : 0 ≤ D) (_hV_nn : 0 ≤ V)
    (hT_le : T ^ 2 ≤ 2 * Ln) (hU_le : U ^ 2 ≤ 2 * Ln)
    (hD_le : μ' * D ^ 2 ≤ 2 * Ln)
    (hv_orth : V ^ 2 = T ^ 2 + A ^ 2)
    (hA_ub : A ≤ U + s * E)
    (hE_ub : E ≤ D + r * V)
    (hV_ub : V ≤ A + T) :
    (1 - a) ^ 2 * (V ^ 2 + μ' * E ^ 2) ≤ 60 * Ln := by
  -- Key facts
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have h1a_sq_le : (1 - a) ^ 2 ≤ 1 := by
    have : (1 - a) ^ 2 = 1 - 2 * a + a ^ 2 := by ring
    have : a ^ 2 ≤ a := by
      calc a ^ 2 = a * a := by ring
        _ ≤ a * 1 := by exact mul_le_mul_of_nonneg_left ha_lt1.le ha_nn
        _ = a := mul_one a
    linarith
  have h1a_sq_nn : (0 : ℝ) ≤ (1 - a) ^ 2 := sq_nonneg _
  -- B = s·E
  set B := s * E with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hs_nn hE_nn
  -- B ≤ s·D + a·(A + T) from triangle
  have hBE : B ≤ s * D + a * (A + T) := by
    calc B = s * E := rfl
      _ ≤ s * (D + r * V) := by
          apply mul_le_mul_of_nonneg_left hE_ub hs_nn
      _ = s * D + s * r * V := by ring
      _ = s * D + a * V := by rw [hsr]
      _ ≤ s * D + a * (A + T) := by
          have : V ≤ A + T := hV_ub
          linarith [mul_le_mul_of_nonneg_left this ha_nn]
  -- Resolve coupled system: A ≤ U + B, B ≤ sD + a(A+T)
  have hB_res := resolve_coupled_bounds A B T U (s * D) a
    ha_nn ha_lt1 hA_ub hBE hU_nn (mul_nonneg hs_nn hD_nn) hT_nn
  have hBr : (1 - a) * B ≤ s * D + a * U + a * T := by
    have h := (le_div_iff₀ h1a).mp hB_res; linarith
  -- Square: ((1-a)B)² = (1-a)²μ'E²
  have hLHS : ((1 - a) * B) ^ 2 = (1 - a) ^ 2 * (μ' * E ^ 2) := by
    rw [hB_def, show μ' = s ^ 2 from hs_sq.symm]; ring
  -- ((1-a)B)² ≤ (sD+aU+aT)²
  have hBr_sq : ((1 - a) * B) ^ 2 ≤ (s * D + a * U + a * T) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (le_of_lt h1a) hB_nn) hBr 2
  -- (sD+aU+aT)² ≤ 3(s²D²+a²U²+a²T²) = 3(μ'D²+a²U²+a²T²)
  have hRHS : (s * D + a * U + a * T) ^ 2 ≤
      3 * (s ^ 2 * D ^ 2 + a ^ 2 * U ^ 2 + a ^ 2 * T ^ 2) := by
    have h1 : 0 ≤ (s * D - a * U) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (s * D - a * T) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (a * U - a * T) ^ 2 := sq_nonneg _
    have e1 : (s * D - a * U) ^ 2 = s^2*D^2 - 2*s*D*a*U + a^2*U^2 := by ring
    have e2 : (s * D - a * T) ^ 2 = s^2*D^2 - 2*s*D*a*T + a^2*T^2 := by ring
    have e3 : (a * U - a * T) ^ 2 = a^2*U^2 - 2*a^2*U*T + a^2*T^2 := by ring
    have lhs : (s * D + a * U + a * T) ^ 2 =
      s^2*D^2 + a^2*U^2 + a^2*T^2 + 2*s*D*a*U + 2*s*D*a*T + 2*a^2*U*T := by ring
    rw [lhs]; linarith [e1 ▸ h1, e2 ▸ h2, e3 ▸ h3]
  -- a²X² ≤ X² from (1-a²)X² ≥ 0
  have ha2U : a ^ 2 * U ^ 2 ≤ U ^ 2 := by
    have : 0 ≤ (1 - a ^ 2) * U ^ 2 :=
      mul_nonneg (by have := mul_le_mul_of_nonneg_left ha_lt1.le ha_nn; linarith [sq_nonneg a])
        (sq_nonneg U)
    linarith
  have ha2T : a ^ 2 * T ^ 2 ≤ T ^ 2 := by
    have : 0 ≤ (1 - a ^ 2) * T ^ 2 :=
      mul_nonneg (by have := mul_le_mul_of_nonneg_left ha_lt1.le ha_nn; linarith [sq_nonneg a])
        (sq_nonneg T)
    linarith
  -- Core: (1-a)²μ'E² ≤ 18Ln
  have he_mult : (1 - a) ^ 2 * (μ' * E ^ 2) ≤ 18 * Ln := by
    have h1 : ((1 - a) * B) ^ 2 ≤ 3 * (s ^ 2 * D ^ 2 + U ^ 2 + T ^ 2) := by
      linarith [hBr_sq, hRHS, ha2U, ha2T]
    rw [hs_sq] at h1
    linarith [hLHS]
  -- A² ≤ 2(U²+μ'E²)
  have hperp_sq : A ^ 2 ≤ 2 * (U ^ 2 + μ' * E ^ 2) := by
    have h1 : A ≤ U + B := hA_ub
    have h1sq : A ^ 2 ≤ (U + B) ^ 2 := sq_le_sq' (by linarith [hA_nn]) h1
    have h2 := dist_bound_from_v_e U B hU_nn hB_nn
    have h3 : B ^ 2 = μ' * E ^ 2 := by rw [hB_def, show μ' = s ^ 2 from hs_sq.symm]; ring
    linarith
  -- (1-a)²·A² ≤ 40Ln
  have hA_mult : (1 - a) ^ 2 * A ^ 2 ≤ 40 * Ln := by
    -- (1-a)²A² ≤ A² ≤ 2(U²+μ'E²) ≤ 2(2Ln + 18Ln/(1-a)²)
    -- Better: (1-a)²A² ≤ (1-a)²·2(U²+μ'E²) = 2(1-a)²U² + 2(1-a)²μ'E²
    --       ≤ 2U² + 2·18Ln = 4Ln + 36Ln = 40Ln
    have step1 : (1 - a) ^ 2 * A ^ 2 ≤
        2 * ((1 - a) ^ 2 * U ^ 2) + 2 * ((1 - a) ^ 2 * (μ' * E ^ 2)) := by
      have : (1 - a) ^ 2 * A ^ 2 ≤ (1 - a) ^ 2 * (2 * (U ^ 2 + μ' * E ^ 2)) :=
        mul_le_mul_of_nonneg_left hperp_sq h1a_sq_nn
      linarith
    have step2 : (1 - a) ^ 2 * U ^ 2 ≤ U ^ 2 :=
      le_of_le_of_eq (mul_le_mul_of_nonneg_right h1a_sq_le (sq_nonneg U)) (one_mul _)
    linarith
  -- (1-a)²T² ≤ 2Ln
  have hT_mult : (1 - a) ^ 2 * T ^ 2 ≤ 2 * Ln := by
    have : (1 - a) ^ 2 * T ^ 2 ≤ 1 * T ^ 2 :=
      mul_le_mul_of_nonneg_right h1a_sq_le (sq_nonneg T)
    linarith
  -- Combine: (1-a)²(V²+μ'E²) = (1-a)²T² + (1-a)²A² + (1-a)²μ'E² ≤ 2+40+18 = 60Ln
  have h_expand : (1 - a) ^ 2 * (V ^ 2 + μ' * E ^ 2) =
      (1 - a) ^ 2 * T ^ 2 + (1 - a) ^ 2 * A ^ 2 + (1 - a) ^ 2 * (μ' * E ^ 2) := by
    rw [hv_orth]; ring
  linarith

end PLAcceleratedNesterovLean
