/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132WeiE2.Algebra.TrigSigns

/-!
# Tangent expressions for the E2 parametrization

This module rewrites the relevant angles into the half-angle forms used by the algebraic proof.
-/

namespace LeanPool.Erdos132WeiE2.Algebra

lemma cos_A_as_half (A : ℝ) :
    Real.cos A = 2 * Real.cos (A / 2) ^ 2 - 1 := by
  calc
    Real.cos A = Real.cos (2 * (A / 2)) := by congr 1; ring
    _ = _ := Real.cos_two_mul (A / 2)

lemma sin_A_as_half (A : ℝ) :
    Real.sin A = 2 * Real.sin (A / 2) * Real.cos (A / 2) := by
  calc
    Real.sin A = Real.sin (2 * (A / 2)) := by congr 1; ring
    _ = _ := Real.sin_two_mul (A / 2)

lemma cos_B_as_S_sub_A (A B : ℝ) :
    Real.cos B = Real.cos (A + B) * Real.cos A + Real.sin (A + B) * Real.sin A := by
  calc
    Real.cos B = Real.cos ((A + B) - A) := by congr 1; ring
    _ = _ := by rw [Real.cos_sub]

lemma cos_twoA_add_B_as_S_add_A (A B : ℝ) :
    Real.cos (2 * A + B) =
      Real.cos (A + B) * Real.cos A - Real.sin (A + B) * Real.sin A := by
  calc
    Real.cos (2 * A + B) = Real.cos ((A + B) + A) := by congr 1; ring
    _ = _ := by rw [Real.cos_add]

lemma cos_A_add_twoB_as_twoS_sub_A (A B : ℝ) :
    Real.cos (A + 2 * B) =
      (2 * Real.cos (A + B) ^ 2 - 1) * Real.cos A +
        (2 * Real.sin (A + B) * Real.cos (A + B)) * Real.sin A := by
  calc
    Real.cos (A + 2 * B) = Real.cos (2 * (A + B) - A) := by congr 1; ring
    _ = Real.cos (2 * (A + B)) * Real.cos A +
        Real.sin (2 * (A + B)) * Real.sin A := by rw [Real.cos_sub]
    _ = _ := by rw [Real.cos_two_mul, Real.sin_two_mul]

lemma cos_C_as_sin_halfA_add_S (A B C : ℝ)
    (hsum : 2 * C + 3 * A + 2 * B = Real.pi) :
    Real.cos C = Real.sin (A / 2 + (A + B)) := by
  have hC : C = Real.pi / 2 - (A / 2 + (A + B)) := by linarith
  rw [hC, Real.cos_pi_div_two_sub]

lemma two_sin_half_sq (C : ℝ) :
    (2 * Real.sin (C / 2)) ^ 2 = 2 - 2 * Real.cos C := by
  have hcos := Real.cos_two_mul_eq_one_sub (C / 2)
  rw [show 2 * (C / 2) = C by ring] at hcos
  nlinarith

end LeanPool.Erdos132WeiE2.Algebra
