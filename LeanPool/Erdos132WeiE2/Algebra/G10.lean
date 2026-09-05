/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132WeiE2.Algebra.Exclusions

/-!
# The strict E2 comparison between the C-edge and Q-diagonal

This module derives `eC < Q` from the frozen trigonometric interface.
-/

namespace LeanPool.Erdos132WeiE2.Algebra

/-- The exact polynomial identity supplied with the amended G10 certificate. -/
lemma g10_curve_identity (x y : ℝ) :
    (-x ^ 4 * y ^ 2 - 4 * x ^ 4 * y - x ^ 4 - 4 * x ^ 3 * y ^ 2 +
        16 * x ^ 3 * y + 4 * x ^ 3 - 2 * x ^ 2 * y ^ 2 + 30 * x ^ 2 -
        4 * x * y ^ 2 - 16 * x * y + 4 * x - y ^ 2 + 4 * y - 1) =
      -(x ^ 2 + 1) * closurePolynomial x y +
        4 * (x ^ 2 - 4 * x + 1) * ((1 - x ^ 2) * y - 2 * x) := by
  simp only [closurePolynomial]
  ring

/-- G10 from the amended explicit-real interface. -/
lemma ec_lt_q_of_interface (A B C eC Q : ℝ)
    (hB : 0 < B) (hBA : B < A) (hAC : A < C) (hC : C < Real.pi / 3)
    (hsum : 2 * C + 3 * A + 2 * B = Real.pi)
    (hclosure : 2 * Real.sin (A / 2) * (1 + 2 * Real.cos (A + B)) = 1)
    (heC : eC = 2 * Real.sin (C / 2))
    (hQ : Q ^ 2 = 3 - 2 * Real.cos A - 2 * Real.cos B + 2 * Real.cos (A + B))
    (heCnonneg : 0 ≤ eC) (hQnonneg : 0 ≤ Q) : eC < Q := by
  have hA : 0 < A := lt_trans hB hBA
  have hApiThird : A < Real.pi / 3 := lt_trans hAC hC
  have hApi : A < Real.pi := by linarith [Real.pi_pos]
  have hSpos : 0 < A + B := by linarith
  have hSlt := add_lt_two_pi_div_three A B C hB hBA hAC hsum
  have hsinHalfLt : Real.sin (A / 2) < 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith)
  have hcosSHalf : 0 < Real.cos ((A + B) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsinBHalf : 0 < Real.sin (B / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have heCsq : eC ^ 2 = 2 - 2 * Real.cos C := by
    rw [heC, two_sin_half_sq]
  have hsinSdouble : Real.sin (A + B) =
      2 * Real.sin ((A + B) / 2) * Real.cos ((A + B) / 2) := by
    calc
      Real.sin (A + B) = Real.sin (2 * ((A + B) / 2)) := by congr 1; ring
      _ = _ := Real.sin_two_mul ((A + B) / 2)
  have hcosSdouble : Real.cos (A + B) =
      2 * Real.cos ((A + B) / 2) ^ 2 - 1 := by
    calc
      Real.cos (A + B) = Real.cos (2 * ((A + B) / 2)) := by congr 1; ring
      _ = _ := Real.cos_two_mul ((A + B) / 2)
  have hsinBsub : Real.sin (B / 2) =
      Real.sin ((A + B) / 2) * Real.cos (A / 2) -
        Real.cos ((A + B) / 2) * Real.sin (A / 2) := by
    calc
      Real.sin (B / 2) = Real.sin ((A + B) / 2 - A / 2) := by congr 1; ring
      _ = _ := by rw [Real.sin_sub]
  have hclosure' := hclosure
  rw [hcosSdouble] at hclosure'
  have hdiff : Q ^ 2 - eC ^ 2 =
      4 * (1 - 2 * Real.sin (A / 2)) * Real.cos ((A + B) / 2) *
        Real.sin (B / 2) := by
    rw [hQ, heCsq, cos_C_as_sin_halfA_add_S A B C hsum, Real.sin_add,
      cos_B_as_S_sub_A A B, cos_A_as_half A, sin_A_as_half A,
      hsinSdouble, hcosSdouble, hsinBsub]
    linear_combination hclosure' -
      8 * Real.cos ((A + B) / 2) ^ 2 * (Real.sin_sq_add_cos_sq (A / 2))
  have hfactor1 : 0 < 1 - 2 * Real.sin (A / 2) := by linarith
  have hproduct : 0 <
      4 * (1 - 2 * Real.sin (A / 2)) * Real.cos ((A + B) / 2) *
        Real.sin (B / 2) := by
    exact mul_pos (mul_pos (by positivity) hcosSHalf) hsinBHalf
  have hsq : eC ^ 2 < Q ^ 2 := by linarith
  exact lt_of_sq_lt_sq_of_nonneg hsq heCnonneg hQnonneg

end LeanPool.Erdos132WeiE2.Algebra
