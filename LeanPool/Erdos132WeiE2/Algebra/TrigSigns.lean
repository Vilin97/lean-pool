/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132WeiE2.Algebra.Ranges

namespace LeanPool.Erdos132WeiE2.Algebra

lemma ra_sq_sub_ea_sq_identity (A B : ℝ) :
    (4 - 4 * Real.cos A - 2 * Real.cos B + 4 * Real.cos (A + B) -
        2 * Real.cos (2 * A + B)) - (2 * Real.sin (A / 2)) ^ 2 =
      4 * (Real.sin (A / 2)) ^ 2 * (1 + 2 * Real.cos (A + B)) := by
  have hcosA : Real.cos A = 1 - 2 * (Real.sin (A / 2)) ^ 2 := by
    calc
      Real.cos A = Real.cos (2 * (A / 2)) := by congr 1; ring
      _ = 1 - 2 * (Real.sin (A / 2)) ^ 2 := Real.cos_two_mul_eq_one_sub (A / 2)
  have hsinA : Real.sin A = 2 * Real.sin (A / 2) * Real.cos (A / 2) := by
    calc
      Real.sin A = Real.sin (2 * (A / 2)) := by congr 1; ring
      _ = 2 * Real.sin (A / 2) * Real.cos (A / 2) := Real.sin_two_mul (A / 2)
  have hcosB : Real.cos B =
      Real.cos (A + B) * Real.cos A + Real.sin (A + B) * Real.sin A := by
    calc
      Real.cos B = Real.cos ((A + B) - A) := by congr 1; ring
      _ = _ := by rw [Real.cos_sub]
  have hcosTwo : Real.cos (2 * A + B) =
      Real.cos (A + B) * Real.cos A - Real.sin (A + B) * Real.sin A := by
    calc
      Real.cos (2 * A + B) = Real.cos ((A + B) + A) := by congr 1; ring
      _ = _ := by rw [Real.cos_add]
  rw [hcosB, hcosTwo, hcosA, hsinA]
  ring

lemma rb_sq_sub_eb_sq_identity (A B : ℝ) :
    (4 - 2 * Real.cos A - 4 * Real.cos B + 4 * Real.cos (A + B) -
        2 * Real.cos (A + 2 * B)) - (2 * Real.sin (B / 2)) ^ 2 =
      4 * (Real.sin (B / 2)) ^ 2 * (1 + 2 * Real.cos (A + B)) := by
  have hcosB : Real.cos B = 1 - 2 * (Real.sin (B / 2)) ^ 2 := by
    calc
      Real.cos B = Real.cos (2 * (B / 2)) := by congr 1; ring
      _ = 1 - 2 * (Real.sin (B / 2)) ^ 2 := Real.cos_two_mul_eq_one_sub (B / 2)
  have hsinB : Real.sin B = 2 * Real.sin (B / 2) * Real.cos (B / 2) := by
    calc
      Real.sin B = Real.sin (2 * (B / 2)) := by congr 1; ring
      _ = 2 * Real.sin (B / 2) * Real.cos (B / 2) := Real.sin_two_mul (B / 2)
  have hcosA : Real.cos A =
      Real.cos (A + B) * Real.cos B + Real.sin (A + B) * Real.sin B := by
    calc
      Real.cos A = Real.cos ((A + B) - B) := by congr 1; ring
      _ = _ := by rw [Real.cos_sub]
  have hcosTwo : Real.cos (A + 2 * B) =
      Real.cos (A + B) * Real.cos B - Real.sin (A + B) * Real.sin B := by
    calc
      Real.cos (A + 2 * B) = Real.cos ((A + B) + B) := by congr 1; ring
      _ = _ := by rw [Real.cos_add]
  rw [hcosA, hcosTwo, hcosB, hsinB]
  ring

lemma ra_sq_sub_rb_sq_identity (A B : ℝ) :
    (4 - 4 * Real.cos A - 2 * Real.cos B + 4 * Real.cos (A + B) -
        2 * Real.cos (2 * A + B)) -
      (4 - 2 * Real.cos A - 4 * Real.cos B + 4 * Real.cos (A + B) -
        2 * Real.cos (A + 2 * B)) =
      2 * ((Real.cos B - Real.cos A) +
        (Real.cos (A + 2 * B) - Real.cos (2 * A + B))) := by
  ring

lemma one_add_two_cos_pos {A B : ℝ} (hpos : 0 < A + B)
    (hlt : A + B < 2 * Real.pi / 3) :
    0 < 1 + 2 * Real.cos (A + B) := by
  have hangle : A + B < Real.pi - Real.pi / 3 := by linarith
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
    (le_of_lt hpos) (show Real.pi - Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) hangle
  rw [Real.cos_pi_sub, Real.cos_pi_div_three] at hcos
  linarith

lemma cos_B_gt_cos_A {A B : ℝ} (hB : 0 < B) (hBA : B < A) (hApi : A < Real.pi) :
    Real.cos A < Real.cos B :=
  Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hB) (le_of_lt hApi) hBA

lemma cos_add_two_mul_gt_cos_two_mul_add {A B : ℝ}
    (hpos : 0 < A + 2 * B) (hlt : A + 2 * B < 2 * A + B)
    (hpi : 2 * A + B < Real.pi) :
    Real.cos (2 * A + B) < Real.cos (A + 2 * B) :=
  Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hpos) (le_of_lt hpi) hlt

lemma sin_half_pos {X : ℝ} (hX : 0 < X) (hXpi : X < Real.pi) :
    0 < Real.sin (X / 2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

lemma sin_A_half_pos {A : ℝ} (hA : 0 < A) (hApi : A < Real.pi) :
    0 < Real.sin (A / 2) := sin_half_pos hA hApi

lemma sin_B_half_pos {B : ℝ} (hB : 0 < B) (hBpi : B < Real.pi) :
    0 < Real.sin (B / 2) := sin_half_pos hB hBpi

lemma sin_C_half_pos {C : ℝ} (hC : 0 < C) (hCpi : C < Real.pi) :
    0 < Real.sin (C / 2) := sin_half_pos hC hCpi

lemma ra_sq_gt_ea_sq (RA eA A B : ℝ)
    (hid : RA ^ 2 - eA ^ 2 =
      4 * (Real.sin (A / 2)) ^ 2 * (1 + 2 * Real.cos (A + B)))
    (hsin : 0 < Real.sin (A / 2)) (hcos : 0 < 1 + 2 * Real.cos (A + B)) :
    eA ^ 2 < RA ^ 2 := by
  nlinarith [sq_pos_of_pos hsin]

lemma rb_sq_gt_eb_sq (RB eB A B : ℝ)
    (hid : RB ^ 2 - eB ^ 2 =
      4 * (Real.sin (B / 2)) ^ 2 * (1 + 2 * Real.cos (A + B)))
    (hsin : 0 < Real.sin (B / 2)) (hcos : 0 < 1 + 2 * Real.cos (A + B)) :
    eB ^ 2 < RB ^ 2 := by
  nlinarith [sq_pos_of_pos hsin]

lemma ra_sq_gt_rb_sq (RA RB A B : ℝ)
    (hid : RA ^ 2 - RB ^ 2 =
      2 * ((Real.cos B - Real.cos A) +
        (Real.cos (A + 2 * B) - Real.cos (2 * A + B))))
    (hcosBA : Real.cos A < Real.cos B)
    (hcosAdd : Real.cos (2 * A + B) < Real.cos (A + 2 * B)) :
    RB ^ 2 < RA ^ 2 := by
  linarith

lemma lt_of_sq_lt_sq_of_nonneg {a b : ℝ} (hsq : a ^ 2 < b ^ 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : a < b :=
  (sq_lt_sq₀ ha hb).mp hsq

lemma ra_gt_ea {RA eA : ℝ} (hsq : eA ^ 2 < RA ^ 2)
    (hRA : 0 ≤ RA) (heA : 0 ≤ eA) : eA < RA :=
  lt_of_sq_lt_sq_of_nonneg hsq heA hRA

lemma rb_gt_eb {RB eB : ℝ} (hsq : eB ^ 2 < RB ^ 2)
    (hRB : 0 ≤ RB) (heB : 0 ≤ eB) : eB < RB :=
  lt_of_sq_lt_sq_of_nonneg hsq heB hRB

lemma ra_gt_rb {RA RB : ℝ} (hsq : RB ^ 2 < RA ^ 2)
    (hRA : 0 ≤ RA) (hRB : 0 ≤ RB) : RB < RA :=
  lt_of_sq_lt_sq_of_nonneg hsq hRB hRA

end LeanPool.Erdos132WeiE2.Algebra
