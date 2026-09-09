/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCoarseMajorant

@[expose] public section

/-! A single polynomial base absorbs the finite residual multiplicity and
the fixed profile envelope, before the geometric tail is summed. -/

namespace EulerPacketCoarseMajorant


def tailBase (R H C : ℝ) (N : ℕ) : ℝ :=
  (1+C*(1+18*((N+2 : ℕ) : ℝ)^2))*H^2*gradeBase R N

theorem tailBase_nonneg (R H C : ℝ) (hC : 0 ≤ C) (N : ℕ) :
    0 ≤ tailBase R H C N := by
  unfold tailBase
  exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg H)) (gradeBase_nonneg R N)

theorem tailBase_ge_one (R H C : ℝ) (hR : 1 ≤ R) (hH : 1 ≤ H)
    (hC : 0 ≤ C) (N : ℕ) (hN : 1 ≤ N) : 1 ≤ tailBase R H C N := by
  have hf : (1 : ℝ) ≤ 1+C*(1+18*((N+2 : ℕ) : ℝ)^2) := by
    have h : 0 ≤ C*(1+18*((N+2 : ℕ) : ℝ)^2) := by positivity
    linarith only [h]
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hf (one_le_pow₀ hH)) (gradeBase_ge_one R hR N hN)

/-- The envelope is absorbed once into the base, with no dependence on
the surviving grade in that base. -/
theorem tailBase_absorption (R H C : ℝ) (hC : 0 ≤ C) (N n : ℕ) :
    (1+18*((N+2 : ℕ) : ℝ)^2)*C*H^(2*n+2)*(gradeBase R N)^(n+1) ≤
      (tailBase R H C N)^(n+1) := by
  let A : ℝ := 1+C*(1+18*((N+2 : ℕ) : ℝ)^2)
  have hA : 1 ≤ A := by
    have h : 0 ≤ C*(1+18*((N+2 : ℕ) : ℝ)^2) := by positivity
    dsimp [A]
    linarith only [h]
  have hf : (1+18*((N+2 : ℕ) : ℝ)^2)*C ≤ A^(n+1) := by
    calc
      _ ≤ A := by dsimp [A]; nlinarith
      _ ≤ A*A^n := le_mul_of_one_le_right (le_trans zero_le_one hA) (one_le_pow₀ hA)
      _ = A^(n+1) := (pow_succ' A n).symm
  have hH : H^(2*n+2) = (H^2)^(n+1) := by
    rw [← pow_mul]
    congr 1
  calc
    _ = ((1+18*((N+2 : ℕ) : ℝ)^2)*C)*
        ((H^2)^(n+1)*(gradeBase R N)^(n+1)) := by rw [hH]; ring
    _ ≤ A^(n+1)*((H^2)^(n+1)*(gradeBase R N)^(n+1)) :=
      mul_le_mul_of_nonneg_right hf
        (mul_nonneg (pow_nonneg (sq_nonneg H) _) (pow_nonneg (gradeBase_nonneg R N) _))
    _ = (tailBase R H C N)^(n+1) := by
      unfold tailBase
      rw [mul_pow, mul_pow]
      change A^(n+1)*((H^2)^(n+1)*(gradeBase R N)^(n+1)) =
        (A^(n+1)*(H^2)^(n+1))*(gradeBase R N)^(n+1)
      ring

def tailPolynomialConstant (R H C : ℝ) : ℝ :=
  (1+163*C)*H^2*(4*R*550^2)^110

theorem tailPolynomialConstant_nonneg (R H C : ℝ) (hC : 0 ≤ C) :
    0 ≤ tailPolynomialConstant R H C := by
  unfold tailPolynomialConstant
  positivity

theorem gradeBase_polynomial (R : ℝ) (N : ℕ) :
    gradeBase R N = (4*R*550^2)^110*(N : ℝ)^220 := by
  unfold gradeBase
  rw [show 4*R*(550*(N : ℝ))^2 = (4*R*550^2)*(N : ℝ)^2 by ring, mul_pow, ← pow_mul]

/-- Finite multiplicity raises the degree of the base from 220 to 222. -/
theorem tailBase_polynomial_bound (R H C : ℝ) (hC : 0 ≤ C) (N : ℕ) (hN : 1 ≤ N) :
    tailBase R H C N ≤ tailPolynomialConstant R H C*(N : ℝ)^222 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn2 : (1 : ℝ) ≤ (N : ℝ)^2 := one_le_pow₀ hn
  have hnplus : (N : ℝ)+2 ≤ 3*(N : ℝ) := by linarith
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ (N : ℝ)+2 by positivity) hnplus 2
  have hf : (1 : ℝ)+18*((N+2 : ℕ) : ℝ)^2 ≤ 163*(N : ℝ)^2 := by
    push_cast
    nlinarith only [hp, hn2]
  have hm := mul_le_mul_of_nonneg_left hf hC
  have hfactor : (1 : ℝ)+C*(1+18*((N+2 : ℕ) : ℝ)^2) ≤
      (1+163*C)*(N : ℝ)^2 := by nlinarith only [hm, hn2]
  calc
    _ ≤ ((1+163*C)*(N : ℝ)^2)*H^2*gradeBase R N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor (sq_nonneg H))
        (gradeBase_nonneg R N)
    _ = tailPolynomialConstant R H C*(N : ℝ)^222 := by
      rw [gradeBase_polynomial]
      unfold tailPolynomialConstant
      rw [show 222 = 2+220 from rfl, pow_add]
      ring

end EulerPacketCoarseMajorant
