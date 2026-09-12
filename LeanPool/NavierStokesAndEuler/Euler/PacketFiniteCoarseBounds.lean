/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTailBase
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketShiftArithmetic
import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds
import Mathlib.Algebra.Order.Star.Real

/-! Low packet grades retain fixed polynomial costs; higher grades use one common tail base. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open EulerPacketProfileRecursion EulerPacketShiftArithmetic EulerPacketCoarseMajorant EulerGevrey

/-- Fixed velocity grade cost, given by `(3*H^(2*n))*((4*R)^(highShift n)*((highShift
n).factorial : ℝ)^2)`. -/
def fixedVelocityGradeCost (R H : ℝ) (n : ℕ) : ℝ :=
  (3*H^(2*n))*((4*R)^(highShift n)*((highShift n).factorial : ℝ)^2)

theorem fixedVelocityGradeCost_nonneg (R H : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    0 ≤ fixedVelocityGradeCost R H n := by
  unfold fixedVelocityGradeCost
  rw [pow_mul H 2 n]
  positivity

namespace Field

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} {G : Field P T raw}
  {q d n : ℕ} {R A H : ℝ}

theorem WordBound.split_fixed_shift (hG : G.WordBound q R A d) (hR : 0 ≤ R) (hA : 0 ≤ A) :
    G.WordBound q (4*R) (A*((4*R)^d*(d.factorial : ℝ)^2)) 0 := by
  intro j
  exact (hG j).trans ((mul_le_mul_of_nonneg_left (majorant_coarse_split R hR d j) hA).trans_eq
    (by ring))

theorem WordBound.fixed_velocity_grade (hG : G.WordBound q R (3 * H ^ (2 * n)) (highShift n))
    (hR : 0 ≤ R) (hH : 0 ≤ H) :
    G.WordBound q (4*R) (fixedVelocityGradeCost R H n) 0 :=
  hG.split_fixed_shift hR (mul_nonneg (by norm_num) (pow_nonneg hH _))

theorem WordBound.coarse_velocity_grade (hG : G.WordBound q R (3 * H ^ (2 * n)) (highShift n))
    (hR : 1 ≤ R) (hH : 1 ≤ H) (C : ℝ) (hC : 1 ≤ C) (N : ℕ) (hN : 1 ≤ N)
    (hn : n ≤ 2 * N + 2) : G.WordBound q (4*R) ((tailBase R H C N)^(n+1)) 0 := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hNN : (2 : ℝ) ≤ ((N+2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ N+2 by omega)
  have hP : (3 : ℝ) ≤ 1+18*((N+2 : ℕ) : ℝ)^2 := by nlinarith
  have hPC : (3 : ℝ) ≤ (1+18*((N+2 : ℕ) : ℝ)^2)*C :=
    hP.trans (le_mul_of_one_le_right (by positivity) hC)
  have ha : 3*H^(2*n) ≤ (1+18*((N+2 : ℕ) : ℝ)^2)*C*H^(2*n+2) := by
    calc
      _ ≤ 3*H^(2*n+2) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH (by omega)) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right hPC (pow_nonneg hH0 _)
  have hA : 0 ≤ (1+18*((N+2 : ℕ) : ℝ)^2)*C*H^(2*n+2) := by positivity
  have h := (hG.mono_amplitude (zero_le_one.trans hR) ha).coarse_grade hR hA N n hN hn
    (show highShift n ≤ 110*(n+1) by unfold highShift; omega)
  exact h.mono_amplitude (by linarith) (tailBase_absorption R H C hC0 N n)

end Field
end EulerPacketCylinderField
