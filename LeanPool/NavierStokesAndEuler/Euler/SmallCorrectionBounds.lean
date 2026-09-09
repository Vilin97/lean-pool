/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ConstantCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTower
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldSobolevBudget
import Mathlib.Algebra.Order.Star.Real

/-! The literal spatial convection of a small smooth cylinder field has
a quadratic residual envelope at every Sobolev order. No residual estimate
or differential equation is postulated. -/

@[expose] public section


noncomputable section

namespace EulerSmallCorrection

open Set Finset EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerPacketCylinderField EulerPacketProfileRecursion EulerGevrey
  EulerPacketWeights EulerH6Pressure EulerSobolevGevreyOperators
  EulerCylinderPathProduct EulerConstantCorrection EulerAllOrderCorrectionData

variable (P : ℝ) [Fact (0 < P)]

/-- Residual cost, given by `1+108*productBlockConstant P*C^2*R`. -/
def residualCost (C R : ℝ) : ℝ := 1+108*productBlockConstant P*C^2*R

theorem residualCost_pos (C R : ℝ) (hR : 0 ≤ R) : 0 < residualCost P C R := by
  have hp := productBlockConstant_nonneg P
  unfold residualCost
  positivity

variable {P} {T : ℝ} {raw : VectorField} (G : Field P T raw)

/-- Residual, given by `(G.smul ε).spatialTransport (G.smul ε)`. -/
def residual (ε : ℝ) := (G.smul ε).spatialTransport (G.smul ε)

/-- Input, given by `data P (G.smul ε).toFieldTower (residual G ε).toFieldTower`. -/
def input (ε : ℝ) : Data P T :=
  data P (G.smul ε).toFieldTower (residual G ε).toFieldTower

theorem weighted_shift_one {q : ℕ} {R A : ℝ}
    (hG : G.WordBound q R A 1) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (s N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (hsmall : ρ * R ≤ 1 / 2) (t : Icc (0 : ℝ) T) :
    weightedNorm P q N ρ (G.toFieldTower.realization s t) ≤ 12*A*R := by
  have h := hG.toFieldTower_weightedNorm_le s N hN ρ hρ t
  simp_rw [Field.weight_majorant_one] at h
  rw [← mul_sum] at h
  exact h.trans ((mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (Field.square_geometric_le_twelve (ρ*R) (mul_nonneg hρ.le hR) hsmall (N+1)) hR)
    hA).trans_eq (by ring))

theorem scaled_word {C R : ℝ} (hG : G.WordBound 6 R C 0) (ε : ℝ) (hε : 0 ≤ ε) :
    (G.smul ε).WordBound 6 R (ε*C) 0 := by
  simpa only [abs_of_nonneg hε] using hG.smul ε

theorem residual_word {C R : ℝ} (hG : G.WordBound 6 R C 0)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 ≤ ε) :
    (residual G ε).WordBound 6 R (9*productBlockConstant P*(ε*C)*(ε*C)) 1 :=
  (scaled_word G hG ε hε).spatialTransport (scaled_word G hG ε hε) hR
    (mul_nonneg hε hC) (mul_nonneg hε hC)

theorem residual_weighted {C R : ℝ} (hG : G.WordBound 6 R C 0)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 ≤ ε)
    (s N : ℕ) (hN : N + 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (hsmall : ρ * R ≤ 1 / 2) (t : Icc (0 : ℝ) T) :
    weightedNorm P 6 N ρ ((residual G ε).toFieldTower.realization s t) ≤
      ε^2*residualCost P C R := by
  have hp := productBlockConstant_nonneg P
  have hh := weighted_shift_one (residual G ε) (residual_word G hG hC hR ε hε)
    hR (by positivity) s N hN ρ hρ hsmall t
  apply hh.trans
  unfold residualCost
  nlinarith only [sq_nonneg ε]

end EulerSmallCorrection
