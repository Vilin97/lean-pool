/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteCoarseBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteProfileFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketApproximationNormalization
import LeanPool.NavierStokesAndEuler.Euler.PacketExponentialTail
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteApproximationBounds

/-! Actual inverse-frame approximate fields have bounds independent of packet length. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.ProfileRegularity

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPacketCoarseMajorant EulerParameterWordGevrey

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile} {support : Set Space}
  (hT : 0 < T) (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le support (a i))
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hR : 1 ≤ R) (ha : a 0 = 0) (hN : 1 ≤ N)
  {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)

include hG hR ha hN hRc

theorem normalizedVelocity_bound (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    ((C.inverse.multiply (velocityField hT G k⁻¹)).smul k).WordBound 6 (4*R)
      (BC.multiplierCost*(fixedVelocityGradeCost R S.H0 1+fixedVelocityGradeCost R S.H0 2+1)) 0 :=
          by
  have hk0 : 0 ≤ k := by linarith
  have hsmall : k⁻¹*tailBase R S.H0 BC.termCost N ≤ 1/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using
      EulerPacketTailBound.grade_ratio_le_half k (tailBase R S.H0 BC.termCost N) hk hbase
  have h := velocity_bound hT G hG hR ha hN BC.termCost BC.one_le_termCost
    k⁻¹ (inv_nonneg.mpr hk0) hsmall
  exact BC.normalized_approximation_bound (velocityField hT G k⁻¹) h (by linarith)
    (hRc.trans (by linarith)) hk (tailBase_nonneg R S.H0 BC.termCost BC.termCost_nonneg N) hbase
    (fixedVelocityGradeCost_nonneg R S.H0 (zero_le_one.trans hR) 1)
    (fixedVelocityGradeCost_nonneg R S.H0 (zero_le_one.trans hR) 2)

/-- This is the inverse-frame image of W_t. The derivative of the inverse
frame is a separate coefficient term in the time derivative of z_a. -/
theorem normalizedVelocityTimeTerm_bound (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    ((C.inverse.multiply (velocityDerivativeField hT G k⁻¹)).smul k).WordBound 6 (4*R)
      (BC.multiplierCost*(fixedVelocityGradeCost R S.H0 1+fixedVelocityGradeCost R S.H0 2+1)) 0 :=
          by
  have hk0 : 0 ≤ k := by linarith
  have hsmall : k⁻¹*tailBase R S.H0 BC.termCost N ≤ 1/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using
      EulerPacketTailBound.grade_ratio_le_half k (tailBase R S.H0 BC.termCost N) hk hbase
  have h := velocityDerivative_bound hT G hG hR ha hN BC.termCost BC.one_le_termCost
    k⁻¹ (inv_nonneg.mpr hk0) hsmall
  exact BC.normalized_approximation_bound (velocityDerivativeField hT G k⁻¹) h (by linarith)
    (hRc.trans (by linarith)) hk (tailBase_nonneg R S.H0 BC.termCost BC.termCost_nonneg N) hbase
    (fixedVelocityGradeCost_nonneg R S.H0 (zero_le_one.trans hR) 1)
    (fixedVelocityGradeCost_nonneg R S.H0 (zero_le_one.trans hR) 2)

end EulerPacketCylinderField.ProfileRegularity
