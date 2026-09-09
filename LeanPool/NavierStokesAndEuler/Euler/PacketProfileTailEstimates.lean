/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTailBase
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailFields
import LeanPool.NavierStokesAndEuler.Euler.PacketExponentialTail
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileTailGrade
import LeanPool.NavierStokesAndEuler.Euler.PacketTailNormalization
import LeanPool.NavierStokesAndEuler.Euler.PacketTailSumBounds

/-! Actual residual tail estimates after the single final factorial split. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.ProfileRegularity

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketCoarseMajorant

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile} {support : Set Space}
  (hT : 0 < T) (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le support (a i))
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

theorem tail_grade_coarse_bound
    (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (ha : a 0 = 0) (hb : (a 1).mean = 0) (n : ℕ) (hn : N + 1 ≤ n) (hn' : n ≤ 2 * N + 2) :
    (tailGradeField hT G C ha n hn).WordBound 6 (4*R)
      ((tailBase R S.H0 BC.termCost N)^(n+1)) 0 := by
  have h := tail_grade_bound hT G BC hG hN hR hRc ha hb n hn
  have hA : 0 ≤ (1+18*((N+2 : ℕ) : ℝ)^2)*BC.termCost*S.H0^(2*n+2) :=
    mul_nonneg (mul_nonneg (by positivity) BC.termCost_nonneg) (pow_nonneg S.H0_pos.le _)
  have hc := h.coarse_grade hR hA N n hN hn' le_rfl
  exact hc.mono_amplitude (by linarith)
    (tailBase_absorption R S.H0 BC.termCost BC.termCost_nonneg N n)

theorem tail_sum_bound
    (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (ha : a 0 = 0) (hb : (a 1).mean = 0) (κ : ℝ) (hκ : 0 ≤ κ)
    (hsmall : κ * tailBase R S.H0 BC.termCost N ≤ 1 / 2) :
    (tailSumField hT G C ha κ).WordBound 6 (4*R)
      (2*tailBase R S.H0 BC.termCost N*(κ*tailBase R S.H0 BC.termCost N)^(N+1)) 0 :=
  (prefixThrough hT G).tailSum_bound_of_grades C hT
    (G N le_rfl).correctorDerivative (G N le_rfl).corrector_time (G N le_rfl).pressure ha
    6 (4*R) κ (tailBase R S.H0 BC.termCost N) (by linarith) hκ
    (tailBase_nonneg R S.H0 BC.termCost BC.termCost_nonneg N) hsmall
    (fun n hn hn' => tail_grade_coarse_bound hT G BC hG hN hR hRc ha hb n hn hn')

theorem normalized_tail_bound
    (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (ha : a 0 = 0) (hb : (a 1).mean = 0) (k X : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (hcoef : BC.multiplierCost ≤ k ^ (1 / 100 : ℝ))
    (hX : 6 ≤ X) (hNX : X - 1 ≤ (N : ℝ)) :
    ((C.inverse.multiply (tailSumField hT G C ha k⁻¹)).smul k).WordBound 6 (4*R)
      (Real.exp (-(7/10)*X*Real.log k)) 0 := by
  have hk0 : 0 ≤ k := by linarith
  have hsmall : k⁻¹*tailBase R S.H0 BC.termCost N ≤ 1/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using
      EulerPacketTailBound.grade_ratio_le_half k (tailBase R S.H0 BC.termCost N) hk hbase
  have hsum := tail_sum_bound hT G BC hG hN hR hRc ha hb k⁻¹ (inv_nonneg.mpr hk0) hsmall
  exact BC.normalized_tail_exponential (tailSumField hT G C ha k⁻¹) N hsum
    (hRc.trans (by linarith)) (by linarith) hk
    (tailBase_nonneg R S.H0 BC.termCost BC.termCost_nonneg N) hbase hcoef hX hNX

end EulerPacketCylinderField.ProfileRegularity
