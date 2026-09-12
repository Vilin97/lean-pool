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
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketTailBound

/-! Actual residual tail estimates after the single final factorial split. -/

section

/-! The actual finite residual tail inherits the geometric-series word bound. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

theorem weighted_tail_sum_le (κ B : ℝ) (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (hsmall : κ * B ≤ 1 / 2) (N : ℕ) :
    (∑ n ∈ tailGrades N, κ^n*B^(n+1)) ≤ 2*B*(κ*B)^(N+1) := by
  calc
    _ = B*(∑ n ∈ Ico (N+1) (2*N+3), (κ*B)^n) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      simp only [pow_succ,mul_pow]
      ring
    _ ≤ B*(2*(κ*B)^(N+1)) := mul_le_mul_of_nonneg_left
      (EulerPacketTailBound.sum_geometric_Ico_le (κ*B) (mul_nonneg hκ hB) hsmall _ _) hB
    _ = _ := by ring

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {N : ℕ} {a : ℕ → Profile}

theorem PrefixFields.tailSum_bound_of_grades (F : PrefixFields P T (N + 1) a)
    (C : CoefficientData P T O) (hT : 0 < T) {correctorT : VectorField}
    (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector N (by omega)) Ct)
    (pressure : Field P T (pressureGradient (a N).highPressure)) (ha : a 0 = 0)
    (q : ℕ) (R κ B : ℝ) (hR : 0 ≤ R) (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (hsmall : κ * B ≤ 1 / 2)
    (hgrade : ∀ n (hn : N + 1 ≤ n), n ≤ 2 * N + 2 →
      (F.tailGradeField C hT Ct hCt pressure ha n hn).WordBound q R (B ^ (n + 1)) 0) :
    (F.tailSumField C hT Ct hCt pressure ha κ).WordBound q R (2*B*(κ*B)^(N+1)) 0 := by
  let W := fun r : {n // n ∈ tailGrades N} =>
    (F.tailGradeField C hT Ct hCt pressure ha r.1 (Finset.mem_Ico.mp r.2).1).smul (κ^r.1)
  have hw : ∀ r ∈ (tailGrades N).attach,
      (W r).WordBound q R (κ^r.1*B^(r.1+1)) 0 := by
    intro r _
    have hm := Finset.mem_Ico.mp r.2
    have hb := (hgrade r.1 hm.1 (by omega)).smul (κ^r.1)
    simpa only [abs_of_nonneg (pow_nonneg hκ r.1)] using hb
  have hs := Field.wordBound_finsetSum (tailGrades N).attach _ W
    (fun r => κ^r.1*B^(r.1+1)) hw
  have hsum : (∑ r ∈ (tailGrades N).attach, κ^r.1*B^(r.1+1)) =
      ∑ n ∈ tailGrades N, κ^n*B^(n+1) :=
    Finset.sum_attach (tailGrades N) (fun n => κ^n*B^(n+1))
  rw [hsum] at hs
  exact (hs.mono_amplitude hR (weighted_tail_sum_le κ B hκ hB hsmall N)).of_path_eq
    (F.tailSumField C hT Ct hCt pressure ha κ) rfl

end EulerPacketCylinderField

end
end

end

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
