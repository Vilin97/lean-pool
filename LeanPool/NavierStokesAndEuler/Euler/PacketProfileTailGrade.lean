/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailActual
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketTailGradeBounds

/-! Uniform profile budgets bound each literal residual grade of the finite packet. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.ProfileRegularity

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile} {support : Set Space}
  (hT : 0 < T) (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le support (a i))
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}

theorem prefixThrough_bound
    (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i) :
    PrefixBound (prefixThrough hT G) hT.le S R where
  high i hi hip := (hG i (by omega) hip).high
  mean i hi hip := (hG i (by omega) (by omega)).mean
  corrector i hi hip := (hG i (by omega) hip).corrector

variable {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

theorem tail_grade_bound
    (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (ha : a 0 = 0) (hb : (a 1).mean = 0) (n : ℕ) (hn : N + 1 ≤ n) :
    (tailGradeField hT G C ha n hn).WordBound 6 R
      ((1+18*((N+2 : ℕ) : ℝ)^2)*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) :=
  (prefixThrough_bound hT G hG).tail_grade_bound BC hT hN hR hRc
    (G N le_rfl).correctorDerivative (G N le_rfl).corrector_time (G N le_rfl).pressure
    (hG N le_rfl hN).correctorDerivative (hG N le_rfl hN).pressure ha hb n hn

theorem literal_tail_grade_bound
    (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (ha : a 0 = 0) (hb : (a 1).mean = 0) (n : ℕ) (hn : N + 1 ≤ n) :
    (literalTailGradeField hT G C ha n hn).WordBound 6 R
      ((1+18*((N+2 : ℕ) : ℝ)^2)*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) :=
  (tail_grade_bound hT G BC hG hN hR hRc ha hb n hn).of_path_eq
    (literalTailGradeField hT G C ha n hn) (literalTailGradeField_path hT G C ha n hn)

end EulerPacketCylinderField.ProfileRegularity
