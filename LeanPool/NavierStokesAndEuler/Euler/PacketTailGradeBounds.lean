/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieceBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailFields
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketTailLinearBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketTailNonlinearBounds

/-! Each surviving grade of the literal packet residual has a fixed-radius estimate. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.PrefixBound

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T (N + 1) a} {hT : 0 ≤ T}
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} (B : PrefixBound F hT S R)
  {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

include B

theorem tail_grade_bound (hTime : 0 < T) (hN : 1 ≤ N) (hR : 1 ≤ R)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    {correctorT : VectorField} (Ct : Field P T correctorT)
    (hCt : TimeDerivative hTime.le (F.corrector N (Nat.lt_succ_self N)) Ct)
    (pressure : Field P T (pressureGradient (a N).highPressure))
    (hCtB : (Ct.normalized hT (S.high N) (S.high_pos N)).WordBound 6 R 1 (highShift N))
    (hpB : (pressure.normalized hT (S.high N) (S.high_pos N)).WordBound 6 R 1 (highShift N))
    (ha : a 0 = 0) (hb : (a 1).mean = 0) (n : ℕ) (hn : N + 1 ≤ n) :
    (F.tailGradeField C hTime Ct hCt pressure ha n hn).WordBound 6 R
      ((1+18*((N+2 : ℕ) : ℝ)^2)*BC.termCost*S.H0^(2*n+2)) (110*(n+1)) := by
  have hc : (a 0).corrector=0 := by rw [ha]; rfl
  have hL := B.tail_linear_bound BC hTime hN hR hRc Ct hCt pressure hCtB hpB n
  have hQ := B.tail_nonlinear_bound BC hN hR hRc hc hb n
  have hs := hL.add hQ
  have he : BC.termCost*S.H0^(2*n+2)+18*((N+2 : ℕ) : ℝ)^2*BC.termCost*S.H0^(2*n+2) =
      (1+18*((N+2 : ℕ) : ℝ)^2)*BC.termCost*S.H0^(2*n+2) := by ring
  rw [he] at hs
  exact hs.of_path_eq (F.tailGradeField C hTime Ct hCt pressure ha n hn)
    (F.tailGradeField_path C hTime Ct hCt pressure ha n hn)

end EulerPacketCylinderField.PrefixBound
