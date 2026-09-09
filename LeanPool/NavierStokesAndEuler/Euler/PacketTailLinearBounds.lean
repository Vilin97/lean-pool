/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownPieceBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderLinearTermBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds

/-! The only surviving linear tail grade has the same fixed coefficient budget. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerPacketShiftArithmetic EulerParameterWordGevrey

theorem CoefficientBudget.linear_and_pressure_le {P T : ℝ} [Fact (0 < P)]
    {O : Operators} {C : CoefficientData P T O} (B : CoefficientBudget C) :
    B.linearCost+B.multiplierCost ≤ B.termCost := by
  have hs := B.slowCost_nonneg
  unfold CoefficientBudget.linearCost CoefficientBudget.termCost
  linarith

namespace PrefixBound

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile}
  {F : PrefixFields P T (N + 1) a} {hT : 0 ≤ T}
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} (B : PrefixBound F hT S R)
  {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

include B

theorem tail_linear_bound (hTime : 0 < T) (hN : 1 ≤ N) (hR : 1 ≤ R)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    {correctorT : VectorField} (Ct : Field P T correctorT)
    (hCt : TimeDerivative hTime.le (F.corrector N (by omega)) Ct)
    (pressure : Field P T (pressureGradient (a N).highPressure))
    (hCtB : (Ct.normalized hT (S.high N) (S.high_pos N)).WordBound 6 R 1 (highShift N))
    (hpB : (pressure.normalized hT (S.high N) (S.high_pos N)).WordBound 6 R 1 (highShift N))
    (n : ℕ) :
    (F.tailLinearField C hTime Ct hCt pressure n).WordBound 6 R
      (BC.termCost*S.H0^(2*n+2)) (110*(n+1)) := by
  by_cases hn : n=N+1
  · have hC := B.corrector N (by omega) hN
    have hL := BC.previousLinear_bound hTime S (N+1) (S.high N) (S.high_pos N)
      (F.corrector N (by omega)) Ct hCt
      (by simpa only [Field.WordBound,Field.normalized_path,Nat.add_sub_cancel] using hC)
      (by
          simpa only [Field.WordBound,Field.normalized_path,Nat.add_sub_cancel] using hCtB) hRc (by
              simp)
    have hQ := BC.previousPressure_bound hTime S (N+1) (S.high N) (S.high_pos N)
      (a N).highPressure pressure
      (by
          simpa only [Field.WordBound,Field.normalized_path,Nat.add_sub_cancel] using hpB) hRc (by
              simp)
    have hL' := hL.remove_profile hTime.le (S.high N) (S.high_pos N)
      (S.H0^(2*N)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse N hN)
    have hQ' := hQ.remove_profile hTime.le (S.high N) (S.high_pos N)
      (S.H0^(2*N)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse N hN)
    have hs := hL'.add hQ'
    have ha : S.H0^(2*N)*BC.linearCost+S.H0^(2*N)*BC.multiplierCost ≤
        BC.termCost*S.H0^(2*n+2) := by
      calc
        _ = (BC.linearCost+BC.multiplierCost)*S.H0^(2*N) := by ring
        _ ≤ BC.termCost*S.H0^(2*N) :=
          mul_le_mul_of_nonneg_right BC.linear_and_pressure_le (pow_nonneg S.H0_pos.le _)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ S.H0_one_le (by omega)) BC.termCost_nonneg
    have hs' := (hs.mono_amplitude (zero_le_one.trans hR) ha).mono_shift hR
      (mul_nonneg BC.termCost_nonneg (pow_nonneg S.H0_pos.le _))
      (show highShift (N+1-1) ≤ 110*(n+1) by unfold highShift; omega)
    apply hs'.ofRawEq (F.tailLinearField C hTime Ct hCt pressure n)
    intro t x θ
    simp only [ite_eq_left hn]
    rfl
  · exact (Field.wordBound_of_zero (F.tailLinearField C hTime Ct hCt pressure n)
      (fun _ _ _ => by rw [ite_eq_right hn]) 6 R (110*(n+1))).mono_amplitude
      (zero_le_one.trans hR) (mul_nonneg BC.termCost_nonneg (pow_nonneg S.H0_pos.le _))

end PrefixBound
end EulerPacketCylinderField
