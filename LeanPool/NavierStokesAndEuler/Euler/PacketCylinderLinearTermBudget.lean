/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketTimeProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer

@[expose] public section

/-! The old-corrector time term and old pressure term use the same fixed coefficient budget. -/

noncomputable section

namespace EulerPacketCylinderField.CoefficientBudget

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerPacketTimeProfile EulerPacketShiftArithmetic

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {C : CoefficientData P T O}
  (B : CoefficientBudget C)

theorem slowCost_le : B.slowCost ≤ B.termCost := by
  have h := B.twice_slowCost_le
  have h0 := B.slowCost_nonneg
  linarith

theorem fastCost_le : B.fastCost ≤ B.termCost := B.fastCost_le_slowCost.trans B.slowCost_le

theorem linearCost_le : B.linearCost ≤ B.termCost := by
  have h := B.twice_linearCost_le
  have h0 := B.linearCost_nonneg
  linarith

theorem multiplierCost_le : B.multiplierCost ≤ B.termCost := by
  have h := B.twice_multiplierCost_le
  have h0 := B.multiplierCost_nonneg
  linarith

variable (hT : 0 < T) (S : Scales (Icc (0 : ℝ) T)) (p : ℕ)
  (b : C(Icc (0 : ℝ) T,ℝ)) (hb : ∀ t, 0 < b t)

theorem previousLinear_bound {raw raw_t : VectorField}
    (G : Field P T raw) (H : Field P T raw_t) (htime : TimeDerivative hT.le G H)
    {R : ℝ}
    (hG : (G.normalized hT.le (S.high (p-1)) (S.high_pos (p-1))).WordBound 6 R 1 (highShift (p-1)))
    (hH : (H.normalized hT.le (S.high (p-1)) (S.high_pos (p-1))).WordBound 6 R 1 (highShift (p-1)))
    (hRc : sobolevCoefficientRadius (Fin 4) B.Rc ≤ R)
    (hprofile : ∀ t, S.high (p-1) t ≤ b t) :
    ((Field.linearPart C.strain G H hT htime O.interval C.interval_eq).normalized hT.le b
      hb).WordBound
      6 R B.linearCost (highShift (p-1)) := by
  have hm := Field.WordBound.normalized_linearPart hT.le (S.high (p-1)) (S.high_pos (p-1))
    C.strain G H hT htime O.interval C.interval_eq hG hH
    B.Rc B.amplitude B.Rc_nonneg B.amplitude_nonneg zero_le_one hRc B.strain_bound
  have h := hm.enlargeProfile hT.le b hb hprofile
  simpa only [linearCost,multiplierCost,mul_one] using h

theorem previousPressure_bound (q : ScalarField) (G : Field P T (pressureGradient q))
    {R : ℝ}
    (hG : (G.normalized hT.le (S.high (p-1)) (S.high_pos (p-1))).WordBound 6 R 1 (highShift (p-1)))
    (hRc : sobolevCoefficientRadius (Fin 4) B.Rc ≤ R)
    (hprofile : ∀ t, S.high (p-1) t ≤ b t) :
    ((Field.slowPressure C.inverse q G).normalized hT.le b hb).WordBound 6 R B.multiplierCost
      (highShift (p-1)) := by
  have hm := Field.WordBound.normalized_slowPressure hT.le (S.high (p-1)) (S.high_pos (p-1))
    C.inverse q G hG B.Rc B.amplitude B.Rc_nonneg B.amplitude_nonneg zero_le_one hRc B.inverse_bound
  have h := hm.enlargeProfile hT.le b hb hprofile
  simpa only [multiplierCost,mul_one] using h

end EulerPacketCylinderField.CoefficientBudget
