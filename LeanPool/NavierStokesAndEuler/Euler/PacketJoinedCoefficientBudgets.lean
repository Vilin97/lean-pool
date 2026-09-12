/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionCoefficientBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCoefficientBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceOperators
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketNormalBudget
public import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus

/-! Both nonlinear-profile and exact-correction coefficient budgets are
derived from the original joined-source coefficient bounds. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open EulerTransversePacketProvider

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))

/-- Joined coefficient budget as an element of `CoefficientBudget (joinedSourceCoefficientData P
M D τ hτ hτT B hTime)`. -/
def joinedCoefficientBudget {R : ℝ} (NB : EulerTransversePacketJoin.NormalBudget D 6 R) :
    CoefficientBudget (joinedSourceCoefficientData P M D τ hτ hτT B hTime) :=
  (sourceCoefficientBudget P M D (InitialData.zero P D) hTime NB.Rc NB.C
    NB.Rc_nonneg NB.C_nonneg NB.inverse_bound NB.strain_bound).ofRawEq
    (joinedSourceCoefficientData P M D τ hτ hτT B hTime)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

end EulerPacketCylinderField

namespace EulerTransversePacketJoin.Budget

open EulerTransversePacketProvider EulerPacketCorrectionCoefficients
  EulerOperatorGevreyCalculus EulerGevrey

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}
  (L : Budget D τ hτ hτT B (Fin 4) 6) (NB : NormalBudget D 6 L.R)

/-- No additional coefficient-bound hypothesis is needed by correction:
the source frame, frame derivative and inverse bounds already suffice. -/
def correctionCoefficients (P : ℝ) [Fact (0 < P)] : CorrectionCoefficientBudget D P :=
  correctionCoefficientBudget D P (max L.Rc NB.Rc) L.C₀ L.C₁ NB.C
    (L.Rc_nonneg.trans (le_max_left _ _)) L.C₀_nonneg L.C₁_nonneg NB.C_nonneg
    (fun n t x => (L.frame_bound n t x).trans
      (mul_le_mul_of_nonneg_left
        (majorant_radius_mono L.Rc (max L.Rc NB.Rc) L.Rc_nonneg (le_max_left _ _) 0 n) L.C₀_nonneg))
    (fun n t x => (L.frameDerivative_bound n t x).trans
      (mul_le_mul_of_nonneg_left
        (majorant_radius_mono L.Rc (max L.Rc NB.Rc) L.Rc_nonneg (le_max_left _ _) 0 n) L.C₁_nonneg))
    (fun n t x => (NB.inverse_bound n t x).trans
      (mul_le_mul_of_nonneg_left
        (majorant_radius_mono NB.Rc (max L.Rc NB.Rc) NB.Rc_nonneg (le_max_right _ _) 0 n)
            NB.C_nonneg))

end EulerTransversePacketJoin.Budget
