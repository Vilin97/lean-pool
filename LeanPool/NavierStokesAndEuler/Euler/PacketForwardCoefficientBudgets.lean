/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionCoefficientBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCoefficientBudget
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardBudget
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketNormalBudget

@[expose] public section

/-! The actual forward source coefficients supply both the nonlinear-profile
budget and the all-order correction coefficient budget. -/

noncomputable section

namespace EulerPacketCylinderField

open EulerTransversePacketProvider

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)

def forwardCoefficientBudget {R : ℝ} (NB : EulerTransversePacketJoin.NormalBudget D 6 R) :
    CoefficientBudget (sourceCoefficientData P M D (InitialData.zero P D) hTime) :=
  sourceCoefficientBudget P M D (InitialData.zero P D) hTime NB.Rc NB.C
    NB.Rc_nonneg NB.C_nonneg NB.inverse_bound NB.strain_bound

end EulerPacketCylinderField

namespace EulerTransversePacketForward.Budget

open EulerTransversePacketProvider EulerPacketCorrectionCoefficients
  EulerOperatorGevreyCalculus EulerGevrey

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (L : Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)

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

end EulerTransversePacketForward.Budget
