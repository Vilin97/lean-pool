/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardUniformProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceResidualFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketTailBase
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileTailEstimates

/-! Exponentially small literal residual for the actual zero-history packet. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketTimeProfile EulerParameterWordGevrey EulerPacketCoarseMajorant
  EulerTransversePacketProvider

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (Y : InitialData P D)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketForward.Budget.GradeGuards (P := P) L NB 1)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (sourceCoefficientData P M D (InitialData.zero P D) hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (S : Scales (Icc (0 : ℝ) M.T)) (α : ℝ) (hα : 0 < α)
  (hgrowth : timeProfileChange S.growth hTime = α • L.g)
  (hprimaryBudget : ProfileBudget (forwardSourcePrimaryWitness P M D hTime Y) S L.R 1)

include NB W LM WM BC hRc hcost hα hgrowth hprimaryBudget

theorem forwardTailSum_normalized_bound (N : ℕ) (hN : 1 ≤ N) (k X : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (hcoef : BC.multiplierCost ≤ k ^ (1 / 100 : ℝ))
    (hX : 6 ≤ X) (hNX : X - 1 ≤ (N : ℝ)) :
    (((sourceCoefficientData P M D (InitialData.zero P D) hTime).inverse.multiply
      (sourceTailSumField P M D hTime (InitialData.zero P D) Y N k⁻¹)).smul k).WordBound
        6 (4*L.R) (Real.exp (-(7/10)*X*Real.log k)) 0 := by
  let a := sourceProfiles P M D (InitialData.zero P D) Y
  let G : ∀ i, i ≤ N → ProfileRegularity P M.T M.T_pos.le D.support (a i) :=
    fun i _ => sourceProfileWitness P M D hTime (InitialData.zero P D) Y i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => forwardSource_profile_budgets P M D hTime Y L NB W LM WM BC
      hRc hcost S α hα hgrowth hprimaryBudget i hi
  have ha : a 0 = 0 := profiles_zero _ _
  have hb : (a 1).mean = 0 := by
    simp only [a,sourceProfiles,profiles_one,homogeneousPrimary,primaryProfile]
  exact ProfileRegularity.normalized_tail_bound M.T_pos G BC hG hN L.radius_one hRc ha hb
    k X hk hbase hcoef hX hNX

theorem forwardResidual_normalized_bound (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k X : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (hcoef : BC.multiplierCost ≤ k ^ (1 / 100 : ℝ))
    (hX : 6 ≤ X) (hNX : X - 1 ≤ (N : ℝ)) :
    (((sourceCoefficientData P M D (InitialData.zero P D) hTime).inverse.multiply
      (sourceResidualField P M D hTime (InitialData.zero P D) Y Cagree N hN
        k⁻¹ (inv_ne_zero (by linarith)))).smul k).WordBound
          6 (4*L.R) (Real.exp (-(7/10)*X*Real.log k)) 0 := by
  have h := forwardTailSum_normalized_bound P M D hTime Y L NB W LM WM BC
    hRc hcost S α hα hgrowth hprimaryBudget N hN k X hk hbase hcoef hX hNX
  exact h.of_path_eq _ rfl

end EulerPacketCylinderField
