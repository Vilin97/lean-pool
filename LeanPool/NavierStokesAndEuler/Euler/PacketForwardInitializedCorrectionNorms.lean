/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldDrift

@[expose] public section

/-! Cutoff-independent background, derivative, drift and residual budgets
for the actual zero-history correction data. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketCoarseMajorant EulerPacketCorrectionConstants
  EulerCylinderSobolevSpace EulerSobolevGevreyOperators EulerSobolevDriftNorm
  EulerFunctionalVelocity EulerSobolevTransport

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB 1)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (sourceCoefficientData period M D (InitialData.zero period D) hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB (wordCost (Fin 4) 6
    δ*‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime=α • L.g)
  (Cagree : SourceCoefficientAgreement M D)
  (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ))

include NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth hbase

theorem forwardInitializedCorrection_background (s Q : ℕ) (hQ : Q+6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ*(4*L.R) ≤ 1/2) (t : Icc (0 : ℝ) D.T) :
    weightedNorm period 6 Q ρ
      ((forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k
        hk).approximation.realization s t)
        ≤ 2*velocity L.R S.H0 BC.multiplierCost := by
  have hz := forwardInitializedNormalizedField_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  exact hz.toFieldTower_weightedNorm_le_two (by have := L.radius_one; linarith)
    (velocity_nonneg L.R S.H0 BC.multiplierCost (zero_le_one.trans L.radius_one)
      BC.multiplierCost_nonneg) s Q hQ ρ hρ hsmall t

theorem forwardInitializedCorrection_background_derivative (s Q : ℕ) (hQ : Q+6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ*(4*L.R) ≤ 1/2) (t : Icc (0 : ℝ) D.T) :
    (∑ i : Fin 4, weightedNorm period 6 Q ρ (derivativeOperator period s i
      ((forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k
        hk).approximation.realization (s+1) t)))
        ≤ 12*velocity L.R S.H0 BC.multiplierCost*(4*L.R) := by
  have hz := forwardInitializedNormalizedField_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  exact hz.toFieldTower_weightedDerivativeNorm_le_twelve (by have := L.radius_one; linarith)
    (velocity_nonneg L.R S.H0 BC.multiplierCost (zero_le_one.trans L.radius_one)
      BC.multiplierCost_nonneg) s Q hQ ρ hρ hsmall t

theorem forwardInitializedCorrection_drift (s Q : ℕ) (hQ : Q+6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ*(4*L.R) ≤ 1/2) (t : Icc (0 : ℝ) D.T) :
    weightedDriftNorm period 6 Q ρ (velocityMap (velocityComponents k⁻¹ D.m₀))
      ((forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k
        hk).approximation.realization s t)
        ≤ drift L.R S.H0 BC.multiplierCost/k := by
  have hz := forwardInitializedNormalizedField_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  have hn := forwardInitializedNormalizedField_normal_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  have hR0 := zero_le_one.trans L.radius_one
  have hk0 : 0 < k := by linarith
  have hd := hz.toFieldTower_weightedDrift_le_two k⁻¹ D.m₀ hn (by linarith)
    (velocity_nonneg L.R S.H0 BC.multiplierCost hR0 BC.multiplierCost_nonneg)
    (div_nonneg (normal_nonneg L.R S.H0 BC.multiplierCost hR0 BC.multiplierCost_nonneg) hk0.le)
    s Q hQ ρ hρ hsmall t
  exact hd.trans_eq (drift_div_frequency L.R S.H0 BC.multiplierCost k hk0)

theorem forwardInitializedCorrection_residual (X : ℝ)
    (hcoef : BC.multiplierCost ≤ k^(1/100 : ℝ)) (hX : 6 ≤ X) (hNX : X-1 ≤ (N : ℝ))
    (s Q : ℕ) (hQ : Q+6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (hsmall : ρ*(4*L.R) ≤ 1/2) (t : Icc (0 : ℝ) D.T) :
    weightedNorm period 6 Q ρ
      ((forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree N hN k
        hk).residual.realization s t)
        ≤ 2*Real.exp (-(7/10)*X*Real.log k) := by
  have hr := forwardInitializedNormalizedResidualField_bound M D hTime δ hδ ξ hs α
    L NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth Cagree N hN k X hk hbase hcoef hX hNX
  exact hr.toFieldTower_weightedNorm_le_two (by have := L.radius_one; linarith)
    (Real.exp_pos _).le s Q hQ ρ hρ hsmall t

end EulerPacketTerminalDatum
