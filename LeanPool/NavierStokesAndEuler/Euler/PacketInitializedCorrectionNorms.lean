/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.SobolevDriftNorm
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldDrift
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldSobolevBudget

/-! Cutoff-independent background, derivative, drift and residual budgets
for the actual initialized correction data. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketCoarseMajorant EulerPacketCorrectionConstants
  EulerCylinderSobolevSpace EulerSobolevGevreyOperators EulerSobolevDriftNorm
  EulerFunctionalVelocity EulerSobolevTransport

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (H : EulerTransversePacketPrimary.Budget L)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := period) L NB)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (joinedSourceCoefficientData period M D τ hτ hτT B hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile)
  (Cagree : SourceCoefficientAgreement M D)
  (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth hbase

theorem initializedCorrection_background (s Q : ℕ) (hQ : Q + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ * (4 * L.R) ≤ 1 / 2) (t : Icc (0 : ℝ) D.T) :
    weightedNorm period 6 Q ρ
      ((initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k
          hk).approximation.realization s t)
        ≤ 2*velocity L.R S.H0 BC.multiplierCost := by
  have hz := initializedNormalizedField_bound M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  exact hz.toFieldTower_weightedNorm_le_two (by have := L.radius_bounds.1; linarith)
    (velocity_nonneg L.R S.H0 BC.multiplierCost (zero_le_one.trans L.radius_bounds.1)
      BC.multiplierCost_nonneg) s Q hQ ρ hρ hsmall t

theorem initializedCorrection_background_derivative (s Q : ℕ) (hQ : Q + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ * (4 * L.R) ≤ 1 / 2) (t : Icc (0 : ℝ) D.T) :
    (∑ i : Fin 4, weightedNorm period 6 Q ρ (derivativeOperator period s i
      ((initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k
          hk).approximation.realization (s+1) t)))
        ≤ 12*velocity L.R S.H0 BC.multiplierCost*(4*L.R) := by
  have hz := initializedNormalizedField_bound M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  exact hz.toFieldTower_weightedDerivativeNorm_le_twelve (by have := L.radius_bounds.1; linarith)
    (velocity_nonneg L.R S.H0 BC.multiplierCost (zero_le_one.trans L.radius_bounds.1)
      BC.multiplierCost_nonneg) s Q hQ ρ hρ hsmall t

theorem initializedCorrection_drift (s Q : ℕ) (hQ : Q + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ * (4 * L.R) ≤ 1 / 2) (t : Icc (0 : ℝ) D.T) :
    weightedDriftNorm period 6 Q ρ (velocityMap (velocityComponents k⁻¹ D.m₀))
      ((initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k
          hk).approximation.realization s t)
        ≤ drift L.R S.H0 BC.multiplierCost/k := by
  have hz := initializedNormalizedField_bound M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  have hn := initializedNormalizedField_normal_bound M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase
  have hR0 := zero_le_one.trans L.radius_bounds.1
  have hk0 : 0 < k := by linarith
  have hd := hz.toFieldTower_weightedDrift_le_two k⁻¹ D.m₀ hn (by linarith)
    (velocity_nonneg L.R S.H0 BC.multiplierCost hR0 BC.multiplierCost_nonneg)
    (div_nonneg (normal_nonneg L.R S.H0 BC.multiplierCost hR0 BC.multiplierCost_nonneg) hk0.le)
    s Q hQ ρ hρ hsmall t
  exact hd.trans_eq (drift_div_frequency L.R S.H0 BC.multiplierCost k hk0)

theorem initializedCorrection_residual (X : ℝ)
    (hcoef : BC.multiplierCost ≤ k ^ (1 / 100 : ℝ)) (hX : 6 ≤ X) (hNX : X - 1 ≤ (N : ℝ))
    (s Q : ℕ) (hQ : Q + 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (hsmall : ρ * (4 * L.R) ≤ 1 / 2) (t : Icc (0 : ℝ) D.T) :
    weightedNorm period 6 Q ρ
      ((initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k
          hk).residual.realization s t)
        ≤ 2*Real.exp (-(7/10)*X*Real.log k) := by
  have hr := initializedNormalizedResidualField_bound M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth Cagree N hN k X hk hbase hcoef hX hNX
  exact hr.toFieldTower_weightedNorm_le_two (by have := L.radius_bounds.1; linarith)
    (Real.exp_pos _).le s Q hQ ρ hρ hsmall t

end EulerPacketTerminalDatum
