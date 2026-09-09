/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardResidualBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardApproximationBounds

@[expose] public section

/-! Actual finite velocity, normal drift and residual estimates for the
zero-history recursion initialized by the literal compact periodic wave. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketCoarseMajorant

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

def forwardInitializedPacketField (N : ℕ) (κ : ℝ) :=
  sourcePacketPullbackField period M D hTime (InitialData.zero period D)
    (initialData D δ hδ (α • ξ) hs) N κ

def forwardInitializedResidualField (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) (hκ : κ ≠ 0) :=
  sourceResidualField period M D hTime (InitialData.zero period D)
    (initialData D δ hδ (α • ξ) hs) Cagree N hN κ hκ

variable
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB 1)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (sourceCoefficientData period M D (InitialData.zero period D) hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketForward.Budget.GradeGuards (P := period) L NB
    (wordCost (Fin 4) 6 δ*‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.g)

include NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem forwardInitializedPacket_normalized_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ)) :
    ((forwardInitializedPacketField M D hTime δ hδ ξ hs α N k⁻¹).smul k).WordBound
      6 (4*L.R) (BC.multiplierCost*(fixedVelocityGradeCost L.R S.H0 1+
        fixedVelocityGradeCost L.R S.H0 2+1)) 0 :=
  forwardPacket_normalized_bound period M D hTime (initialData D δ hδ (α • ξ) hs)
    L NB W LM WM BC hRc hcost S α hα hgrowth
    (forwardInitialized_primary_budget M D hTime δ hδ ξ hs α L NB hδ1 hα hR WP S hgrowth)
    N hN k hk hbase

theorem forwardInitializedPacket_normal_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ)) :
    (((forwardInitializedPacketField M D hTime δ hδ ξ hs α N k⁻¹).smul k).map
      (normalComponentMap D.m₀)).WordBound 6 (4*L.R)
        (BC.multiplierCost*(fixedVelocityGradeCost L.R S.H0 2+2)/k) 0 :=
  forwardPacket_normal_bound period M D hTime (initialData D δ hδ (α • ξ) hs)
    L NB W LM WM BC hRc hcost S α hα hgrowth
    (forwardInitialized_primary_budget M D hTime δ hδ ξ hs α L NB hδ1 hα hR WP S hgrowth)
    N hN k hk hbase

theorem forwardInitializedResidual_normalized_bound (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k X : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ))
    (hcoef : BC.multiplierCost ≤ k^(1/100 : ℝ)) (hX : 6 ≤ X) (hNX : X-1 ≤ (N : ℝ)) :
    (((sourceCoefficientData period M D (InitialData.zero period D) hTime).inverse.multiply
      (forwardInitializedResidualField M D hTime δ hδ ξ hs α Cagree N hN k⁻¹
        (inv_ne_zero (by linarith)))).smul k).WordBound
          6 (4*L.R) (Real.exp (-(7/10)*X*Real.log k)) 0 :=
  forwardResidual_normalized_bound period M D hTime (initialData D δ hδ (α • ξ) hs)
    L NB W LM WM BC hRc hcost S α hα hgrowth
    (forwardInitialized_primary_budget M D hTime δ hδ ξ hs α L NB hδ1 hα hR WP S hgrowth)
    Cagree N hN k X hk hbase hcoef hX hNX

end EulerPacketTerminalDatum
