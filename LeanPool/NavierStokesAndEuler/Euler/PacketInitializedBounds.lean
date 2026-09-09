/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedResidualBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedApproximationBounds

@[expose] public section

/-! The literal terminal wave yields the actual finite packet, its small normal
drift, and its exponentially small residual.  Primary bounds and the primary
equation are supplied by the construction itself. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerParameterWordGevrey EulerPacketCoarseMajorant

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)

def initializedPacketField (N : ℕ) (κ : ℝ) :=
  joinedPacketPullbackField period M D hTime τ hτ hτT B
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs)) N κ

def initializedResidualField (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (κ : ℝ) (hκ : κ ≠ 0) :=
  joinedResidualField period M D hTime τ hτ hτT B
    (EulerTransversePacketPrimary.vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (EulerTransversePacketPrimary.scalar τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (fun t => joinedTerminalPrimary_pressure_smooth period M D τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs) t.val)
    (joinedTerminalPrimary_tangent period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimary_equation period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    Cagree N hN κ hκ

variable
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
    δ*‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime=α • L.fullProfile)

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem initializedPacket_normalized_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ)) :
    ((initializedPacketField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹).smul k).WordBound
      6 (4*L.R) (BC.multiplierCost*(fixedVelocityGradeCost L.R S.H0 1+
        fixedVelocityGradeCost L.R S.H0 2+1)) 0 :=
  joinedPacket_normalized_bound period M D hTime τ hτ hτT B L NB W LM WM BC hRc hcost S α hα hgrowth
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimary_budget M D hTime τ hτ hτT B L H NB δ hδ hδ1 ξ hs α hα hR WP S hgrowth)
    rfl (joinedTerminalPrimary_tangent period M D hTime τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs)) N hN k hk hbase

theorem initializedPacket_normal_bound (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ)) :
    (((initializedPacketField M D hTime τ hτ hτT B δ hδ ξ hs α N k⁻¹).smul k).map
      (normalComponentMap D.m₀)).WordBound 6 (4*L.R)
        (BC.multiplierCost*(fixedVelocityGradeCost L.R S.H0 2+2)/k) 0 :=
  joinedPacket_normal_bound period M D hTime τ hτ hτT B L NB W LM WM BC hRc hcost S α hα hgrowth
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimary_budget M D hTime τ hτ hτT B L H NB δ hδ hδ1 ξ hs α hα hR WP S hgrowth)
    rfl (joinedTerminalPrimary_tangent period M D hTime τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs)) N hN k hk hbase

theorem initializedResidual_normalized_bound (Cagree : SourceCoefficientAgreement M D)
    (N : ℕ) (hN : 1 ≤ N) (k X : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k^(1/100 : ℝ))
    (hcoef : BC.multiplierCost ≤ k^(1/100 : ℝ)) (hX : 6 ≤ X) (hNX : X-1 ≤ (N : ℝ)) :
    (((joinedSourceCoefficientData period M D τ hτ hτT B hTime).inverse.multiply
      (initializedResidualField M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k⁻¹
        (inv_ne_zero (by linarith)))).smul k).WordBound
          6 (4*L.R) (Real.exp (-(7/10)*X*Real.log k)) 0 :=
  joinedResidual_normalized_bound period M D hTime τ hτ hτT B L NB W LM WM BC hRc hcost S α hα
    hgrowth
    (EulerTransversePacketPrimary.vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (EulerTransversePacketPrimary.scalar τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimary_budget M D hTime τ hτ hτT B L H NB δ hδ hδ1 ξ hs α hα hR WP S hgrowth)
    (fun t => joinedTerminalPrimary_pressure_smooth period M D τ hτ hτT B
      (initialData D δ hδ (α • ξ) hs) t.val)
    (joinedTerminalPrimary_tangent period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimary_equation period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    Cagree N hN k X hk hbase hcoef hX hNX

end EulerPacketTerminalDatum
