/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedUniformCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileEnvelope

/-! An actual canonical all-order correction from one polynomial frequency
guard. This constructor does not appeal to an eventual threshold depending
on a chosen parent or on an arbitrary radius witness. -/

@[expose] public section


noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPacketCorrectionConstants EulerPacketCorrectionScalar EulerPacketSourceFrequency
  EulerPacketCorrectionCoefficients
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (Cagree : SourceCoefficientAgreement M D)
  (W : ℝ)
  (hW : EulerPacketRadiusPolynomial.RadiusPrimitives LM L NB
    (joinedCoefficientBudget period M D hTime τ hτ hτT B NB) δ ξ W)
  (hprofile : ∀ t, α * L.fullProfile t ≤ W)
  (k : ℝ) (hk : 4 ≤ k) (hX : 64 ≤ expansion k) (hlog : 1 ≤ Real.log k)
  (hfrequency :
      EulerPacketInitializedCost.uniformConstant * W ^ EulerPacketInitializedCost.uniformPower ≤
    smallPower k)
  (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
  (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)

/-- Initialized uniform budget used in packet initialized uniform budget. -/
def initializedUniformBudget : EulerAllOrderDriftCorrection.Budget period D.T_pos
    (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
      (truncation k) (truncation_bounds k (by linarith)).1 k hk) := by
  let BC := joinedCoefficientBudget period M D hTime τ hτ hτT B NB
  let L' := initializedJoinedBudget LM L NB BC δ ξ
  let H' := initializedPrimaryBudget LM L NB BC δ ξ
  let NB' := initializedNormalBudget LM L NB BC δ ξ
  let LM' := initializedMeanBudget LM L NB BC δ ξ
  have guards := initializedRadius_guards LM L NB BC δ ξ
  let S := Scales.ofTimeProfile L.fullProfile L.fullProfile_pos hTime.symm α hα
  have hH0 : S.H0 ≤ W := Scales.ofTimeProfile_H0_le L.fullProfile L.fullProfile_pos
    hTime.symm α hα W hW.one hprofile
  have hprofile' : timeProfileChange S.growth hTime=α • L'.fullProfile := by
    change timeProfileChange S.growth hTime=α • L.fullProfile
    exact Scales.ofTimeProfile_growth L.fullProfile L.fullProfile_pos hTime.symm α hα
  let Kc := L.correctionCoefficients NB period
  have costs := EulerPacketInitializedCost.initialized_five_costs_bound
    LM L NB BC δ ξ W S.H0 hδ hW S.H0_pos.le hH0
  exact initializedAllOrderBudget M D hTime τ hτ hτT B δ hδ ξ hs α Cagree
    L' H' NB' guards.1 LM' guards.2.1 BC guards.2.2.2.2.2 guards.2.2.2.2.1
    hδ1 hα guards.2.2.2.1 guards.2.2.1 S hprofile' Kc k hk hX hlog
    (costs.1.trans hfrequency) (costs.2.1.trans hfrequency) (costs.2.2.1.trans hfrequency)
    (costs.2.2.2.1.trans hfrequency) (costs.2.2.2.2.trans hfrequency) Ξ hΞ hF hdet

theorem initializedUniformBudget_delta :
    (initializedUniformBudget M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα L NB LM Cagree
      W hW hprofile k hk hX hlog hfrequency Ξ hΞ hF hdet).delta=delta (expansion k) := rfl

theorem initializedUniformBudget_initialRadius :
    (initializedUniformBudget M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα L NB LM Cagree
      W hW hprofile k hk hX hlog hfrequency Ξ hΞ hF hdet).initialRadius =
      initialRadius
        (initializedRadius LM L NB (joinedCoefficientBudget period M D hTime τ hτ hτT B NB) δ ξ)
        (L.correctionCoefficients NB period).M (L.correctionCoefficients NB period).Rc := rfl

end EulerPacketTerminalDatum
