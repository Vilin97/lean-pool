/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardUniformCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedAllOrderBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedUniformBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileEnvelope

@[expose] public section

/-! The actual zero-history correction from the same fixed polynomial
frequency comparison, together with its uniform weighted output bounds. -/

noncomputable section

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPacketCorrectionConstants EulerPacketCorrectionScalar EulerPacketSourceFrequency
  EulerPacketCorrectionCoefficients
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T)
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (Cagree : SourceCoefficientAgreement M D)
  (W : ℝ)
  (hW : EulerPacketForwardRadius.RadiusPrimitives L LM NB
    (forwardCoefficientBudget period M D hTime NB) δ ξ W)
  (hprofile : ∀ t, α*L.g t ≤ W)
  (k : ℝ) (hk : 4 ≤ k) (hX : 64 ≤ expansion k) (hlog : 1 ≤ Real.log k)
  (hfrequency :
    EulerPacketInitializedCost.uniformConstant*W^EulerPacketInitializedCost.uniformPower ≤
    smallPower k)
  (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
  (hF : ∀ t x, fderiv ℝ (Ξ t) x=D.F.field t x)
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1)

def forwardUniformBudget : EulerAllOrderDriftCorrection.Budget period D.T_pos
    (forwardInitializedCorrectionData M D hTime δ hδ ξ hs α Cagree
      (truncation k) (truncation_bounds k (by linarith)).1 k hk) := by
  let BC := forwardCoefficientBudget period M D hTime NB
  let L' := forwardInitializedLinearBudget LM L NB BC δ ξ
  let NB' := forwardInitializedNormalBudget LM L NB BC δ ξ
  let LM' := forwardInitializedMeanBudget LM L NB BC δ ξ
  have guards := forwardInitializedRadius_guards LM L NB BC δ ξ
  let S := Scales.ofTimeProfile L.g L.positive hTime.symm α hα
  have hH0 : S.H0 ≤ W := Scales.ofTimeProfile_H0_le L.g L.positive
    hTime.symm α hα W hW.one hprofile
  have hprofile' : timeProfileChange S.growth hTime=α • L'.g := by
    change timeProfileChange S.growth hTime=α • L.g
    exact Scales.ofTimeProfile_growth L.g L.positive hTime.symm α hα
  let Kc := L.correctionCoefficients NB period
  have costs := EulerPacketInitializedCost.forward_five_costs_bound
    LM L NB BC δ ξ W S.H0 hδ hW S.H0_pos.le hH0
  exact forwardInitializedAllOrderBudget M D hTime δ hδ ξ hs α Cagree
    L' NB' guards.1 LM' guards.2.1 BC guards.2.2.2.2.2 guards.2.2.2.2.1
    hδ1 hα guards.2.2.2.1 guards.2.2.1 S hprofile' Kc k hk hX hlog
    (costs.1.trans hfrequency) (costs.2.1.trans hfrequency) (costs.2.2.1.trans hfrequency)
    (costs.2.2.2.1.trans hfrequency) (costs.2.2.2.2.trans hfrequency) Ξ hΞ hF hdet

theorem forwardUniformBudget_delta :
    (forwardUniformBudget M D hTime δ hδ hδ1 ξ hs α hα L NB LM Cagree
      W hW hprofile k hk hX hlog hfrequency Ξ hΞ hF hdet).delta=delta (expansion k) := rfl

theorem forwardUniformBudget_initialRadius :
    (forwardUniformBudget M D hTime δ hδ hδ1 ξ hs α hα L NB LM Cagree
      W hW hprofile k hk hX hlog hfrequency Ξ hΞ hF hdet).initialRadius=
      initialRadius
        (forwardInitializedRadius LM L NB (forwardCoefficientBudget period M D hTime NB) δ ξ)
        (L.correctionCoefficients NB period).M (L.correctionCoefficients NB period).Rc := rfl


open EulerPacketCorrectionOutput EulerSobolevGevreyOperators EulerAllOrderDriftCorrection

local notation "Q" => forwardUniformBudget M D hTime δ hδ hδ1 ξ hs α hα
  L NB LM Cagree W hW hprofile k hk hX hlog hfrequency Ξ hΞ hF hdet

theorem forwardUniformBudget_weighted (s N : ℕ) (hN : N+6 ≤ s) (t : Icc (0 : ℝ) D.T) :
    weightedNorm period 6 N ((Q).initialRadius/4) (((Q).fieldTower period).realization s t) ≤
      EulerPacketInitializedCost.weightSize W*delta (expansion k) ∧
    weightedNorm period 6 N ((Q).initialRadius/4) (((Q).pressureTower period).realization s t) ≤
      EulerPacketInitializedCost.weightSize W*delta (expansion k) ∧
    weightedNorm period 6 N ((Q).initialRadius/4) (((Q).timeDerivativeTower period).realization s
      t) ≤
      EulerPacketInitializedCost.weightSize W*delta (expansion k) := by
  let BC := forwardCoefficientBudget period M D hTime NB
  let R := forwardInitializedRadius LM L NB BC δ ξ
  let S := Scales.ofTimeProfile L.g L.positive hTime.symm α hα
  let Kc := L.correctionCoefficients NB period
  have hH0 : S.H0 ≤ W := Scales.ofTimeProfile_H0_le L.g L.positive
    hTime.symm α hα W hW.one hprofile
  obtain ⟨_,hR,hH,hC,hK⟩ := EulerPacketInitializedCost.forward_actual_parameters LM L NB BC δ ξ
    W S.H0 hδ hW hH0
  have hR0 : 0 ≤ R := zero_le_one.trans
    (forwardInitializedLinearBudget LM L NB BC δ ξ).radius_one
  obtain ⟨_,_,_,he,hp,ht⟩ := correction_output_bound period D Kc R S.H0 BC.multiplierCost
    (EulerPacketInitializedCost.envelope W) hR0 S.H0_pos.le BC.multiplierCost_nonneg
    hR hH hC hK.inverse hK.base hK.pressure hK.linear hK.quadratic hK.radius
  have hsize : (Q).correctionSize period=correctionBase D*delta (expansion k) := by
    change EulerGevreyMetricEstimate.metricAmplification D.inverseBound⁻¹*(delta (expansion k)/2)=_
    unfold correctionBase
    ring
  have hpressure : (Q).pressureCost period (N+6) (by omega)=
      correctionPressureCost D period Kc R S.H0 BC.multiplierCost := by rfl
  have htime : (Q).timeDerivativeCost period (N+6) (by omega)=
      correctionTimeCost D period Kc R S.H0 BC.multiplierCost := by rfl
  have hqe := (Q).fieldTower_reducedNorm period s N hN t
  have hqp := (Q).pressureTower_reducedNorm_delta period (N+6) (by omega) N (by omega) s hN t
  have hqt := (Q).timeDerivativeTower_reducedNorm_delta period (N+6) (by omega) N (by omega) s hN t
  rw [hsize] at hqe
  rw [hpressure] at hqp
  rw [htime] at hqt
  exact ⟨hqe.trans (mul_le_mul_of_nonneg_right he (delta_pos _).le),
    hqp.trans (mul_le_mul_of_nonneg_right hp (delta_pos _).le),
    hqt.trans (mul_le_mul_of_nonneg_right ht (delta_pos _).le)⟩


end EulerPacketTerminalDatum
