/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedUniformBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedParameterBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionOutputPolynomial

@[expose] public section

/-! The very same canonical correction has uniform all-order weighted
bounds for its field, pressure and actual time derivative. -/

noncomputable section

namespace EulerPacketInitializedCost

open EulerPacketCorrectionOutput EulerPacketProfileRecursion EulerPacketTerminalDatum

def weightSize (W : ℝ) : ℝ := outputEnvelope period (envelope W)

theorem weightSize_pos (W : ℝ) (hW : 0 ≤ W) : 0 < weightSize W :=
  zero_lt_one.trans_le (output_components period (envelope W)
    (zero_le_one.trans (envelope_bounds W hW).1)).1

end EulerPacketInitializedCost

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPacketCorrectionConstants EulerPacketCorrectionScalar EulerPacketSourceFrequency
  EulerPacketCorrectionCoefficients EulerPacketCorrectionOutput EulerSobolevGevreyOperators
  EulerAllOrderDriftCorrection
open scoped ContDiff

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T=D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
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
  (hprofile : ∀ t, α*L.fullProfile t ≤ W)
  (k : ℝ) (hk : 4 ≤ k) (hX : 64 ≤ expansion k) (hlog : 1 ≤ Real.log k)
  (hfrequency :
    EulerPacketInitializedCost.uniformConstant*W^EulerPacketInitializedCost.uniformPower ≤
    smallPower k)
  (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
  (hF : ∀ t x, fderiv ℝ (Ξ t) x=D.F.field t x)
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1)

local notation "Q" => initializedUniformBudget M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα
  L NB LM Cagree W hW hprofile k hk hX hlog hfrequency Ξ hΞ hF hdet

theorem initializedUniformBudget_weighted (s N : ℕ) (hN : N+6 ≤ s) (t : Icc (0 : ℝ) D.T) :
    weightedNorm period 6 N ((Q).initialRadius/4) (((Q).fieldTower period).realization s t) ≤
      EulerPacketInitializedCost.weightSize W*delta (expansion k) ∧
    weightedNorm period 6 N ((Q).initialRadius/4) (((Q).pressureTower period).realization s t) ≤
      EulerPacketInitializedCost.weightSize W*delta (expansion k) ∧
    weightedNorm period 6 N ((Q).initialRadius/4) (((Q).timeDerivativeTower period).realization s
      t) ≤
      EulerPacketInitializedCost.weightSize W*delta (expansion k) := by
  let BC := joinedCoefficientBudget period M D hTime τ hτ hτT B NB
  let R := initializedRadius LM L NB BC δ ξ
  let S := Scales.ofTimeProfile L.fullProfile L.fullProfile_pos hTime.symm α hα
  let Kc := L.correctionCoefficients NB period
  have hH0 : S.H0 ≤ W := Scales.ofTimeProfile_H0_le L.fullProfile L.fullProfile_pos
    hTime.symm α hα W hW.one hprofile
  obtain ⟨_,hR,hH,hC,hK⟩ := EulerPacketInitializedCost.actual_parameters LM L NB BC δ ξ
    W S.H0 hδ hW hH0
  have hR0 : 0 ≤ R := zero_le_one.trans
    (initializedJoinedBudget LM L NB BC δ ξ).radius_bounds.1
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
