/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedUniformCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionPrimitiveBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketSourcePrimitiveBounds

/-! Reusable bounds for the actual parameters entering the canonical
correction. They all use the same fixed polynomial envelope. -/

@[expose] public section


noncomputable section

namespace EulerPacketInitializedCost

open EulerPacketTerminalDatum EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketCorrectionPrimitive

theorem envelope_bounds (W : ℝ) (hW : 0 ≤ W) :
    1 ≤ envelope W ∧ W ≤ envelope W ∧ EulerPacketRadiusPolynomial.radiusEnvelope W ≤ envelope W ∧
      primitiveEnvelope period W ≤ envelope W := by
  have hrq := EulerPacketRadiusPolynomial.requiredEnvelope_nonneg W hW
  have hm := EulerPacketRadiusPolynomial.meanEnvelope_nonneg W hW
  have hg := EulerPacketRadiusPolynomial.gradeEnvelope_nonneg W hW
  have ht := EulerPacketRadiusPolynomial.terminalEnvelope_nonneg W hW
  have hr : 0 ≤ EulerPacketRadiusPolynomial.radiusEnvelope W := by
    unfold EulerPacketRadiusPolynomial.radiusEnvelope
    positivity
  have hp := (primitive_components period W hW).1
  unfold envelope
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le)}
  {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (BC : CoefficientBudget C) (δ : ℝ) (ξ : U)

theorem actual_parameters (W H0 : ℝ) (hδ : 0 < δ)
    (H : EulerPacketRadiusPolynomial.RadiusPrimitives LM L NB BC δ ξ W) (hH0 : H0 ≤ W) :
    1 ≤ envelope W ∧ initializedRadius LM L NB BC δ ξ ≤ envelope W ∧
    H0 ≤ envelope W ∧ BC.multiplierCost ≤ envelope W ∧
    CorrectionBounds D period (L.correctionCoefficients NB period) (envelope W) := by
  obtain ⟨h1,hW,hR,hP⟩ := envelope_bounds W (zero_le_one.trans H.one)
  have hr := (EulerPacketRadiusPolynomial.initializedRadius_le_envelope LM L NB BC δ ξ W hδ
      H).trans hR
  have hc : BC.multiplierCost ≤ W := by
    have ht := BC.twice_multiplierCost_le
    have hn := BC.multiplierCost_nonneg
    linarith only [ht,hn,H.coefficient_cost]
  exact ⟨h1,hr,hH0.trans hW,hc.trans hW,
    (L.correctionCoefficients_primitive_bound NB period W H.one H.joined_radius H.normal_radius
      H.joined_frame H.joined_first H.normal_amplitude).mono D period hP⟩

end EulerPacketInitializedCost

namespace EulerPacketRadiusPolynomial.RadiusPrimitives

open EulerPacketTerminalDatum EulerPacketProfileRecursion EulerPacketCylinderField

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le)}
  {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  {LM : EulerMeanPacketProvider.Budget M 6 Rm}
  {L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6}
  {NB : EulerTransversePacketJoin.NormalBudget D 6 L.R}
  {BC : CoefficientBudget C} {δ : ℝ} {ξ : U} {X Y : ℝ}

theorem mono (H : RadiusPrimitives LM L NB BC δ ξ X) (hXY : X ≤ Y) :
    RadiusPrimitives LM L NB BC δ ξ Y := {
  one := H.one.trans hXY
  total_time := H.total_time
  mean_time := H.mean_time
  history_inverse_time := H.history_inverse_time.trans hXY
  mean_inverse_time := H.mean_inverse_time.trans hXY
  history_gram := H.history_gram.trans hXY
  original_joined := H.original_joined.trans hXY
  original_mean := H.original_mean.trans hXY
  joined_radius := H.joined_radius.trans hXY
  joined_frame := H.joined_frame.trans hXY
  joined_first := H.joined_first.trans hXY
  joined_curvature := H.joined_curvature.trans hXY
  joined_propagator := H.joined_propagator.trans hXY
  joined_inverse := H.joined_inverse.trans hXY
  normal_radius := H.normal_radius.trans hXY
  normal_amplitude := H.normal_amplitude.trans hXY
  normal_inverse := H.normal_inverse.trans hXY
  mean_radius := H.mean_radius.trans hXY
  mean_frame := H.mean_frame.trans hXY
  mean_first := H.mean_first.trans hXY
  mean_forcing := H.mean_forcing.trans hXY
  coefficient_radius := H.coefficient_radius.trans hXY
  coefficient_cost := H.coefficient_cost.trans hXY
  delta_inverse := H.delta_inverse.trans hXY
  terminal := H.terminal.trans hXY }

end EulerPacketRadiusPolynomial.RadiusPrimitives
