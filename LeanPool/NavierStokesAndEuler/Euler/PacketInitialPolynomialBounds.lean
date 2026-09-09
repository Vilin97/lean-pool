/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialCostPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedInitial
import LeanPool.NavierStokesAndEuler.Euler.PacketUniformInitialBounds

/-! Fixed-order source polynomial bounds for the literal initial increments.
These use the same finite frequency guard as the constructed exact packet. -/

@[expose] public section


noncomputable section

namespace EulerPacketUniformSource

theorem initial_frequency_guard (X k : ℝ) (hX : 1 ≤ X)
    (h : frequencyConstant * X ^ frequencyPower ≤ EulerPacketSourceFrequency.smallPower k) :
    EulerPacketInitializedCost.uniformConstant *
      (profileEnvelope X)^EulerPacketInitializedCost.uniformPower ≤
        EulerPacketSourceFrequency.smallPower k := by
  have hW := (profileEnvelope_bounds X hX).1
  exact (EulerPacketInitializedOutputCost.envelope_components _ (zero_le_one.trans hW)).1.trans
    ((EulerPacketInitializedOutputCost.envelope_bound _ hW).trans
      ((frequency_bound X hX).trans h))

end EulerPacketUniformSource

namespace EulerPacketTerminalDatum

open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketCorrectionCoefficients EulerPhysicalL2Scaling
  EulerPacketUniformSource EulerPacketInitialCost EulerPacketSourceFrequency

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (X : ℝ) (hX : 1 ≤ X)
  (hW : EulerPacketRadiusPolynomial.RadiusPrimitives LM L NB
    (joinedCoefficientBudget period M D hTime τ hτ hτT B NB) δ ξ (profileEnvelope X))
  (hprofile : ∀ t, α * L.fullProfile t ≤ profileEnvelope X)
  (k : ℝ) (hk : 4 ≤ k)
  (hfrequency : frequencyConstant * X ^ frequencyPower ≤ smallPower k)

include hδ1 hα L NB LM hX hW hprofile hk hfrequency

theorem initialized_initial_polynomial_bounds (s : ℕ) :
    derivativeSum s (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α (truncation k) k) ≤
      (M.ℓ⁻¹)^s*k^s*α*(sourceConstant s*X^sourcePower s) ∧
    derivativeSum s (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α (truncation k) k) ≤
      (M.ℓ⁻¹)^s/k^2*(sourceConstant s*X^sourcePower s) := by
  have h := initialized_uniform_initial_bounds M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα
    L NB LM (profileEnvelope X) hW hprofile k hk (initial_frequency_guard X k hX hfrequency) s
  have hc := source_bound s X hX
  have hell : 0 ≤ M.ℓ⁻¹ := (inv_pos.mpr M.ℓ_pos).le
  have hk0 : 0 ≤ k := by linarith only [hk]
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_left hc (by positivity)),
    h.2.trans (mul_le_mul_of_nonneg_left hc (by positivity))⟩

end EulerPacketTerminalDatum
