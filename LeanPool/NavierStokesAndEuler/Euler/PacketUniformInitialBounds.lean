/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialCostPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedInitial
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedInitialExact
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedParameterBounds

/-! The actual initial increments for the canonical uniformly selected
packet satisfy source (22), with fixed-order polynomial costs. -/

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
  (W : ℝ)
  (hW : EulerPacketRadiusPolynomial.RadiusPrimitives LM L NB
    (joinedCoefficientBudget period M D hTime τ hτ hτT B NB) δ ξ W)
  (hprofile : ∀ t, α * L.fullProfile t ≤ W)
  (k : ℝ) (hk : 4 ≤ k)
  (hfrequency :
      EulerPacketInitializedCost.uniformConstant * W ^ EulerPacketInitializedCost.uniformPower ≤
    smallPower k)

open EulerPhysicalL2Scaling EulerPacketPhysicalCost EulerCylinderCoordinates

include hδ1 hα L NB LM hW hprofile hk hfrequency

theorem initialized_uniform_initial_bounds (s : ℕ) :
    derivativeSum s (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α (truncation k) k) ≤
      (M.ℓ⁻¹)^s*k^s*α*EulerPacketInitialCost.envelope s (EulerPacketInitializedCost.envelope W) ∧
    derivativeSum s (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α (truncation k) k) ≤
      (M.ℓ⁻¹)^s/k^2*EulerPacketInitialCost.envelope s (EulerPacketInitializedCost.envelope W) := by
  let BC := joinedCoefficientBudget period M D hTime τ hτ hτT B NB
  let L' := initializedJoinedBudget LM L NB BC δ ξ
  let H' := initializedPrimaryBudget LM L NB BC δ ξ
  let NB' := initializedNormalBudget LM L NB BC δ ξ
  let LM' := initializedMeanBudget LM L NB BC δ ξ
  have guards := initializedRadius_guards LM L NB BC δ ξ
  let S := Scales.ofTimeProfile L.fullProfile L.fullProfile_pos hTime.symm α hα
  have hH0 : S.H0 ≤ W := Scales.ofTimeProfile_H0_le L.fullProfile L.fullProfile_pos
    hTime.symm α hα W hW.one hprofile
  have hgrowth : timeProfileChange S.growth hTime=α • L'.fullProfile :=
    Scales.ofTimeProfile_growth L.fullProfile L.fullProfile_pos hTime.symm α hα
  have costs := EulerPacketInitializedCost.initialized_five_costs_bound
    LM L NB BC δ ξ W S.H0 hδ hW S.H0_pos.le hH0
  have hbase : EulerPacketCoarseMajorant.tailBase L'.R S.H0 BC.termCost (truncation k) ≤ k^(1/100 :
      ℝ) :=
    tailBase_frequency L'.R S.H0 BC.termCost k BC.termCost_nonneg (by
        linarith) (costs.1.trans hfrequency)
  have hn := (truncation_bounds k (by linarith)).1
  have hh := initializedInitialHigh_Hm M D hTime τ hτ hτT B δ hδ ξ hs α
    L' H' NB' guards.1 LM' guards.2.1 BC guards.2.2.2.2.2 guards.2.2.2.2.1
    hδ1 hα guards.2.2.2.1 guards.2.2.1 S hgrowth (truncation k) hn k hk hbase s
  have hm := initializedInitialMean_Hm M D hTime τ hτ hτT B δ hδ ξ hs α
    L' H' NB' guards.1 LM' guards.2.1 BC guards.2.2.2.2.2 guards.2.2.2.2.1
    hδ1 hα guards.2.2.2.1 guards.2.2.1 S hgrowth (truncation k) hn k hk hbase s
  have hb := EulerPacketInitializedCost.actual_parameters LM L NB BC δ ξ W S.H0 hδ hW hH0
  have hp := EulerPacketInitialCost.costs_le_envelope s L'.R S.H0
    (EulerPacketInitializedCost.envelope W) (zero_le_one.trans L'.radius_bounds.1) S.H0_pos.le
    hb.2.1 hb.2.2.1
  have hhigh : EulerPacketInitial.highCost L'.R S.H0 *
      physicalDerivativeCost period (4*L'.R)
        (‖coordinateEquiv.symm.toContinuousLinearMap‖*(1+‖D.m₀‖)) s ≤
      EulerPacketInitialCost.envelope s (EulerPacketInitializedCost.envelope W) := by
    simpa only [D.m₀_unit,show (1 : ℝ)+1=2 by norm_num,coordinateCost] using hp.1
  have hell : 0 ≤ M.ℓ⁻¹ := (inv_pos.mpr M.ℓ_pos).le
  have hk0 : 0 ≤ k := by linarith
  exact ⟨hh.trans (mul_le_mul_of_nonneg_left hhigh (by positivity)),
    hm.trans (mul_le_mul_of_nonneg_left hp.2 (by positivity))⟩

variable (Cagree : SourceCoefficientAgreement M D)
  (hX : 64 ≤ expansion k) (hlog : 1 ≤ Real.log k)
  (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
  (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)

local notation "Q" => initializedUniformBudget M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα
  L NB LM Cagree W hW hprofile k hk hX hlog hfrequency Ξ hΞ hF hdet

theorem initializedUniformBudget_initial (s : ℕ) :
    scale M.ℓ (initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree (truncation k) (truncation_bounds k (by linarith)).1 k hk Q
      ⟨0,le_rfl,D.T_pos.le⟩ id) =
      initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α (truncation k) k +
      initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α (truncation k) k ∧
    derivativeSum s (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α (truncation k) k) ≤
      (M.ℓ⁻¹)^s*k^s*α*EulerPacketInitialCost.envelope s (EulerPacketInitializedCost.envelope W) ∧
    derivativeSum s (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α (truncation k) k) ≤
      (M.ℓ⁻¹)^s/k^2*EulerPacketInitialCost.envelope s (EulerPacketInitializedCost.envelope W) :=
  ⟨initializedExactPhysicalVelocity_initial_split M D hTime τ hτ hτT B δ hδ ξ hs α
    Cagree (truncation k) (truncation_bounds k (by linarith)).1 k hk Q,
   initialized_uniform_initial_bounds M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα
    L NB LM W hW hprofile k hk hfrequency s⟩

end EulerPacketTerminalDatum
