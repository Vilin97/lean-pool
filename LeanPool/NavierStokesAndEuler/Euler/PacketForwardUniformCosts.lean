/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCanonicalRadius
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionPrimitiveBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardCoefficientBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedUniformCosts
import LeanPool.NavierStokesAndEuler.Euler.PacketFiveCostGuards
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedParameterBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketSourcePrimitiveBounds

/-! The direct-forward branch uses the identical fixed polynomial cost
envelope as the positive-history branch. -/

@[expose] public section


noncomputable section

namespace EulerPacketInitializedCost

open EulerPacketTerminalDatum EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketCorrectionCoefficients EulerPacketCorrectionConstants EulerPacketCorrectionScalar
  EulerPacketCoarseMajorant EulerPolynomialCost EulerPacketCorrectionPrimitive

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U}
  {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (BC : CoefficientBudget C) (δ : ℝ) (ξ : U)

theorem forward_actual_parameters (W H0 : ℝ) (hδ : 0 < δ)
    (H : EulerPacketForwardRadius.RadiusPrimitives L LM NB BC δ ξ W) (hH0 : H0 ≤ W) :
    1 ≤ envelope W ∧ forwardInitializedRadius LM L NB BC δ ξ ≤ envelope W ∧
    H0 ≤ envelope W ∧ BC.multiplierCost ≤ envelope W ∧
    CorrectionBounds D period (L.correctionCoefficients NB period) (envelope W) := by
  obtain ⟨h1,hW,hR,hP⟩ := envelope_bounds W (zero_le_one.trans H.one)
  have hr := (EulerPacketForwardRadius.canonicalRadius_le_envelope L LM NB BC δ ξ W hδ H).trans hR
  have hc : BC.multiplierCost ≤ W := by
    have ht := BC.twice_multiplierCost_le
    have hn := BC.multiplierCost_nonneg
    linarith only [ht,hn,H.coefficient_cost]
  exact ⟨h1,hr,hH0.trans hW,hc.trans hW,
    (L.correctionCoefficients_primitive_bound NB period W H.one H.forward_radius H.normal_radius
      H.forward_frame H.forward_first H.normal_amplitude).mono D period hP⟩

theorem forward_five_costs_bound (W H0 : ℝ) (hδ : 0 < δ)
    (H : EulerPacketForwardRadius.RadiusPrimitives L LM NB BC δ ξ W)
    (hH0 : 0 ≤ H0) (hHW : H0 ≤ W) :
    let R := forwardInitializedRadius LM L NB BC δ ξ
    let Kc := L.correctionCoefficients NB period
    tailPolynomialConstant R H0 BC.termCost ≤ uniformConstant*W^uniformPower ∧
    BC.multiplierCost ≤ uniformConstant*W^uniformPower ∧
    12*growth D period Kc R H0 BC.multiplierCost*D.T ≤ uniformConstant*W^uniformPower ∧
    8*growth D period Kc R H0 BC.multiplierCost*D.T*drift R H0 BC.multiplierCost/
      initialRadius R Kc.M Kc.Rc ≤ uniformConstant*W^uniformPower ∧
    8*growth D period Kc R H0 BC.multiplierCost*D.T/
      initialRadius R Kc.M Kc.Rc ≤ uniformConstant*W^uniformPower := by
  obtain ⟨he,hr,hh,hc,hK⟩ := forward_actual_parameters LM L NB BC δ ξ W H0 hδ H hHW
  have hR0 := zero_le_one.trans (forwardInitializedLinearBudget LM L NB BC δ ξ).radius_one
  have hEW := (envelope_bounds W (zero_le_one.trans H.one)).2.1
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := EulerPacketFiveCost.five_costs_bound period D
    (L.correctionCoefficients NB period) (forwardInitializedRadius LM L NB BC δ ξ)
    H0 BC.multiplierCost BC.termCost (envelope W) he hR0 hH0 BC.multiplierCost_nonneg hr hh hc
    (H.coefficient_cost.trans hEW) hK.inverse hK.metric hK.first hK.time hK.base hK.pressure
    hK.linear hK.quadratic hK.radius (H.total_time.trans (H.one.trans hEW))
  have h := envelope_bound W H.one
  exact ⟨h₁.trans h,h₂.trans h,h₃.trans h,h₄.trans h,h₅.trans h⟩

end EulerPacketInitializedCost
