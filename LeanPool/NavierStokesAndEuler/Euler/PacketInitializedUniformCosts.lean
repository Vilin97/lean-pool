/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionPrimitivePolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiveCostPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedCoefficientBudgets
import LeanPool.NavierStokesAndEuler.Euler.PacketFiveCostGuards
import LeanPool.NavierStokesAndEuler.Euler.PacketSourcePrimitiveBounds

/-! A fixed polynomial bounds all five costs for the literal canonical
initialized packet radius. No arbitrary radius witness is used. -/

@[expose] public section


noncomputable section

namespace EulerPacketInitializedCost

open EulerPacketTerminalDatum EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketCorrectionCoefficients EulerPacketCorrectionConstants EulerPacketCorrectionScalar
  EulerPacketCoarseMajorant EulerPolynomialCost

/-- Envelope, given by `1+W+EulerPacketRadiusPolynomial.radiusEnvelope W +
EulerPacketCorrectionPrimitive.primitiveEnvelope period W`. -/
def envelope (W : ℝ) : ℝ := 1+W+EulerPacketRadiusPolynomial.radiusEnvelope W +
  EulerPacketCorrectionPrimitive.primitiveEnvelope period W

/-- Polynomial, constructed using `Polynomial.C`. -/
def polynomial : Polynomial ℝ :=
  Polynomial.C (EulerPacketFiveCost.costConstant period) *
    (1+Polynomial.X+EulerPacketRadiusPolynomial.radiusPolynomial +
      EulerPacketCorrectionPrimitive.primitivePolynomial period)^(EulerPacketFiveCost.costPower
          period)

/-- Uniform constant, given by `coefficientCost polynomial`. -/
def uniformConstant : ℝ := coefficientCost polynomial
/-- Uniform power, given by `polynomial.natDegree`. -/
def uniformPower : ℕ := polynomial.natDegree

theorem uniformConstant_pos : 0 < uniformConstant := coefficientCost_pos _

theorem polynomial_eval (W : ℝ) : polynomial.eval W =
    EulerPacketFiveCost.costConstant period*(envelope W)^EulerPacketFiveCost.costPower period := by
  unfold polynomial envelope
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_one,Polynomial.eval_X,
    EulerPacketRadiusPolynomial.radiusPolynomial_eval,
    EulerPacketCorrectionPrimitive.primitivePolynomial_eval]

theorem envelope_bound (W : ℝ) (hW : 1 ≤ W) :
    EulerPacketFiveCost.costConstant period*(envelope W)^EulerPacketFiveCost.costPower period ≤
      uniformConstant*W^uniformPower := by
  rw [← polynomial_eval]
  exact (le_abs_self _).trans (eval_bound polynomial W hW)

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le)}
  {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (BC : CoefficientBudget C) (δ : ℝ) (ξ : U)

theorem initialized_five_costs_bound (W H0 : ℝ) (hδ : 0 < δ)
    (H : EulerPacketRadiusPolynomial.RadiusPrimitives LM L NB BC δ ξ W)
    (hH0 : 0 ≤ H0) (hHW : H0 ≤ W) :
    let R := initializedRadius LM L NB BC δ ξ
    let Kc := L.correctionCoefficients NB period
    tailPolynomialConstant R H0 BC.termCost ≤ uniformConstant*W^uniformPower ∧
    BC.multiplierCost ≤ uniformConstant*W^uniformPower ∧
    12*growth D period Kc R H0 BC.multiplierCost*D.T ≤ uniformConstant*W^uniformPower ∧
    8*growth D period Kc R H0 BC.multiplierCost*D.T*drift R H0 BC.multiplierCost/
      initialRadius R Kc.M Kc.Rc ≤ uniformConstant*W^uniformPower ∧
    8*growth D period Kc R H0 BC.multiplierCost*D.T/
      initialRadius R Kc.M Kc.Rc ≤ uniformConstant*W^uniformPower := by
  have hW0 := zero_le_one.trans H.one
  have hR1 : 1 ≤ initializedRadius LM L NB BC δ ξ :=
    (initializedJoinedBudget LM L NB BC δ ξ).radius_bounds.1
  have hR := EulerPacketRadiusPolynomial.initializedRadius_le_envelope LM L NB BC δ ξ W hδ H
  have hRE : 0 ≤ EulerPacketRadiusPolynomial.radiusEnvelope W :=
    (zero_le_one.trans hR1).trans hR
  have hPE := (EulerPacketCorrectionPrimitive.primitive_components period W hW0).1
  have hEW : W ≤ envelope W := by unfold envelope; linarith
  have hER : EulerPacketRadiusPolynomial.radiusEnvelope W ≤ envelope W := by
    unfold envelope
    linarith
  have hEP : EulerPacketCorrectionPrimitive.primitiveEnvelope period W ≤ envelope W := by
    unfold envelope
    linarith
  have hE : 1 ≤ envelope W := H.one.trans hEW
  have hK := (L.correctionCoefficients_primitive_bound NB period W H.one H.joined_radius
    H.normal_radius H.joined_frame H.joined_first H.normal_amplitude).mono D period hEP
  have hmult : BC.multiplierCost ≤ W := by
    have ht := BC.twice_multiplierCost_le
    have hn := BC.multiplierCost_nonneg
    linarith only [ht,hn,H.coefficient_cost]
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := EulerPacketFiveCost.five_costs_bound period D
    (L.correctionCoefficients NB period) (initializedRadius LM L NB BC δ ξ)
    H0 BC.multiplierCost BC.termCost (envelope W) hE (zero_le_one.trans hR1) hH0
    BC.multiplierCost_nonneg (hR.trans hER) (hHW.trans hEW) (hmult.trans hEW)
    (H.coefficient_cost.trans hEW) hK.inverse hK.metric hK.first hK.time hK.base hK.pressure
    hK.linear hK.quadratic hK.radius (H.total_time.trans (H.one.trans hEW))
  have he := envelope_bound W H.one
  exact ⟨h₁.trans he,h₂.trans he,h₃.trans he,h₄.trans he,h₅.trans he⟩

end EulerPacketInitializedCost
