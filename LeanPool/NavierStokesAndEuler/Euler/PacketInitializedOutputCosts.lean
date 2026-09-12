/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedUniformBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedFlowData
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedParameterBounds

/-! One fixed polynomial controls both correction admissibility and every
source multiplier in the same-Q shear/Hessian and graph-flow estimates. -/

@[expose] public section


noncomputable section

namespace EulerPacketInitializedOutputCost

open EulerPacketTerminalDatum EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketCorrectionConstants EulerPacketCorrectionScalar EulerPacketCorrectionCoefficients
  EulerPacketPhysicalCost EulerPacketFiveCost EulerPolynomialCost EulerAllOrderDriftCorrection
  EulerPacketCorrectionOutput

/-- Envelope, constructed using `1`. -/
def envelope (W : ℝ) : ℝ := 1 +
  EulerPacketInitializedCost.uniformConstant*W^EulerPacketInitializedCost.uniformPower +
  extraEnvelope (EulerPacketInitializedCost.envelope W)

/-- Polynomial, constructed using `1`. -/
def polynomial : Polynomial ℝ := 1 +
  Polynomial.C EulerPacketInitializedCost.uniformConstant *
    Polynomial.X^EulerPacketInitializedCost.uniformPower +
  extraPolynomial.comp (1+Polynomial.X+EulerPacketRadiusPolynomial.radiusPolynomial +
    EulerPacketCorrectionPrimitive.primitivePolynomial period)

/-- Uniform constant, given by `coefficientCost polynomial`. -/
def uniformConstant : ℝ := coefficientCost polynomial
/-- Uniform power, given by `polynomial.natDegree`. -/
def uniformPower : ℕ := polynomial.natDegree

theorem uniformConstant_pos : 0 < uniformConstant := coefficientCost_pos _

theorem polynomial_eval (W : ℝ) : polynomial.eval W=envelope W := by
  unfold polynomial envelope EulerPacketInitializedCost.envelope
  simp only [Polynomial.eval_add,Polynomial.eval_one,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_comp,
    EulerPacketRadiusPolynomial.radiusPolynomial_eval,
    EulerPacketCorrectionPrimitive.primitivePolynomial_eval,extraPolynomial_eval]

theorem envelope_bound (W : ℝ) (hW : 1 ≤ W) : envelope W ≤ uniformConstant*W^uniformPower := by
  rw [← polynomial_eval]
  exact (le_abs_self _).trans (eval_bound polynomial W hW)

theorem envelope_components (W : ℝ) (hW : 0 ≤ W) :
    EulerPacketInitializedCost.uniformConstant*W^EulerPacketInitializedCost.uniformPower ≤ envelope
        W ∧
    extraEnvelope (EulerPacketInitializedCost.envelope W) ≤ envelope W := by
  have hC := EulerPacketInitializedCost.uniformConstant_pos.le
  have hE0 := zero_le_one.trans (EulerPacketInitializedCost.envelope_bounds W hW).1
  have hO := zero_le_one.trans (output_components period _ hE0).1
  have he := (extra_components (EulerPacketInitializedCost.envelope W) hE0).1
  have hE := hO.trans he
  have hp : 0 ≤
      EulerPacketInitializedCost.uniformConstant*W^EulerPacketInitializedCost.uniformPower :=
    mul_nonneg hC (pow_nonneg hW _)
  unfold envelope
  exact ⟨by linarith,by linarith⟩

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le)}
  {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (BC : CoefficientBudget C) (δ : ℝ) (ξ : U)

theorem actual_output_costs (W H0 : ℝ) (hδ : 0 < δ)
    (H : EulerPacketRadiusPolynomial.RadiusPrimitives LM L NB BC δ ξ W)
    (hH0 : 0 ≤ H0) (hHW : H0 ≤ W) :
    let R := initializedRadius LM L NB BC δ ξ
    let Kc := L.correctionCoefficients NB period
    let ρ := initialRadius R Kc.M Kc.Rc/4
    let Z := EulerPacketInitializedCost.envelope W
    EulerPacketInitializedCost.weightSize W ≤ extraEnvelope Z ∧
    physicalInputRadius (4*R) (4*R) ρ ≤ extraEnvelope Z ∧
    liftedInputConstant period*(velocity R H0 BC.multiplierCost+normal R H0 BC.multiplierCost) ≤
        extraEnvelope Z ∧
    2*liftedInputConstant period*EulerPacketInitializedCost.weightSize W ≤ extraEnvelope Z ∧
    2*liftedInputConstant period*(6*NB.blockAmplitude *
      (fixedVelocityGradeCost R H0 1+fixedVelocityGradeCost R H0 2+1) +
      EulerPacketInitializedCost.weightSize W) ≤ extraEnvelope Z ∧
    weightedPhysicalGradientCost D period L.Rc L.C₀ ρ (EulerPacketInitializedCost.weightSize W) ≤
        extraEnvelope Z ∧
    initializedGlobalShearCost R H0 NB.C ≤ extraEnvelope Z ∧
    initializedPressureHessianCost NB R H0 L.Rc L.C₀ ≤ extraEnvelope Z := by
  let R := initializedRadius LM L NB BC δ ξ
  let Kc := L.correctionCoefficients NB period
  let ρ := initialRadius R Kc.M Kc.Rc/4
  let Z := EulerPacketInitializedCost.envelope W
  obtain ⟨hZ1,hRZ,hHZ,hCZ,hK⟩ := EulerPacketInitializedCost.actual_parameters
    LM L NB BC δ ξ W H0 hδ H hHW
  change R ≤ Z at hRZ
  change H0 ≤ Z at hHZ
  change BC.multiplierCost ≤ Z at hCZ
  have hZ : 0 ≤ Z := zero_le_one.trans hZ1
  have hWZ := (EulerPacketInitializedCost.envelope_bounds W (zero_le_one.trans H.one)).2.1
  have hR0 : 0 ≤ R := zero_le_one.trans (initializedJoinedBudget LM L NB BC δ ξ).radius_bounds.1
  have hC0 := BC.multiplierCost_nonneg
  have hLR := H.joined_radius.trans hWZ
  have hLC := H.joined_frame.trans hWZ
  have hNR := H.normal_radius.trans hWZ
  have hNC := H.normal_amplitude.trans hWZ
  have hNI := H.normal_inverse.trans hWZ
  have hρ0 : 0 < ρ := div_pos (initialRadius_bounds R Kc.M Kc.Rc hR0
    (zero_le_one.trans Kc.M_one_le) Kc.Rc_nonneg).1 (by norm_num)
  have hiR : (initialRadius R Kc.M Kc.Rc)⁻¹ ≤ inverseRadiusEnvelope Z := by
    simp only [initialRadius,one_div,inv_inv]
    unfold inverseRadiusEnvelope
    have hm : Kc.M ≤ Z := hK.pressure
    have hr : Kc.Rc ≤ Z := hK.radius
    have hp := mul_le_mul hm hr Kc.Rc_nonneg hZ
    nlinarith only [hp,hRZ,hr]
  have hρinv : ρ⁻¹ ≤ 4*inverseRadiusEnvelope Z := by
    change (initialRadius R Kc.M Kc.Rc/4)⁻¹ ≤ _
    rw [inv_div,div_eq_mul_inv]
    gcongr
  have hiZ : 0 ≤ inverseRadiusEnvelope Z := by unfold inverseRadiusEnvelope; positivity
  have hrf : physicalInputRadius (4*R) (4*R) ρ ≤ radiusEnvelope Z := by
    simp only [physicalInputRadius,max_self,liftedInputRadius]
    change 1+coordinateCost*(4*R+ρ⁻¹) ≤ 1+coordinateCost*(4*Z+4*inverseRadiusEnvelope Z)
    have hc : 0 ≤ coordinateCost := norm_nonneg _
    gcongr
  have hv := velocity_mono hR0 hH0 hC0 hRZ hHZ hCZ
  have ha1 := gradeCost_mono R H0 Z hR0 hH0 hRZ hHZ 1
  have ha2 := gradeCost_mono R H0 Z hR0 hH0 hRZ hHZ 2
  have hg1 := fixedVelocityGradeCost_nonneg R H0 hR0 1
  have hg2 := fixedVelocityGradeCost_nonneg R H0 hR0 2
  have hg1Z := hg1.trans ha1
  have hg2Z := hg2.trans ha2
  have hn : normal R H0 BC.multiplierCost ≤ normal Z Z Z := by unfold normal; gcongr
  have hl := zero_le_one.trans (liftedInputConstant_one_le period)
  have hav : liftedInputConstant period*(velocity R H0 BC.multiplierCost+normal R H0
      BC.multiplierCost) ≤
      velocityInputEnvelope Z := by unfold velocityInputEnvelope; gcongr
  have hb := EulerPacketRadiusPolynomial.normal_block_le NB Z hZ hNR hNC hNI
  have hb0 := NB.blockAmplitude_nonneg
  have hbZ := hb0.trans hb
  have ht : 6*NB.blockAmplitude*(fixedVelocityGradeCost R H0 1+fixedVelocityGradeCost R H0 2+1) ≤
      timeEnvelope Z := by unfold timeEnvelope; gcongr
  have hat : 2*liftedInputConstant period*(6*NB.blockAmplitude *
      (fixedVelocityGradeCost R H0 1+fixedVelocityGradeCost R H0 2+1) +
      EulerPacketInitializedCost.weightSize W) ≤ timeInputEnvelope Z := by
    unfold timeInputEnvelope EulerPacketInitializedCost.weightSize
    gcongr
  have hphys := physicalFixedCost_one_le D L.Rc L.C₀ ρ⁻¹ Z (4*inverseRadiusEnvelope Z)
    L.Rc_nonneg L.C₀_nonneg (inv_nonneg.mpr hρ0.le) hLR hLC hρinv
  have hphys0 := EulerPacketPhysicalGevrey.physicalFixedCost_nonneg D L.Rc L.C₀ ρ⁻¹ 1
    L.Rc_nonneg L.C₀_nonneg (inv_nonneg.mpr hρ0.le)
  have hphysZ := hphys0.trans hphys
  have he := EulerCylinderSobolevSpace.sobolevEmbeddingConstant_nonneg period 3
  have ho := zero_le_one.trans (output_components period Z hZ).1
  have herr : weightedPhysicalGradientCost D period L.Rc L.C₀ ρ
      (EulerPacketInitializedCost.weightSize W) ≤
      weightedErrorEnvelope Z := by
    calc
      _ = ((1+9*L.C₀)*EulerPacketPhysicalGevrey.physicalFixedCost D L.Rc L.C₀ ρ⁻¹ 1 *
          EulerCylinderSobolevSpace.sobolevEmbeddingConstant period 3)*outputEnvelope period Z := by
        unfold weightedPhysicalGradientCost EulerPacketInitializedCost.weightSize
        ring
      _ ≤ ((1+9*Z)*physicalEnvelope Z (4*inverseRadiusEnvelope Z) *
          EulerCylinderSobolevSpace.sobolevEmbeddingConstant period 3)*outputEnvelope period Z := by
              gcongr
      _ = _ := rfl
  have hshear := shearCost_le R H0 NB.C Z hR0 hH0 NB.C_nonneg hRZ hHZ hNC
  have hhess := hessianCost_le D NB R H0 L.Rc L.C₀ Z hR0 hH0 L.Rc_nonneg L.C₀_nonneg
    hRZ hHZ hLR hLC hNR hNC
  obtain ⟨hwe,hr,ha,hb,ht',he',hs,hp⟩ := extra_components Z hZ
  exact ⟨hwe,hrf.trans hr,hav.trans ha,hb,hat.trans ht',herr.trans he',hshear.trans hs,hhess.trans
      hp⟩

end EulerPacketInitializedOutputCost
