/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiveCostPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionSourceBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionCoefficientBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionConstants
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionScalar

/-! Uniform polynomial bounds for the actual correction, pressure and
time-derivative amplitudes at the retained radius. -/

section

/-! Fixed source constants in the smaller-radius estimates for the actual
initialized all-order correction. They do not depend on the cutoff or frequency. -/

@[expose] public section

noncomputable section

namespace EulerPacketCorrectionConstants

open EulerPacketCorrectionCoefficients EulerGevreyMetricEstimate EulerGevreyCorrectionSourceBounds
  EulerPacketCorrectionScalar

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (Kc : CorrectionCoefficientBudget D P)

/-- Correction base, given by `metricAmplification D.inverseBound⁻¹/2`. -/
def correctionBase : ℝ := metricAmplification D.inverseBound⁻¹/2

/-- Correction source cost, constructed using `sourceBound`. -/
def correctionSourceCost (R H C : ℝ) : ℝ :=
  sourceBound P (2*velocity R H C) (12*velocity R H C*(4*R)) Kc.A0 Kc.A2 1
    (correctionBase D) ((8/initialRadius R Kc.M Kc.Rc)*correctionBase D)

/-- Correction pressure cost, given by `2*Kc.M*correctionSourceCost D P Kc R H C`. -/
def correctionPressureCost (R H C : ℝ) : ℝ := 2*Kc.M*correctionSourceCost D P Kc R H C

/-- Correction time cost, given by `(1+2*Kc.M*(448*Kc.B+1))*correctionSourceCost D P Kc R H C`. -/
def correctionTimeCost (R H C : ℝ) : ℝ :=
  (1+2*Kc.M*(448*Kc.B+1))*correctionSourceCost D P Kc R H C

end EulerPacketCorrectionConstants

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCorrectionOutput

open EulerPacketCorrectionConstants EulerPacketCorrectionCoefficients
  EulerPacketCorrectionScalar EulerGevreyCorrectionSourceBounds EulerGevreyMetricEstimate
  EulerPacketFiveCost EulerH6Nonlinear EulerPolynomialCost

variable (P : ℝ) [Fact (0 < P)]

/-- Base envelope, given by `(1+Real.sqrt 5461*X)/2`. -/
def baseEnvelope (X : ℝ) : ℝ := (1+Real.sqrt 5461*X)/2

/-- Source envelope, given by `sourceBound P (2*velocity X X X) (48*velocity X X X*X) X X 1
(baseEnvelope X) (8*inverseRadiusEnvelope X*baseEnvelope X)`. -/
def sourceEnvelope (X : ℝ) : ℝ :=
  sourceBound P (2*velocity X X X) (48*velocity X X X*X) X X 1
    (baseEnvelope X) (8*inverseRadiusEnvelope X*baseEnvelope X)

/-- Output envelope, given by `1+baseEnvelope X+2*X*sourceEnvelope P
X+(1+2*X*(448*X+1))*sourceEnvelope P X`. -/
def outputEnvelope (X : ℝ) : ℝ :=
  1+baseEnvelope X+2*X*sourceEnvelope P X+(1+2*X*(448*X+1))*sourceEnvelope P X

/-- Output polynomial as an element of `Polynomial ℝ`. -/
def outputPolynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let p := Polynomial.C (productConstant P 3)
  let b := (1+Polynomial.C (Real.sqrt 5461)*X)*Polynomial.C (1/2)
  let v := velocityPolynomial
  let d := 8*(1+8*X+4*X^2+X)*b
  let s := p*(2*v+b)*d+1+(p*(48*v*X)+X+2*X*p*(2*v))*b+X*p*b^2
  1+b+2*X*s+(1+2*X*(448*X+1))*s

theorem outputPolynomial_eval (X : ℝ) : (outputPolynomial P).eval X=outputEnvelope P X := by
  unfold outputPolynomial outputEnvelope sourceEnvelope baseEnvelope inverseRadiusEnvelope
      sourceBound
  dsimp only
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,Polynomial.eval_ofNat,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, velocityPolynomial_eval,
        div_eq_mul_inv, one_mul]

/-- Output constant, given by `coefficientCost (outputPolynomial P)`. -/
def outputConstant : ℝ := coefficientCost (outputPolynomial P)
/-- Output power, given by `(outputPolynomial P).natDegree`. -/
def outputPower : ℕ := (outputPolynomial P).natDegree

theorem outputConstant_pos : 0 < outputConstant P := coefficientCost_pos _

theorem outputEnvelope_power (X : ℝ) (hX : 1 ≤ X) :
    outputEnvelope P X ≤ outputConstant P*X^outputPower P := by
  rw [← outputPolynomial_eval]
  exact (le_abs_self _).trans (eval_bound (outputPolynomial P) X hX)

theorem output_components (X : ℝ) (hX : 0 ≤ X) :
    1 ≤ outputEnvelope P X ∧ baseEnvelope X ≤ outputEnvelope P X ∧
    2*X*sourceEnvelope P X ≤ outputEnvelope P X ∧
    (1+2*X*(448*X+1))*sourceEnvelope P X ≤ outputEnvelope P X := by
  have hv := velocity_nonneg X X X hX hX
  have hb : 0 ≤ baseEnvelope X := by unfold baseEnvelope; positivity
  have hi : 0 ≤ inverseRadiusEnvelope X := by unfold inverseRadiusEnvelope; positivity
  have hs : 0 ≤ sourceEnvelope P X := sourceBound_nonneg P (by positivity) (by positivity)
    hX hX zero_le_one hb (by positivity)
  have h2 : 0 ≤ 2*X*sourceEnvelope P X := by positivity
  have h3 : 0 ≤ (1+2*X*(448*X+1))*sourceEnvelope P X := by positivity
  unfold outputEnvelope
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (Kc : CorrectionCoefficientBudget D P)

theorem correctionBase_nonneg : 0 ≤ correctionBase D := by
  unfold correctionBase metricAmplification
  positivity [D.inverseBound_pos]

theorem correctionSourceCost_nonneg (R H C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    0 ≤ correctionSourceCost D P Kc R H C := by
  have hv := velocity_nonneg R H C hR hC
  have hb := correctionBase_nonneg D
  have hρ := (initialRadius_bounds R Kc.M Kc.Rc hR
    (zero_le_one.trans Kc.M_one_le) Kc.Rc_nonneg).1
  exact sourceBound_nonneg P (by positivity) (by positivity) Kc.A0_nonneg Kc.A2_nonneg
    zero_le_one hb (by positivity)

theorem correction_output_bound (R H C X : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hRX : R ≤ X) (hHX : H ≤ X) (hCX : C ≤ X) (hi : D.inverseBound ≤ X)
    (hB : Kc.B ≤ X) (hM : Kc.M ≤ X) (hA0 : Kc.A0 ≤ X) (hA2 : Kc.A2 ≤ X)
    (hRc : Kc.Rc ≤ X) :
    0 ≤ correctionBase D ∧ 0 ≤ correctionPressureCost D P Kc R H C ∧
    0 ≤ correctionTimeCost D P Kc R H C ∧
    correctionBase D ≤ outputEnvelope P X ∧
    correctionPressureCost D P Kc R H C ≤ outputEnvelope P X ∧
    correctionTimeCost D P Kc R H C ≤ outputEnvelope P X := by
  have hX : 0 ≤ X := hR.trans hRX
  have hv0 := velocity_nonneg R H C hR hC
  have hv := velocity_mono hR hH hC hRX hHX hCX
  have hvX : 0 ≤ velocity X X X := hv0.trans hv
  have hb0 := correctionBase_nonneg D
  have hbX : 0 ≤ baseEnvelope X := by unfold baseEnvelope; positivity
  have hb : correctionBase D ≤ baseEnvelope X := by
    unfold correctionBase metricAmplification baseEnvelope
    simp only [div_eq_mul_inv,inv_inv]
    gcongr
  have hρ := (initialRadius_bounds R Kc.M Kc.Rc hR
    (zero_le_one.trans Kc.M_one_le) Kc.Rc_nonneg).1
  have hiR : (initialRadius R Kc.M Kc.Rc)⁻¹ ≤ inverseRadiusEnvelope X := by
    simp only [initialRadius,one_div,inv_inv]
    unfold inverseRadiusEnvelope
    have hp := mul_le_mul hM hRc Kc.Rc_nonneg hX
    nlinarith
  have hiX : 0 ≤ inverseRadiusEnvelope X := by unfold inverseRadiusEnvelope; positivity
  have hder : 12*velocity R H C*(4*R) ≤ 48*velocity X X X*X := by
    calc
      _ = 48*velocity R H C*R := by ring
      _ ≤ _ := by gcongr
  have hde : (8/initialRadius R Kc.M Kc.Rc)*correctionBase D ≤
      8*inverseRadiusEnvelope X*baseEnvelope X := by
    rw [div_eq_mul_inv]
    gcongr
  have hP := productConstant_nonneg P 3
  have hs : correctionSourceCost D P Kc R H C ≤ sourceEnvelope P X := by
    unfold correctionSourceCost sourceEnvelope sourceBound
    gcongr
  have hs0 := correctionSourceCost_nonneg P D Kc R H C hR hC
  have hsX : 0 ≤ sourceEnvelope P X := hs0.trans hs
  have hm0 := zero_le_one.trans Kc.M_one_le
  have hB0 := Kc.B_nonneg
  have hp0 : 0 ≤ correctionPressureCost D P Kc R H C := by
    unfold correctionPressureCost
    positivity
  have ht0 : 0 ≤ correctionTimeCost D P Kc R H C := by
    unfold correctionTimeCost
    positivity [Kc.B_nonneg]
  obtain ⟨_,hbo,hpo,hto⟩ := output_components P X hX
  refine ⟨hb0,hp0,ht0,hb.trans hbo,?_,?_⟩
  · apply le_trans _ hpo
    unfold correctionPressureCost
    gcongr
  · apply le_trans _ hto
    unfold correctionTimeCost
    gcongr

end EulerPacketCorrectionOutput
