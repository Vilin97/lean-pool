/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CoefficientCostMonotone
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionCoefficientBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget

@[expose] public section

/-! Fixed polynomials majorize all primitive coefficient constants of the
packet correction. The pressure inverse is the genuine fixed-order recursion. -/

noncomputable section

namespace EulerPacketCorrectionPrimitive

open EulerParameterWordGevrey EulerCoefficientJetPressureBounds
  EulerPacketCorrectionCoefficients EulerPolynomialCost EulerCylinderPathProduct

def metricEnvelope (X : ℝ) : ℝ := correctionMetricEnvelope X X
def linearEnvelope (X : ℝ) : ℝ := correctionLinearEnvelope X X X
def quadraticEnvelope (X : ℝ) : ℝ := correctionQuadraticEnvelope X X X
def radiusEnvelope (X : ℝ) : ℝ := 1+(1+metricEnvelope X)*(64*X)+64*X
def pressureEnvelope (X : ℝ) : ℝ :=
  1+pressureCost ((1+X)^2)⁻¹ (metricEnvelope X) 5+
    pressureCost ((1+X)^2)⁻¹ (metricEnvelope X) 6
def multiplierEnvelope (X : ℝ) : ℝ := 3*sobolevCoefficientAmplitude (Fin 4) 6 X X
def termEnvelope (P : ℝ) [Fact (0 < P)] (X : ℝ) : ℝ :=
  2*(1+multiplierEnvelope X+9*productBlockConstant P*multiplierEnvelope X)
def primitiveEnvelope (P : ℝ) [Fact (0 < P)] (X : ℝ) : ℝ :=
  1+(1+X)+X^2+3*X*X*X+2*X*X+metricEnvelope X+linearEnvelope X+
    quadraticEnvelope X+radiusEnvelope X+pressureEnvelope X+
    multiplierEnvelope X+termEnvelope P X

def metricPolynomial : Polynomial ℝ :=
  coefficientPolynomial 6 (4*Polynomial.X) (3*Polynomial.X*Polynomial.X)
def linearPolynomial : Polynomial ℝ :=
  2*coefficientPolynomial 6 (4*Polynomial.X) (6*Polynomial.X*Polynomial.X)
def quadraticPolynomial : Polynomial ℝ :=
  6*coefficientPolynomial 6 (4*Polynomial.X) (3*Polynomial.X*(Polynomial.X*Polynomial.X))
def radiusPolynomial : Polynomial ℝ :=
  1+(1+metricPolynomial)*(64*Polynomial.X)+64*Polynomial.X
def pressurePolynomialEnvelope : Polynomial ℝ :=
  1+pressurePolynomial ((1+Polynomial.X)^2) metricPolynomial 5+
    pressurePolynomial ((1+Polynomial.X)^2) metricPolynomial 6
def multiplierPolynomial : Polynomial ℝ :=
  3*coefficientPolynomial 6 Polynomial.X Polynomial.X
def termPolynomial (P : ℝ) [Fact (0 < P)] : Polynomial ℝ :=
  2*(1+multiplierPolynomial+9*Polynomial.C (productBlockConstant P)*multiplierPolynomial)
def primitivePolynomial (P : ℝ) [Fact (0 < P)] : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  1+(1+X)+X^2+3*X*X*X+2*X*X+metricPolynomial+linearPolynomial+
    quadraticPolynomial+radiusPolynomial+pressurePolynomialEnvelope+
    multiplierPolynomial+termPolynomial P

theorem metricPolynomial_eval (X : ℝ) : metricPolynomial.eval X=metricEnvelope X := by
  simp only [metricPolynomial,coefficientPolynomial_eval,metricEnvelope,correctionMetricEnvelope,
    Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]

theorem linearPolynomial_eval (X : ℝ) : linearPolynomial.eval X=linearEnvelope X := by
  simp only [linearPolynomial,coefficientPolynomial_eval,linearEnvelope,correctionLinearEnvelope,
    Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]

theorem quadraticPolynomial_eval (X : ℝ) : quadraticPolynomial.eval X=quadraticEnvelope X := by
  simp only [quadraticPolynomial,coefficientPolynomial_eval,quadraticEnvelope,correctionQuadraticEnvelope,
    Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]

theorem radiusPolynomial_eval (X : ℝ) : radiusPolynomial.eval X=radiusEnvelope X := by
  simp only [radiusPolynomial,radiusEnvelope,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_one,Polynomial.eval_ofNat,Polynomial.eval_X,metricPolynomial_eval]

theorem pressurePolynomialEnvelope_eval (X : ℝ) :
    pressurePolynomialEnvelope.eval X=pressureEnvelope X := by
  simp only [pressurePolynomialEnvelope,pressureEnvelope,pressurePolynomial_eval,
    Polynomial.eval_add,Polynomial.eval_one,Polynomial.eval_pow,Polynomial.eval_X,
    metricPolynomial_eval]

theorem multiplierPolynomial_eval (X : ℝ) : multiplierPolynomial.eval X=multiplierEnvelope X := by
  simp only [multiplierPolynomial,multiplierEnvelope,Polynomial.eval_mul,Polynomial.eval_ofNat,
    coefficientPolynomial_eval,Polynomial.eval_X]

theorem termPolynomial_eval (P : ℝ) [Fact (0 < P)] (X : ℝ) : (termPolynomial P).eval X=termEnvelope
  P X := by
  simp only [termPolynomial,termEnvelope,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_C,multiplierPolynomial_eval]

theorem primitivePolynomial_eval (P : ℝ) [Fact (0 < P)] (X : ℝ) :
    (primitivePolynomial P).eval X=primitiveEnvelope P X := by
  simp only [primitivePolynomial,primitiveEnvelope,Polynomial.eval_add,Polynomial.eval_one,
    Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_X,
    metricPolynomial_eval,linearPolynomial_eval,quadraticPolynomial_eval,radiusPolynomial_eval,
    pressurePolynomialEnvelope_eval,multiplierPolynomial_eval,termPolynomial_eval]

def primitiveConstant (P : ℝ) [Fact (0 < P)] : ℝ := coefficientCost (primitivePolynomial P)
def primitivePower (P : ℝ) [Fact (0 < P)] : ℕ := (primitivePolynomial P).natDegree

theorem primitiveConstant_pos (P : ℝ) [Fact (0 < P)] : 0 < primitiveConstant P :=
  coefficientCost_pos _

theorem primitiveEnvelope_power (P : ℝ) [Fact (0 < P)] (X : ℝ) (hX : 1 ≤ X) :
    primitiveEnvelope P X ≤ primitiveConstant P*X^(primitivePower P) := by
  rw [← primitivePolynomial_eval]
  exact (le_abs_self _).trans (eval_bound (primitivePolynomial P) X hX)

theorem primitive_components (P X : ℝ) [Fact (0 < P)] (hX : 0 ≤ X) :
    1 ≤ primitiveEnvelope P X ∧ 1+X ≤ primitiveEnvelope P X ∧
    X^2 ≤ primitiveEnvelope P X ∧ 3*X*X*X ≤ primitiveEnvelope P X ∧
    2*X*X ≤ primitiveEnvelope P X ∧ metricEnvelope X ≤ primitiveEnvelope P X ∧
    linearEnvelope X ≤ primitiveEnvelope P X ∧ quadraticEnvelope X ≤ primitiveEnvelope P X ∧
    radiusEnvelope X ≤ primitiveEnvelope P X ∧ pressureEnvelope X ≤ primitiveEnvelope P X ∧
    multiplierEnvelope X ≤ primitiveEnvelope P X ∧ termEnvelope P X ≤ primitiveEnvelope P X := by
  have hm : 0 ≤ metricEnvelope X :=
    sobolevCoefficientAmplitude_nonneg 6 (4*X) (3*X*X) (by positivity) (by positivity)
  have hl : 0 ≤ linearEnvelope X := mul_nonneg (by norm_num)
    (sobolevCoefficientAmplitude_nonneg 6 (4*X) (6*X*X) (by positivity) (by positivity))
  have hq : 0 ≤ quadraticEnvelope X := mul_nonneg (by norm_num)
    (sobolevCoefficientAmplitude_nonneg 6 (4*X) (3*X*(X*X)) (by positivity) (by positivity))
  have hr : 0 ≤ radiusEnvelope X := by unfold radiusEnvelope; positivity
  have h5 := pressureCost_nonneg ((1+X)^2)⁻¹ (metricEnvelope X) (by positivity) hm 5
  have h6 := pressureCost_nonneg ((1+X)^2)⁻¹ (metricEnvelope X) (by positivity) hm 6
  have hp : 0 ≤ pressureEnvelope X := by unfold pressureEnvelope; positivity
  have hb : 0 ≤ multiplierEnvelope X := mul_nonneg (by norm_num)
    (sobolevCoefficientAmplitude_nonneg 6 X X hX hX)
  have ht : 0 ≤ termEnvelope P X := by
    have hc := productBlockConstant_nonneg P
    unfold termEnvelope
    positivity
  have h1 : 0 ≤ 1+X := by positivity
  have h2 : 0 ≤ X^2 := sq_nonneg X
  have h3 : 0 ≤ 3*X*X*X := by positivity
  have h4 : 0 ≤ 2*X*X := by positivity
  unfold primitiveEnvelope
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

end EulerPacketCorrectionPrimitive
