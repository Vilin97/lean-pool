/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionOutputPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactGlobalShear
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedHessianError
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCoefficientBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketRadiusCostPolynomial
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedRadiusPolynomial

/-! Fixed polynomial envelopes for the physical remainder, correction
error and lifted-flow input costs. All spatial derivative orders here are
fixed (H6 and one physical derivative). -/

@[expose] public section


noncomputable section

namespace EulerPacketPhysicalCost

open EulerSmoothLimit EulerPacketTerminalDatum EulerPacketProfileRecursion
  EulerPacketCylinderField EulerPacketCorrectionConstants EulerPacketCorrectionScalar
  EulerPacketCorrectionOutput EulerPacketFiveCost EulerCylinderSobolevSpace
  EulerCylinderCoordinates EulerPacketPhysicalGevrey EulerPacketInverseFlowGevrey
  EulerAllOrderDriftCorrection EulerPacketGraphHessian EulerPolynomialCost
  EulerParameterWordGevrey

/-- Coordinate cost, given by `‖coordinateEquiv.symm.toContinuousLinearMap‖`. -/
def coordinateCost : ℝ := ‖coordinateEquiv.symm.toContinuousLinearMap‖

/-- Physical envelope, given by `3*X*((1+18*X^2*X)*(9*X^2*(X+coordinateCost*2*S)+2))`. -/
def physicalEnvelope (X S : ℝ) : ℝ :=
  3*X*((1+18*X^2*X)*(9*X^2*(X+coordinateCost*2*S)+2))

/-- Shear envelope as an element of `ℝ`. -/
def shearEnvelope (X : ℝ) : ℝ :=
  coordinateCost*(sobolevEmbeddingConstant period 3*fixedVelocityGradeCost X X 1*(4*X))*X +
    (8*coordinateCost*sobolevEmbeddingConstant period 3*X*(fixedVelocityGradeCost X X 2+2))*X

/-- Hessian envelope, constructed using `sobolevEmbeddingConstant`. -/
def hessianEnvelope (X : ℝ) : ℝ :=
  sobolevEmbeddingConstant period 3*fixedVelocityGradeCost X X 1*X^2*(X+coordinateCost*(4*X)) +
    9*X*physicalEnvelope X (4*X)*sobolevEmbeddingConstant period 3*(fixedVelocityGradeCost X X 2+2)

/-- Time envelope, given by `6*EulerPacketRadiusPolynomial.normalEnvelope X *
(fixedVelocityGradeCost X X 1+fixedVelocityGradeCost X X 2+1)`. -/
def timeEnvelope (X : ℝ) : ℝ :=
  6*EulerPacketRadiusPolynomial.normalEnvelope X *
    (fixedVelocityGradeCost X X 1+fixedVelocityGradeCost X X 2+1)

/-- Radius envelope, given by `1+coordinateCost*(4*X+4*inverseRadiusEnvelope X)`. -/
def radiusEnvelope (X : ℝ) : ℝ := 1+coordinateCost*(4*X+4*inverseRadiusEnvelope X)

/-- Velocity input envelope, given by `liftedInputConstant period*(velocity X X X+normal X X
X)`. -/
def velocityInputEnvelope (X : ℝ) : ℝ := liftedInputConstant period*(velocity X X X+normal X X X)
/-- Error input envelope, given by `2*liftedInputConstant period*outputEnvelope period X`. -/
def errorInputEnvelope (X : ℝ) : ℝ := 2*liftedInputConstant period*outputEnvelope period X
/-- Time input envelope, given by `2*liftedInputConstant period*(timeEnvelope X+outputEnvelope
period X)`. -/
def timeInputEnvelope (X : ℝ) : ℝ := 2*liftedInputConstant period*(timeEnvelope X+outputEnvelope
    period X)
/-- Weighted error envelope, given by `(1+9*X)*physicalEnvelope X (4*inverseRadiusEnvelope
X)*sobolevEmbeddingConstant period 3 * outputEnvelope period X`. -/
def weightedErrorEnvelope (X : ℝ) : ℝ :=
  (1+9*X)*physicalEnvelope X (4*inverseRadiusEnvelope X)*sobolevEmbeddingConstant period 3 *
    outputEnvelope period X

/-- Extra envelope as an element of `ℝ`. -/
def extraEnvelope (X : ℝ) : ℝ :=
  1+outputEnvelope period X+radiusEnvelope X+velocityInputEnvelope X+errorInputEnvelope X +
    timeInputEnvelope X+weightedErrorEnvelope X+shearEnvelope X+hessianEnvelope X

/-- Extra polynomial as an element of `Polynomial ℝ`. -/
def extraPolynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let c := Polynomial.C coordinateCost
  let e := Polynomial.C (sobolevEmbeddingConstant period 3)
  let l := Polynomial.C (liftedInputConstant period)
  let o := outputPolynomial period
  let i := 1+8*X+4*X^2+X
  let a1 := gradePolynomial 1
  let a2 := gradePolynomial 2
  let v := velocityPolynomial
  let n := X*(a2+2)
  let nb := coefficientPolynomial 6 (5*X+1) (1+X+6*X^2+729*X^6)
  let ti := 6*nb*(a1+a2+1)
  let pp := fun S : Polynomial ℝ => 3*X*((1+18*X^2*X)*(9*X^2*(X+c*2*S)+2))
  let sh := c*(e*a1*(4*X))*X+(8*c*e*X*(a2+2))*X
  let he := e*a1*X^2*(X+c*(4*X))+9*X*pp (4*X)*e*(a2+2)
  1+o+(1+c*(4*X+4*i))+l*(v+n)+2*l*o+2*l*(ti+o)+(1+9*X)*pp (4*i)*e*o+sh+he

theorem extraPolynomial_eval (X : ℝ) : extraPolynomial.eval X=extraEnvelope X := by
  unfold extraPolynomial extraEnvelope radiusEnvelope velocityInputEnvelope errorInputEnvelope
    timeInputEnvelope weightedErrorEnvelope shearEnvelope hessianEnvelope physicalEnvelope
    timeEnvelope EulerPacketRadiusPolynomial.normalEnvelope EulerPacketRadiusPolynomial.coeff
    inverseRadiusEnvelope normal
  dsimp only
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,
    Polynomial.eval_ofNat,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,
    outputPolynomial_eval,gradePolynomial_eval,velocityPolynomial_eval,coefficientPolynomial_eval]

/-- Extra constant, given by `coefficientCost extraPolynomial`. -/
def extraConstant : ℝ := coefficientCost extraPolynomial
/-- Extra power, given by `extraPolynomial.natDegree`. -/
def extraPower : ℕ := extraPolynomial.natDegree

theorem extraConstant_pos : 0 < extraConstant := coefficientCost_pos _

theorem extraEnvelope_power (X : ℝ) (hX : 1 ≤ X) : extraEnvelope X ≤ extraConstant*X^extraPower :=
    by
  rw [← extraPolynomial_eval]
  exact (le_abs_self _).trans (eval_bound extraPolynomial X hX)

theorem physicalEnvelope_nonneg (X S : ℝ) (hX : 0 ≤ X) (hS : 0 ≤ S) :
    0 ≤ physicalEnvelope X S := by
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  unfold physicalEnvelope
  positivity

theorem extra_components (X : ℝ) (hX : 0 ≤ X) :
    outputEnvelope period X ≤ extraEnvelope X ∧ radiusEnvelope X ≤ extraEnvelope X ∧
    velocityInputEnvelope X ≤ extraEnvelope X ∧ errorInputEnvelope X ≤ extraEnvelope X ∧
    timeInputEnvelope X ≤ extraEnvelope X ∧ weightedErrorEnvelope X ≤ extraEnvelope X ∧
    shearEnvelope X ≤ extraEnvelope X ∧ hessianEnvelope X ≤ extraEnvelope X := by
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  have he := sobolevEmbeddingConstant_nonneg period 3
  have hl := zero_le_one.trans (liftedInputConstant_one_le period)
  have ho := zero_le_one.trans (output_components period X hX).1
  have hi : 0 ≤ inverseRadiusEnvelope X := by unfold inverseRadiusEnvelope; positivity
  have hr : 0 ≤ radiusEnvelope X := by unfold radiusEnvelope; positivity
  have hv := velocity_nonneg X X X hX hX
  have hn := normal_nonneg X X X hX hX
  have hvi : 0 ≤ velocityInputEnvelope X := by unfold velocityInputEnvelope; positivity
  have hei : 0 ≤ errorInputEnvelope X := by unfold errorInputEnvelope; positivity
  have ha1 := fixedVelocityGradeCost_nonneg X X hX 1
  have ha2 := fixedVelocityGradeCost_nonneg X X hX 2
  have hb := EulerPacketRadiusPolynomial.normalEnvelope_nonneg X hX
  have ht : 0 ≤ timeEnvelope X := by unfold timeEnvelope; positivity
  have hti : 0 ≤ timeInputEnvelope X := by unfold timeInputEnvelope; positivity
  have hpp1 := physicalEnvelope_nonneg X (4*X) hX (by positivity)
  have hpp2 := physicalEnvelope_nonneg X (4*inverseRadiusEnvelope X) hX (by positivity)
  have hw : 0 ≤ weightedErrorEnvelope X := by unfold weightedErrorEnvelope; positivity
  have hsh : 0 ≤ shearEnvelope X := by unfold shearEnvelope; positivity
  have hhe : 0 ≤ hessianEnvelope X := by unfold hessianEnvelope; positivity
  unfold extraEnvelope
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem gradeCost_mono (R H X : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hRX : R ≤ X) (hHX : H ≤ X) (n : ℕ) :
    fixedVelocityGradeCost R H n ≤ fixedVelocityGradeCost X X n := by
  have hX := hR.trans hRX
  unfold fixedVelocityGradeCost
  gcongr

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)

theorem physicalFixedCost_one_le (R C S X Y : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hRX : R ≤ X) (hCX : C ≤ X) (hSY : S ≤ Y) :
    physicalFixedCost D R C S 1 ≤ physicalEnvelope X Y := by
  have hX := hR.trans hRX
  have hY := hS.trans hSY
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  simp only [physicalFixedCost,physicalRadiusCost,sourceInverseRadius,physicalEnvelope,
    coordinateCost,D.m₀_unit,Nat.factorial_one,Nat.cast_one,pow_one,one_pow,mul_one]
  norm_num only
  gcongr

theorem shearCost_le (R H C X : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hRX : R ≤ X) (hHX : H ≤ X) (hCX : C ≤ X) :
    initializedGlobalShearCost R H C ≤ shearEnvelope X := by
  have hX := hR.trans hRX
  have he := sobolevEmbeddingConstant_nonneg period 3
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  have ha1 := gradeCost_mono R H X hR hH hRX hHX 1
  have ha2 := gradeCost_mono R H X hR hH hRX hHX 2
  have hg1 := fixedVelocityGradeCost_nonneg R H hR 1
  have hg2 := fixedVelocityGradeCost_nonneg R H hR 2
  have hg1X := hg1.trans ha1
  have hg2X := hg2.trans ha2
  have hrem : 0 ≤ initializedRemainderDerivativeCost R H := by
    unfold initializedRemainderDerivativeCost
    positivity
  unfold initializedGlobalShearCost shearEnvelope
  rw [abs_of_nonneg hrem]
  unfold initializedRemainderDerivativeCost coordinateCost
  gcongr

theorem hessianCost_le {q : ℕ} {R₀ : ℝ}
    (N : EulerTransversePacketJoin.NormalBudget D q R₀)
    (R H Rc C X : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hRX : R ≤ X) (hHX : H ≤ X) (hRcX : Rc ≤ X) (hCX : C ≤ X)
    (hNR : N.Rc ≤ X) (hNC : N.C ≤ X) :
    initializedPressureHessianCost N R H Rc C ≤ hessianEnvelope X := by
  have hX := hR.trans hRX
  have he := sobolevEmbeddingConstant_nonneg period 3
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  have ha1 := gradeCost_mono R H X hR hH hRX hHX 1
  have ha2 := gradeCost_mono R H X hR hH hRX hHX 2
  have hg1 := fixedVelocityGradeCost_nonneg R H hR 1
  have hg2 := fixedVelocityGradeCost_nonneg R H hR 2
  have hg1X := hg1.trans ha1
  have hg2X := hg2.trans ha2
  have hpp := physicalFixedCost_one_le D Rc C (4*R) X (4*X) hRc hC (by positivity)
    hRcX hCX (by gcongr)
  have hp0 := physicalFixedCost_nonneg D Rc C (4*R) 1 hRc hC (by positivity)
  have hpX := hp0.trans hpp
  have hNC0 := N.C_nonneg
  have hNR0 := N.Rc_nonneg
  unfold initializedPressureHessianCost fastHessianCost hessianEnvelope coordinateCost
  gcongr

end EulerPacketPhysicalCost
