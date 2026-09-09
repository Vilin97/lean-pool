/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedAllOrderBudget
public import LeanPool.NavierStokesAndEuler.Euler.PolynomialCostMajorant

@[expose] public section

/-! A single explicit polynomial controls the five scalar costs used by
the actual all-order packet correction. This is a uniform estimate on
primitive source bounds, not a per-parent eventual-frequency assertion. -/

noncomputable section

namespace EulerPacketFiveCost

open EulerPacketCorrectionConstants EulerPacketCorrectionCoefficients
  EulerPacketCorrectionScalar EulerPacketCoarseMajorant EulerPacketCylinderField
  EulerNonlinearEnergyConstants EulerGevreyCorrectionBound EulerGevreyMetricEstimate
  EulerGevreyGrowthCoefficient EulerH6Nonlinear EulerCylinderSobolevSpace
  EulerBaseTransportL2 EulerSobolevTransportCommutator EulerPolynomialCost
  EulerPacketProfileRecursion EulerPacketShiftArithmetic EulerSmoothLimit
open scoped BoundedContinuousFunction

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ (Space →L[ℝ] Space)) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ (Space →L[ℝ] Space)) := inferInstance

variable (P : ℝ) [Fact (0 < P)]

/-- The growth constant written in inverse-coercivity variables. -/
def rawGrowth (i m f t B M A0 A2 B0 B1 : ℝ) : ℝ :=
  let μ := 1+Real.sqrt 5461*i
  let s := sourceConstant B M
  let tr := transportConstant P B M
  let loss := lossConstant P M
  let k := m*i
  let g0 := (t+4*f^2*i^2)*i^2/2+f*i^2*sobolevEmbeddingConstant P 6*B0
  let g1 := f*i^2*sobolevEmbeddingConstant P 6*μ
  1+g0+g1+k*s+k*((s*(productConstant P 3*B1+A0+2*A2*productConstant P 3*B0)+tr*B0)*μ)+
    k*((s*A2*productConstant P 3+tr)*μ^2)+k*(loss*μ^2)

def growthEnvelope (X : ℝ) : ℝ :=
  rawGrowth P X X X X X X X X (2*velocity X X X) (48*velocity X X X*X)

def inverseRadiusEnvelope (X : ℝ) : ℝ := 1+8*X+4*X^2+X

def fiveEnvelope (X : ℝ) : ℝ :=
  1+tailPolynomialConstant X X X+X+12*growthEnvelope P X*X+
    8*growthEnvelope P X*X*drift X X X*inverseRadiusEnvelope X+
    8*growthEnvelope P X*X*inverseRadiusEnvelope X

def gradePolynomial (n : ℕ) : Polynomial ℝ :=
  3*Polynomial.X^(2*n)*((4*Polynomial.X)^(highShift n)*
    Polynomial.C ((highShift n).factorial : ℝ)^2)

def velocityPolynomial : Polynomial ℝ :=
  Polynomial.X*(gradePolynomial 1+gradePolynomial 2+1)

def driftPolynomial : Polynomial ℝ :=
  2*(3*velocityPolynomial+Polynomial.X*(gradePolynomial 2+2))

def growthPolynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let μ := 1+Polynomial.C (Real.sqrt 5461)*X
  let s := 1+2*X*(3136*X+1)
  let tr := Polynomial.C (5461*baseTransportConstant P)+
    2688*X*(8*X*Polynomial.C (5460*lowerProductConstant P 3))
  let loss := (4+32*X)*Polynomial.C (productConstant P 3)
  let p := Polynomial.C (productConstant P 3)
  let e := Polynomial.C (sobolevEmbeddingConstant P 6)
  let V := velocityPolynomial
  let k := X*X
  let g0 := (X+4*X^2*X^2)*X^2*Polynomial.C (1/2)+X*X^2*e*(2*V)
  let g1 := X*X^2*e*μ
  1+g0+g1+k*s+k*((s*(p*(48*V*X)+X+2*X*p*(2*V))+tr*(2*V))*μ)+
    k*((s*X*p+tr)*μ^2)+k*(loss*μ^2)

def fivePolynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let G := growthPolynomial P
  let I := 1+8*X+4*X^2+X
  let tail := (1+163*X)*X^2*(4*X*Polynomial.C ((550 : ℝ)^2))^110
  1+tail+X+12*G*X+8*G*X*driftPolynomial*I+8*G*X*I

omit [Fact (0 < P)] in
theorem gradePolynomial_eval (n : ℕ) (X : ℝ) :
    (gradePolynomial n).eval X=fixedVelocityGradeCost X X n := by
  unfold gradePolynomial fixedVelocityGradeCost
  rw [Polynomial.eval_mul,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_pow,Polynomial.eval_C]

omit [Fact (0 < P)] in
theorem velocityPolynomial_eval (X : ℝ) : velocityPolynomial.eval X=velocity X X X := by
  unfold velocityPolynomial velocity
  rw [Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_add,Polynomial.eval_add,
    gradePolynomial_eval,gradePolynomial_eval,Polynomial.eval_one]

omit [Fact (0 < P)] in
theorem driftPolynomial_eval (X : ℝ) : driftPolynomial.eval X=drift X X X := by
  unfold driftPolynomial drift normal
  rw [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,velocityPolynomial_eval,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_add,gradePolynomial_eval,Polynomial.eval_ofNat]

theorem growthPolynomial_eval (X : ℝ) : (growthPolynomial P).eval X=growthEnvelope P X := by
  unfold growthPolynomial growthEnvelope rawGrowth sourceConstant transportConstant lossConstant
  dsimp only
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one,velocityPolynomial_eval,div_eq_mul_inv]
  ring

theorem fivePolynomial_eval (X : ℝ) : (fivePolynomial P).eval X=fiveEnvelope P X := by
  unfold fivePolynomial fiveEnvelope inverseRadiusEnvelope tailPolynomialConstant
  dsimp only
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one,growthPolynomial_eval,driftPolynomial_eval]

def costConstant : ℝ := coefficientCost (fivePolynomial P)
def costPower : ℕ := (fivePolynomial P).natDegree

theorem costConstant_pos : 0 < costConstant P := coefficientCost_pos _

theorem fiveEnvelope_power (X : ℝ) (hX : 1 ≤ X) :
    fiveEnvelope P X ≤ costConstant P*X^(costPower P) := by
  rw [← fivePolynomial_eval]
  exact (le_abs_self _).trans (eval_bound (fivePolynomial P) X hX)

theorem velocity_mono {R H C X : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H) (_hC : 0 ≤ C)
    (hRX : R ≤ X) (hHX : H ≤ X) (hCX : C ≤ X) : velocity R H C ≤ velocity X X X := by
  have hX : 0 ≤ X := hR.trans hRX
  unfold velocity fixedVelocityGradeCost
  gcongr

theorem drift_mono {R H C X : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hRX : R ≤ X) (hHX : H ≤ X) (hCX : C ≤ X) : drift R H C ≤ drift X X X := by
  have hX : 0 ≤ X := hR.trans hRX
  unfold drift normal
  have hv := velocity_mono hR hH hC hRX hHX hCX
  unfold fixedVelocityGradeCost
  gcongr

private theorem rawGrowth_mono {i m f t B M A0 A2 B0 B1 X Y0 Y1 : ℝ}
    (hi : 0 ≤ i) (_hm : 0 ≤ m) (hf : 0 ≤ f) (_ht : 0 ≤ t) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hA0 : 0 ≤ A0) (hA2 : 0 ≤ A2) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hiX : i ≤ X) (hmX : m ≤ X) (hfX : f ≤ X) (htX : t ≤ X) (hBX : B ≤ X)
    (hMX : M ≤ X) (hA0X : A0 ≤ X) (hA2X : A2 ≤ X) (hB0X : B0 ≤ Y0) (hB1X : B1 ≤ Y1) :
    rawGrowth P i m f t B M A0 A2 B0 B1 ≤ rawGrowth P X X X X X X X X Y0 Y1 := by
  have hX : 0 ≤ X := hi.trans hiX
  have hY0 : 0 ≤ Y0 := hB0.trans hB0X
  have hY1 : 0 ≤ Y1 := hB1.trans hB1X
  have hp := productConstant_nonneg P 3
  have hb := baseTransportConstant_nonneg P
  have hl := lowerProductConstant_nonneg P 3
  have he := sobolevEmbeddingConstant_nonneg P 6
  unfold rawGrowth sourceConstant transportConstant lossConstant
  dsimp only
  gcongr

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (Kc : CorrectionCoefficientBudget D P)

private local instance : NormedAddCommGroup C(Set.Icc (0 : ℝ) D.T, Space →ᵇ (Space →L[ℝ] Space)) :=
  inferInstance

theorem growth_eq_raw (R H C : ℝ) :
    growth D P Kc R H C = rawGrowth P D.inverseBound (inverseMetricBound D)
      (inverseMetricFirstBound D) (inverseMetricTimeBound D) Kc.B Kc.M Kc.A0 Kc.A2
      (2*velocity R H C) (48*velocity R H C*R) := by
  unfold growth growthCoefficient rawGrowth energyConstant
    EulerNonlinearEnergyConstants.linearCoefficient
    EulerNonlinearEnergyConstants.quadraticCoefficient
    EulerNonlinearEnergyConstants.lossCoefficient growthBudgetBase growthBudgetSlope
      metricAmplification
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow,inv_inv]
  ring

theorem growth_le_envelope (R H C X : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hRX : R ≤ X) (hHX : H ≤ X) (hCX : C ≤ X)
    (hi : D.inverseBound ≤ X) (hm : inverseMetricBound D ≤ X)
    (hf : inverseMetricFirstBound D ≤ X) (ht : inverseMetricTimeBound D ≤ X)
    (hB : Kc.B ≤ X) (hM : Kc.M ≤ X) (hA0 : Kc.A0 ≤ X) (hA2 : Kc.A2 ≤ X) :
    growth D P Kc R H C ≤ growthEnvelope P X := by
  have hv := velocity_mono hR hH hC hRX hHX hCX
  have hv0 := velocity_nonneg R H C hR hC
  have hvX : 0 ≤ velocity X X X := hv0.trans hv
  have hm0 : 0 ≤ inverseMetricBound D := norm_nonneg (inverseMetricCoefficient D).path
  have hf0 : 0 ≤ inverseMetricFirstBound D :=
    norm_nonneg (iteratedFDeriv ℝ 1 (EulerMeanCoefficients.translateCoefficientPath
      (inverseMetricCoefficient D).path) 0)
  have ht0 : 0 ≤ inverseMetricTimeBound D := norm_nonneg (inverseMetricTimeCoefficient D).path
  rw [growth_eq_raw]
  exact rawGrowth_mono P D.inverseBound_pos.le hm0 hf0 ht0
    Kc.B_nonneg (zero_le_one.trans Kc.M_one_le) Kc.A0_nonneg Kc.A2_nonneg
    (by positivity) (by positivity) hi hm hf ht hB hM hA0 hA2 (by gcongr) (by gcongr)

end EulerPacketFiveCost
