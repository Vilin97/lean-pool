/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceUniformEnvelope
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialPhysical

/-! At each fixed Sobolev order, the two actual initial-increment costs
are fixed polynomials in the source primitives. Frequency and amplitude
are kept outside these polynomials. -/

@[expose] public section


noncomputable section

namespace EulerPacketInitialCost

open Finset EulerPhysicalL2Scaling EulerPacketTerminalDatum EulerPacketInitial
  EulerPacketPhysicalCost EulerPacketFiveCost EulerPacketCorrectionOutput EulerPolynomialCost

/-- Jet polynomial map, given by `∑ n ∈ range (s+1), R^n*Polynomial.C ((n.factorial : ℝ)^2)`. -/
def jetPolynomialMap (R : Polynomial ℝ) (s : ℕ) : Polynomial ℝ :=
  ∑ n ∈ range (s+1), R^n*Polynomial.C ((n.factorial : ℝ)^2)

theorem jetPolynomialMap_eval (R : Polynomial ℝ) (s : ℕ) (X : ℝ) :
    (jetPolynomialMap R s).eval X=jetPolynomial (R.eval X) s := by
  simp only [jetPolynomialMap,jetPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_C]

/-- Physical polynomial, given by `∑ n ∈ range (s+1), Polynomial.C ((4*C)^n*Real.sqrt
(2/period+2*period)) * jetPolynomialMap R (n+1)`. -/
def physicalPolynomial (R : Polynomial ℝ) (C : ℝ) (s : ℕ) : Polynomial ℝ :=
  ∑ n ∈ range (s+1), Polynomial.C ((4*C)^n*Real.sqrt (2/period+2*period)) *
    jetPolynomialMap R (n+1)

theorem physicalPolynomial_eval (R : Polynomial ℝ) (C : ℝ) (s : ℕ) (X : ℝ) :
    (physicalPolynomial R C s).eval X=physicalDerivativeCost period (R.eval X) C s := by
  simp only [physicalPolynomial,physicalDerivativeCost,Polynomial.eval_finsetSum,
    Polynomial.eval_mul,Polynomial.eval_C,jetPolynomialMap_eval]

theorem jetPolynomial_mono {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) (s : ℕ) :
    jetPolynomial R s ≤ jetPolynomial S s := by
  unfold jetPolynomial
  apply sum_le_sum
  intro n _
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR hRS n) (sq_nonneg _)

theorem physicalDerivativeCost_mono {R S C D : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hRS : R ≤ S) (hCD : C ≤ D) (s : ℕ) :
    physicalDerivativeCost period R C s ≤ physicalDerivativeCost period S D s := by
  unfold physicalDerivativeCost
  apply sum_le_sum
  intro n _
  have hj := jetPolynomial_mono hR hRS (n+1)
  have hj0 := jetPolynomial_nonneg R hR (n+1)
  have hj1 := hj0.trans hj
  have hD := hC.trans hCD
  have hs := Real.sqrt_nonneg (2/period+2*period)
  gcongr

/-- Envelope, given by `1+(highCost X X+meanCost X X)*physicalDerivativeCost period (4*X)
(coordinateCost*2) s`. -/
def envelope (s : ℕ) (X : ℝ) : ℝ :=
  1+(highCost X X+meanCost X X)*physicalDerivativeCost period (4*X) (coordinateCost*2) s

/-- Polynomial, given by `1+(gradePolynomial 1+2*gradePolynomial 2+3) * physicalPolynomial
(4*Polynomial.X) (coordinateCost*2) s`. -/
def polynomial (s : ℕ) : Polynomial ℝ :=
  1+(gradePolynomial 1+2*gradePolynomial 2+3) *
    physicalPolynomial (4*Polynomial.X) (coordinateCost*2) s

theorem polynomial_eval (s : ℕ) (X : ℝ) : (polynomial s).eval X=envelope s X := by
  unfold polynomial envelope highCost meanCost
  simp only [Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_one,Polynomial.eval_ofNat,physicalPolynomial_eval,
    Polynomial.eval_X,gradePolynomial_eval]
  ring

theorem costs_le_envelope (s : ℕ) (R H X : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hRX : R ≤ X) (hHX : H ≤ X) :
    highCost R H*physicalDerivativeCost period (4*R) (coordinateCost*2) s ≤ envelope s X ∧
    meanCost R H*physicalDerivativeCost period (4*R) coordinateCost s ≤ envelope s X := by
  have hX := hR.trans hRX
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  have h1 := gradeCost_mono R H X hR hH hRX hHX 1
  have h2 := gradeCost_mono R H X hR hH hRX hHX 2
  have hhigh : highCost R H ≤ highCost X X := by unfold highCost; linarith
  have hmean : meanCost R H ≤ meanCost X X := by unfold meanCost; linarith
  have hd1 := physicalDerivativeCost_mono (by positivity : 0 ≤ 4*R)
    (by positivity : 0 ≤ coordinateCost*2) (by linarith : 4*R ≤ 4*X) le_rfl s
  have hd2 := physicalDerivativeCost_mono (by positivity : 0 ≤ 4*R)
    hc (by linarith : 4*R ≤ 4*X) (by linarith : coordinateCost ≤ coordinateCost*2) s
  have hv := highCost_nonneg X X hX
  have hm := meanCost_nonneg X X hX
  have hd := physicalDerivativeCost_nonneg period (4*X) (coordinateCost*2) (by
      positivity) (by positivity) s
  have hh := mul_le_mul hhigh hd1
    (physicalDerivativeCost_nonneg period (4*R) (coordinateCost*2) (by
        positivity) (by positivity) s) hv
  have hm' := mul_le_mul hmean hd2
    (physicalDerivativeCost_nonneg period (4*R) coordinateCost (by positivity) hc s) hm
  unfold envelope
  constructor
  · nlinarith only [hh,mul_nonneg hm hd]
  · nlinarith only [hm',mul_nonneg hv hd]

/-- Source polynomial as an element of `Polynomial ℝ`. -/
def sourcePolynomial (s : ℕ) : Polynomial ℝ :=
  (polynomial s).comp ((1+Polynomial.X+EulerPacketRadiusPolynomial.radiusPolynomial +
    EulerPacketCorrectionPrimitive.primitivePolynomial period).comp
        EulerPacketUniformSource.profilePolynomial)

/-- Source constant, given by `coefficientCost (sourcePolynomial s)`. -/
def sourceConstant (s : ℕ) : ℝ := coefficientCost (sourcePolynomial s)
/-- Source power, given by `(sourcePolynomial s).natDegree`. -/
def sourcePower (s : ℕ) : ℕ := (sourcePolynomial s).natDegree

theorem sourceConstant_pos (s : ℕ) : 0 < sourceConstant s := coefficientCost_pos _

theorem sourcePolynomial_eval (s : ℕ) (X : ℝ) :
    (sourcePolynomial s).eval X =
      envelope s (EulerPacketInitializedCost.envelope (EulerPacketUniformSource.profileEnvelope X))
          := by
  simp only [sourcePolynomial,Polynomial.eval_comp,polynomial_eval,Polynomial.eval_add,
    Polynomial.eval_one,Polynomial.eval_X,EulerPacketRadiusPolynomial.radiusPolynomial_eval,
    EulerPacketCorrectionPrimitive.primitivePolynomial_eval,
    EulerPacketUniformSource.profilePolynomial_eval,EulerPacketInitializedCost.envelope]

theorem source_bound (s : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    envelope s (EulerPacketInitializedCost.envelope (EulerPacketUniformSource.profileEnvelope X)) ≤
      sourceConstant s*X^sourcePower s := by
  rw [← sourcePolynomial_eval]
  exact (le_abs_self _).trans (eval_bound (sourcePolynomial s) X hX)

end EulerPacketInitialCost
