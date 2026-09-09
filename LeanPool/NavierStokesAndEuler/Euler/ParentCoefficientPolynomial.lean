/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketParentLabelCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentNormalBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentTransverseCosts
public import LeanPool.NavierStokesAndEuler.Euler.PolynomialCostMajorant

@[expose] public section

/-! A fixed polynomial in the genuine parent label bound controls the
coefficient leaves of the normal, joined and mean packet budgets. -/

noncomputable section

namespace EulerParentCoefficientPolynomial

open EulerPacketParentLabelBounds EulerPacketParentMeanCoercivity
  EulerPolynomialCost EulerMeanSmoothRepresentative

def radiusCeiling (K : ℝ) : ℝ := 1024+4*K
def curvatureCeiling (K : ℝ) : ℝ := 27*(frameAmplitude K)^2*gradientAmplitude K
def normalAmplitude (K : ℝ) : ℝ :=
  EulerPacketParentNormalBudget.amplitude (frameAmplitude K) (gradientAmplitude K)
def normalInverse (K : ℝ) : ℝ :=
  EulerPacketParentNormalBudget.inverseRadius (radiusCeiling K) (frameAmplitude K)
    (gradientAmplitude K)
def normalRadius (K : ℝ) : ℝ :=
  EulerPacketParentNormalBudget.radius (radiusCeiling K) (frameAmplitude K) (gradientAmplitude K)
def transverseInverse (K : ℝ) : ℝ :=
  EulerPacketParentTransverseCosts.inverseRadius (radiusCeiling K) (frameAmplitude K)
def leafEnvelope (K : ℝ) : ℝ :=
  1+radiusCeiling K+gradientAmplitude K+frameAmplitude K+curvatureCeiling K+
    normalAmplitude K+normalInverse K+normalRadius K+
    gramInverseEnvelope (frameAmplitude K)+transverseInverse K+
    inverseEnvelope (frameAmplitude K) (gradientAmplitude K)

def leafPolynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let R := 1024+4*X
  let G := Polynomial.C embeddingCost*X^2
  let F := 1+G
  let H := 27*F^2*G
  let A := 9*F^2+H
  let I := 2*(1+(1+F)^2*(3*A^2+2))*(R+1)
  let N := 16*(R+4*I+1)
  let C := (3*F^2+1)^2
  let J := 2*(1+C*(3*F^2+2))*(R+1)
  let V := 1+(2*C^2*F^2*G+C*G)+C*F
  1+R+G+F+H+A+I+N+C+J+2*V^2

theorem leafPolynomial_eval (K : ℝ) : leafPolynomial.eval K=leafEnvelope K := by
  simp only [leafPolynomial,leafEnvelope,radiusCeiling,gradientAmplitude,frameAmplitude,
    curvatureCeiling,normalAmplitude,normalInverse,normalRadius,transverseInverse,
    EulerPacketParentNormalBudget.amplitude,EulerPacketParentNormalBudget.inverseRadius,
    EulerPacketParentNormalBudget.radius,EulerPacketParentTransverseCosts.inverseRadius,
    gramInverseEnvelope,inverseEnvelope,transportEnvelope,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
    Polynomial.eval_one,Polynomial.eval_X,Polynomial.eval_C]

def leafConstant : ℝ := coefficientCost leafPolynomial
def leafPower : ℕ := leafPolynomial.natDegree

theorem leafConstant_pos : 0 < leafConstant := coefficientCost_pos _

theorem leafEnvelope_power (K : ℝ) (hK : 1 ≤ K) :
    leafEnvelope K ≤ leafConstant*K^leafPower := by
  rw [← leafPolynomial_eval]
  exact (le_abs_self _).trans (eval_bound leafPolynomial K hK)

theorem radiusCeiling_le (K : ℝ) (hK : 0 ≤ K) : coefficientRadius K ≤ radiusCeiling K := by
  unfold coefficientRadius radiusCeiling
  exact max_le (by linarith) (by linarith)

theorem leaf_bounds (K : ℝ) (hK : 0 ≤ K) :
    1 ≤ leafEnvelope K ∧ coefficientRadius K ≤ leafEnvelope K ∧
    gradientAmplitude K ≤ leafEnvelope K ∧ frameAmplitude K ≤ leafEnvelope K ∧
    curvatureCeiling K ≤ leafEnvelope K ∧ normalAmplitude K ≤ leafEnvelope K ∧
    EulerPacketParentNormalBudget.inverseRadius (coefficientRadius K) (frameAmplitude K)
      (gradientAmplitude K) ≤ leafEnvelope K ∧
    EulerPacketParentNormalBudget.radius (coefficientRadius K) (frameAmplitude K)
      (gradientAmplitude K) ≤ leafEnvelope K ∧
    gramInverseEnvelope (frameAmplitude K) ≤ leafEnvelope K ∧
    EulerPacketParentTransverseCosts.inverseRadius (coefficientRadius K) (frameAmplitude K) ≤
      leafEnvelope K ∧
    inverseEnvelope (frameAmplitude K) (gradientAmplitude K) ≤ leafEnvelope K := by
  have hG := gradientAmplitude_nonneg K
  have hF := frameAmplitude_nonneg K
  have hR : 0 ≤ radiusCeiling K := by unfold radiusCeiling; positivity
  have hH : 0 ≤ curvatureCeiling K := by unfold curvatureCeiling; positivity
  have hA : 0 ≤ normalAmplitude K := EulerPacketParentNormalBudget.amplitude_nonneg _ _ hG
  have hI : 0 ≤ normalInverse K := EulerPacketParentNormalBudget.inverseRadius_nonneg _ _ _ hR
  have hN : 0 ≤ normalRadius K := EulerPacketParentNormalBudget.radius_nonneg _ _ _ hR
  have hC : 0 ≤ gramInverseEnvelope (frameAmplitude K) := by unfold gramInverseEnvelope; positivity
  have hJ : 0 ≤ transverseInverse K := EulerPacketParentTransverseCosts.inverseRadius_nonneg _ _ hR
  have hV := inverseEnvelope_nonneg (frameAmplitude K) (gradientAmplitude K)
  have hr := radiusCeiling_le K hK
  have hi : EulerPacketParentNormalBudget.inverseRadius (coefficientRadius K)
      (frameAmplitude K) (gradientAmplitude K) ≤ normalInverse K := by
    unfold normalInverse EulerPacketParentNormalBudget.inverseRadius
    gcongr
  have hn : EulerPacketParentNormalBudget.radius (coefficientRadius K)
      (frameAmplitude K) (gradientAmplitude K) ≤ normalRadius K := by
    unfold normalRadius EulerPacketParentNormalBudget.radius
    change 16*(coefficientRadius K+4*EulerPacketParentNormalBudget.inverseRadius
      (coefficientRadius K) (frameAmplitude K) (gradientAmplitude K)+1) ≤
      16*(radiusCeiling K+4*normalInverse K+1)
    linarith
  have hj : EulerPacketParentTransverseCosts.inverseRadius (coefficientRadius K)
      (frameAmplitude K) ≤ transverseInverse K := by
    unfold transverseInverse EulerPacketParentTransverseCosts.inverseRadius
    gcongr
  unfold leafEnvelope
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

open EulerSmoothLimit EulerPacketPiola

theorem frameLower_inv_le {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (D : EulerTransversePacketProvider.Data U) (K : ℝ) (hK : 0 ≤ K)
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det=1)
    (hF : ∀ t x, ‖D.F.field t x‖ ≤ frameAmplitude K) :
    D.frameLower⁻¹ ≤ leafEnvelope K := by
  have hi : D.frameLower⁻¹ ≤ gramInverseEnvelope (frameAmplitude K) := by
    simpa only [gramInverseEnvelope,add_comm] using
      D.frameLower_inv_le_of_frame (frameAmplitude K) (frameAmplitude_nonneg K) hdet hF
  exact hi.trans (leaf_bounds K hK).2.2.2.2.2.2.2.2.1

end EulerParentCoefficientPolynomial
