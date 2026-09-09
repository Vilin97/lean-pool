/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PolynomialCostMajorant
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentLabelCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.TransverseHistoryPolynomialCost
import LeanPool.NavierStokesAndEuler.Euler.TransverseHistoryParentCost

/-! One fixed polynomial controls the complete history sensitivity
envelope for all parent label constants and reciprocal time bounds. -/

@[expose] public section


noncomputable section

namespace EulerParentHistoryCost

open EulerPacketParentLabelBounds EulerPacketParentMeanCoercivity
  EulerTransverseHistoryBounds EulerTransverseEndpointDifference EulerPolynomialCost

/-- Label history envelope, constructed using `parentDifferenceEnvelope`. -/
def labelHistoryEnvelope (K Ti : ℝ) : ℝ :=
  parentDifferenceEnvelope Ti (frameAmplitude K) (gradientAmplitude K)
    (27*(frameAmplitude K)^2*gradientAmplitude K) (coefficientRadius K)

/-- Label history polynomial as an element of `Polynomial ℝ`. -/
def labelHistoryPolynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let v := Polynomial.C embeddingCost*X^2
  let f := 1+v
  let h := 27*f^2*v
  let R := 1024+4*X
  let ci := (3*f^2+1)^2
  let r := 1+(2*ci^2*f^2*v+ci*v)+ci*f
  let d := v+f
  let a := 1+h
  let x := f*R
  let y := v*R
  let z := h*R
  let s := r*(1+d^2*(2*r^2)*a)*(2*X*d)
  let e := (1+3*d^2*(2*r^2)*a+2*d^4*(2*r^2)^2*a^2)*(y+x) +
    (d^3*(2*r^2)+d^5*(2*r^2)^2*a)*z
  let sd := r*(2*X*e+(y+x)*s)
  let g := (4*ci^2*f^2*v+2*ci*v)*x+2*ci*f*y
  x*(2*(X+4*ci*f*v))*s+f*(4*g*s+(2*(X+4*ci*f*v))*sd)

theorem labelHistoryPolynomial_eval (P : ℝ) :
    labelHistoryPolynomial.eval P =
      parentDifferenceEnvelope P (frameAmplitude P) (gradientAmplitude P)
        (27*(frameAmplitude P)^2*gradientAmplitude P) (1024+4*P) := by
  simp [labelHistoryPolynomial,parentDifferenceEnvelope,differenceEnvelope,
    slopeDifferenceEnvelope,slopeEnvelope,generatorDifferenceEnvelope,endpointDifferenceCost,
    gramInverseEnvelope,transportEnvelope,frameAmplitude,gradientAmplitude]

/-- Label history constant, given by `coefficientCost labelHistoryPolynomial`. -/
def labelHistoryConstant : ℝ := coefficientCost labelHistoryPolynomial
/-- Label history power, given by `labelHistoryPolynomial.natDegree`. -/
def labelHistoryPower : ℕ := labelHistoryPolynomial.natDegree

theorem labelHistoryConstant_pos : 0 < labelHistoryConstant := coefficientCost_pos _

theorem labelHistoryEnvelope_power (K Ti : ℝ) (hK : 0 ≤ K) (hTi : 0 ≤ Ti) :
    labelHistoryEnvelope K Ti ≤ labelHistoryConstant*(1+K+Ti)^labelHistoryPower := by
  let P := 1+K+Ti
  have hP : 1 ≤ P := by dsimp [P]; linarith
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hKP : K ≤ P := by dsimp [P]; linarith
  have hTiP : Ti ≤ P := by dsimp [P]; linarith
  have hE := embeddingCost_nonneg
  have hF0 := frameAmplitude_nonneg K
  have hV0 := gradientAmplitude_nonneg K
  have hV : gradientAmplitude K ≤ gradientAmplitude P := by
    unfold gradientAmplitude
    gcongr
  have hF : frameAmplitude K ≤ frameAmplitude P := add_le_add (le_refl (1 : ℝ)) hV
  have hH : 27*(frameAmplitude K)^2*gradientAmplitude K ≤
      27*(frameAmplitude P)^2*gradientAmplitude P := by gcongr
  have hR : coefficientRadius K ≤ 1024+4*P := by
    unfold coefficientRadius
    apply max_le
    · linarith
    · linarith
  have he : labelHistoryEnvelope K Ti ≤ labelHistoryPolynomial.eval P := by
    rw [labelHistoryPolynomial_eval]
    exact parentDifferenceEnvelope_mono hTi hF0 hV0 (by positivity)
      (coefficientRadius_nonneg K) hTiP hF hV hH hR
  exact he.trans ((le_abs_self _).trans (eval_bound labelHistoryPolynomial P hP))

end EulerParentHistoryCost
