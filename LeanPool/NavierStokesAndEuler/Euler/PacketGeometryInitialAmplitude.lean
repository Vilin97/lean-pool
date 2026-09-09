/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedRadiusPolynomial
import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryGuards
import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryProfileEnvelope
import LeanPool.NavierStokesAndEuler.Euler.PacketPressureScaleCosts
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceUniformEnvelope

/-! The actual chosen primary amplitude has exponential initial decay.
Its prefactor is a fixed polynomial in the same source parameters. -/

@[expose] public section


noncomputable section

namespace EulerPacketInitialAmplitude

open EulerPolynomialCost EulerParentInitializedRadius

/-- Envelope, given by `4*X^2*(1+sourceEnvelope X)`. -/
def envelope (X : ℝ) : ℝ := 4*X^2*(1+sourceEnvelope X)
/-- Polynomial, given by `4*Polynomial.X^2*(1+sourcePolynomial)`. -/
def polynomial : Polynomial ℝ := 4*Polynomial.X^2*(1+sourcePolynomial)
/-- Bound constant, given by `coefficientCost polynomial`. -/
def boundConstant : ℝ := coefficientCost polynomial
/-- Degree, given by `polynomial.natDegree`. -/
def degree : ℕ := polynomial.natDegree

theorem constant_pos : 0 < boundConstant := coefficientCost_pos _

theorem polynomial_eval (X : ℝ) : polynomial.eval X=envelope X := by
  simp only [polynomial,envelope,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_add,Polynomial.eval_one,sourcePolynomial_eval]

theorem envelope_bound (X : ℝ) (hX : 1 ≤ X) : envelope X ≤ boundConstant*X^degree := by
  rw [← polynomial_eval]
  exact (le_abs_self _).trans (eval_bound polynomial X hX)

theorem horizon_le_cost (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    H ≤ 560*H^10/ε := by
  have hp : H ≤ H^10 := by simpa only [pow_one] using pow_le_pow_right₀ hH (by norm_num : 1 ≤ 10)
  apply (le_div_iff₀ hε).mpr
  have hm : H*ε ≤ H := (mul_le_mul_of_nonneg_left hε1 (zero_le_one.trans hH)).trans_eq (mul_one _)
  nlinarith only [hp,hm,pow_nonneg (zero_le_one.trans hH) 10]

end EulerPacketInitialAmplitude

namespace EulerPacketSourceGeometry.Guards

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketInitialAmplitude
  EulerPacketUniformSource EulerParentInitializedRadius EulerPacketPressureScale EulerGevrey

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T} {P : ParentFrame D τ}
  {H : HistoryData (D.initial τ hτ hτT.le)} (J : Guards hτ hτT P H)
  (hball : (1 / 2 : ℝ) ≤ J.radius)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT H (Fin 4) 6)

theorem primaryAmplitude_polynomial (X x : ℝ) (hX : 1 ≤ X)
    (hH : P.horizon ≤ X) (hh : J.hchild ≤ X) (hδ : J.δ ≤ 1)
    (hC : L.C₀ ≤ sourceEnvelope X) (hσ : P.sigma * x ≤ 2) :
    J.primaryAmplitude hball ≤ boundConstant*X^degree*Real.exp (-x/8) := by
  have hF : ∀ t y, ‖D.F.field t y‖ ≤ L.C₀ := by
    intro t y
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using L.frame_bound 0 t y
  have hf := (P.rayScale_inv_le_frameBound hτ hτT).trans
    (D.frameBound_le_of_frame L.C₀ L.C₀_nonneg hF)
  have hf0 : 0 ≤ (P.rayScale hτ hτT)⁻¹ :=
    (inv_pos.mpr (rayScale_pos hτ hτT P)).le
  have hfS : (P.rayScale hτ hτT)⁻¹ ≤ 1+sourceEnvelope X := by linarith only [hf,hC]
  have hX0 := zero_le_one.trans hX
  have hS := zero_le_one.trans (sourceEnvelope_one X hX)
  have hH0 := zero_le_one.trans J.horizon_lower
  have hc0 := J.child_nonneg
  have hd0 := J.delta_nonneg
  have hpref : 4*P.horizon*J.δ*J.hchild/P.rayScale hτ hτT ≤ envelope X := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ 4*X*1*X*(1+sourceEnvelope X) := by gcongr
      _ = _ := by unfold envelope; ring
  have hs := sigma_exponential_bound P.sigma x J.sigma_pos hσ
  have hp := J.primaryAmplitude_exponential hball
  apply hp.trans
  apply (mul_le_mul hpref hs (Real.exp_pos _).le ?_).trans
  · exact mul_le_mul_of_nonneg_right (envelope_bound X hX) (Real.exp_pos _).le
  · unfold envelope
    positivity

omit [CompleteSpace U] in
include J in
theorem horizon_le_growthCost : P.horizon ≤ 560*P.horizon^10/P.epsilon :=
  horizon_le_cost P.horizon P.epsilon J.horizon_lower J.epsilon_pos J.epsilon_small

end EulerPacketSourceGeometry.Guards

namespace EulerPacketSourceGeometry.ForwardGuards

open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketInitialAmplitude
  EulerPacketUniformSource EulerParentInitializedRadius EulerPacketPressureScale

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {P : ParentFrame D 0} (J : ForwardGuards P)
  (hball : (1 / 2 : ℝ) ≤ J.radius)

theorem primaryAmplitude_polynomial (X x : ℝ) (hX : 1 ≤ X)
    (hH : P.horizon ≤ X) (hh : J.hchild ≤ X) (hδ : J.δ ≤ 1) (hσ : P.sigma * x ≤ 2) :
    J.primaryAmplitude hball ≤ boundConstant*X^degree*Real.exp (-x/8) := by
  have hS := zero_le_one.trans (sourceEnvelope_one X hX)
  have hX0 := zero_le_one.trans hX
  have hH0 := zero_le_one.trans J.horizon_lower
  have hc0 := J.child_nonneg
  have hd0 := J.delta_nonneg
  have hpref : 4*P.horizon*J.δ*J.hchild ≤ envelope X := by
    calc
      _ ≤ 4*X*1*X := by gcongr
      _ ≤ 4*X*1*X*(1+sourceEnvelope X) := by nlinarith only [mul_nonneg (sq_nonneg X) hS]
      _ = _ := by unfold envelope; ring
  have hs := sigma_exponential_bound P.sigma x J.sigma_pos hσ
  apply (J.primaryAmplitude_exponential hball).trans
  apply (mul_le_mul hpref hs (Real.exp_pos _).le ?_).trans
  · exact mul_le_mul_of_nonneg_right (envelope_bound X hX) (Real.exp_pos _).le
  · unfold envelope
    positivity

include J hball in
theorem horizon_le_growthCost : P.horizon ≤ 560*P.horizon^10/P.epsilon := by
  have he : P.epsilon ≤ 1 := (J.lowGeometry hball).epsilon_le_one
  exact horizon_le_cost P.horizon P.epsilon J.horizon_lower J.epsilon_pos he

end EulerPacketSourceGeometry.ForwardGuards
