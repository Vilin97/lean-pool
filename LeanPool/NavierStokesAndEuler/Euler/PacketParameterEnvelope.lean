/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketBaseGuardScales
public import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyScales
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceParameterScales

/-! The source size used by the canonical packet solve is bounded by
one explicit polynomial-exponential envelope, including the base-sized
boundary coefficient and both reciprocal time intervals. -/

@[expose] public section


noncomputable section

namespace EulerPacketParameterEnvelope

open Real EulerPacketSourceParameterScales EulerPacketUniformFrequencyScales
  EulerPacketSourceScaleSequence EulerPacketSourceScaleChoice EulerParentInitializedRadius
  EulerPacketSourceScales

/-- Bound constant, given by `8+1120*(2*Cθ)^10+CB+Cξ`. -/
def boundConstant (Cθ CB Cξ : ℝ) : ℝ := 8+1120*(2*Cθ)^10+CB+Cξ

theorem constant_pos (Cθ CB Cξ : ℝ) (hB : 0 ≤ CB) (hξ : 0 ≤ Cξ) :
    0 < boundConstant Cθ CB Cξ := by
  unfold boundConstant
  positivity

theorem source_size_le (J D : ℕ) (hJ : 2 ≤ J) (X : ℝ) (hX : 1 ≤ X)
    (Cθ CB Cξ d c : ℝ) (hθ : 1 ≤ Cθ) (hB : 0 ≤ CB) (hξC : 0 ≤ Cξ)
    (hd : 0 ≤ d) (hc : 1 ≤ c) (hdc : d ≤ c)
    (R : ℕ) (hRc : (R : ℝ) * d ≤ c)
    (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
    (hbaseK : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4))
    (n : ℕ) (K Ti TiTotal Cp B ξ Θ Ei : ℝ) (hK0 : 0 ≤ K)
    (hK : K ≤ previousFrequency J D X n ^ d)
    (hTi : Ti ≤ 12 / EulerPacketBaseGuardScales.baseHorizon J X)
    (hTiTotal : TiTotal ≤ 12 / EulerPacketBaseGuardScales.baseHorizon J X)
    (hBc : B ≤ CB * X ^ 1000) (hξ : ξ ≤ Cξ * K ^ R)
    (hΘ0 : 0 ≤ Θ) (hΘ : Θ ≤ sourceTheta J Cθ (scaleSequence J X) n)
    (hEi0 : 0 ≤ Ei) (hEi : Ei ≤ 2 * previousShear J X n)
    (hCp : Cp ≤ 560 * Θ ^ 10 * Ei) :
    parameterSize K Ti TiTotal Cp B (spike J X n) ξ+shear J X n ≤
      parameterEnvelope J (boundConstant Cθ CB Cξ) c 20 1000 X n := by
  let z := predecessorExponent J X n
  let E := exp (c*z)
  let F := polynomialFactor J X n
  have hz : 0 ≤ z := predecessorExponent_nonneg J (by omega) X hX n
  have hE : 1 ≤ E := exponential_one_le J (by omega) X c hX (zero_le_one.trans hc) n
  have hF : 1 ≤ F := polynomialFactor_one J (by omega) X hX n
  have hF0 := zero_le_one.trans hF
  have hE0 := zero_le_one.trans hE
  have hFE : 1 ≤ F*E := one_le_mul_of_one_le_of_one_le hF hE
  have hFF : F ≤ F*E := le_mul_of_one_le_right hF0 hE
  have hEE : E ≤ F*E := le_mul_of_one_le_left hE0 hF
  have hExp : exp z ≤ E := exp_le_exp.mpr (by nlinarith only [hz,hc])
  have hKd : K ≤ exp (d*z) := hK.trans (previousFrequency_power_le J D hJ X d hX hd hbaseK n)
  have hKE : K ≤ E := hKd.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdc hz))
  have hKF : K ≤ F*E := hKE.trans hEE
  have hT := inverse_time_le_factor J (by omega) X hX n
  have hTiF : Ti ≤ 2*(F*E) := hTi.trans (hT.trans (mul_le_mul_of_nonneg_left hFF (by norm_num)))
  have hTiTotalF : TiTotal ≤ 2*(F*E) :=
    hTiTotal.trans (hT.trans (mul_le_mul_of_nonneg_left hFF (by norm_num)))
  have hxn := sequence_initial_le J (by omega) X (zero_le_one.trans hX) n
  have hxpow : X^1000 ≤ F := by
    have hp := monomial_le_polynomialFactor J (by omega) X hX n 0 1000 (by decide) le_rfl
    simp only [pow_zero,one_mul] at hp
    exact (pow_le_pow_left₀ (zero_le_one.trans hX) hxn 1000).trans hp
  have hBF : B ≤ CB*(F*E) := hBc.trans
    (mul_le_mul_of_nonneg_left (hxpow.trans hFF) hB)
  have hξE : ξ ≤ Cξ*E := by
    apply hξ.trans
    apply mul_le_mul_of_nonneg_left _ hξC
    apply (pow_le_pow_left₀ hK0 hKd R).trans
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hRc hz]
  have hξF : ξ ≤ Cξ*(F*E) := hξE.trans (mul_le_mul_of_nonneg_left hEE hξC)
  have hDF : (spike J X n)⁻¹ ≤ F*E :=
    (spike_inverse_le_exponential J hJ X hX n).trans (hExp.trans hEE)
  have hhF : shear J X n ≤ F*E :=
    (shear_le_exponential J hJ X hX n).trans (hExp.trans hEE)
  have hΘbig : Θ ≤ 2*Cθ*((J+n : ℕ) : ℝ)^2*(scaleSequence J X n)^2 :=
    hΘ.trans (sourceTheta_bounds (by omega) hθ
      (fun m => sequence_one_le J (by omega) X hX m) n).2
  have hEibig : Ei ≤ 2*exp z := hEi.trans
    (mul_le_mul_of_nonneg_left (previousShear_le_exponential J hJ X hX hbaseH n) (by norm_num))
  have hsmallpoly : ((J+n : ℕ) : ℝ)^20*(scaleSequence J X n)^20 ≤ F :=
    monomial_le_polynomialFactor J (by omega) X hX n 20 20 le_rfl (by decide)
  have hCpF : Cp ≤ (1120*(2*Cθ)^10)*(F*E) := by
    calc
      _ ≤ 560*(2*Cθ*((J+n : ℕ) : ℝ)^2*(scaleSequence J X n)^2)^10*(2*exp z) := by
        apply hCp.trans
        gcongr
      _ = (1120*(2*Cθ)^10)*(((J+n : ℕ) : ℝ)^20*(scaleSequence J X n)^20)*exp z := by
        simp only [mul_pow,← pow_mul]
        ring
      _ ≤ (1120*(2*Cθ)^10)*F*E := by
        gcongr
      _ = _ := by ring
  have hsum : parameterSize K Ti TiTotal Cp B (spike J X n) ξ+shear J X n ≤
      boundConstant Cθ CB Cξ*(F*E) := by
    unfold parameterSize boundConstant
    nlinarith only [hFE,hKF,hTiF,hTiTotalF,hBF,hξF,hDF,hhF,hCpF]
  apply hsum.trans_eq
  dsimp [F,E,z,parameterEnvelope,polynomialFactor,predecessorExponent]
  ring

end EulerPacketParameterEnvelope
