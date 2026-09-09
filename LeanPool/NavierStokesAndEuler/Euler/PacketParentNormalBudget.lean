/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketParentCoefficientBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketNormalBudget

/-! The normal/pressure/corrector budget follows from the actual deformation
and its first time derivative. Its radius is an explicit polynomial in their
Gevrey radius and amplitudes; no inverse or strain jet bound is an input. -/

@[expose] public section


noncomputable section

namespace EulerPacketParentNormalBudget

open Set EulerSmoothLimit EulerMeanCoefficients EulerPacketCofactor EulerPacketPiola
  EulerGevrey EulerTimeLpGramGevrey EulerParameterWordGevrey EulerSourceCylinderTimeBounds

/-- Amplitude, given by `9*C^2+27*C^2*C₁`. -/
def amplitude (C C₁ : ℝ) : ℝ := 9*C^2+27*C^2*C₁

/-- Inverse radius, given by `2*(1+(1+C)^2*(3*(amplitude C C₁)^2+2))*(R+1)`. -/
def inverseRadius (R C C₁ : ℝ) : ℝ :=
  2*(1+(1+C)^2*(3*(amplitude C C₁)^2+2))*(R+1)

/-- Radius, given by `16*(R+4*inverseRadius R C C₁+1)`. -/
def radius (R C C₁ : ℝ) : ℝ := 16*(R+4*inverseRadius R C C₁+1)

theorem amplitude_nonneg (C C₁ : ℝ) (hC₁ : 0 ≤ C₁) : 0 ≤ amplitude C C₁ := by
  unfold amplitude
  positivity

theorem inverseRadius_nonneg (R C C₁ : ℝ) (hR : 0 ≤ R) : 0 ≤ inverseRadius R C C₁ := by
  unfold inverseRadius
  positivity

theorem radius_nonneg (R C C₁ : ℝ) (hR : 0 ≤ R) : 0 ≤ radius R C C₁ := by
  have hi := inverseRadius_nonneg R C C₁ hR
  unfold radius
  positivity

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)
  (R C C₁ : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → EndSpace) x‖ ≤ C * majorant R 0 n)
  (hF₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → EndSpace) x‖ ≤ C₁ * majorant R 0 n)

include hR hC hF in
theorem inverse_guard :
    2*gramCost D.normalLower (amplitude C C₁) 1*(R+1) ≤ inverseRadius R C C₁ := by
  have hzero : ∀ t x, ‖D.F.field t x‖ ≤ C := by
    intro t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using hF 0 t x
  have hi := D.normalLower_inv_le_of_frame C hC hzero
  calc
    _ = 2*(1+D.normalLower⁻¹*(3*(amplitude C C₁)^2+2))*(R+1) := by
      unfold gramCost
      ring
    _ ≤ 2*(1+(1+C)^2*(3*(amplitude C C₁)^2+2))*(R+1) := by gcongr

/-- Source normal budget, bundling `Rc`, `C`, `Ri`, `Rc_nonneg` and the required compatibility
proofs. -/
def sourceNormalBudget (q : ℕ) : EulerTransversePacketJoin.NormalBudget D q (radius R C C₁) where
  Rc := R
  C := amplitude C C₁
  Ri := inverseRadius R C C₁
  Rc_nonneg := hR
  C_nonneg := amplitude_nonneg C C₁ hC₁
  inverse_radius := inverse_guard D R C C₁ hR hC hF
  inverse_bound n t x := (coefficientInverse_bound D.F D.FInv.field hdet D.inverse_left
    R C hR hC hF n t x).trans
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (by positivity : 0 ≤ 27*C^2*C₁))
        (majorant_nonneg R hR 0 n))
  strain_bound n t x := (coefficientStrain_bound D.F D.F₁ D.M hdet D.strain_equation
    R C C₁ hR hC hC₁ hF hF₁ n t x).trans
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (by positivity : 0 ≤ 9*C^2))
        (majorant_nonneg R hR 0 n))
  radius := by
    norm_num [sobolevCoefficientRadius,
        EulerTransversePacketProvider.Data.correctorCoefficientRadius, radius]
    ring_nf
    exact le_rfl

end EulerPacketParentNormalBudget
