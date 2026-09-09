/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketApproximationNormalization

@[expose] public section

/-! Fixed smooth matrix coefficients preserve the finite packet's
inverse-frequency normalization with an explicit, frequency-independent
cost. This also applies to the actual inverse-frame time derivative. -/

noncomputable section


namespace EulerPacketCylinderField.MatrixCoefficient

open EulerSmoothLimit EulerPacketProfileRecursion EulerParameterWordGevrey
  EulerPacketFiniteFrequency EulerMeanCoefficients EulerGevrey
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)]
  {coef : EulerPacketPointJets.Domain → Space →L[ℝ] Space}
  (K : MatrixCoefficient T coef) {raw : VectorField} (G : Field P T raw)

theorem normalized_approximation_bound (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hK : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath K.path) a‖ ≤ C*majorant Rc 0 n)
    {R k B C₁ C₂ : ℝ}
    (hG : G.WordBound 6 R (k⁻¹*C₁+(k⁻¹)^2*C₂+2*B*(k⁻¹*B)^3) 0)
    (hR : 0 ≤ R) (hKR : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hk : 4 ≤ k) (hB0 : 0 ≤ B) (hB : B ≤ k^(1/100 : ℝ))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ((K.multiply G).smul k).WordBound 6 R
      ((3*sobolevCoefficientAmplitude (Fin 4) 6 Rc C)*(C₁+C₂+1)) 0 := by
  have hk0 : 0 ≤ k := by linarith
  have hi : 0 ≤ k⁻¹ := inv_nonneg.mpr hk0
  have hA : 0 ≤ k⁻¹*C₁+(k⁻¹)^2*C₂+2*B*(k⁻¹*B)^3 := by positivity
  have h := (hG.multiply K Rc C hRc hC hA hKR hK).smul k
  rw [abs_of_nonneg hk0] at h
  have hc : 0 ≤ 3*sobolevCoefficientAmplitude (Fin 4) 6 Rc C :=
    mul_nonneg (by norm_num) (sobolevCoefficientAmplitude_nonneg 6 Rc C hRc hC)
  have hb4 := fourth_power_le_frequency k B (by linarith) hB0 hB
  have hs := mul_le_mul_of_nonneg_left (normalized_low_high_le k B C₁ C₂ (by linarith) hC₂ hb4) hc
  exact h.mono_amplitude hR (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hs)

end EulerPacketCylinderField.MatrixCoefficient
