/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFrequencyBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketTailNormalization

/-! Inverse-frame normalized approximation bounds are independent of truncation length. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.CoefficientBudget

open EulerPacketProfileRecursion EulerParameterWordGevrey EulerPacketFiniteFrequency

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {C : CoefficientData P T O}
  (BC : CoefficientBudget C) {raw : VectorField} (G : Field P T raw)

theorem normalized_approximation_bound {R k B C₁ C₂ : ℝ}
    (hG : G.WordBound 6 R (k⁻¹ * C₁ + (k⁻¹) ^ 2 * C₂ + 2 * B * (k⁻¹ * B) ^ 3) 0)
    (hR : 0 ≤ R) (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (hk : 4 ≤ k) (hB0 : 0 ≤ B) (hB : B ≤ k ^ (1 / 100 : ℝ))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ((C.inverse.multiply G).smul k).WordBound 6 R (BC.multiplierCost*(C₁+C₂+1)) 0 := by
  have hk0 : 0 ≤ k := by linarith
  have hi : 0 ≤ k⁻¹ := inv_nonneg.mpr hk0
  have hA : 0 ≤ k⁻¹*C₁+(k⁻¹)^2*C₂+2*B*(k⁻¹*B)^3 := by positivity
  have h := BC.normalized_inverse_bound G hG hA hRc k hk0
  have hb4 := fourth_power_le_frequency k B (by linarith) hB0 hB
  have hs := mul_le_mul_of_nonneg_left (normalized_low_high_le k B C₁ C₂ (by linarith) hC₂ hb4)
    BC.multiplierCost_nonneg
  have he : k*BC.multiplierCost*(k⁻¹*C₁+(k⁻¹)^2*C₂+2*B*(k⁻¹*B)^3) =
      BC.multiplierCost*(k*(k⁻¹*C₁+(k⁻¹)^2*C₂+2*B*(k⁻¹*B)^3)) := by ring
  exact h.mono_amplitude hR (he.trans_le hs)

end EulerPacketCylinderField.CoefficientBudget
