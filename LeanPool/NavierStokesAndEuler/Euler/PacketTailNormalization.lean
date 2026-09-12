/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketExponentialTail

/-! Actual inverse-frame normalization preserves the exponentially small residual estimate. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.CoefficientBudget

open EulerSmoothLimit EulerPacketProfileRecursion EulerParameterWordGevrey

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {C : CoefficientData P T O}
  (BC : CoefficientBudget C) {raw : VectorField} (G : Field P T raw)

theorem normalized_inverse_bound {R A : ℝ} {d : ℕ}
    (hG : G.WordBound 6 R A d) (hA : 0 ≤ A)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R) (k : ℝ) (hk : 0 ≤ k) :
    ((C.inverse.multiply G).smul k).WordBound 6 R (k*BC.multiplierCost*A) d := by
  have h := (hG.multiply C.inverse BC.Rc BC.amplitude BC.Rc_nonneg BC.amplitude_nonneg
    hA hRc BC.inverse_bound).smul k
  simpa only [abs_of_nonneg hk,multiplierCost,mul_assoc] using h

theorem normalized_tail_exponential {R B k X : ℝ} (N : ℕ)
    (hG : G.WordBound 6 R (2 * B * (k⁻¹ * B) ^ (N + 1)) 0)
    (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)
    (hR : 0 ≤ R) (hk : 4 ≤ k) (hB0 : 0 ≤ B)
    (hB : B ≤ k ^ (1 / 100 : ℝ)) (hC : BC.multiplierCost ≤ k ^ (1 / 100 : ℝ))
    (hX : 6 ≤ X) (hN : X - 1 ≤ (N : ℝ)) :
    ((C.inverse.multiply G).smul k).WordBound 6 R
      (Real.exp (-(7/10)*X*Real.log k)) 0 := by
  have hk0 : 0 ≤ k := by linarith
  have hA : 0 ≤ 2*B*(k⁻¹*B)^(N+1) :=
    mul_nonneg (mul_nonneg (by norm_num) hB0) (pow_nonneg (mul_nonneg (inv_nonneg.mpr hk0) hB0) _)
  have h := BC.normalized_inverse_bound G hG hA hRc k hk0
  have he : k*BC.multiplierCost*(2*B*(k⁻¹*B)^(N+1)) =
      2*BC.multiplierCost*k*B*(B/k)^(N+1) := by rw [div_eq_mul_inv]; ring
  rw [he] at h
  exact h.mono_amplitude hR (EulerPacketTailBound.normalized_tail_exponential
    k B BC.multiplierCost X hk hB0 BC.multiplierCost_nonneg hB hC N hX hN)

end EulerPacketCylinderField.CoefficientBudget
