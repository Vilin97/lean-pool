/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.NonlinearEnergyConstants
import LeanPool.NavierStokesAndEuler.Euler.GevreyGrowthCoefficient

/-! Separate the full background norm from the drift norm in the radius-loss term. -/

@[expose] public section


noncomputable section

namespace EulerDriftEnergyConstants

open EulerGevreyCorrectionBound EulerGevreyMetricEstimate EulerGevreyGrowthCoefficient
  EulerNonlinearEnergyConstants

variable (period : ℝ) [Fact (0 < period)]

/-- The full velocity enters the zero-order coefficient; only the drift enters the loss term. -/
def forcingPolynomial (B M Z0 B0 B1 A0 A2 residual c Rc ρ X Y : ℝ) : ℝ :=
  sourceConstant B M * residual + linearCoefficient period B M Z0 B1 A0 A2 c * X +
    quadraticCoefficient period B M A2 c * X ^ 2 +
    lossCoefficient period M c * (ρ⁻¹ + Rc) * (B0 + X) * Y

/-- The existing polynomial growth constant absorbs the sharp drift forcing without
replacing its small drift envelope by the full background envelope. -/
theorem actual_scalar_bound (g0 g1 k B M Z0 B0 B1 A0 A2 c Rc ρ residual X Y b : ℝ)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hk : 0 ≤ k) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hZ0 : 0 ≤ Z0) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hA0 : 0 ≤ A0)
    (hA2 : 0 ≤ A2) (hc : 0 < c) (hRc : 0 ≤ Rc) (hρ : 0 < ρ)
    (hr : 0 ≤ residual) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    let C := energyConstant period g0 g1 k B M Z0 B1 A0 A2 c
    (g0 + g1 * X) * X + b * Y +
        k * forcingPolynomial period B M Z0 B0 B1 A0 A2 residual c Rc ρ X Y ≤
      C * (X + X ^ 2 + residual) + (b + C * (ρ⁻¹ + Rc) * (B0 + X)) * Y := by
  obtain ⟨hl, hq, hd⟩ := coefficients_nonneg period B M Z0 B1 A0 A2 c
    hB hM hZ0 hB1 hA0 hA2 hc
  have hs := sourceConstant_nonneg hB hM
  have h := absorb_scalar_coefficients g0 g1 (k * sourceConstant B M)
    (k * linearCoefficient period B M Z0 B1 A0 A2 c)
    (k * quadraticCoefficient period B M A2 c) (k * lossCoefficient period M c)
    residual X Y B0 (ρ⁻¹ + Rc) (energyConstant period g0 g1 k B M Z0 B1 A0 A2 c)
    hg0 hg1 (mul_nonneg hk hs) (mul_nonneg hk hl) (mul_nonneg hk hq)
    (mul_nonneg hk hd) hr hX hY hB0 (add_nonneg (inv_nonneg.mpr hρ.le) hRc)
    (le_refl _) b
  calc
    _ = (g0 + g1 * X) * X + b * Y +
        ((k * sourceConstant B M) * residual +
        (k * linearCoefficient period B M Z0 B1 A0 A2 c) * X +
        (k * quadraticCoefficient period B M A2 c) * X ^ 2 +
        (k * lossCoefficient period M c) * (ρ⁻¹ + Rc) * (B0 + X) * Y) := by
      unfold forcingPolynomial
      ring
    _ ≤ _ := h

end EulerDriftEnergyConstants
