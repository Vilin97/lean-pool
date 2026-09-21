/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.DoubleLayerIntegral
import LeanPool.OperatorTheory.Operator.Crouzeix.PositiveKernelBound

/-!
# The normalized positive-kernel bound for the double layer

The double-layer kernel in the Crouzeix--Palencia argument has total mass
`4 * pi • 1`, while the contour representation of the symmetrized operator
has the real normalization factor `(2 * pi)⁻¹`.  Contractivity of integration
against a positive operator kernel therefore gives the sharp factor `2`.

This file records precisely that scaling step.  The positivity,
integrability, and mass identity remain explicit inputs, so the theorem can
be applied after the geometric and Cauchy-integral parts of the argument have
identified the concrete double-layer kernel.

## Main declaration

* `norm_inv_two_pi_smul_intervalIntegral_le_two_mul_of_nonneg` -- a positive
  kernel of mass `4 * pi • 1`, normalized by `(2 * pi)⁻¹`, integrates every
  scalar weight bounded by `M` to an operator of norm at most `2 * M`.
-/

open MeasureTheory
open scoped InnerProductSpace Interval Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The sharp factor-two scaling of positive-kernel contractivity for a
double-layer kernel with total mass `4 * pi • 1`. -/
theorem norm_inv_two_pi_smul_intervalIntegral_le_two_mul_of_nonneg
    {K : ℝ → E →L[ℂ] E} {f : ℝ → ℂ} {M : ℝ}
    (hK : IntervalIntegrable K volume 0 (2 * Real.pi))
    (hfK : IntervalIntegrable (fun t ↦ f t • K t) volume 0 (2 * Real.pi))
    (hpos : ∀ t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), 0 ≤ K t)
    (hnorm : ∫ t in (0 : ℝ)..(2 * Real.pi), K t =
      (4 * Real.pi) • (1 : E →L[ℂ] E))
    (hM : 0 ≤ M) (hf : ∀ t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), ‖f t‖ ≤ M) :
    ‖(2 * Real.pi)⁻¹ • (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t)‖ ≤ 2 * M := by
  have hcontract : ‖∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t‖ ≤
      (4 * Real.pi) * M :=
    norm_intervalIntegral_smul_le_of_nonneg Real.two_pi_pos.le hK hfK hpos hnorm
      (by positivity) hM hf
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr Real.two_pi_pos)]
  calc
    (2 * Real.pi)⁻¹ * ‖∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t‖ ≤
        (2 * Real.pi)⁻¹ * ((4 * Real.pi) * M) :=
      mul_le_mul_of_nonneg_left hcontract (inv_nonneg.mpr Real.two_pi_pos.le)
    _ = 2 * M := by
      field_simp [Real.pi_ne_zero]
      ring

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
