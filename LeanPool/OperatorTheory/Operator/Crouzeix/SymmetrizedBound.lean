/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.DoubleLayerBound

/-!
# Assembly of the symmetrized double-layer bound

This file packages the last norm-estimate step of L4.2d.  Once an operator
sum `F + G†` has been represented as the `(2 * pi)⁻¹`-normalized integral of
a scalar weight against a positive operator kernel of total mass
`4 * pi • 1`, positive-kernel contractivity gives the sharp estimate
`norm (F + G†) ≤ 2 * M`.

All analytic and geometric inputs remain visible in the theorem statement:
the representation, interval integrability, positivity, mass normalization,
and scalar boundary bound.  The theorem therefore composes directly with a
Cauchy representation of `p(A) + G†` without asserting that missing identity
itself.

## Main declaration

* `norm_add_star_le_two_mul_of_doubleLayer_representation` -- the final
  factor-two norm estimate from a normalized positive double-layer
  representation.
-/

open MeasureTheory
open scoped InnerProductSpace Interval Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- An explicit normalized positive double-layer representation of `F + G†`
implies the sharp bound `‖F + G†‖ ≤ 2 * M`. -/
theorem norm_add_star_le_two_mul_of_doubleLayer_representation
    (F G : E →L[ℂ] E) {K : ℝ → E →L[ℂ] E} {f : ℝ → ℂ} {M : ℝ}
    (hrepresentation : F + star G =
      (2 * Real.pi)⁻¹ • (∫ t in (0 : ℝ)..(2 * Real.pi), f t • K t))
    (hK : IntervalIntegrable K volume 0 (2 * Real.pi))
    (hfK : IntervalIntegrable (fun t ↦ f t • K t) volume 0 (2 * Real.pi))
    (hpos : ∀ t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), 0 ≤ K t)
    (hnorm : ∫ t in (0 : ℝ)..(2 * Real.pi), K t =
      (4 * Real.pi) • (1 : E →L[ℂ] E))
    (hM : 0 ≤ M) (hf : ∀ t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), ‖f t‖ ≤ M) :
    ‖F + star G‖ ≤ 2 * M := by
  rw [hrepresentation]
  exact norm_inv_two_pi_smul_intervalIntegral_le_two_mul_of_nonneg
    hK hfK hpos hnorm hM hf

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
