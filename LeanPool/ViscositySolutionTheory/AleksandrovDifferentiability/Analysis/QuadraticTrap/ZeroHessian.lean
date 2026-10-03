/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.QuadraticTrap.RealScalar

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Zero Hessian estimate constructors

Convenience constructors for second-order differentiability with zero Hessian.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If the affine remainder is little-o of `‖z‖ ^ 2`, then the second-order expansion holds with
zero Hessian. -/
theorem hasSecondOrderExpansionAt_zero_of_affineRemainder_isLittleO
    {u : E → ℝ} {x p : E}
    (h : (fun z : E => affineRemainder u x p (x + z)) =o[nhds 0]
      (fun z : E => ‖z‖ ^ 2)) :
    HasSecondOrderExpansionAt u x p (0 : E →L[ℝ] E) := by
  refine hasSecondOrderExpansionAt_of_affineRemainder_isLittleO ?_
  simpa using h

/-- The zero continuous linear operator is symmetric. -/
theorem isSymmetricOperator_zero : IsSymmetricOperator (0 : E →L[ℝ] E) := by
  rw [IsSymmetricOperator]
  exact LinearMap.IsSymmetric.zero

/-- If the affine remainder is little-o of `‖z‖ ^ 2`, then `u` is second-order differentiable at
`x` with zero Hessian candidate. -/
theorem secondOrderDifferentiableAt_of_affineRemainder_isLittleO
    {u : E → ℝ} {x p : E}
    (h : (fun z : E => affineRemainder u x p (x + z)) =o[nhds 0]
      (fun z : E => ‖z‖ ^ 2)) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_hasSecondOrderExpansionAt isSymmetricOperator_zero
    (hasSecondOrderExpansionAt_zero_of_affineRemainder_isLittleO h)

/-- A neighborhood family of quadratic norm bounds is exactly the estimate needed to make the
affine remainder little-o of `‖z‖ ^ 2`. This is a Lean-friendly interface for later density and
blow-up arguments, which often produce one `ε`-quadratic bound at a time. -/
theorem affineRemainder_isLittleO_of_eventually_norm_le_mul
    {u : E → ℝ} {x p : E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0, ‖affineRemainder u x p (x + z)‖ ≤ ε * ‖z‖ ^ 2) :
    (fun z : E => affineRemainder u x p (x + z)) =o[nhds 0]
      (fun z : E => ‖z‖ ^ 2) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [h c hc] with z hz
  have hsq_norm : ‖(‖z‖ ^ 2 : ℝ)‖ = ‖z‖ ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
  simpa [hsq_norm] using hz

/-- A family of local quadratic norm bounds gives a zero-Hessian second-order expansion. -/
theorem hasSecondOrderExpansionAt_zero_of_eventually_norm_affineRemainder_le_mul
    {u : E → ℝ} {x p : E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0, ‖affineRemainder u x p (x + z)‖ ≤ ε * ‖z‖ ^ 2) :
    HasSecondOrderExpansionAt u x p (0 : E →L[ℝ] E) :=
  hasSecondOrderExpansionAt_zero_of_affineRemainder_isLittleO
    (affineRemainder_isLittleO_of_eventually_norm_le_mul h)

/-- A family of local quadratic norm bounds gives second-order differentiability with zero
Hessian candidate. -/
theorem secondOrderDifferentiableAt_of_eventually_norm_affineRemainder_le_mul
    {u : E → ℝ} {x p : E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhds 0, ‖affineRemainder u x p (x + z)‖ ≤ ε * ‖z‖ ^ 2) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_affineRemainder_isLittleO
    (affineRemainder_isLittleO_of_eventually_norm_le_mul h)

/-- A punctured-neighborhood normalized quotient bound is another convenient way to produce the
little-o affine-remainder estimate. The value at the base point is handled separately by
`affineRemainder_self`. -/
theorem affineRemainder_isLittleO_of_eventually_norm_div_norm_sq_le
    {u : E → ℝ} {x p : E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
        ‖affineRemainder u x p (x + z)‖ / ‖z‖ ^ 2 ≤ ε) :
    (fun z : E => affineRemainder u x p (x + z)) =o[nhds 0]
      (fun z : E => ‖z‖ ^ 2) := by
  apply affineRemainder_isLittleO_of_eventually_norm_le_mul
  intro ε hε
  have hpunctured :=
    (eventually_nhdsWithin_iff.mp (h ε hε) :
      ∀ᶠ z in nhds (0 : E), z ∈ ({0}ᶜ : Set E) →
        ‖affineRemainder u x p (x + z)‖ / ‖z‖ ^ 2 ≤ ε)
  filter_upwards [hpunctured] with z hz
  by_cases hz0 : z = 0
  · subst z
    simp
  · have hquot : ‖affineRemainder u x p (x + z)‖ / ‖z‖ ^ 2 ≤ ε := by
      exact hz (by simpa using hz0)
    have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz0)
    exact (div_le_iff₀ hden).mp hquot

/-- A punctured-neighborhood normalized quotient bound gives a zero-Hessian second-order
expansion. -/
theorem hasSecondOrderExpansionAt_zero_of_eventually_norm_div_norm_sq_le
    {u : E → ℝ} {x p : E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
        ‖affineRemainder u x p (x + z)‖ / ‖z‖ ^ 2 ≤ ε) :
    HasSecondOrderExpansionAt u x p (0 : E →L[ℝ] E) :=
  hasSecondOrderExpansionAt_zero_of_affineRemainder_isLittleO
    (affineRemainder_isLittleO_of_eventually_norm_div_norm_sq_le h)

/-- A punctured-neighborhood normalized quotient bound gives second-order differentiability with
zero Hessian candidate. -/
theorem secondOrderDifferentiableAt_of_eventually_norm_div_norm_sq_le
    {u : E → ℝ} {x p : E}
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in nhdsWithin (0 : E) {z : E | z ≠ 0},
        ‖affineRemainder u x p (x + z)‖ / ‖z‖ ^ 2 ≤ ε) :
    SecondOrderDifferentiableAt u x :=
  secondOrderDifferentiableAt_of_affineRemainder_isLittleO
    (affineRemainder_isLittleO_of_eventually_norm_div_norm_sq_le h)


end AleksandrovDifferentiability
