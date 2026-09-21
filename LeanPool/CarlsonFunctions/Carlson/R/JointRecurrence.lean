/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.SlitRecurrence
public import LeanPool.CarlsonFunctions.Carlson.R.Recurrence.JointCoefficients

/-!
# Polynomial coefficients in parameters and nodes

The coefficients in Carlson's homogeneity recurrence are represented by genuine
multivariate polynomials, not by witnesses chosen for fixed parameters. The
coordinates are `none` for `a`, `some (inl i)` for `bᵢ`, and `some (inr i)` for `zᵢ`.
The R-functions have exponents `-a-n`. Formal differentiation in `none` therefore
provides the correction coefficients needed for the corresponding L-recurrence.

This constructs a universal homogeneity recurrence. It does not yet construct
universal coefficient witnesses for arbitrary lists of associated shifts.
-/

open Complex Set
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The same polynomial family gives the R-relation for every parameter and slit node. -/
theorem sum_carlsonAssociatedRecurrenceJointPolynomial_mul_rSlit
    (a : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    ∑ n ∈ Finset.range (Fintype.card ι + 1),
      (carlsonAssociatedRecurrenceJointPolynomial n).eval (carlsonRecurrencePoint a b z) *
        regCarlsonRSlit (-a - n) b z = 0 := by
  simp_rw [eval_carlsonAssociatedRecurrenceJointPolynomial]
  cases isEmpty_or_nonempty ι with
  | inl h => simp [regCarlsonRSlit_eq_zero_of_isEmpty _ b hz]
  | inr h => exact sum_carlsonAssociatedRecurrencePolynomial_mul_rSlit a b hz

end DirichletTransform
