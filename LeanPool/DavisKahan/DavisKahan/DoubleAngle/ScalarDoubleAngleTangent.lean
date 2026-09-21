/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The scalar double-angle tangent

`tan 2θ = 2 tan θ / (1 - tan² θ)`, and its branch-free modulus
`|tan 2θ| = 2 tan θ / |1 - tan² θ|`, as functions of a real number.

Nothing here is about operators, let alone finite-dimensional ones.  Both
functions lived in `TanTwoThetaKyFan.lean` and `TanTwoThetaBranchFree.lean`,
which do assume a finite-dimensional ambient space, and so ended up in
`TauCeti.DavisKahan.FiniteDimensional` -- with the visible consequence that
dimension-free `tan 2Θ` files had to open the finite-dimensional namespace in
order to name a quotient of two reals.  They belong to the `tan 2Θ` vocabulary,
and the finite-dimensional theorems consume them from here.
-/

namespace TauCeti
namespace DavisKahan.TanTwoTheta

/-- The double-angle tangent of a single-angle tangent value:
`tan 2θ = 2 tan θ / (1 - tan² θ)`. -/
noncomputable def doubleAngleTangent (t : ℝ) : ℝ := 2 * t / (1 - t ^ 2)

/-- The double-angle tangent vanishes at zero. -/
@[simp] theorem doubleAngleTangent_zero : doubleAngleTangent 0 = 0 := by
  simp [doubleAngleTangent]

/-- The double-angle tangent is nonnegative on the admissible range. -/
theorem doubleAngleTangent_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    0 ≤ doubleAngleTangent t := by
  have h1t : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  exact div_nonneg (by linarith) h1t.le

/-- **The branch-free double-angle tangent magnitude**
`|tan 2θ| = 2 tan θ / |1 - tan² θ|`.

Unlike `doubleAngleTangent` this is meaningful on both sides of `π/4`: it is
the modulus of `tan 2θ`, which is what a unitarily invariant norm of `tan 2Θ`
reads off.  In terms of `s = sin θ` it is `2 s √(1 - s²) / |1 - 2 s²|`. -/
noncomputable def absDoubleAngleTangent (t : ℝ) : ℝ := 2 * t / |1 - t ^ 2|

/-- The branch-free double-angle tangent vanishes at zero. -/
@[simp] theorem absDoubleAngleTangent_zero : absDoubleAngleTangent 0 = 0 := by
  simp [absDoubleAngleTangent]

/-- The branch-free double-angle tangent is nonnegative wherever the single
angle is. -/
theorem absDoubleAngleTangent_nonneg {t : ℝ} (h0 : 0 ≤ t) :
    0 ≤ absDoubleAngleTangent t :=
  div_nonneg (by linarith) (abs_nonneg _)

/-- On the acute quarter the branch-free magnitude is the selected-branch
double-angle tangent, so a branch-free theorem genuinely extends the
selected-branch one. -/
theorem absDoubleAngleTangent_eq_doubleAngleTangent {t : ℝ} (h1 : t < 1)
    (h0 : 0 ≤ t) : absDoubleAngleTangent t = doubleAngleTangent t := by
  have : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  rw [absDoubleAngleTangent, doubleAngleTangent, abs_of_pos this]

end DavisKahan.TanTwoTheta
end TauCeti
