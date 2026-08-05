/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.Polar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Algebraic foundations of the planar Delaunay generating function

For negative Kepler energy `-1 / (2 * I₁²)` and angular momentum `I₂`, the radial
Hamilton–Jacobi equation has two turning radii. This file verifies their sum, product, and the
factorization of the squared radial momentum. These identities underlie the square root integrated
in the Delaunay generating function.
-/

namespace LeanPool.PoincareThreeBody

/-- The periapsis radius associated with Delaunay actions. -/
noncomputable def periapsisRadius (firstAction secondAction : ℝ) : ℝ :=
  firstAction * (firstAction - Real.sqrt (firstAction ^ 2 - secondAction ^ 2))

/-- The apoapsis radius associated with Delaunay actions. -/
noncomputable def apoapsisRadius (firstAction secondAction : ℝ) : ℝ :=
  firstAction * (firstAction + Real.sqrt (firstAction ^ 2 - secondAction ^ 2))

lemma periapsis_add_apoapsis (firstAction secondAction : ℝ) :
    periapsisRadius firstAction secondAction + apoapsisRadius firstAction secondAction =
      2 * firstAction ^ 2 := by
  unfold periapsisRadius apoapsisRadius
  ring

lemma periapsis_mul_apoapsis {firstAction secondAction : ℝ}
    (hactions : secondAction ^ 2 ≤ firstAction ^ 2) :
    periapsisRadius firstAction secondAction * apoapsisRadius firstAction secondAction =
      firstAction ^ 2 * secondAction ^ 2 := by
  have hsqrt : (Real.sqrt (firstAction ^ 2 - secondAction ^ 2)) ^ 2 =
      firstAction ^ 2 - secondAction ^ 2 := by
    rw [Real.sq_sqrt]
    linarith
  unfold periapsisRadius apoapsisRadius
  nlinarith

/-- The radial momentum radicand factors through the two Kepler turning radii. -/
theorem delaunayRadialMomentumSq_factorization {radius firstAction secondAction : ℝ}
    (hradius : radius ≠ 0) (hfirstAction : firstAction ≠ 0)
    (hactions : secondAction ^ 2 ≤ firstAction ^ 2) :
    delaunayRadialMomentumSq radius firstAction secondAction =
      ((apoapsisRadius firstAction secondAction - radius) *
          (radius - periapsisRadius firstAction secondAction)) /
        (firstAction ^ 2 * radius ^ 2) := by
  have hsum := periapsis_add_apoapsis firstAction secondAction
  have hproduct := periapsis_mul_apoapsis hactions
  unfold delaunayRadialMomentumSq
  field_simp [hradius, hfirstAction]
  rw [← hsum, ← hproduct]
  ring

lemma periapsis_le_apoapsis {firstAction secondAction : ℝ}
    (hfirstAction : 0 ≤ firstAction) :
    periapsisRadius firstAction secondAction ≤
      apoapsisRadius firstAction secondAction := by
  unfold periapsisRadius apoapsisRadius
  have hsqrt : 0 ≤ Real.sqrt (firstAction ^ 2 - secondAction ^ 2) :=
    Real.sqrt_nonneg _
  have hproduct : 0 ≤
      firstAction * Real.sqrt (firstAction ^ 2 - secondAction ^ 2) :=
    mul_nonneg hfirstAction hsqrt
  linarith

end LeanPool.PoincareThreeBody
