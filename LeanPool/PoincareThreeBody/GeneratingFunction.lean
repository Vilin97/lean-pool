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

/-- Angular action of an elliptic Kepler orbit with first action `I₁` and eccentricity `e`. -/
noncomputable def angularActionFromEccentricity (firstAction eccentricity : ℝ) : ℝ :=
  firstAction * Real.sqrt (1 - eccentricity ^ 2)

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

lemma angularActionFromEccentricity_pos {firstAction eccentricity : ℝ}
    (hfirstAction : 0 < firstAction) (heccentricity : 0 < eccentricity)
    (heccentricityOne : eccentricity < 1) :
    0 < angularActionFromEccentricity firstAction eccentricity := by
  unfold angularActionFromEccentricity
  exact mul_pos hfirstAction (Real.sqrt_pos.mpr (by nlinarith))

lemma angularActionFromEccentricity_lt_firstAction {firstAction eccentricity : ℝ}
    (hfirstAction : 0 < firstAction) (heccentricity : 0 < eccentricity) :
    angularActionFromEccentricity firstAction eccentricity < firstAction := by
  have hsqrt : Real.sqrt (1 - eccentricity ^ 2) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    nlinarith
  unfold angularActionFromEccentricity
  nlinarith [Real.sqrt_nonneg (1 - eccentricity ^ 2)]

lemma delaunayDiscriminant_angularActionFromEccentricity
    {firstAction eccentricity : ℝ} (heccentricity : 0 ≤ eccentricity)
    (heccentricityOne : eccentricity ≤ 1) :
    firstAction ^ 2 - (angularActionFromEccentricity firstAction eccentricity) ^ 2 =
      (firstAction * eccentricity) ^ 2 := by
  have hsqrt : (Real.sqrt (1 - eccentricity ^ 2)) ^ 2 = 1 - eccentricity ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  unfold angularActionFromEccentricity
  nlinarith

lemma sqrt_delaunayDiscriminant_angularActionFromEccentricity
    {firstAction eccentricity : ℝ} (hfirstAction : 0 ≤ firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity ≤ 1) :
    Real.sqrt
        (firstAction ^ 2 - (angularActionFromEccentricity firstAction eccentricity) ^ 2) =
      firstAction * eccentricity := by
  rw [delaunayDiscriminant_angularActionFromEccentricity heccentricity heccentricityOne,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hfirstAction heccentricity)]

lemma periapsisRadius_angularActionFromEccentricity
    {firstAction eccentricity : ℝ} (hfirstAction : 0 ≤ firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity ≤ 1) :
    periapsisRadius firstAction (angularActionFromEccentricity firstAction eccentricity) =
      firstAction ^ 2 * (1 - eccentricity) := by
  unfold periapsisRadius
  rw [sqrt_delaunayDiscriminant_angularActionFromEccentricity hfirstAction heccentricity
    heccentricityOne]
  ring

lemma apoapsisRadius_angularActionFromEccentricity
    {firstAction eccentricity : ℝ} (hfirstAction : 0 ≤ firstAction)
    (heccentricity : 0 ≤ eccentricity) (heccentricityOne : eccentricity ≤ 1) :
    apoapsisRadius firstAction (angularActionFromEccentricity firstAction eccentricity) =
      firstAction ^ 2 * (1 + eccentricity) := by
  unfold apoapsisRadius
  rw [sqrt_delaunayDiscriminant_angularActionFromEccentricity hfirstAction heccentricity
    heccentricityOne]
  ring

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

lemma delaunayAction_discriminant_pos {firstAction secondAction : ℝ}
    (hsecondAction : 0 < secondAction) (hactions : secondAction < firstAction) :
    0 < firstAction ^ 2 - secondAction ^ 2 := by
  nlinarith

lemma sqrt_delaunayAction_discriminant_lt {firstAction secondAction : ℝ}
    (hsecondAction : 0 < secondAction) (hactions : secondAction < firstAction) :
    Real.sqrt (firstAction ^ 2 - secondAction ^ 2) < firstAction := by
  rw [Real.sqrt_lt' (lt_trans hsecondAction hactions)]
  nlinarith

lemma periapsisRadius_pos {firstAction secondAction : ℝ}
    (hsecondAction : 0 < secondAction) (hactions : secondAction < firstAction) :
    0 < periapsisRadius firstAction secondAction := by
  unfold periapsisRadius
  exact mul_pos (lt_trans hsecondAction hactions)
    (sub_pos.mpr (sqrt_delaunayAction_discriminant_lt hsecondAction hactions))

lemma apoapsisRadius_pos {firstAction secondAction : ℝ}
    (hsecondAction : 0 < secondAction) (hactions : secondAction < firstAction) :
    0 < apoapsisRadius firstAction secondAction := by
  unfold apoapsisRadius
  exact mul_pos (lt_trans hsecondAction hactions)
    (add_pos_of_pos_of_nonneg (lt_trans hsecondAction hactions) (Real.sqrt_nonneg _))

lemma periapsisRadius_lt_apoapsisRadius {firstAction secondAction : ℝ}
    (hsecondAction : 0 < secondAction) (hactions : secondAction < firstAction) :
    periapsisRadius firstAction secondAction <
      apoapsisRadius firstAction secondAction := by
  unfold periapsisRadius apoapsisRadius
  have hfirstAction : 0 < firstAction := lt_trans hsecondAction hactions
  have hsqrt : 0 < Real.sqrt (firstAction ^ 2 - secondAction ^ 2) :=
    Real.sqrt_pos.mpr (delaunayAction_discriminant_pos hsecondAction hactions)
  nlinarith

/-- Between periapsis and apoapsis, the radial momentum square prescribed by the Delaunay actions
is nonnegative. -/
theorem delaunayRadialMomentumSq_nonneg_of_mem_turningInterval
    {radius firstAction secondAction : ℝ}
    (hsecondAction : 0 < secondAction) (hactions : secondAction < firstAction)
    (hlower : periapsisRadius firstAction secondAction ≤ radius)
    (hupper : radius ≤ apoapsisRadius firstAction secondAction) :
    0 ≤ delaunayRadialMomentumSq radius firstAction secondAction := by
  have hfirstAction : 0 < firstAction := lt_trans hsecondAction hactions
  have hradius : 0 < radius := lt_of_lt_of_le
    (periapsisRadius_pos hsecondAction hactions) hlower
  rw [delaunayRadialMomentumSq_factorization hradius.ne' hfirstAction.ne'
    (by nlinarith [delaunayAction_discriminant_pos hsecondAction hactions])]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hupper) (sub_nonneg.mpr hlower)) (by positivity)

end LeanPool.PoincareThreeBody
