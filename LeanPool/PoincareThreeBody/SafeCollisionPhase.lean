/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.AlignedAverageBlowup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# A phase avoiding every boundary collision

Shifting the aligned orientation by `π/q` puts it halfway between the possible collision phases.
The exclusion is ultimately the parity contradiction `1 + 2ql = 2pk`.
-/

namespace LeanPool.PoincareThreeBody

/-- An orientation halfway between resonant collision phases. -/
noncomputable def resonantSafeOrientation (p q : ℕ) : ℝ :=
  resonantCollisionOrientation p q + Real.pi / q

theorem resonantCollisionEccentricity_apoapsis_identity
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    resonantSemimajorAxis p q * (1 + resonantCollisionEccentricity p q) = 1 := by
  have haxisPositive := resonantSemimajorAxis_pos hp hq
  unfold resonantCollisionEccentricity
  field_simp [haxisPositive.ne']
  ring

/-- The safe orientation never meets the unit primary, even at the limiting collision
eccentricity. -/
theorem safeOrientation_primaryDistance_ne_zero_at_collisionBoundary
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (haxisHalf : 1 / 2 < resonantSemimajorAxis p q)
    (haxisOne : resonantSemimajorAxis p q < 1) (time : ℝ) :
    (orientedResonantEllipsePosition p q (resonantCollisionEccentricity p q)
          (resonantSafeOrientation p q) time 0 - 1) ^ 2 +
        (orientedResonantEllipsePosition p q (resonantCollisionEccentricity p q)
          (resonantSafeOrientation p q) time 1) ^ 2 ≠ 0 := by
  let eccentricity := resonantCollisionEccentricity p q
  let anomaly := resonantEccentricAnomaly p q eccentricity time
  let position := orientedResonantEllipsePosition p q eccentricity
    (resonantSafeOrientation p q) time
  have heccentricity : 0 ≤ eccentricity :=
    (resonantCollisionEccentricity_pos hp hq haxisOne).le
  have heccentricityOne : eccentricity < 1 :=
    resonantCollisionEccentricity_lt_one hp hq haxisHalf
  intro hcollision
  have hpositionZero : position 0 = 1 := by
    dsimp [position, eccentricity] at hcollision ⊢
    nlinarith [sq_nonneg
      (orientedResonantEllipsePosition p q (resonantCollisionEccentricity p q)
        (resonantSafeOrientation p q) time 1)]
  have hpositionOne : position 1 = 0 := by
    dsimp [position, eccentricity] at hcollision ⊢
    nlinarith [sq_nonneg
      (orientedResonantEllipsePosition p q (resonantCollisionEccentricity p q)
        (resonantSafeOrientation p q) time 0 - 1)]
  have hradiusSq :
      (eccentricRadius (resonantFirstAction p q) eccentricity anomaly) ^ 2 = 1 := by
    have hnorm := orientedResonantEllipsePosition_sq
      (p := p) (q := q) (orientation := resonantSafeOrientation p q) (time := time)
      heccentricity heccentricityOne.le
    dsimp [position, anomaly, eccentricity] at hpositionZero hpositionOne hnorm ⊢
    rw [hpositionZero, hpositionOne] at hnorm
    norm_num at hnorm
    exact hnorm.symm
  have hradiusPositive :
      0 < eccentricRadius (resonantFirstAction p q) eccentricity anomaly :=
    eccentricRadius_pos (resonantFirstAction_pos hp hq).ne'
      heccentricity heccentricityOne
  have hradius :
      eccentricRadius (resonantFirstAction p q) eccentricity anomaly = 1 := by
    nlinarith
  have hcos : Real.cos anomaly = -1 := by
    have haxisPositive := resonantSemimajorAxis_pos hp hq
    dsimp [anomaly, eccentricity] at hradius ⊢
    unfold eccentricRadius resonantCollisionEccentricity at hradius
    rw [← resonantSemimajorAxis] at hradius
    field_simp [haxisPositive.ne'] at hradius
    have heccentricityForm :
        (1 - resonantSemimajorAxis p q) / resonantSemimajorAxis p q =
          resonantCollisionEccentricity p q := by
      unfold resonantCollisionEccentricity
      field_simp [haxisPositive.ne']
    rw [heccentricityForm] at hradius
    change resonantSemimajorAxis p q -
      (1 - resonantSemimajorAxis p q) * Real.cos anomaly = 1 at hradius
    nlinarith [haxisOne]
  have hsin : Real.sin anomaly = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq anomaly]
  rcases Real.cos_eq_neg_one_iff.mp hcos with ⟨turns, hturns⟩
  have hmean : resonantMeanAnomaly p q time = anomaly := by
    have hkepler := eccentricMeanAnomaly_eccentricAnomaly heccentricity
      (resonantMeanAnomaly p q time)
    change eccentricMeanAnomaly eccentricity anomaly = resonantMeanAnomaly p q time at hkepler
    unfold eccentricMeanAnomaly at hkepler
    rw [hsin, mul_zero, sub_zero] at hkepler
    exact hkepler.symm
  have hboundary := resonantCollisionEccentricity_apoapsis_identity hp hq
  have hpositionFormula :
      position 0 = -Real.cos (time - resonantSafeOrientation p q) := by
    dsimp [position]
    unfold orientedResonantEllipsePosition positionInRotatingFrame
      inertialEllipsePosition
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [show resonantEccentricAnomaly p q eccentricity time = anomaly by rfl,
      hcos, hsin]
    simp only [mul_zero, add_zero]
    have hscale : resonantFirstAction p q ^ 2 * (1 + eccentricity) = 1 := by
      simpa [resonantSemimajorAxis] using hboundary
    calc
      Real.cos (time - resonantSafeOrientation p q) *
          (resonantFirstAction p q ^ 2 * (-1 - eccentricity)) =
          -Real.cos (time - resonantSafeOrientation p q) *
            (resonantFirstAction p q ^ 2 * (1 + eccentricity)) := by ring
      _ = -Real.cos (time - resonantSafeOrientation p q) := by rw [hscale]; ring
  have hrotationCos : Real.cos (time - resonantSafeOrientation p q) = -1 := by
    rw [hpositionFormula] at hpositionZero
    linarith
  rcases Real.cos_eq_neg_one_iff.mp hrotationCos with ⟨rotations, hrotations⟩
  have hpReal : (p : ℝ) ≠ 0 := by positivity
  have hqReal : (q : ℝ) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hmeanEquation :
      (q : ℝ) / (p : ℝ) * time =
        Real.pi + (turns : ℝ) * (2 * Real.pi) := by
    calc
      (q : ℝ) / (p : ℝ) * time = resonantMeanAnomaly p q time := by
        rfl
      _ = anomaly := hmean
      _ = Real.pi + (turns : ℝ) * (2 * Real.pi) := hturns.symm
  have hrotationEquation :
      time - (resonantApoapsisTime p q - Real.pi + Real.pi / q) =
        Real.pi + (rotations : ℝ) * (2 * Real.pi) := by
    calc
      time - (resonantApoapsisTime p q - Real.pi + Real.pi / q) =
          time - resonantSafeOrientation p q := by rfl
      _ = Real.pi + (rotations : ℝ) * (2 * Real.pi) := hrotations.symm
  have hparityReal :
      (1 : ℝ) + 2 * (q : ℝ) * (rotations : ℝ) =
        2 * (p : ℝ) * (turns : ℝ) := by
    unfold resonantApoapsisTime at hrotationEquation
    field_simp [hpReal, hqReal] at hmeanEquation hrotationEquation
    have hparityPi : Real.pi *
        ((1 : ℝ) + 2 * (q : ℝ) * (rotations : ℝ) -
          2 * (p : ℝ) * (turns : ℝ)) = 0 := by
      linear_combination hmeanEquation - hrotationEquation
    have hparityZero :
        (1 : ℝ) + 2 * (q : ℝ) * (rotations : ℝ) -
          2 * (p : ℝ) * (turns : ℝ) = 0 :=
      (mul_eq_zero.mp hparityPi).resolve_left hpi
    linarith
  have hparityInt :
      (1 : ℤ) + 2 * (q : ℤ) * rotations = 2 * (p : ℤ) * turns := by
    exact_mod_cast hparityReal
  have hmod := congrArg (fun value : ℤ ↦ value % 2) hparityInt
  norm_num [Int.add_emod, Int.mul_emod] at hmod

end LeanPool.PoincareThreeBody
