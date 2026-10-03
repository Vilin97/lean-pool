/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Assembly.GiantOrbit
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.ParabolicEscape

/-!
# Nonparabolic coordinates outside the endgame component

At the exponent used by the explicit route, a normalized parabolic trace has
rotation order at least `p ^ (5 / 6)`. Consequently, once every point at that
threshold is connected to a fixed base point, every point outside the base
component has nonparabolic coordinates.
-/

@[expose] public section

namespace BGS.Markoff

/-- A point outside a component containing every endgame-large point has
nonparabolic first and second coordinates. -/
theorem first_two_nonparabolic_of_not_sameComponent_of_endgame_large_connected
    {p : ℕ} [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpTwo : p ≠ 2)
    (base z : NormalizedMarkoffSurface (ZMod p))
    (hlarge : ∀ y : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ maximalCoordinateRotationOrder y.1 →
        SameNormalizedComponent base y)
    (hnot : ¬ SameNormalizedComponent base z) :
    z.1.u1 ^ 2 ≠ 4 ∧ z.1.u2 ^ 2 ≠ 4 := by
  constructor
  · intro hparabolic
    apply hnot
    apply hlarge z
    have hcases :=
      (normalizedTrace_sq_eq_four_iff_parabolic p z.1.u1).mp hparabolic
    have hthreshold :=
      endgamePowerThreshold_le_rotationOrder_of_parabolicTrace
        p hpTwo (1 / 3 : ℝ) (by norm_num) z.1.u1 hcases
    calc
      (p : ℝ) ^ (5 / 6 : ℝ) =
          (p : ℝ) ^ ((1 : ℝ) / 2 + 1 / 3) := by norm_num
      _ ≤ (rotationOrder z.1.u1 : ℝ) := hthreshold
      _ ≤ maximalCoordinateRotationOrder z.1 := by
        exact_mod_cast
          rotationOrder_first_le_maximalCoordinateRotationOrder z.1
  · intro hparabolic
    apply hnot
    apply hlarge z
    have hcases :=
      (normalizedTrace_sq_eq_four_iff_parabolic p z.1.u2).mp hparabolic
    have hthreshold :=
      endgamePowerThreshold_le_rotationOrder_of_parabolicTrace
        p hpTwo (1 / 3 : ℝ) (by norm_num) z.1.u2 hcases
    calc
      (p : ℝ) ^ (5 / 6 : ℝ) =
          (p : ℝ) ^ ((1 : ℝ) / 2 + 1 / 3) := by norm_num
      _ ≤ (rotationOrder z.1.u2 : ℝ) := hthreshold
      _ ≤ maximalCoordinateRotationOrder z.1 := by
        exact_mod_cast
          rotationOrder_second_le_maximalCoordinateRotationOrder z.1

end BGS.Markoff
