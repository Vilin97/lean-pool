/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball

/-!
# Volume scaling for the interior harmonic gradient display

The interior harmonic gradient display of the paper carries the factor
`ρ ^ (-3)` and is integrated over the half ball `B_{ρ/2}(x₀)`.  Its
`L^{5/6}`-type norm against the spatial measure therefore carries the half
ball volume raised to the power `5 / 6`.  This file records the resulting
scale bookkeeping: the product of the `ρ ^ (-3)` weight with
`|B_{ρ/2}(x₀)| ^ (5/6)` is bounded by `ρ ^ (-1/2)`, which is exactly the
factor appearing in display (3.5) of the paper.

The only input is the closed formula for the volume of a Euclidean ball in
three dimensions, `volume_vec3Ball_eq`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter

open scoped BigOperators ENNReal NNReal Topology

open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Core.Step4

/-- The explicit round ball of `CKN.Foundation.Sobolev.Cutoff.Ball` agrees
with the norm ball `vec3Ball` used by the parabolic geometry. -/
private lemma euclideanBall_eq_vec3Ball_scaling {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr, mem_vec3Ball]
  simp only [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

/-- The volume of the half ball `B_{ρ/2}(x₀)`, namely `(ρ/2)³ · (4π/3)`,
written as a single `ENNReal.ofReal`. -/
private lemma volume_euclideanBall_half (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (euclideanBall x₀ (ρ / 2)) =
      ENNReal.ofReal ((ρ / 2) ^ 3 * (Real.pi * 4 / 3)) := by
  have hpos : 0 < ρ / 2 := by linarith only [hρ]
  rw [euclideanBall_eq_vec3Ball_scaling hpos, volume_vec3Ball_eq,
    ← ENNReal.ofReal_pow (le_of_lt hpos), ← ENNReal.ofReal_mul (by positivity)]

/-- The `5/6`-power of the half ball volume, with the spatial dimension
extracted from the power: `((ρ/2)³ · (4π/3)) ^ (5/6) = (ρ/2) ^ (5/2) ·
(4π/3) ^ (5/6)`. -/
private lemma rpow_five_sixths_half_volume {ρ : ℝ} (hρ : 0 < ρ) :
    (((ρ / 2) ^ 3 * (Real.pi * 4 / 3)) ^ (5 / 6 : ℝ)) =
      (ρ / 2) ^ (5 / 2 : ℝ) * (Real.pi * 4 / 3) ^ (5 / 6 : ℝ) := by
  have hcube : ((ρ / 2) ^ 3) ^ (5 / 6 : ℝ) = (ρ / 2) ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (ρ / 2) 3, ← Real.rpow_mul (by positivity)]
    congr 1
    norm_num
  rw [Real.mul_rpow (by positivity) (by positivity), hcube]

/-- The numerical bound `2 ^ (-5/2) · (4π/3) ^ (5/6) ≤ 1` behind display (3.5):
it is the statement that the three-dimensional ball constant `4π/3 ≤ 8 = 2³`
raises to the power `5/6` to at most `2 ^ (5/2)`. -/
private lemma two_rpow_neg_five_halves_mul_pi_rpow_le_one :
    2 ^ (-5 / 2 : ℝ) * (Real.pi * 4 / 3) ^ (5 / 6 : ℝ) ≤ 1 := by
  have hpi : Real.pi * 4 / 3 ≤ (8 : ℝ) := by
    nlinarith only [Real.pi_le_four]
  have h8 : (Real.pi * 4 / 3) ^ (5 / 6 : ℝ) ≤ (8 : ℝ) ^ (5 / 6 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hpi (by norm_num)
  have h8eq : (8 : ℝ) ^ (5 / 6 : ℝ) = 2 ^ (5 / 2 : ℝ) := by
    have hcast : (8 : ℝ) = 2 ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [hcast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    norm_num
  have hbase : (0 : ℝ) < 2 ^ (-5 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (-5 / 2)
  calc 2 ^ (-5 / 2 : ℝ) * (Real.pi * 4 / 3) ^ (5 / 6 : ℝ)
      ≤ 2 ^ (-5 / 2 : ℝ) * 2 ^ (5 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (h8.trans_eq h8eq) hbase.le
    _ = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2) (-5 / 2) (5 / 2)]
        rw [show (-5 / 2 : ℝ) + 5 / 2 = 0 by norm_num, Real.rpow_zero]

/-- The scale identity behind display (3.5): the `ρ ^ (-3)` weight of the
interior harmonic gradient, times the half ball volume `(ρ/2) ^ (5/2)`,
equals `2 ^ (-5/2) · ρ ^ (-1/2)`. -/
private lemma inv_cube_mul_half_rpow {ρ : ℝ} (hρ : 0 < ρ) :
    (ρ ^ 3)⁻¹ * (ρ / 2) ^ (5 / 2 : ℝ) =
      2 ^ (-5 / 2 : ℝ) * ρ ^ (-1 / 2 : ℝ) := by
  have hρ3 : (ρ ^ 3)⁻¹ = ρ ^ (-3 : ℝ) := by
    rw [← Real.rpow_natCast ρ 3, ← Real.rpow_neg (le_of_lt hρ)]
    congr 1
  have hhalf : (ρ / 2) ^ (5 / 2 : ℝ) = 2 ^ (-5 / 2 : ℝ) * ρ ^ (5 / 2 : ℝ) := by
    rw [Real.div_rpow (le_of_lt hρ) (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]
    rw [show ((2 : ℝ) ^ (5 / 2 : ℝ))⁻¹ = (2 : ℝ) ^ (-5 / 2 : ℝ) by
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      norm_num]
    ring
  rw [hρ3, hhalf]
  rw [show ρ ^ (-3 : ℝ) * (2 ^ (-5 / 2 : ℝ) * ρ ^ (5 / 2 : ℝ)) =
      (ρ ^ (-3 : ℝ) * ρ ^ (5 / 2 : ℝ)) * 2 ^ (-5 / 2 : ℝ) by ring]
  rw [← Real.rpow_add hρ (-3) (5 / 2)]
  rw [show (-3 : ℝ) + 5 / 2 = -1 / 2 by norm_num]
  ring

/-- The real-variable form of display (3.5): after extracting the scale
identity from the half ball volume, the remaining factor
`2 ^ (-5/2) · (4π/3) ^ (5/6)` is at most `1`. -/
private lemma real_scaling_bound {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C) :
    C * (ρ ^ 3)⁻¹ * ((ρ / 2) ^ (5 / 2 : ℝ) * (Real.pi * 4 / 3) ^ (5 / 6 : ℝ)) ≤
      C * ρ ^ (-1 / 2 : ℝ) := by
  rw [show C * (ρ ^ 3)⁻¹ *
        ((ρ / 2) ^ (5 / 2 : ℝ) * (Real.pi * 4 / 3) ^ (5 / 6 : ℝ)) =
      C * ((ρ ^ 3)⁻¹ * (ρ / 2) ^ (5 / 2 : ℝ)) *
        (Real.pi * 4 / 3) ^ (5 / 6 : ℝ) by ring]
  rw [inv_cube_mul_half_rpow hρ]
  rw [show C * (2 ^ (-5 / 2 : ℝ) * ρ ^ (-1 / 2 : ℝ)) *
        (Real.pi * 4 / 3) ^ (5 / 6 : ℝ) =
      C * ρ ^ (-1 / 2 : ℝ) *
        (2 ^ (-5 / 2 : ℝ) * (Real.pi * 4 / 3) ^ (5 / 6 : ℝ)) by ring]
  calc C * ρ ^ (-1 / 2 : ℝ) *
        (2 ^ (-5 / 2 : ℝ) * (Real.pi * 4 / 3) ^ (5 / 6 : ℝ))
      ≤ C * ρ ^ (-1 / 2 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left two_rpow_neg_five_halves_mul_pi_rpow_le_one
          (by positivity)
    _ = C * ρ ^ (-1 / 2 : ℝ) := by ring

/-- Display (3.5), volume factor: the interior harmonic gradient display
carries the weight `ρ ^ (-3)` on the half ball `B_{ρ/2}(x₀)`, and its
`5/6`-power against the spatial measure is bounded by the single factor
`ρ ^ (-1/2)` that appears in the display.  Concretely,
`C ρ ^ (-3) · |B_{ρ/2}(x₀)| ^ (5/6) ≤ C ρ ^ (-1/2)` for `ρ > 0` and `C ≥ 0`. -/
theorem halfBall_volume_rpow_five_sixths_mul_inv_cube_le
    (x₀ : Vec3) {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C) :
    ENNReal.ofReal (C * (ρ ^ 3)⁻¹) *
        (volume (euclideanBall x₀ (ρ / 2))) ^ (5 / 6 : ℝ) ≤
      ENNReal.ofReal (C * ρ ^ (-1 / 2 : ℝ)) := by
  have hbase : (0 : ℝ) ≤ (ρ / 2) ^ 3 * (Real.pi * 4 / 3) := by positivity
  have hpow : (volume (euclideanBall x₀ (ρ / 2))) ^ (5 / 6 : ℝ) =
      ENNReal.ofReal (((ρ / 2) ^ 3 * (Real.pi * 4 / 3)) ^ (5 / 6 : ℝ)) := by
    rw [volume_euclideanBall_half x₀ hρ]
    rw [ENNReal.ofReal_rpow_of_nonneg hbase (by norm_num)]
  calc ENNReal.ofReal (C * (ρ ^ 3)⁻¹) *
        (volume (euclideanBall x₀ (ρ / 2))) ^ (5 / 6 : ℝ)
      = ENNReal.ofReal
          (C * (ρ ^ 3)⁻¹ * (((ρ / 2) ^ 3 * (Real.pi * 4 / 3)) ^ (5 / 6 : ℝ))) := by
        rw [hpow, ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal
          (C * (ρ ^ 3)⁻¹ *
            ((ρ / 2) ^ (5 / 2 : ℝ) * (Real.pi * 4 / 3) ^ (5 / 6 : ℝ))) := by
        rw [rpow_five_sixths_half_volume hρ]
    _ ≤ ENNReal.ofReal (C * ρ ^ (-1 / 2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal (real_scaling_bound hρ hC)

end CKN.Core.Step4
