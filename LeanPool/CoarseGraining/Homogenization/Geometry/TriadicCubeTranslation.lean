/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCube
public import LeanPool.CoarseGraining.Homogenization.Geometry.Translation

/-! # Triadic Cube Translation -/

@[expose] public section

open scoped Pointwise

/-!
# Translations from centered triadic cubes

This file records the elementary geometry identifying an arbitrary triadic cube
with a translate of the centered cube at the same scale, and the centered cube
at any scale with a positive dilation of the unit centered cube.
-/

namespace Homogenization

/-- Translation vector carrying the centered cube of scale `Q.scale` to `Q`. -/
noncomputable def triadicCubeShift {d : ℕ} (Q : TriadicCube d) : Vec d :=
  fun i => (Q.index i : ℝ) * cubeScaleFactor Q

theorem cubeSet_eq_translateSet_originCube_of_triadicCube {d : ℕ}
    (Q : TriadicCube d) :
    cubeSet Q =
      translateSet (triadicCubeShift Q) (cubeSet (originCube d Q.scale)) := by
  cases Q with
  | mk scale index =>
      apply Set.ext
      intro x
      rw [mem_translateSet_iff_sub_mem]
      constructor
      · intro hx i
        simpa [triadicCubeShift, cubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, add_mul] using hx i
      · intro hx i
        simpa [triadicCubeShift, cubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, add_mul] using hx i

theorem openCubeSet_eq_translateSet_originCube_of_triadicCube {d : ℕ}
    (Q : TriadicCube d) :
    openCubeSet Q =
      translateSet (triadicCubeShift Q) (openCubeSet (originCube d Q.scale)) := by
  cases Q with
  | mk scale index =>
      apply Set.ext
      intro x
      rw [mem_translateSet_iff_sub_mem]
      constructor
      · intro hx i
        simpa [triadicCubeShift, openCubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, add_mul] using hx i
      · intro hx i
        simpa [triadicCubeShift, openCubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, add_mul] using hx i

theorem openCubeSet_originCube_eq_smul_originCube_zero {d : ℕ} (m : ℤ) :
    openCubeSet (originCube d m) =
      cubeScaleFactor (originCube d m) • openCubeSet (originCube d 0) := by
  ext y
  let r : ℝ := cubeScaleFactor (originCube d m)
  have hr_pos : 0 < r := by
    simpa [r, cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) m)
  constructor
  · intro hy
    rw [Set.mem_smul_set]
    refine ⟨r⁻¹ • y, ?_, ?_⟩
    · intro i
      have hyi := hy i
      have hlo_scaled : (-(1 / 2 : ℝ)) * r < y i := by
        simpa [r, originCube, cubeScaleFactor] using hyi.1
      have hhi_scaled : y i < (1 / 2 : ℝ) * r := by
        simpa [r, originCube, cubeScaleFactor] using hyi.2
      constructor
      · have hlo : (-(1 / 2 : ℝ)) < y i / r :=
          (lt_div_iff₀ hr_pos).mpr hlo_scaled
        simpa [r, originCube, cubeScaleFactor, mul_comm, div_eq_mul_inv] using hlo
      · have hhi : y i / r < (1 / 2 : ℝ) :=
          (div_lt_iff₀ hr_pos).mpr hhi_scaled
        simpa [r, originCube, cubeScaleFactor, mul_comm, div_eq_mul_inv] using hhi
    · ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      change r * (r⁻¹ * y i) = y i
      rw [← mul_assoc, mul_inv_cancel₀ hr_pos.ne', one_mul]
  · intro hy
    rw [Set.mem_smul_set] at hy
    rcases hy with ⟨x, hx, rfl⟩
    intro i
    have hxi := hx i
    constructor
    · have hlo := mul_lt_mul_of_pos_left hxi.1 hr_pos
      simpa [r, originCube, cubeScaleFactor, mul_comm, mul_left_comm, mul_assoc] using hlo
    · have hhi := mul_lt_mul_of_pos_left hxi.2 hr_pos
      simpa [r, originCube, cubeScaleFactor, mul_comm, mul_left_comm, mul_assoc] using hhi

theorem openCubeSet_eq_translateSet_smul_originCube_zero {d : ℕ}
    (Q : TriadicCube d) :
    openCubeSet Q =
      translateSet (triadicCubeShift Q)
        (cubeScaleFactor Q • openCubeSet (originCube d 0)) := by
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
    openCubeSet_originCube_eq_smul_originCube_zero (d := d) Q.scale]
  simp [originCube, cubeScaleFactor]

end Homogenization
