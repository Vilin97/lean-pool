/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentSmoothBound

/-! # Reflection Parent Energy Factor -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace MeanZeroNeumannPoissonSolution

private noncomputable def originCubeParentReducedSolverEnergyInside
    (d : ℕ) (m : ℤ) : ℝ :=
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := cubeMeanZeroH1CoerciveConstant Q
  let V : ℝ := cubeVolume Q
  let B : ℝ := V + 1
  let Kinner : ℝ :=
    (3 : ℝ) *
      ((d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          (((1 / 2 : ℝ) - (1 / 3 : ℝ)) * cubeRadius Qp)) ^ 2)
  let Kouter : ℝ :=
    (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d /
        (((7 / 8 : ℝ) - (3 / 4 : ℝ)) * cubeRadius Qp)) ^ 2
  (4 : ℝ) *
    ((2 : ℝ) * ((3 : ℝ) ^ d * V) +
      Kinner *
        ((2 : ℝ) * ((3 : ℝ) ^ d * (C * B) ^ 2) +
          (2 : ℝ) * (Kouter * ((3 : ℝ) ^ d * (C * (C * B)) ^ 2))))

private theorem originCubeParentReducedSolverEnergyInside_nonneg
    (d : ℕ) (m : ℤ) :
    0 ≤ originCubeParentReducedSolverEnergyInside d m := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := cubeMeanZeroH1CoerciveConstant Q
  let V : ℝ := cubeVolume Q
  let B : ℝ := V + 1
  let Kinner : ℝ :=
    (3 : ℝ) *
      ((d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          (((1 / 2 : ℝ) - (1 / 3 : ℝ)) * cubeRadius Qp)) ^ 2)
  let Kouter : ℝ :=
    (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d /
        (((7 / 8 : ℝ) - (3 / 4 : ℝ)) * cubeRadius Qp)) ^ 2
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    exact cubeVolume_nonneg Q
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    linarith
  have hKinner_nonneg : 0 ≤ Kinner := by
    dsimp [Kinner]
    exact mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg d) (sq_nonneg _))
  have hKouter_nonneg : 0 ≤ Kouter := by
    dsimp [Kouter]
    exact mul_nonneg (Nat.cast_nonneg d) (sq_nonneg _)
  have hmain_nonneg :
      0 ≤ (2 : ℝ) * ((3 : ℝ) ^ d * V) +
        Kinner *
          ((2 : ℝ) * ((3 : ℝ) ^ d * (C * B) ^ 2) +
            (2 : ℝ) * (Kouter * ((3 : ℝ) ^ d * (C * (C * B)) ^ 2))) := by
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (by norm_num)
        (mul_nonneg (by positivity) hV_nonneg)
    · refine mul_nonneg hKinner_nonneg ?_
      refine add_nonneg ?_ ?_
      · exact mul_nonneg (by norm_num)
          (mul_nonneg (by positivity) (sq_nonneg _))
      · exact mul_nonneg (by norm_num)
          (mul_nonneg hKouter_nonneg
            (mul_nonneg (by positivity) (sq_nonneg _)))
  dsimp [originCubeParentReducedSolverEnergyInside, Q, Qp, C, V, B, Kinner, Kouter]
  exact mul_nonneg (by norm_num) hmain_nonneg

/-- The coefficient obtained by factoring the normalized forcing norm out of
the reflected-parent solver energy bound. -/
noncomputable def originCubeParentReducedSolverEnergyConstant
    (d : ℕ) (m : ℤ) : ℝ :=
  (originCubeParentReducedSolverEnergyInside d m) ^ (1 / (2 : ℝ))

theorem originCubeParentReducedSolverEnergyConstant_nonneg
    (d : ℕ) (m : ℤ) :
    0 ≤ originCubeParentReducedSolverEnergyConstant d m := by
  unfold originCubeParentReducedSolverEnergyConstant
  exact Real.rpow_nonneg
    (originCubeParentReducedSolverEnergyInside_nonneg d m) _

theorem originCubeParentReducedSolverEnergyBound_eq_constant_mul_cubeLpNorm
    (d : ℕ) (m : ℤ) (F : Vec d → ℝ) (i : Fin d) :
    originCubeParentReducedSolverEnergyBound d m F i =
      originCubeParentReducedSolverEnergyConstant d m *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let C : ℝ := cubeMeanZeroH1CoerciveConstant Q
  let V : ℝ := cubeVolume Q
  let B : ℝ := V + 1
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  let Kinner : ℝ :=
    (3 : ℝ) *
      ((d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          (((1 / 2 : ℝ) - (1 / 3 : ℝ)) * cubeRadius Qp)) ^ 2)
  let Kouter : ℝ :=
    (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d /
        (((7 / 8 : ℝ) - (3 / 4 : ℝ)) * cubeRadius Qp)) ^ 2
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞) F
  have hfactor :
      (4 : ℝ) *
        ((2 : ℝ) * ((3 : ℝ) ^ d * (V * L ^ (2 : ℝ))) +
          Kinner *
            ((2 : ℝ) * ((3 : ℝ) ^ d * (C * (B * L)) ^ 2) +
              (2 : ℝ) *
                (Kouter * ((3 : ℝ) ^ d * (C * (C * (B * L))) ^ 2)))) =
        originCubeParentReducedSolverEnergyInside d m * L ^ 2 := by
    dsimp [originCubeParentReducedSolverEnergyInside, Q, Qp, C, V, B, L, Kinner, Kouter]
    rw [Real.rpow_two]
    ring
  calc
    originCubeParentReducedSolverEnergyBound d m F i
        = ((originCubeParentReducedSolverEnergyInside d m) * L ^ 2) ^
            (1 / (2 : ℝ)) := by
          dsimp [originCubeParentReducedSolverEnergyBound, Q, Qp, C, L, B, Kinner, Kouter]
          rw [hfactor]
    _ = (originCubeParentReducedSolverEnergyInside d m) ^ (1 / (2 : ℝ)) *
          (L ^ 2) ^ (1 / (2 : ℝ)) := by
          rw [Real.mul_rpow
            (originCubeParentReducedSolverEnergyInside_nonneg d m) (sq_nonneg L)]
    _ = originCubeParentReducedSolverEnergyConstant d m * L := by
          unfold originCubeParentReducedSolverEnergyConstant
          rw [show (L ^ 2) ^ (1 / (2 : ℝ)) = L by
            rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hL_nonneg]]

end MeanZeroNeumannPoissonSolution

end

end Homogenization
