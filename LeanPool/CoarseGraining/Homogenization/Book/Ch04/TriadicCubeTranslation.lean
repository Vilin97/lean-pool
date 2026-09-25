/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.SignedPermutation
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition

/-! # Triadic Cube Translation -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

noncomputable section

/-- Integer shift taking a nonnegative-scale origin cube to a cube at the same
scale. -/
def scaleTranslationShift {d : ℕ} (k : ℤ) (R : TriadicCube d) : Fin d → ℤ :=
  fun i => Int.ofNat (3 ^ Int.toNat k) * R.index i

/-- At nonnegative scale, every triadic cube is an integer translate of the
origin cube at the same scale. -/
theorem cubeSet_eq_translateSet_originCube_of_nonneg_scale {d : ℕ}
    {R : TriadicCube d} (hk : 0 ≤ R.scale) :
    cubeSet R =
      translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
        (cubeSet (originCube d R.scale)) := by
  calc
    cubeSet R =
        translateSet (fun i => (R.index i : ℝ) * cubeScaleFactor R)
          (cubeSet (originCube d R.scale)) :=
      cubeSet_eq_translateSet_originCube_of_triadicCube R
    _ =
        translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
          (cubeSet (originCube d R.scale)) := by
          congr 1
          funext i
          have hpow :
              (((Int.ofNat (3 ^ Int.toNat R.scale) : ℤ) : ℝ)) = cubeScaleFactor R := by
            calc
              (((Int.ofNat (3 ^ Int.toNat R.scale) : ℤ) : ℝ))
                  = (((3 ^ Int.toNat R.scale : ℕ) : ℝ)) := by
                      simp
              _ = (3 : ℝ) ^ Int.toNat R.scale := by
                    simp [Nat.cast_pow]
              _ = (3 : ℝ) ^ R.scale := by
                    symm
                    calc
                      (3 : ℝ) ^ R.scale = (3 : ℝ) ^ ((Int.toNat R.scale : ℤ)) := by
                        rw [Int.toNat_of_nonneg hk]
                      _ = (3 : ℝ) ^ Int.toNat R.scale := by
                        rw [zpow_natCast]
              _ = cubeScaleFactor R := by
                    simp [cubeScaleFactor]
          calc
            (R.index i : ℝ) * cubeScaleFactor R
                = (R.index i : ℝ) *
                    (((Int.ofNat (3 ^ Int.toNat R.scale) : ℤ) : ℝ)) := by
                      rw [hpow.symm]
            _ = (((Int.ofNat (3 ^ Int.toNat R.scale) : ℤ) : ℝ)) *
                  (R.index i : ℝ) := by
                    ring
            _ = intVecToRealVec (scaleTranslationShift R.scale R) i := by
                    simp [intVecToRealVec, scaleTranslationShift]

/-- Descendants of the origin cube at a fixed scale have that scale. -/
theorem scale_eq_of_mem_descendantsAtScale_originCube {d : ℕ}
    {n m : ℤ} {R : TriadicCube d} (hnm : n ≤ m)
    (hR : R ∈ descendantsAtScale (originCube d m) n) :
    R.scale = n := by
  calc
    R.scale = (originCube d m).scale - Int.toNat ((originCube d m).scale - n) := by
      exact scale_eq_sub_of_mem_descendantsAtScale (Q := originCube d m) hnm hR
    _ = m - Int.toNat (m - n) := by
      rfl
    _ = n := by
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hnm)]
      ring

/-- A descendant of a nonnegative-scale origin cube is an integer translate of
the origin cube at the descendant scale. -/
theorem cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
    {d : ℕ} {n m : ℤ} {R : TriadicCube d} (hn : 0 ≤ n) (hnm : n ≤ m)
    (hR : R ∈ descendantsAtScale (originCube d m) n) :
    cubeSet R =
      translateSet (intVecToRealVec (scaleTranslationShift n R))
        (cubeSet (originCube d n)) := by
  have hscaleR : R.scale = n :=
    scale_eq_of_mem_descendantsAtScale_originCube hnm hR
  have hscale_nonneg : 0 ≤ R.scale := by
    simpa [hscaleR] using hn
  calc
    cubeSet R =
        translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
          (cubeSet (originCube d R.scale)) :=
      cubeSet_eq_translateSet_originCube_of_nonneg_scale hscale_nonneg
    _ =
        translateSet (intVecToRealVec (scaleTranslationShift n R))
          (cubeSet (originCube d n)) := by
        simp [hscaleR]

end
end Ch04
end Book
end Homogenization
