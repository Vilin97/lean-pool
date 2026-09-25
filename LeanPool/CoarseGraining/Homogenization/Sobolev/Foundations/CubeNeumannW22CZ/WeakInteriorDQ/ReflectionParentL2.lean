/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.MemL2AndPairings
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionGeometry

/-! # Reflection Parent L2 -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

variable {d : ℕ} {m : ℤ}

/-- The all-face reflected scalar is `L²` on the centered parent cube. -/
theorem memScalarL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar
    {F : Vec d → ℝ}
    (hF : MemScalarL2 (openCubeSet (originCube d m)) F) :
    MemScalarL2 (openCubeSet (originCube d (m + 1)))
      (cubeCoordinateFoldReflectedScalar (originCube d m) F) := by
  have hblock :=
    memScalarL2_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar
      (originCube d m) hF
  have hmeasure :
      volumeMeasureOn (openCubeSet (originCube d (m + 1))) =
        volumeMeasureOn (cubeFaceReflectionBlockSet (originCube d m)) := by
    simpa [volumeMeasureOn] using
      MeasureTheory.Measure.restrict_congr_set
        (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm
  simpa [MemScalarL2, hmeasure] using hblock

/-- The all-face reflected vector field is `L²` on the centered parent cube. -/
theorem memVectorL2_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
    {G : Vec d → Vec d}
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G) :
    MemVectorL2 (openCubeSet (originCube d (m + 1)))
      (cubeCoordinateFoldReflectedVectorField (originCube d m) G) := by
  have hblock :=
    memVectorL2_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField
      (originCube d m) hG
  have hmeasure :
      volumeMeasureOn (openCubeSet (originCube d (m + 1))) =
        volumeMeasureOn (cubeFaceReflectionBlockSet (originCube d m)) := by
    simpa [volumeMeasureOn] using
      MeasureTheory.Measure.restrict_congr_set
        (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm
  simpa [MemVectorL2, hmeasure] using hblock

/-- Scalar reflected energy on the centered parent cube is `3^d` copies of
the original cube energy. -/
theorem setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedScalar_sq_of_memScalarL2_three_pow
    {F : Vec d → ℝ}
    (hF : MemScalarL2 (openCubeSet (originCube d m)) F) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        cubeCoordinateFoldReflectedScalar (originCube d m) F x *
          cubeCoordinateFoldReflectedScalar (originCube d m) F x
        ∂MeasureTheory.volume =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet (originCube d m), F y * F y
          ∂MeasureTheory.volume := by
  rw [setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
    (m := m)
    (f := fun x =>
      cubeCoordinateFoldReflectedScalar (originCube d m) F x *
        cubeCoordinateFoldReflectedScalar (originCube d m) F x)]
  exact
    setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedScalar_sq_of_memScalarL2_three_pow
      (originCube d m) hF

/-- Vector reflected energy on the centered parent cube is `3^d` copies of
the original cube energy. -/
theorem setIntegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_self_pairing_of_memVectorL2_three_pow
    {G : Vec d → Vec d}
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        vecDot
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x)
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x)
        ∂MeasureTheory.volume =
      (3 : ℝ) ^ d *
        ∫ y in openCubeSet (originCube d m), vecDot (G y) (G y)
          ∂MeasureTheory.volume := by
  rw [setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
    (m := m)
    (f := fun x =>
      vecDot
        (cubeCoordinateFoldReflectedVectorField (originCube d m) G x)
        (cubeCoordinateFoldReflectedVectorField (originCube d m) G x))]
  exact
    setIntegral_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField_self_pairing_of_memVectorL2_three_pow
      (originCube d m) hG

end

end Homogenization
