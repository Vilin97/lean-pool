/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Origin Cube Measure Bridge -/

@[expose] public section

namespace Homogenization

/--
The half-open and open realizations of the centered cube at scale `n` agree
almost everywhere for Lebesgue measure.
-/
theorem cubeSet_originCube_ae_eq_openCubeSet {d : ℕ} (n : ℤ) :
    cubeSet (originCube d n) =ᵐ[MeasureTheory.volume] openCubeSet (originCube d n) :=
  cubeSet_ae_eq_openCubeSet (originCube d n)

/--
Restricted Lebesgue measure on the half-open centered cube agrees with the
restriction to the corresponding open cube.
-/
theorem volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube
    {d : ℕ} (n : ℤ) :
    MeasureTheory.volume.restrict (cubeSet (originCube d n)) =
      MeasureTheory.volume.restrict (openCubeSet (originCube d n)) :=
  MeasureTheory.Measure.restrict_congr_set (cubeSet_originCube_ae_eq_openCubeSet (d := d) n)

/--
Almost-everywhere statements over the half-open centered cube are equivalent to
the corresponding statements over the open centered cube.
-/
theorem ae_restrict_cubeSet_originCube_iff {d : ℕ} {n : ℤ} {p : Vec d → Prop} :
    (∀ᵐ x ∂MeasureTheory.volume.restrict (cubeSet (originCube d n)), p x) ↔
      ∀ᵐ x ∂MeasureTheory.volume.restrict (openCubeSet (originCube d n)), p x := by
  exact MeasureTheory.ae_restrict_congr_set (cubeSet_originCube_ae_eq_openCubeSet (d := d) n)

/--
Integrability on the half-open centered cube is equivalent to integrability on
the corresponding open cube.
-/
theorem integrableOn_cubeSet_originCube_iff_integrableOn_openCubeSet_originCube
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℤ} {f : Vec d → E} :
    MeasureTheory.IntegrableOn f (cubeSet (originCube d n)) MeasureTheory.volume ↔
      MeasureTheory.IntegrableOn f (openCubeSet (originCube d n)) MeasureTheory.volume := by
  exact MeasureTheory.integrableOn_congr_set_ae
    (cubeSet_originCube_ae_eq_openCubeSet (d := d) n)

/--
Set integrals over the half-open centered cube and the corresponding open cube
agree.
-/
theorem setIntegral_cubeSet_originCube_eq_setIntegral_openCubeSet_originCube
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℤ} {f : Vec d → E} :
    ∫ x in cubeSet (originCube d n), f x ∂MeasureTheory.volume =
      ∫ x in openCubeSet (originCube d n), f x ∂MeasureTheory.volume := by
  exact MeasureTheory.setIntegral_congr_set
    (cubeSet_originCube_ae_eq_openCubeSet (d := d) n)

end Homogenization
