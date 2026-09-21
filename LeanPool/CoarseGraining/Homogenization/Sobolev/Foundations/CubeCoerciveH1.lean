/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1Dilation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1Translation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareMeanZero

/-! # Cube Coercive H1 -/

namespace Homogenization

open scoped Pointwise

noncomputable section

/-- A centered triadic cube is the dilation of the unit centered cube by its
side length. -/
theorem openCubeSet_originCube_eq_smul_unit (d : ℕ) (m : ℤ) :
    openCubeSet (originCube d m) =
      cubeScaleFactor (originCube d m) • openCubeSet (originCube d 0) := by
  ext x
  let s : ℝ := cubeScaleFactor (originCube d m)
  have hs_pos : 0 < s := by
    dsimp [s, cubeScaleFactor, originCube]
    positivity
  constructor
  · intro hx
    refine ⟨s⁻¹ • x, ?_, ?_⟩
    · rw [mem_openCubeSet_originCube_iff]
      intro i
      have hxi := (mem_openCubeSet_originCube_iff.mp hx) i
      rw [zpow_zero]
      constructor
      · have hlo_s : (-(1 / 2 : ℝ)) * s < x i := by
          simpa [s] using hxi.1
        have hmul := mul_lt_mul_of_pos_left hlo_s (inv_pos.mpr hs_pos)
        have hs_cancel : s⁻¹ * ((-(1 / 2 : ℝ)) * s) = -(1 / 2 : ℝ) := by
          field_simp [hs_pos.ne']
        change (-(1 / 2 : ℝ)) * 1 < s⁻¹ * x i
        nlinarith
      · have hhi_s : x i < (1 / 2 : ℝ) * s := by
          simpa [s] using hxi.2
        have hmul := mul_lt_mul_of_pos_left hhi_s (inv_pos.mpr hs_pos)
        have hs_cancel : s⁻¹ * ((1 / 2 : ℝ) * s) = (1 / 2 : ℝ) := by
          field_simp [hs_pos.ne']
        change s⁻¹ * x i < (1 / 2 : ℝ) * 1
        nlinarith
    · ext i
      change s * (s⁻¹ * x i) = x i
      field_simp [hs_pos.ne']
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hyi := (mem_openCubeSet_originCube_iff.mp hy) i
    rw [zpow_zero] at hyi
    constructor
    · have hmul := mul_lt_mul_of_pos_left hyi.1 hs_pos
      change (-(1 / 2 : ℝ)) * s < s * y i
      simpa [mul_comm] using hmul
    · have hmul := mul_lt_mul_of_pos_left hyi.2 hs_pos
      change s * y i < (1 / 2 : ℝ) * s
      simpa [mul_comm] using hmul

/-- Centered cubes have an explicit coordinate bound by their side length. -/
theorem isBoundedDomain_openCubeSet_originCube_scale
    (d : ℕ) (m : ℤ) :
    IsBoundedDomain (openCubeSet (originCube d m)) := by
  refine ⟨cubeScaleFactor (originCube d m), ?_, ?_⟩
  · dsimp [cubeScaleFactor, originCube]
    positivity
  · intro x hx i
    have hscale_pos : 0 < (3 : ℝ) ^ m := by positivity
    have hxi := (mem_openCubeSet_originCube_iff.mp hx) i
    rw [cubeScaleFactor_originCube]
    rw [abs_le]
    constructor
    · linarith
    · linarith

/-- Centered cubes as bounded open convex domains, with the explicit
side-length coordinate bound above. -/
theorem isOpenBoundedConvexDomain_openCubeSet_originCube_scale
    (d : ℕ) (m : ℤ) :
    IsOpenBoundedConvexDomain (openCubeSet (originCube d m)) :=
  ⟨isOpen_openCubeSet (originCube d m),
    isBoundedDomain_openCubeSet_originCube_scale d m,
    convex_openCubeSet (originCube d m)⟩

/-- The bounded-open-convex mean-zero `H¹` coercive estimate on a centered
triadic cube. -/
noncomputable def originCubeMeanZeroH1CoerciveEstimate
    (d : ℕ) (m : ℤ) :
    H1CoerciveEstimate (openCubeSet (originCube d m)) := by
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d m))) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).isFiniteMeasure_restrict_volume
  exact
    h1CoerciveEstimate_of_isOpenBoundedConvexDomain
      (U := openCubeSet (originCube d m))
      (isOpenBoundedConvexDomain_openCubeSet_originCube_scale d m)

theorem originCubeMeanZeroH1CoerciveEstimate_constant_le_chosenBound
    (d : ℕ) (m : ℤ) :
    (originCubeMeanZeroH1CoerciveEstimate d m).fixedValue ≤
      H1Function.h1CoerciveEstimateChosenBound
        (d := d) (U := openCubeSet (originCube d m))
        (isOpenBoundedConvexDomain_openCubeSet_originCube_scale d m) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d m))) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).isFiniteMeasure_restrict_volume
  unfold originCubeMeanZeroH1CoerciveEstimate
  exact
    h1CoerciveEstimate_of_isOpenBoundedConvexDomain_constant_le_chosenBound
      (U := openCubeSet (originCube d m))
      (isOpenBoundedConvexDomain_openCubeSet_originCube_scale d m)

/-- A cube coercive estimate obtained by proving Poincare on the centered cube
at the same scale and translating it to the target cube.  This avoids any
dependence on the target cube's location. -/
noncomputable def translatedCubeMeanZeroH1CoerciveEstimate {d : ℕ}
    (Q : TriadicCube d) :
    H1CoerciveEstimate (openCubeSet Q) := by
  letI :
      MeasureTheory.IsFiniteMeasure
        (volumeMeasureOn (openCubeSet (originCube d Q.scale))) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet
        (originCube d Q.scale)).isFiniteMeasure_restrict_volume
  let hC₀ : H1CoerciveEstimate (openCubeSet (originCube d Q.scale)) :=
    originCubeMeanZeroH1CoerciveEstimate d Q.scale
  refine
    { fixedValue := hC₀.fixedValue
      constant_nonneg := hC₀.constant_nonneg
      bound := ?_ }
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q]
  exact (hC₀.translate (triadicCubeShift Q)).bound

theorem translatedCubeMeanZeroH1CoerciveEstimate_constant {d : ℕ}
    (Q : TriadicCube d) :
    (translatedCubeMeanZeroH1CoerciveEstimate Q).fixedValue =
      (originCubeMeanZeroH1CoerciveEstimate d Q.scale).fixedValue := by
  unfold translatedCubeMeanZeroH1CoerciveEstimate
  rfl

theorem translatedCubeMeanZeroH1CoerciveEstimate_constant_nonneg {d : ℕ}
    (Q : TriadicCube d) :
    0 ≤ (translatedCubeMeanZeroH1CoerciveEstimate Q).fixedValue :=
  (translatedCubeMeanZeroH1CoerciveEstimate Q).constant_nonneg

theorem translatedCubeMeanZeroH1CoerciveEstimate_constant_le_origin_chosenBound {d : ℕ}
    (Q : TriadicCube d) :
    (translatedCubeMeanZeroH1CoerciveEstimate Q).fixedValue ≤
      H1Function.h1CoerciveEstimateChosenBound
        (d := d) (U := openCubeSet (originCube d Q.scale))
        (isOpenBoundedConvexDomain_openCubeSet_originCube_scale d Q.scale) := by
  rw [translatedCubeMeanZeroH1CoerciveEstimate_constant Q]
  exact originCubeMeanZeroH1CoerciveEstimate_constant_le_chosenBound d Q.scale

/-- Scale-correct coercive estimate on a centered cube, obtained by dilating the
unit centered cube estimate. -/
noncomputable def scaledOriginCubeMeanZeroH1CoerciveEstimate
    (d : ℕ) (m : ℤ) :
    H1CoerciveEstimate (openCubeSet (originCube d m)) := by
  let s : ℝ := cubeScaleFactor (originCube d m)
  have hs_pos : 0 < s := by
    dsimp [s, cubeScaleFactor, originCube]
    positivity
  let hCunit : H1CoerciveEstimate (openCubeSet (originCube d 0)) :=
    originCubeMeanZeroH1CoerciveEstimate d 0
  let hCdil : H1CoerciveEstimate (s • openCubeSet (originCube d 0)) :=
    hCunit.dilate hs_pos
  refine
    { fixedValue := s * hCunit.fixedValue
      constant_nonneg := mul_nonneg hs_pos.le hCunit.constant_nonneg
      bound := ?_ }
  rw [openCubeSet_originCube_eq_smul_unit d m]
  exact hCdil.bound

theorem scaledOriginCubeMeanZeroH1CoerciveEstimate_constant
    (d : ℕ) (m : ℤ) :
    (scaledOriginCubeMeanZeroH1CoerciveEstimate d m).fixedValue =
      cubeScaleFactor (originCube d m) *
        (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue := by
  rfl

/-- Scale-correct coercive estimate on any triadic cube, obtained by dilating
the unit centered cube and then translating to the target cube. -/
noncomputable def scaledTranslatedCubeMeanZeroH1CoerciveEstimate {d : ℕ}
    (Q : TriadicCube d) :
    H1CoerciveEstimate (openCubeSet Q) := by
  letI :
      MeasureTheory.IsFiniteMeasure
        (volumeMeasureOn (openCubeSet (originCube d Q.scale))) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet
        (originCube d Q.scale)).isFiniteMeasure_restrict_volume
  let hC₀ : H1CoerciveEstimate (openCubeSet (originCube d Q.scale)) :=
    scaledOriginCubeMeanZeroH1CoerciveEstimate d Q.scale
  refine
    { fixedValue := hC₀.fixedValue
      constant_nonneg := hC₀.constant_nonneg
      bound := ?_ }
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q]
  exact (hC₀.translate (triadicCubeShift Q)).bound

theorem scaledTranslatedCubeMeanZeroH1CoerciveEstimate_constant {d : ℕ}
    (Q : TriadicCube d) :
    (scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q).fixedValue =
      cubeScaleFactor Q * (originCubeMeanZeroH1CoerciveEstimate d 0).fixedValue := by
  unfold scaledTranslatedCubeMeanZeroH1CoerciveEstimate
  rw [scaledOriginCubeMeanZeroH1CoerciveEstimate_constant]
  rfl

end

end Homogenization
