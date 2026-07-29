/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ClassThetaRadial
public import LeanPool.Odlyzko.CompletedZeta.LogarithmicMellinHalfIntegral

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A radial log vector used in the Odlyzko-bound argument. -/
noncomputable def radialLogVector (t : ℝ) :
    mixedEmbedding.realSpace K :=
  fun w ↦ if w = w₀ then t else 0

omit [IsTotallyComplex K] in
open Classical in
@[simp]
theorem radialLogVector_apply_w₀ (t : ℝ) :
    radialLogVector K t w₀ = t := by
  simp [radialLogVector]

omit [IsTotallyComplex K] in
open Classical in
theorem radialLogVector_neg (t : ℝ) :
    radialLogVector K (-t) = -radialLogVector K t := by
  ext w
  by_cases hw : w = w₀ <;> simp [radialLogVector, hw]

omit [IsTotallyComplex K] in
open Classical in
theorem fractionalShapeCovolumeConstant_pos
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < fractionalShapeCovolumeConstant K I := by
  rw [fractionalShapeCovolumeConstant]
  have hnQ :
      0 < FractionalIdeal.absNorm
        (I : FractionalIdeal (𝓞 K)⁰ K) :=
    lt_of_le_of_ne
      (FractionalIdeal.absNorm_nonneg _)
      (fun h ↦ Units.ne_zero I
        (FractionalIdeal.absNorm_eq_zero_iff.mp h.symm))
  have hn :
      0 < (FractionalIdeal.absNorm
        (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by simp_all
  exact mul_pos hn (Real.sqrt_pos.2
    (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))))

open Classical in
/-- A fractional shape covolume center used in the Odlyzko-bound argument. -/
noncomputable def fractionalShapeCovolumeCenter
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  -Real.log (fractionalShapeCovolumeConstant K I) /
    (Module.finrank ℚ K : ℝ)

omit [IsTotallyComplex K] in
open Classical in
theorem fractionalShapeCovolumeCenter_traceDual
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    fractionalShapeCovolumeCenter K (traceDualIdealUnit K I) =
      -fractionalShapeCovolumeCenter K I := by
  rw [fractionalShapeCovolumeCenter, fractionalShapeCovolumeCenter,
    fractionalShapeCovolumeConstant_traceDual,
    Real.log_inv]
  ring

open Classical in
/-- A centered fractional shape coordinates used in the Odlyzko-bound argument. -/
noncomputable def centeredFractionalShapeCoordinates
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedEmbedding.realSpace K) :
    mixedEmbedding.realSpace K :=
  y + radialLogVector K (fractionalShapeCovolumeCenter K I)

omit [IsTotallyComplex K] in
open Classical in
theorem centeredFractionalShapeCoordinates_traceDual_neg
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedEmbedding.realSpace K) :
    centeredFractionalShapeCoordinates K (traceDualIdealUnit K I) (-y) =
      -centeredFractionalShapeCoordinates K I y := by
  rw [centeredFractionalShapeCoordinates,
    centeredFractionalShapeCoordinates,
    fractionalShapeCovolumeCenter_traceDual,
    radialLogVector_neg]
  grind

open Classical in
theorem covolume_shapeIdealLattice_centered
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedEmbedding.realSpace K) :
    ZLattice.covolume
        (shapeIdealLattice K I
          (expMapBasis (centeredFractionalShapeCoordinates K I y))
          (fun w ↦
            (expMapBasis_pos
              (centeredFractionalShapeCoordinates K I y) w).ne')) =
      Real.exp (y w₀ * (Module.finrank ℚ K : ℝ)) := by
  rw [covolume_shapeIdealLattice_expMapBasis,
    centeredFractionalShapeCoordinates]
  simp only [Pi.add_apply, radialLogVector_apply_w₀,
    fractionalShapeCovolumeCenter]
  have hfin : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hA := fractionalShapeCovolumeConstant_pos K I
  rw [show
      FractionalIdeal.absNorm
          (I : FractionalIdeal (𝓞 K)⁰ K) * √|discr K| =
        fractionalShapeCovolumeConstant K I by rfl]
  rw [show
      (y w₀ + -Real.log (fractionalShapeCovolumeConstant K I) /
          (Module.finrank ℚ K : ℝ)) *
          (Module.finrank ℚ K : ℝ) =
        y w₀ * (Module.finrank ℚ K : ℝ) -
          Real.log (fractionalShapeCovolumeConstant K I) by
    grind]
  rw [Real.exp_sub, Real.exp_log hA, div_mul_cancel₀ _ hA.ne']

open Classical in
theorem fractionalShapeIdealTheta_centered_poisson
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedEmbedding.realSpace K) :
    fractionalShapeIdealTheta K I
        (expMapBasis (centeredFractionalShapeCoordinates K I y))
        (fun w ↦
          (expMapBasis_pos
            (centeredFractionalShapeCoordinates K I y) w).ne') =
      (Real.toNNReal
        (Real.exp (y w₀ * (Module.finrank ℚ K : ℝ))))⁻¹ •
        fractionalShapeIdealTheta K (traceDualIdealUnit K I)
          (expMapBasis
            (centeredFractionalShapeCoordinates K
              (traceDualIdealUnit K I) (-y)))
          (fun w ↦
            (expMapBasis_pos
              (centeredFractionalShapeCoordinates K
                (traceDualIdealUnit K I) (-y)) w).ne') := by
  rw [fractionalShapeIdealTheta_poissonSummation,
    covolume_shapeIdealLattice_centered]
  congr 2
  funext w
  rw [centeredFractionalShapeCoordinates_traceDual_neg,
    expMapBasis_neg]

end NumberField.Odlyzko
