/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ClassThetaCenter

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A centered nonzero fractional shape theta mellin kernel used in the Odlyzko-bound argument. -/
noncomputable def centeredNonzeroFractionalShapeThetaMellinKernel
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    (y : mixedEmbedding.realSpace K) : ℂ :=
  logarithmicMellinWeight K s y *
    (fractionalShapeIdealTheta K I
      (expMapBasis (centeredFractionalShapeCoordinates K I y))
      (fun w ↦
        (expMapBasis_pos
          (centeredFractionalShapeCoordinates K I y) w).ne') - 1)

open Classical in
/-- A centered class theta poisson correction used in the Odlyzko-bound argument. -/
noncomputable def centeredClassThetaPoissonCorrection
    (s : ℂ) (y : mixedEmbedding.realSpace K) : ℂ :=
  logarithmicMellinWeight K s (-y) *
    (((((Real.toNNReal
      (Real.exp ((-y) w₀ * (Module.finrank ℚ K : ℝ))))⁻¹ : ℝ) : ℂ)) - 1)

omit [IsTotallyComplex K] in
open Classical in
theorem logarithmicMellinWeight_neg_mul_centered_invCovolume
    (s : ℂ) (y : mixedEmbedding.realSpace K) :
    logarithmicMellinWeight K s (-y) *
        (((Real.toNNReal
          (Real.exp ((-y) w₀ *
            (Module.finrank ℚ K : ℝ))))⁻¹ : ℝ) : ℂ) =
      logarithmicMellinWeight K (1 - s) y := by
  rw [show
      (((Real.toNNReal
        (Real.exp ((-y) w₀ *
          (Module.finrank ℚ K : ℝ))))⁻¹ : ℝ) : ℂ) =
        (Real.exp ((-y) w₀ *
          (Module.finrank ℚ K : ℝ)) : ℂ)⁻¹ by
    simp [Real.toNNReal_of_nonneg (Real.exp_pos _).le]]
  simp only [Pi.neg_apply]
  push_cast
  rw [← Complex.exp_neg]
  rw [logarithmicMellinWeight, logarithmicMellinWeight,
    ← Complex.exp_add]
  simp only [Pi.neg_apply]
  push_cast
  ring_nf

open Classical in
theorem centeredNonzeroFractionalShapeThetaMellinKernel_neg_poisson
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    (y : mixedEmbedding.realSpace K) :
    centeredNonzeroFractionalShapeThetaMellinKernel K I s (-y) =
      centeredNonzeroFractionalShapeThetaMellinKernel K
          (traceDualIdealUnit K I) (1 - s) y +
        centeredClassThetaPoissonCorrection K s y := by
  rw [centeredNonzeroFractionalShapeThetaMellinKernel,
    fractionalShapeIdealTheta_centered_poisson]
  simp only [NNReal.smul_def, Complex.real_smul, NNReal.coe_inv,
    neg_neg, centeredNonzeroFractionalShapeThetaMellinKernel,
    centeredClassThetaPoissonCorrection]
  ring_nf
  rw [logarithmicMellinWeight_neg_mul_centered_invCovolume]
  ring

open Classical in
theorem centeredNonzeroFractionalShapeThetaMellinKernel_vadd_unitCoordinateLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    (g : unitCoordinateLattice (K := K))
    (y : mixedEmbedding.realSpace K) :
    centeredNonzeroFractionalShapeThetaMellinKernel K I s
        ((g : mixedEmbedding.realSpace K) + y) =
      centeredNonzeroFractionalShapeThetaMellinKernel K I s y := by
  rw [centeredNonzeroFractionalShapeThetaMellinKernel,
    centeredNonzeroFractionalShapeThetaMellinKernel,
    logarithmicMellinWeight_vadd_unitCoordinateLattice]
  congr 1
  obtain ⟨z, hz⟩ := g.prop
  rw [← hz]
  have htheta :=
    fractionalShapeIdealTheta_add_unitCoordinateShift K I
      (y + radialLogVector K
        (fractionalShapeCovolumeCenter K I)) z
  simpa only [centeredFractionalShapeCoordinates,
    unitCoordinateShiftHom_apply, add_comm, add_left_comm, add_assoc] using
      congrArg (fun z : ℂ ↦ z - 1) htheta

omit [IsTotallyComplex K] in
open Classical in
theorem centeredClassThetaPoissonCorrection_eq
    (s : ℂ) (y : mixedEmbedding.realSpace K) :
    centeredClassThetaPoissonCorrection K s y =
      logarithmicMellinWeight K (1 - s) y -
        logarithmicMellinWeight K s (-y) := by
  rw [centeredClassThetaPoissonCorrection, mul_sub, mul_one,
    logarithmicMellinWeight_neg_mul_centered_invCovolume]

omit [IsTotallyComplex K] in
open Classical in
theorem integrableOn_centeredClassThetaPoissonCorrection
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (centeredClassThetaPoissonCorrection K s)
      (positiveUnitFundamentalParamSet (K := K)) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hreflect : (1 - s).re < 0 := by simp_all
  apply IntegrableOn.congr_fun
    ((integrableOn_positive_logarithmicMellinWeight K hreflect).sub
      (integrableOn_positive_logarithmicMellinWeight_neg K hs0))
    _ measurableSet_positiveUnitFundamentalParamSet
  intro y _
  exact centeredClassThetaPoissonCorrection_eq K s y |>.symm

omit [IsTotallyComplex K] in
open Classical in
theorem setIntegral_centeredClassThetaPoissonCorrection
    {s : ℂ} (hs : 1 < s.re) :
    (∫ y in positiveUnitFundamentalParamSet (K := K),
      centeredClassThetaPoissonCorrection K s y) =
        -1 / ((Module.finrank ℚ K : ℂ) * (1 - s)) -
          1 / ((Module.finrank ℚ K : ℂ) * s) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hreflect : (1 - s).re < 0 := by simp_all
  have hfirst :=
    integrableOn_positive_logarithmicMellinWeight K hreflect
  have hsecond :=
    integrableOn_positive_logarithmicMellinWeight_neg K hs0
  calc
    (∫ y in positiveUnitFundamentalParamSet (K := K),
        centeredClassThetaPoissonCorrection K s y) =
        ∫ y in positiveUnitFundamentalParamSet (K := K),
          logarithmicMellinWeight K (1 - s) y -
            logarithmicMellinWeight K s (-y) := by
      apply setIntegral_congr_fun measurableSet_positiveUnitFundamentalParamSet
      intro y _
      exact centeredClassThetaPoissonCorrection_eq K s y
    _ = (∫ y in positiveUnitFundamentalParamSet (K := K),
          logarithmicMellinWeight K (1 - s) y) -
        ∫ y in positiveUnitFundamentalParamSet (K := K),
          logarithmicMellinWeight K s (-y) := by
      rw [integral_sub hfirst hsecond]
    _ = -1 / ((Module.finrank ℚ K : ℂ) * (1 - s)) -
          1 / ((Module.finrank ℚ K : ℂ) * s) := by
      rw [setIntegral_positive_logarithmicMellinWeight K hreflect,
        setIntegral_positive_logarithmicMellinWeight_neg K hs0]

end NumberField.Odlyzko
