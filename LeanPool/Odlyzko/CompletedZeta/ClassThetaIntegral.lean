/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ClassRepresentatives
public import LeanPool.Odlyzko.CompletedZeta.ShapeMellinTranslation
public import LeanPool.Odlyzko.CompletedZeta.TotallyComplex

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A shape theta integral constant used in the Odlyzko-bound argument. -/
noncomputable def shapeThetaIntegralConstant : ℝ :=
  2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K *
    NumberField.Units.regulator K

open Classical in
/-- A class completed theta integral used in the Odlyzko-bound argument. -/
noncomputable def classCompletedThetaIntegral
    (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  CompletedZeta.discriminantFactor K s *
    (torsionOrder K : ℂ)⁻¹ *
    (absNorm
      (inverseClassIdealRepresentative K C : Ideal (𝓞 K)) : ℂ) ^ s *
    ((2 : ℂ) ^ nrComplexPlaces K *
      ∫ y in unitFundamentalParamSet K,
        ((shapeThetaIntegralConstant K : ℝ) : ℂ) *
          logarithmicMellinWeight K s y *
          nonzeroIdealShapeTheta K
            (inverseClassIdealRepresentative K C) y)

open Classical in
theorem classCompletedThetaIntegral_eq_fundamentalConeZeta
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    classCompletedThetaIntegral K C s =
      CompletedZeta.discriminantFactor K s *
        (torsionOrder K : ℂ)⁻¹ *
        (absNorm
          (inverseClassIdealRepresentative K C :
            Ideal (𝓞 K)) : ℂ) ^ s *
        (CompletedZeta.complexPlaceGammaFactor s ^ nrComplexPlaces K *
          fundamentalConeZeta K
            (inverseClassIdealRepresentative K C) s) := by
  rw [classCompletedThetaIntegral]
  congr 1
  have hcone :=
    fundamentalConeZeta_eq_integral_nonzeroIdealShapeTheta K
      (inverseClassIdealRepresentative K C) hs
  calc
    (2 : ℂ) ^ nrComplexPlaces K *
          (∫ y in unitFundamentalParamSet K,
            ((shapeThetaIntegralConstant K : ℝ) : ℂ) *
              logarithmicMellinWeight K s y *
              nonzeroIdealShapeTheta K
                (inverseClassIdealRepresentative K C) y) =
        (2 : ℂ) ^ nrComplexPlaces K *
          (((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^
              nrComplexPlaces K *
            fundamentalConeZeta K
              (inverseClassIdealRepresentative K C) s) := by
      congr 1
      symm
      simpa only [shapeThetaIntegralConstant, logarithmicMellinWeight,
        mul_assoc] using hcone
    _ = CompletedZeta.complexPlaceGammaFactor s ^ nrComplexPlaces K *
          fundamentalConeZeta K
            (inverseClassIdealRepresentative K C) s := by
      rw [← mul_assoc, ← mul_pow]
      simp

open Classical in
theorem sum_classCompletedThetaIntegral
    {s : ℂ} (hs : 1 < s.re) :
    ∑ C : ClassGroup (𝓞 K), classCompletedThetaIntegral K C s =
      CompletedZeta.completed K s := by
  simp_rw [classCompletedThetaIntegral_eq_fundamentalConeZeta K _ hs]
  calc
    ∑ C : ClassGroup (𝓞 K),
        CompletedZeta.discriminantFactor K s *
          (torsionOrder K : ℂ)⁻¹ *
          (absNorm
            (inverseClassIdealRepresentative K C :
              Ideal (𝓞 K)) : ℂ) ^ s *
          (CompletedZeta.complexPlaceGammaFactor s ^ nrComplexPlaces K *
            fundamentalConeZeta K
              (inverseClassIdealRepresentative K C) s) =
        CompletedZeta.discriminantFactor K s *
          CompletedZeta.complexPlaceGammaFactor s ^ nrComplexPlaces K *
          ∑ C : ClassGroup (𝓞 K),
            (torsionOrder K : ℂ)⁻¹ *
              (absNorm
                (inverseClassIdealRepresentative K C :
                  Ideal (𝓞 K)) : ℂ) ^ s *
              fundamentalConeZeta K
                (inverseClassIdealRepresentative K C) s := by
      rw [Finset.mul_sum]
      grind
    _ = CompletedZeta.discriminantFactor K s *
          CompletedZeta.complexPlaceGammaFactor s ^ nrComplexPlaces K *
          NumberField.dedekindZeta K s := by
      rw [sum_normalized_fundamentalConeZeta K hs]
    _ = CompletedZeta.completed K s := by
      rw [completedDedekindZeta_of_isTotallyComplex,
        CompletedZeta.complexPlaceGammaFactor]

end NumberField.Odlyzko
