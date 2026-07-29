/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredContinuation

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A centered numerator translation used in the Odlyzko-bound argument. -/
noncomputable def centeredNumeratorTranslation
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    mixedEmbedding.realSpace K :=
  radialLogVector K (fractionalShapeCovolumeCenter K I) -
    denominatorLogCoordinates K I -
    radialLogVector K
      (fractionalShapeCovolumeCenter K
        (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)))

open Classical in
theorem fractionalShapeCovolumeConstant_numerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    fractionalShapeCovolumeConstant K
        (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) =
      fractionalShapeCovolumeConstant K I *
        Real.exp
          (denominatorLogCoordinates K I w₀ *
            (Module.finrank ℚ K : ℝ)) := by
  let d : 𝓞 K :=
    (I : FractionalIdeal (𝓞 K)⁰ K).den
  have hnorm :
      ((|Algebra.norm ℤ d| : ℤ) : ℚ) =
        |Algebra.norm ℚ (algebraMap (𝓞 K) K d)| := by
    have h := congrArg (fun x : ℚ ↦ |x|)
      (Algebra.norm_localization ℤ ℤ⁰ (Sₘ := K) d)
    simpa using h.symm
  have hdenZ : Algebra.norm ℤ d ≠ 0 :=
    fun h ↦ fractionalIdeal_den_ne_zero K I
      (Algebra.norm_eq_zero_iff.mp h)
  rw [fractionalShapeCovolumeConstant,
    fractionalShapeCovolumeConstant,
    FractionalIdeal.coe_mk0,
    FractionalIdeal.coeIdeal_absNorm,
    FractionalIdeal.absNorm_eq,
    exp_denominatorLogCoordinates_mul_finrank]
  change
    ((absNorm
        ((I : FractionalIdeal (𝓞 K)⁰ K).num :
          Ideal (𝓞 K)) : ℚ) : ℝ) * √|discr K| =
      (((absNorm
          ((I : FractionalIdeal (𝓞 K)⁰ K).num :
            Ideal (𝓞 K)) : ℚ) /
            |Algebra.norm ℤ d| : ℚ) : ℝ) *
        √|discr K| *
        ((|Algebra.norm ℚ
          (algebraMap (𝓞 K) K d)| : ℚ) : ℝ)
  rw [← hnorm]
  push_cast
  field_simp

open Classical in
theorem fractionalShapeCovolumeCenter_numerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    fractionalShapeCovolumeCenter K
        (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) =
      fractionalShapeCovolumeCenter K I -
        denominatorLogCoordinates K I w₀ := by
  have hfin : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hA := fractionalShapeCovolumeConstant_pos K I
  rw [fractionalShapeCovolumeCenter,
    fractionalShapeCovolumeCenter,
    fractionalShapeCovolumeConstant_numerator,
    Real.log_mul hA.ne' (Real.exp_ne_zero _),
    Real.log_exp]
  grind

open Classical in
theorem centeredNumeratorTranslation_apply_w₀
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    centeredNumeratorTranslation K I w₀ = 0 := by
  rw [centeredNumeratorTranslation]
  simp only [Pi.sub_apply, radialLogVector_apply_w₀]
  rw [fractionalShapeCovolumeCenter_numerator]
  ring

omit [IsTotallyComplex K] in
open Classical in
theorem centeredFractionalShapeCoordinates_numerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedEmbedding.realSpace K) :
    centeredFractionalShapeCoordinates K
        (FractionalIdeal.mk0 K (fractionalIdealNumerator K I))
        (y + centeredNumeratorTranslation K I) =
      centeredFractionalShapeCoordinates K I y -
        denominatorLogCoordinates K I := by
  rw [centeredFractionalShapeCoordinates,
    centeredFractionalShapeCoordinates,
    centeredNumeratorTranslation]
  grind

open Classical in
theorem centeredNonzeroFractionalShapeThetaMellinKernel_numerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    (y : mixedEmbedding.realSpace K) :
    centeredNonzeroFractionalShapeThetaMellinKernel K I s y =
      centeredNonzeroFractionalShapeThetaMellinKernel K
        (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) s
        (y + centeredNumeratorTranslation K I) := by
  rw [centeredNonzeroFractionalShapeThetaMellinKernel,
    centeredNonzeroFractionalShapeThetaMellinKernel]
  have hweight :
      logarithmicMellinWeight K s
          (y + centeredNumeratorTranslation K I) =
        logarithmicMellinWeight K s y := by
    rw [logarithmicMellinWeight, logarithmicMellinWeight]
    simp only [Pi.add_apply, centeredNumeratorTranslation_apply_w₀, add_zero]
  rw [hweight]
  congr 1
  rw [fractionalShapeIdealTheta_expMapBasis_eq_numerator]
  change
    shapeIdealTheta K (fractionalIdealNumerator K I)
        (expMapBasis
          (centeredFractionalShapeCoordinates K I y -
            denominatorLogCoordinates K I)) _ - 1 =
      shapeIdealTheta K (fractionalIdealNumerator K I)
        (expMapBasis
          (centeredFractionalShapeCoordinates K
            (FractionalIdeal.mk0 K (fractionalIdealNumerator K I))
            (y + centeredNumeratorTranslation K I))) _ - 1
  congr 2
  exact congrArg expMapBasis
    (centeredFractionalShapeCoordinates_numerator K I y).symm

open Classical in
theorem centeredPositiveClassThetaIntegral_eq_numerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    centeredPositiveClassThetaIntegral K I s =
      centeredPositiveClassThetaIntegral K
        (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) s := by
  rw [centeredPositiveClassThetaIntegral,
    centeredPositiveClassThetaIntegral]
  calc
    (∫ y in positiveUnitFundamentalParamSet (K := K),
        centeredNonzeroFractionalShapeThetaMellinKernel K I s y) =
        ∫ y in positiveUnitFundamentalParamSet (K := K),
          centeredNonzeroFractionalShapeThetaMellinKernel K
            (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) s
            (y + centeredNumeratorTranslation K I) := by
      apply setIntegral_congr_fun measurableSet_positiveUnitFundamentalParamSet
      intro y _
      exact centeredNonzeroFractionalShapeThetaMellinKernel_numerator K I s y
    _ = ∫ y in positiveUnitFundamentalParamSet (K := K),
          centeredNonzeroFractionalShapeThetaMellinKernel K
            (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) s y := by
      exact setIntegral_positiveUnitFundamentalParamSet_add_eq
        (centeredNonzeroFractionalShapeThetaMellinKernel K
          (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) s)
        (centeredNonzeroFractionalShapeThetaMellinKernel_vadd_unitCoordinateLattice
          K (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) s)
        (centeredNumeratorTranslation K I)
        (centeredNumeratorTranslation_apply_w₀ K I)

open Classical in
theorem setIntegral_centeredNonzeroFractionalShapeThetaMellinKernel_eq_numerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (∫ y in unitFundamentalParamSet K,
      centeredNonzeroFractionalShapeThetaMellinKernel K I s y) =
      ∫ y in unitFundamentalParamSet K,
        centeredNonzeroFractionalShapeThetaMellinKernel K
          (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) s y := by
  calc
    (∫ y in unitFundamentalParamSet K,
        centeredNonzeroFractionalShapeThetaMellinKernel K I s y) =
        ∫ y in unitFundamentalParamSet K,
          centeredNonzeroFractionalShapeThetaMellinKernel K
            (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) s
            (y + centeredNumeratorTranslation K I) := by
      apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
      intro y _
      exact centeredNonzeroFractionalShapeThetaMellinKernel_numerator K I s y
    _ = ∫ y in unitFundamentalParamSet K,
          centeredNonzeroFractionalShapeThetaMellinKernel K
            (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) s y := by
      exact setIntegral_unitFundamentalParamSet_add_eq
        (centeredNonzeroFractionalShapeThetaMellinKernel K
          (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) s)
        (centeredNonzeroFractionalShapeThetaMellinKernel_vadd_unitCoordinateLattice
          K (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)) s)
        (centeredNumeratorTranslation K I)

open Classical in
theorem integrableOn_centeredNonzeroFractionalShapeThetaMellinKernel
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (centeredNonzeroFractionalShapeThetaMellinKernel K I s)
      (unitFundamentalParamSet K) := by
  let J := fractionalIdealNumerator K I
  let f :=
    centeredNonzeroFractionalShapeThetaMellinKernel K
      (FractionalIdeal.mk0 K J) s
  have hf : IntegrableOn f (unitFundamentalParamSet K) :=
    integrableOn_centeredNonzeroFractionalShapeThetaMellinKernel_mk0 K J hs
  have hshift :
      IntegrableOn (fun y ↦ f (y + centeredNumeratorTranslation K I))
        (unitFundamentalParamSet K) :=
    (integrableOn_unitFundamentalParamSet_comp_add_iff f
      (centeredNonzeroFractionalShapeThetaMellinKernel_vadd_unitCoordinateLattice
        K (FractionalIdeal.mk0 K J) s)
      (centeredNumeratorTranslation K I)).mpr hf
  apply IntegrableOn.congr_fun hshift
    _ measurableSet_unitFundamentalParamSet
  intro y _
  exact
    (centeredNonzeroFractionalShapeThetaMellinKernel_numerator K I s y).symm

end NumberField.Odlyzko
