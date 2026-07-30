/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredReflection
public import LeanPool.Odlyzko.CompletedZeta.ClassThetaIntegral

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

section

open Complex Ideal MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

omit [IsTotallyComplex K] in
open Classical in
theorem logarithmicMellinWeight_covolumeCenter
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    logarithmicMellinWeight K s
        (radialLogVector K (fractionalShapeCovolumeCenter K I)) =
      (fractionalShapeCovolumeConstant K I : ℂ) ^ (-s) := by
  have hfin : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hA := fractionalShapeCovolumeConstant_pos K I
  rw [logarithmicMellinWeight, radialLogVector_apply_w₀,
    fractionalShapeCovolumeCenter]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hA.ne')]
  rw [← Complex.ofReal_log hA.le]
  simp_all

open Classical in
theorem ofReal_sqrt_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (Real.sqrt x : ℂ) ^ s = (x : ℂ) ^ (s / 2) := by
  rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log (Real.sqrt_nonneg x),
    ← Complex.ofReal_log hx.le, Real.log_sqrt hx.le]
  push_cast
  ring_nf

omit [IsTotallyComplex K] in
open Classical in
theorem fractionalShapeCovolumeConstant_mk0_cpow
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    (fractionalShapeCovolumeConstant K
        (FractionalIdeal.mk0 K J) : ℂ) ^ s =
      CompletedZeta.discriminantFactor K s *
        (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ s := by
  rw [fractionalShapeCovolumeConstant,
    FractionalIdeal.coe_mk0,
    FractionalIdeal.coeIdeal_absNorm]
  push_cast
  change
    (((absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) *
        (Real.sqrt |(discr K : ℝ)| : ℂ)) ^ s =
      CompletedZeta.discriminantFactor K s *
        ((absNorm (J : Ideal (𝓞 K)) : ℝ) : ℂ) ^ s
  rw [Complex.mul_cpow_ofReal_nonneg
      (by positivity : 0 ≤ (absNorm (J : Ideal (𝓞 K)) : ℝ))
      (Real.sqrt_nonneg _),
    ofReal_sqrt_cpow (discr_abs_pos K),
    CompletedZeta.discriminantFactor]
  ring

omit [IsTotallyComplex K] in
open Classical in
theorem centeredNonzeroFractionalShapeThetaMellinKernel_eq_covolume_mul
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    (y : mixedEmbedding.realSpace K) :
    centeredNonzeroFractionalShapeThetaMellinKernel K I s y =
      (fractionalShapeCovolumeConstant K I : ℂ) ^ s *
        nonzeroFractionalShapeThetaMellinKernel K I s
          (centeredFractionalShapeCoordinates K I y) := by
  rw [centeredNonzeroFractionalShapeThetaMellinKernel,
    nonzeroFractionalShapeThetaMellinKernel]
  rw [show
      logarithmicMellinWeight K s
          (centeredFractionalShapeCoordinates K I y) =
        logarithmicMellinWeight K s y *
          logarithmicMellinWeight K s
            (radialLogVector K
              (fractionalShapeCovolumeCenter K I)) by
    simpa only [centeredFractionalShapeCoordinates, mul_comm] using
      logarithmicMellinWeight_add K s y
        (radialLogVector K (fractionalShapeCovolumeCenter K I))]
  rw [
    logarithmicMellinWeight_covolumeCenter,
    Complex.cpow_neg]
  have hpow :
      (fractionalShapeCovolumeConstant K I : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
      Complex.ofReal_ne_zero.mpr
        (fractionalShapeCovolumeConstant_pos K I).ne'
  grind

open Classical in
theorem nonzeroFractionalShapeThetaMellinKernel_vadd_unitCoordinateLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ)
    (g : unitCoordinateLattice (K := K))
    (y : mixedEmbedding.realSpace K) :
    nonzeroFractionalShapeThetaMellinKernel K I s
        ((g : mixedEmbedding.realSpace K) + y) =
      nonzeroFractionalShapeThetaMellinKernel K I s y := by
  rw [nonzeroFractionalShapeThetaMellinKernel,
    nonzeroFractionalShapeThetaMellinKernel,
    logarithmicMellinWeight_vadd_unitCoordinateLattice]
  congr 1
  obtain ⟨z, hz⟩ := g.prop
  rw [← hz]
  simpa only [unitCoordinateShiftHom_apply, add_comm] using
    congrArg (fun z : ℂ ↦ z - 1)
      (fractionalShapeIdealTheta_add_unitCoordinateShift K I y z)

open Classical in
theorem nonzeroFractionalShapeThetaMellinKernel_mk0
    (J : (Ideal (𝓞 K))⁰) (s : ℂ)
    (y : mixedEmbedding.realSpace K) :
    nonzeroFractionalShapeThetaMellinKernel K
        (FractionalIdeal.mk0 K J) s y =
      nonzeroShapeThetaMellinKernel K J s y :=
  by
    rw [nonzeroFractionalShapeThetaMellinKernel,
      nonzeroShapeThetaMellinKernel,
      nonzeroIdealShapeTheta_eq_shapeIdealTheta_sub_one]
    rfl

open Classical in
theorem setIntegral_centeredNonzeroFractionalShapeThetaMellinKernel
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (∫ y in unitFundamentalParamSet K,
      centeredNonzeroFractionalShapeThetaMellinKernel K I s y) =
        (fractionalShapeCovolumeConstant K I : ℂ) ^ s *
          ∫ y in unitFundamentalParamSet K,
            nonzeroFractionalShapeThetaMellinKernel K I s y := by
  calc
    (∫ y in unitFundamentalParamSet K,
        centeredNonzeroFractionalShapeThetaMellinKernel K I s y) =
        ∫ y in unitFundamentalParamSet K,
          (fractionalShapeCovolumeConstant K I : ℂ) ^ s *
            nonzeroFractionalShapeThetaMellinKernel K I s
              (y + radialLogVector K
                (fractionalShapeCovolumeCenter K I)) := by
      apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
      intro y _
      simpa only [centeredFractionalShapeCoordinates] using
        centeredNonzeroFractionalShapeThetaMellinKernel_eq_covolume_mul
          K I s y
    _ = (fractionalShapeCovolumeConstant K I : ℂ) ^ s *
          ∫ y in unitFundamentalParamSet K,
            nonzeroFractionalShapeThetaMellinKernel K I s
              (y + radialLogVector K
                (fractionalShapeCovolumeCenter K I)) := by
      rw [integral_const_mul]
    _ = (fractionalShapeCovolumeConstant K I : ℂ) ^ s *
          ∫ y in unitFundamentalParamSet K,
            nonzeroFractionalShapeThetaMellinKernel K I s y := by
      rw [setIntegral_unitFundamentalParamSet_add_eq
        (nonzeroFractionalShapeThetaMellinKernel K I s)
        (nonzeroFractionalShapeThetaMellinKernel_vadd_unitCoordinateLattice
          K I s)
        (radialLogVector K (fractionalShapeCovolumeCenter K I))]

open Classical in
theorem integrableOn_centeredNonzeroFractionalShapeThetaMellinKernel_mk0
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (centeredNonzeroFractionalShapeThetaMellinKernel K
        (FractionalIdeal.mk0 K J) s)
      (unitFundamentalParamSet K) := by
  have hraw :
      IntegrableOn
        (nonzeroFractionalShapeThetaMellinKernel K
          (FractionalIdeal.mk0 K J) s)
        (unitFundamentalParamSet K) := by
    apply IntegrableOn.congr_fun
      (integrableOn_nonzeroShapeThetaMellinKernel K J hs)
      _ measurableSet_unitFundamentalParamSet
    intro y _
    exact (nonzeroFractionalShapeThetaMellinKernel_mk0 K J s y).symm
  have hshift :
      IntegrableOn
        (fun y ↦
          nonzeroFractionalShapeThetaMellinKernel K
            (FractionalIdeal.mk0 K J) s
            (y + radialLogVector K
              (fractionalShapeCovolumeCenter K
                (FractionalIdeal.mk0 K J))))
        (unitFundamentalParamSet K) :=
    (integrableOn_unitFundamentalParamSet_comp_add_iff
      (nonzeroFractionalShapeThetaMellinKernel K
        (FractionalIdeal.mk0 K J) s)
      (nonzeroFractionalShapeThetaMellinKernel_vadd_unitCoordinateLattice
        K (FractionalIdeal.mk0 K J) s)
      (radialLogVector K
        (fractionalShapeCovolumeCenter K
          (FractionalIdeal.mk0 K J)))).mpr hraw
  apply IntegrableOn.congr_fun
    (hshift.const_mul
      ((fractionalShapeCovolumeConstant K
        (FractionalIdeal.mk0 K J) : ℂ) ^ s))
    _ measurableSet_unitFundamentalParamSet
  intro y _
  exact
    (centeredNonzeroFractionalShapeThetaMellinKernel_eq_covolume_mul
      K (FractionalIdeal.mk0 K J) s y).symm

open Classical in
/-- A centered class theta integral used in the Odlyzko-bound argument. -/
noncomputable def centeredClassThetaIntegral
    (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ *
    (2 : ℂ) ^ nrComplexPlaces K *
    (shapeThetaIntegralConstant K : ℂ) *
    ∫ y in unitFundamentalParamSet K,
      centeredNonzeroFractionalShapeThetaMellinKernel K
        (FractionalIdeal.mk0 K
          (inverseClassIdealRepresentative K C)) s y

open Classical in
theorem classCompletedThetaIntegral_eq_centered
    (C : ClassGroup (𝓞 K)) (s : ℂ) :
    classCompletedThetaIntegral K C s =
      centeredClassThetaIntegral K C s := by
  let J := inverseClassIdealRepresentative K C
  rw [classCompletedThetaIntegral, centeredClassThetaIntegral,
    setIntegral_centeredNonzeroFractionalShapeThetaMellinKernel,
    fractionalShapeCovolumeConstant_mk0_cpow]
  have hintegral :
      (∫ y in unitFundamentalParamSet K,
        ((shapeThetaIntegralConstant K : ℝ) : ℂ) *
          logarithmicMellinWeight K s y *
          nonzeroIdealShapeTheta K J y) =
        (shapeThetaIntegralConstant K : ℂ) *
          ∫ y in unitFundamentalParamSet K,
            nonzeroFractionalShapeThetaMellinKernel K
              (FractionalIdeal.mk0 K J) s y := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
    intro y _
    dsimp only
    rw [nonzeroFractionalShapeThetaMellinKernel_mk0]
    rw [nonzeroShapeThetaMellinKernel]
    ring
  grind

open Classical in
theorem sum_centeredClassThetaIntegral
    {s : ℂ} (hs : 1 < s.re) :
    ∑ C : ClassGroup (𝓞 K), centeredClassThetaIntegral K C s =
      CompletedZeta.completed K s := by
  rw [← sum_classCompletedThetaIntegral K hs]
  apply Finset.sum_congr rfl
  intro C _
  exact (classCompletedThetaIntegral_eq_centered K C s).symm

end NumberField.Odlyzko

end

section

open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A centered positive class theta integral used in the Odlyzko-bound argument. -/
noncomputable def centeredPositiveClassThetaIntegral
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  ∫ y in positiveUnitFundamentalParamSet (K := K),
    centeredNonzeroFractionalShapeThetaMellinKernel K I s y

open Classical in
/-- A centered class theta pole term used in the Odlyzko-bound argument. -/
noncomputable def centeredClassThetaPoleTerm (s : ℂ) : ℂ :=
  -1 / ((Module.finrank ℚ K : ℂ) * (1 - s)) -
    1 / ((Module.finrank ℚ K : ℂ) * s)

open Classical in
/-- A centered radially continued class theta integral used in the Odlyzko-bound argument. -/
noncomputable def centeredRadiallyContinuedClassThetaIntegral
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  centeredPositiveClassThetaIntegral K I s +
    centeredPositiveClassThetaIntegral K
      (traceDualIdealUnit K I) (1 - s) +
    centeredClassThetaPoleTerm K s

open Classical in
theorem setIntegral_negative_centeredNonzeroFractionalShapeThetaMellinKernel
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (∫ y in negativeUnitFundamentalParamSet (K := K),
      centeredNonzeroFractionalShapeThetaMellinKernel K I s y) =
      ∫ y in positiveUnitFundamentalParamSet (K := K),
        centeredNonzeroFractionalShapeThetaMellinKernel K
            (traceDualIdealUnit K I) (1 - s) y +
          centeredClassThetaPoissonCorrection K s y := by
  rw [setIntegral_negative_eq_positive_comp_neg
    (centeredNonzeroFractionalShapeThetaMellinKernel K I s)
    (centeredNonzeroFractionalShapeThetaMellinKernel_vadd_unitCoordinateLattice
      K I s)]
  apply setIntegral_congr_fun measurableSet_positiveUnitFundamentalParamSet
  intro y _
  exact centeredNonzeroFractionalShapeThetaMellinKernel_neg_poisson K I s y

omit [IsTotallyComplex K] in
open Classical in
theorem setIntegral_centeredClassThetaPoissonCorrection_eq_poleTerm
    {s : ℂ} (hs : 1 < s.re) :
    (∫ y in positiveUnitFundamentalParamSet (K := K),
      centeredClassThetaPoissonCorrection K s y) =
        centeredClassThetaPoleTerm K s := by
  rw [setIntegral_centeredClassThetaPoissonCorrection K hs,
    centeredClassThetaPoleTerm]

open Classical in
theorem setIntegral_centered_eq_radiallyContinued_mk0
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    (∫ y in unitFundamentalParamSet K,
      centeredNonzeroFractionalShapeThetaMellinKernel K
        (FractionalIdeal.mk0 K J) s y) =
      centeredRadiallyContinuedClassThetaIntegral K
        (FractionalIdeal.mk0 K J) s := by
  let I := FractionalIdeal.mk0 K J
  let f :=
    centeredNonzeroFractionalShapeThetaMellinKernel K I s
  let g :=
    centeredNonzeroFractionalShapeThetaMellinKernel K
      (traceDualIdealUnit K I) (1 - s)
  let c := centeredClassThetaPoissonCorrection K s
  have hf :
      IntegrableOn f (unitFundamentalParamSet K) :=
    integrableOn_centeredNonzeroFractionalShapeThetaMellinKernel_mk0 K J hs
  have hreflect :
      IntegrableOn (fun y ↦ f (-y))
        (positiveUnitFundamentalParamSet (K := K)) :=
    (integrableOn_negative_iff_positive_comp_neg f
      (centeredNonzeroFractionalShapeThetaMellinKernel_vadd_unitCoordinateLattice
        K I s)).mp
      (hf.mono_set Set.inter_subset_left)
  have hgc :
      IntegrableOn (fun y ↦ g y + c y)
        (positiveUnitFundamentalParamSet (K := K)) := by
    apply IntegrableOn.congr_fun hreflect
      _ measurableSet_positiveUnitFundamentalParamSet
    intro y _
    exact
      (centeredNonzeroFractionalShapeThetaMellinKernel_neg_poisson
        K I s y)
  have hc :
      IntegrableOn c (positiveUnitFundamentalParamSet (K := K)) :=
    integrableOn_centeredClassThetaPoissonCorrection K hs
  have hg :
      IntegrableOn g (positiveUnitFundamentalParamSet (K := K)) := by
    apply IntegrableOn.congr_fun (hgc.sub hc)
      _ measurableSet_positiveUnitFundamentalParamSet
    intro y _
    simp
  calc
    (∫ y in unitFundamentalParamSet K,
        centeredNonzeroFractionalShapeThetaMellinKernel K I s y) =
        (∫ y in positiveUnitFundamentalParamSet (K := K), f y) +
          ∫ y in negativeUnitFundamentalParamSet (K := K), f y := by
      exact setIntegral_unitFundamentalParamSet_eq_add_openRadialHalves f hf
    _ = (∫ y in positiveUnitFundamentalParamSet (K := K), f y) +
          ∫ y in positiveUnitFundamentalParamSet (K := K),
            g y + c y := by
      rw [setIntegral_negative_centeredNonzeroFractionalShapeThetaMellinKernel]
    _ = (∫ y in positiveUnitFundamentalParamSet (K := K), f y) +
          (∫ y in positiveUnitFundamentalParamSet (K := K), g y) +
          ∫ y in positiveUnitFundamentalParamSet (K := K), c y := by
      rw [integral_add hg hc]
      ring
    _ = centeredRadiallyContinuedClassThetaIntegral K I s := by
      rw [setIntegral_centeredClassThetaPoissonCorrection_eq_poleTerm K hs]
      rfl

open Classical in
/-- A centered continued class theta integral used in the Odlyzko-bound argument. -/
noncomputable def centeredContinuedClassThetaIntegral
    (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ *
    (2 : ℂ) ^ nrComplexPlaces K *
    (shapeThetaIntegralConstant K : ℂ) *
    centeredRadiallyContinuedClassThetaIntegral K
      (FractionalIdeal.mk0 K
        (inverseClassIdealRepresentative K C)) s

open Classical in
theorem centeredClassThetaIntegral_eq_continued
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    centeredClassThetaIntegral K C s =
      centeredContinuedClassThetaIntegral K C s := by
  rw [centeredClassThetaIntegral, centeredContinuedClassThetaIntegral,
    setIntegral_centered_eq_radiallyContinued_mk0 K
      (inverseClassIdealRepresentative K C) hs]

open Classical in
theorem sum_centeredContinuedClassThetaIntegral
    {s : ℂ} (hs : 1 < s.re) :
    ∑ C : ClassGroup (𝓞 K),
      centeredContinuedClassThetaIntegral K C s =
        CompletedZeta.completed K s := by
  rw [← sum_centeredClassThetaIntegral K hs]
  apply Finset.sum_congr rfl
  intro C _
  exact (centeredClassThetaIntegral_eq_continued K C hs).symm

end NumberField.Odlyzko

end
