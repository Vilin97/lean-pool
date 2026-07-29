/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredIntegral

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

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
