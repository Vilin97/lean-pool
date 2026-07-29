/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredHolomorphy

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

section

open Complex Ideal MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
theorem setIntegral_centered_eq_radiallyContinued
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    (∫ y in unitFundamentalParamSet K,
      centeredNonzeroFractionalShapeThetaMellinKernel K I s y) =
      centeredRadiallyContinuedClassThetaIntegral K I s := by
  let f := centeredNonzeroFractionalShapeThetaMellinKernel K I s
  let g :=
    centeredNonzeroFractionalShapeThetaMellinKernel K
      (traceDualIdealUnit K I) (1 - s)
  let c := centeredClassThetaPoissonCorrection K s
  have hf : IntegrableOn f (unitFundamentalParamSet K) :=
    integrableOn_centeredNonzeroFractionalShapeThetaMellinKernel K I hs
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

end NumberField.Odlyzko

end

section

open Complex Filter Ideal MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors Topology

namespace NumberField.Odlyzko

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- An ideal completed theta integral used in the Odlyzko-bound argument. -/
noncomputable def idealCompletedThetaIntegral
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  CompletedZeta.discriminantFactor K s *
    (torsionOrder K : ℂ)⁻¹ *
    (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ s *
    ((2 : ℂ) ^ nrComplexPlaces K *
      ∫ y in unitFundamentalParamSet K,
        ((shapeThetaIntegralConstant K : ℝ) : ℂ) *
          logarithmicMellinWeight K s y *
          nonzeroIdealShapeTheta K J y)

open Classical in
theorem idealCompletedThetaIntegral_eq_fundamentalConeZeta
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    idealCompletedThetaIntegral K J s =
      CompletedZeta.discriminantFactor K s *
        (torsionOrder K : ℂ)⁻¹ *
        (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ s *
        (CompletedZeta.complexPlaceGammaFactor s ^ nrComplexPlaces K *
          fundamentalConeZeta K J s) := by
  rw [idealCompletedThetaIntegral]
  congr 1
  have hcone :=
    fundamentalConeZeta_eq_integral_nonzeroIdealShapeTheta K J hs
  calc
    (2 : ℂ) ^ nrComplexPlaces K *
          (∫ y in unitFundamentalParamSet K,
            ((shapeThetaIntegralConstant K : ℝ) : ℂ) *
              logarithmicMellinWeight K s y *
              nonzeroIdealShapeTheta K J y) =
        (2 : ℂ) ^ nrComplexPlaces K *
          (((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^
              nrComplexPlaces K * fundamentalConeZeta K J s) := by
      congr 1
      symm
      simpa only [shapeThetaIntegralConstant, logarithmicMellinWeight,
        mul_assoc] using hcone
    _ = CompletedZeta.complexPlaceGammaFactor s ^ nrComplexPlaces K *
          fundamentalConeZeta K J s := by
      rw [← mul_assoc, ← mul_pow]
      simp

open Classical in
theorem idealCompletedThetaIntegral_eq_centered
    (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    idealCompletedThetaIntegral K J s =
      (torsionOrder K : ℂ)⁻¹ *
        (2 : ℂ) ^ nrComplexPlaces K *
        (shapeThetaIntegralConstant K : ℂ) *
        ∫ y in unitFundamentalParamSet K,
          centeredNonzeroFractionalShapeThetaMellinKernel K
            (FractionalIdeal.mk0 K J) s y := by
  rw [idealCompletedThetaIntegral,
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
/-- A centered fractional class contribution used in the Odlyzko-bound argument. -/
noncomputable def centeredFractionalClassContribution
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ *
    (2 : ℂ) ^ nrComplexPlaces K *
    (shapeThetaIntegralConstant K : ℂ) *
    centeredRadiallyContinuedClassThetaIntegral K I s

open Classical in
theorem centeredFractionalClassContribution_eq_partialDedekindZeta
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (C : ClassGroup (𝓞 K)) (hI : ClassGroup.mk K I = C⁻¹)
    {s : ℂ} (hs : 1 < s.re) :
    centeredFractionalClassContribution K I s =
      CompletedZeta.discriminantFactor K s *
        CompletedZeta.complexPlaceGammaFactor s ^ nrComplexPlaces K *
        partialDedekindZeta K C s := by
  let J := fractionalIdealNumerator K I
  have hJ : ClassGroup.mk0 J = C⁻¹ := by
    rw [mk0_fractionalIdealNumerator K I, hI]
  rw [centeredFractionalClassContribution,
    ← setIntegral_centered_eq_radiallyContinued K I hs,
    setIntegral_centeredNonzeroFractionalShapeThetaMellinKernel_eq_numerator]
  rw [← idealCompletedThetaIntegral_eq_centered K J s,
    idealCompletedThetaIntegral_eq_fundamentalConeZeta K J hs,
    partialDedekindZeta_eq_normalized_fundamentalConeZeta_of_mk0
      K C J hJ hs]
  ring

open Classical in
/-- A pole cleared centered fractional class contribution used in the Odlyzko-bound argument. -/
noncomputable def poleClearedCenteredFractionalClassContribution
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  (torsionOrder K : ℂ)⁻¹ *
    (2 : ℂ) ^ nrComplexPlaces K *
    (shapeThetaIntegralConstant K : ℂ) *
    poleClearedCenteredClassThetaIntegral K I s

open Classical in
theorem differentiable_poleClearedCenteredFractionalClassContribution
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Differentiable ℂ (poleClearedCenteredFractionalClassContribution K I) := by
  have h := differentiable_poleClearedCenteredClassThetaIntegral K I
  unfold poleClearedCenteredFractionalClassContribution
  simp_all

open Classical in
theorem poleClearedCenteredFractionalClassContribution_eq_of_mk_eq_of_one_lt_re
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hIJ : ClassGroup.mk K I = ClassGroup.mk K J)
    {s : ℂ} (hs : 1 < s.re) :
    poleClearedCenteredFractionalClassContribution K I s =
      poleClearedCenteredFractionalClassContribution K J s := by
  let C : ClassGroup (𝓞 K) := (ClassGroup.mk K I)⁻¹
  have hIC : ClassGroup.mk K I = C⁻¹ := by simp [C]
  have hJC : ClassGroup.mk K J = C⁻¹ := by simp_all
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    simp_all
  have hI :=
    centeredFractionalClassContribution_eq_partialDedekindZeta
      K I C hIC hs
  have hJ :=
    centeredFractionalClassContribution_eq_partialDedekindZeta
      K J C hJC hs
  rw [poleClearedCenteredFractionalClassContribution,
    poleClearedCenteredFractionalClassContribution,
    poleClearedCenteredClassThetaIntegral_eq_mul_continued K I hs0 hs1,
    poleClearedCenteredClassThetaIntegral_eq_mul_continued K J hs0 hs1,
    centeredFractionalClassContribution] at *
  grind

open Classical in
theorem poleClearedCenteredFractionalClassContribution_eq_of_mk_eq
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hIJ : ClassGroup.mk K I = ClassGroup.mk K J) :
    poleClearedCenteredFractionalClassContribution K I =
      poleClearedCenteredFractionalClassContribution K J := by
  have hI :
      AnalyticOnNhd ℂ
        (poleClearedCenteredFractionalClassContribution K I) Set.univ :=
    DifferentiableOn.analyticOnNhd
      (differentiable_poleClearedCenteredFractionalClassContribution K I).differentiableOn
      isOpen_univ
  have hJ :
      AnalyticOnNhd ℂ
        (poleClearedCenteredFractionalClassContribution K J) Set.univ :=
    DifferentiableOn.analyticOnNhd
      (differentiable_poleClearedCenteredFractionalClassContribution K J).differentiableOn
      isOpen_univ
  have hright :
      {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
  apply hI.eq_of_eventuallyEq hJ
  filter_upwards [hright] with s hs
  exact
    poleClearedCenteredFractionalClassContribution_eq_of_mk_eq_of_one_lt_re
      K I J hIJ hs

end NumberField.Odlyzko

end

section

open Complex Ideal NumberField NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

omit [IsTotallyComplex K] in
open Classical in
theorem poleClearedCenteredClassThetaIntegral_functionalEquation
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    poleClearedCenteredClassThetaIntegral K I s =
      poleClearedCenteredClassThetaIntegral K
        (traceDualIdealUnit K I) (1 - s) := by
  rw [poleClearedCenteredClassThetaIntegral,
    poleClearedCenteredClassThetaIntegral,
    traceDualIdealUnit_traceDualIdealUnit]
  ring_nf

omit [IsTotallyComplex K] in
open Classical in
theorem poleClearedCenteredFractionalClassContribution_functionalEquation
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    poleClearedCenteredFractionalClassContribution K I s =
      poleClearedCenteredFractionalClassContribution K
        (traceDualIdealUnit K I) (1 - s) := by
  rw [poleClearedCenteredFractionalClassContribution,
    poleClearedCenteredFractionalClassContribution,
    poleClearedCenteredClassThetaIntegral_functionalEquation]

open Classical in
/-- A pole cleared completed dedekind zeta continuation used in the Odlyzko-bound argument. -/
noncomputable def poleClearedCompletedDedekindZetaContinuation (s : ℂ) : ℂ :=
  ∑ C : ClassGroup (𝓞 K),
    poleClearedCenteredFractionalClassContribution K
      (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) s

open Classical in
theorem differentiable_poleClearedCompletedDedekindZetaContinuation :
    Differentiable ℂ (poleClearedCompletedDedekindZetaContinuation K) := by
  unfold poleClearedCompletedDedekindZetaContinuation
  apply Differentiable.fun_sum
  intro C _
  exact differentiable_poleClearedCenteredFractionalClassContribution K
    (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))

omit [IsTotallyComplex K] in
open Classical in
theorem mk_traceDual_inverseClassIdealRepresentative_eq_reindexed
    (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk K
        (traceDualIdealUnit K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))) =
      ClassGroup.mk K
        (FractionalIdeal.mk0 K
          (inverseClassIdealRepresentative K
            (traceDualInverseClassEquiv K C))) := by
  rw [mk_traceDualIdealUnit_eq_traceDualClassEquiv,
    ClassGroup.mk_mk0, ClassGroup.mk_mk0,
    mk0_inverseClassIdealRepresentative,
    mk0_inverseClassIdealRepresentative,
    traceDualInverseClassEquiv_apply, inv_inv]

open Classical in
theorem poleClearedCompletedDedekindZetaContinuation_functionalEquation
    (s : ℂ) :
    poleClearedCompletedDedekindZetaContinuation K s =
      poleClearedCompletedDedekindZetaContinuation K (1 - s) := by
  rw [poleClearedCompletedDedekindZetaContinuation,
    poleClearedCompletedDedekindZetaContinuation]
  calc
    (∑ C : ClassGroup (𝓞 K),
        poleClearedCenteredFractionalClassContribution K
          (FractionalIdeal.mk0 K
            (inverseClassIdealRepresentative K C)) s) =
        ∑ C : ClassGroup (𝓞 K),
          poleClearedCenteredFractionalClassContribution K
            (traceDualIdealUnit K
              (FractionalIdeal.mk0 K
                (inverseClassIdealRepresentative K C))) (1 - s) := by
      apply Finset.sum_congr rfl
      intro C _
      exact
        poleClearedCenteredFractionalClassContribution_functionalEquation K
          (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) s
    _ = ∑ C : ClassGroup (𝓞 K),
          poleClearedCenteredFractionalClassContribution K
            (FractionalIdeal.mk0 K
              (inverseClassIdealRepresentative K
                (traceDualInverseClassEquiv K C))) (1 - s) := by
      apply Finset.sum_congr rfl
      intro C _
      exact congrFun
        (poleClearedCenteredFractionalClassContribution_eq_of_mk_eq K
          (traceDualIdealUnit K
            (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)))
          (FractionalIdeal.mk0 K
            (inverseClassIdealRepresentative K
              (traceDualInverseClassEquiv K C)))
          (mk_traceDual_inverseClassIdealRepresentative_eq_reindexed K C))
        (1 - s)
    _ = ∑ C : ClassGroup (𝓞 K),
          poleClearedCenteredFractionalClassContribution K
            (FractionalIdeal.mk0 K
              (inverseClassIdealRepresentative K C)) (1 - s) := by
      exact Equiv.sum_comp (traceDualInverseClassEquiv K)
        (fun C ↦ poleClearedCenteredFractionalClassContribution K
          (FractionalIdeal.mk0 K
            (inverseClassIdealRepresentative K C)) (1 - s))

open Classical in
theorem poleClearedCompletedDedekindZetaContinuation_eq_completedDedekindZeta
    {s : ℂ} (hs : 1 < s.re) :
    poleClearedCompletedDedekindZetaContinuation K s =
      (Module.finrank ℚ K : ℂ) * s * (1 - s) *
        CompletedZeta.completed K s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    simp_all
  rw [poleClearedCompletedDedekindZetaContinuation]
  calc
    (∑ C : ClassGroup (𝓞 K),
        poleClearedCenteredFractionalClassContribution K
          (FractionalIdeal.mk0 K
            (inverseClassIdealRepresentative K C)) s) =
        ∑ C : ClassGroup (𝓞 K),
          (Module.finrank ℚ K : ℂ) * s * (1 - s) *
            centeredContinuedClassThetaIntegral K C s := by
      apply Finset.sum_congr rfl
      intro C _
      rw [poleClearedCenteredFractionalClassContribution,
        poleClearedCenteredClassThetaIntegral_eq_mul_continued K _ hs0 hs1,
        centeredContinuedClassThetaIntegral]
      ring
    _ = (Module.finrank ℚ K : ℂ) * s * (1 - s) *
          ∑ C : ClassGroup (𝓞 K),
            centeredContinuedClassThetaIntegral K C s := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_centeredContinuedClassThetaIntegral K hs]

end NumberField.Odlyzko

end
