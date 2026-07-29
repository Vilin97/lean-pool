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
