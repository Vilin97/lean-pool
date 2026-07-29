/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.IdealElementDecomposition

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain MeasureTheory NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
theorem hasSum_integral_norm_radialMellinGaussian_unitSlab
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J)
    {s : ℂ} (hs : 0 < s.re) :
    HasSum
      (fun z : unitShiftIndex K ↦
        ∫ y in unitFundamentalParamSet K,
          ‖radialMellinGaussian K
            ((((fundamentalUnitForShift z : (𝓞 K)ˣ) : 𝓞 K) : K) *
              idealSetElement K J a)
            s y‖)
      (∫ y : realSpace K,
        ‖radialMellinGaussian K (idealSetElement K J a) s y‖) := by
  let f : realSpace K → ℝ := fun y ↦
    ‖radialMellinGaussian K (idealSetElement K J a) s y‖
  have hf : Integrable f :=
    (integrable_complexPlaceRadialJacobian_smul_mellinGaussian K
      (idealSetElement_ne_zero K J a) hs).norm
  have hpartition :=
    hasSum_integral_iUnion
      (f := f)
      (fun z : unitShiftIndex K ↦
        measurableSet_unitFundamentalTranslate z)
      pairwise_disjoint_unitFundamentalTranslate
      (by
        rw [iUnion_unitFundamentalTranslate]
        simpa only [integrableOn_univ] using hf)
  have hpartition' :
      HasSum
        (fun z : unitShiftIndex K ↦
          ∫ y in unitFundamentalTranslate z, f y)
        (∫ y, f y) := by
    simpa only [iUnion_unitFundamentalTranslate, setIntegral_univ] using
      hpartition
  refine hpartition'.congr_fun fun z ↦ ?_
  rw [setIntegral_unitFundamentalTranslate f z]
  apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
  intro y _
  change
    ‖radialMellinGaussian K
        ((((fundamentalUnitForShift z : (𝓞 K)ˣ) : 𝓞 K) : K) *
          idealSetElement K J a) s y‖ =
      ‖radialMellinGaussian K (idealSetElement K J a) s
        (y + unitCoordinateShift z)‖
  rw [radialMellinGaussian_add_unitCoordinateShift]

open Classical in
theorem summable_prod_integral_norm_radialMellinGaussian_unitSlab
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun p : idealSet K J × unitShiftIndex K ↦
        ∫ y in unitFundamentalParamSet K,
          ‖radialMellinGaussian K
            ((((fundamentalUnitForShift p.2 : (𝓞 K)ˣ) : 𝓞 K) : K) *
              idealSetElement K J p.1)
            s y‖) := by
  apply (summable_prod_of_nonneg fun _ ↦
    integral_nonneg fun _ ↦ norm_nonneg _).mpr
  constructor
  · intro a
    exact (hasSum_integral_norm_radialMellinGaussian_unitSlab
      K J a (lt_trans zero_lt_one hs)).summable
  · refine (summable_integral_norm_idealSet_complexPlaceMellinGaussian
      K J hs).congr fun a ↦ ?_
    rw [(hasSum_integral_norm_radialMellinGaussian_unitSlab
      K J a (lt_trans zero_lt_one hs)).tsum_eq,
      integral_norm_radialMellinGaussian]

open Classical in
theorem summable_prod_integral_radialMellinGaussian_unitSlab
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun p : idealSet K J × unitShiftIndex K ↦
        ∫ y in unitFundamentalParamSet K,
          radialMellinGaussian K
            ((((fundamentalUnitForShift p.2 : (𝓞 K)ˣ) : 𝓞 K) : K) *
              idealSetElement K J p.1)
            s y) := by
  apply Summable.of_norm_bounded
    (summable_prod_integral_norm_radialMellinGaussian_unitSlab K J hs)
  intro p
  exact norm_integral_le_integral_norm _

open Classical in
theorem fundamentalConeZeta_eq_tsum_nonzeroIdealElement_radialIntegral
    (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    ((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^ nrComplexPlaces K *
        fundamentalConeZeta K J s =
      ∑' x : nonzeroIdealElement K J,
        ∫ y in unitFundamentalParamSet K,
          radialMellinGaussian K (((x : 𝓞 K) : K)) s y := by
  let F : idealSet K J × unitShiftIndex K → ℂ := fun p ↦
    ∫ y in unitFundamentalParamSet K,
      radialMellinGaussian K
        ((((fundamentalUnitForShift p.2 : (𝓞 K)ˣ) : 𝓞 K) : K) *
          idealSetElement K J p.1)
        s y
  have hF : Summable F :=
    summable_prod_integral_radialMellinGaussian_unitSlab K J hs
  calc
    ((2 : ℂ)⁻¹ * CompletedZeta.complexPlaceGammaFactor s) ^ nrComplexPlaces K *
          fundamentalConeZeta K J s =
        ∑' a : idealSet K J,
          ∫ q : InfinitePlace K → ℝ,
            complexPlaceMellinGaussian K (idealSetElement K J a) s q
            ∂Measure.pi (fun _ ↦ volume.restrict (Set.Ioi 0)) :=
      (hasSum_integral_idealSet_complexPlaceMellinGaussian K J hs).tsum_eq.symm
    _ = ∑' a : idealSet K J,
          ∫ y : realSpace K,
            radialMellinGaussian K (idealSetElement K J a) s y := by
      apply tsum_congr
      intro a
      exact integral_complexPlaceMellinGaussian_eq_expMapBasis
        K (idealSetElement K J a) s
    _ = ∑' a : idealSet K J,
          ∑' z : unitShiftIndex K, F (a, z) := by
      apply tsum_congr
      intro a
      exact integral_radialMellinGaussian_eq_tsum_unitSlab K
        (idealSetElement_ne_zero K J a) (lt_trans zero_lt_one hs)
    _ = ∑' p : idealSet K J × unitShiftIndex K, F p :=
      hF.tsum_prod.symm
    _ = ∑' x : nonzeroIdealElement K J,
          ∫ y in unitFundamentalParamSet K,
            radialMellinGaussian K (((x : 𝓞 K) : K)) s y := by
      let G : nonzeroIdealElement K J → ℂ := fun x ↦
        ∫ y in unitFundamentalParamSet K,
          radialMellinGaussian K (((x : 𝓞 K) : K)) s y
      rw [← (idealElementMulDecompositionEquiv K J).tsum_eq G]
      apply tsum_congr
      intro p
      apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
      intro y _
      rw [idealElementMulDecompositionEquiv_coe]

end NumberField.Odlyzko
