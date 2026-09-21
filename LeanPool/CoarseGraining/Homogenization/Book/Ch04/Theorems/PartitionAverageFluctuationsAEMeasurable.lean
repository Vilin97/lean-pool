/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.DescendantAveragesAEMeasurable
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageFluctuations

/-! # Partition Average Fluctuations AEMeasurable -/

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Restriction-local Gamma partition fluctuations

This is the a.e.-restriction-local counterpart of the Gamma partition fluctuation
estimate.  It is designed for totalized Ch4 observables which are only
a.e.-equal to local representatives on each descendant cube.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

theorem isBigO_gammaSigma_restrictionCenteredDescendantAverageOnCube_of_restrictionUnitRangeDependentLaw_of_ae_eq_local
    {d : ℕ} {Q : TriadicCube d} {n : ℤ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {σ K : ℝ}
    (hP : RestrictionLawCarrier P)
    (hn : 0 ≤ n) (hnQ : n ≤ Q.scale)
    (hPstat : RestrictionStationaryLaw P) (hPdep : RestrictionUnitRangeDependentLaw P)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_localRep :
      ∀ R ∈ descendantsAtScale Q n,
        ∃ Y : RegCoeffField d → ℝ,
          IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) Y ∧ X (cubeSet R) =ᵐ[P] Y)
    (hX_cov : IsRestrictionTranslationCovariant X)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hX_desc_aemeas :
      ∀ R ∈ descendantsAtScale Q n, AEMeasurable (X (cubeSet R)) P)
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2) (hK : 0 < K)
    (hX0 : IsBigO P (gammaSigma σ) (restrictionCenteredOriginObservable P n X) K) :
    IsBigO P (gammaSigma σ) (restrictionCenteredDescendantAverageOnCube P Q n X)
      (gammaSigmaDescendantsAtScaleConst d n σ *
        (Real.sqrt ((descendantsAtScale Q n).card : ℝ) /
          ((descendantsAtScale Q n).card : ℝ)) * K) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtScale Q n
  let μ0 : ℝ := ∫ a, X (cubeSet (originCube d n)) a ∂P
  let Y : Set (Vec d) → RegCoeffField d → ℝ := fun U a => X U a - μ0
  let Yrep : TriadicCube d → RegCoeffField d → ℝ :=
    fun R =>
      if hR : R ∈ D then Classical.choose (hX_localRep R (by simpa [D] using hR))
      else fun _a => 0
  let Zraw : TriadicCube d → RegCoeffField d → ℝ := fun R a => X (cubeSet R) a - μ0
  let Z : TriadicCube d → RegCoeffField d → ℝ := fun R a => Yrep R a - μ0
  have hY_cov : IsRestrictionTranslationCovariant Y := by
    intro U z a
    simpa [Y] using congrArg (fun x : ℝ => x - μ0) (hX_cov U z a)
  have hY0_aemeas : AEMeasurable (Y (cubeSet (originCube d n))) P := by
    simpa [Y] using! hX0_aemeas.sub measurable_const.aemeasurable
  have hYrep_local :
      ∀ R ∈ D, IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (Yrep R) := by
    intro R hR
    dsimp [Yrep]
    rw [dif_pos hR]
    exact (Classical.choose_spec (hX_localRep R (by simpa [D] using hR))).1
  have hX_eq_Yrep :
      ∀ R ∈ D, X (cubeSet R) =ᵐ[P] Yrep R := by
    intro R hR
    dsimp [Yrep]
    rw [dif_pos hR]
    exact (Classical.choose_spec (hX_localRep R (by simpa [D] using hR))).2
  have hZraw_eq_Z :
      ∀ R ∈ D, Zraw R =ᵐ[P] Z R := by
    intro R hR
    filter_upwards [hX_eq_Yrep R hR] with a ha
    simp [Zraw, Z, ha]
  have hZ_local :
      ∀ R ∈ D, IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (Z R) := by
    intro R hR
    simpa [Z] using (hYrep_local R hR).sub measurable_const
  have hZ_aemeas :
      ∀ R ∈ D, AEMeasurable (Z R) P := by
    intro R hR
    exact hP.aemeasurable_of_isLocalRandomVariable (hZ_local R hR)
  have hZ_tail :
      ∀ R ∈ D, IsBigO P (gammaSigma σ) (Z R) K := by
    intro R hR
    have hscaleR : R.scale = n := by
      calc
        R.scale = Q.scale - Int.toNat (Q.scale - n) := by
          exact scale_eq_sub_of_mem_descendantsAtScale (Q := Q) hnQ (by simpa [D] using hR)
        _ = n := by
              rw [Int.toNat_of_nonneg (sub_nonneg.mpr hnQ)]
              ring
    have hshift :
        cubeSet R =
          translateSet (intVecToRealVec (scaleTranslationShift n R))
            (cubeSet (originCube d n)) := by
      have hscale_nonneg : 0 ≤ R.scale := by
        simpa [hscaleR] using hn
      calc
        cubeSet R =
            translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
              (cubeSet (originCube d R.scale)) :=
          cubeSet_eq_translateSet_originCube_of_nonneg_scale hscale_nonneg
        _ =
            translateSet (intVecToRealVec (scaleTranslationShift n R))
              (cubeSet (originCube d n)) := by
              simp [hscaleR]
    have hYR_aemeas : AEMeasurable (Y (cubeSet R)) P := by
      simpa [Y] using!
        (hX_desc_aemeas R (by simpa [D] using hR)).sub measurable_const.aemeasurable
    have hmap :
        Measure.map (Y (cubeSet R)) P =
          Measure.map (Y (cubeSet (originCube d n))) P := by
      calc
        Measure.map (Y (cubeSet R)) P =
            Measure.map
              (Y
                (translateSet (intVecToRealVec (scaleTranslationShift n R))
                  (cubeSet (originCube d n)))) P := by
              rw [hshift]
        _ = Measure.map (Y (cubeSet (originCube d n))) P := by
              exact map_eq_map_translateReg_of_isRestrictionTranslationCovariant_aemeasurable
                (P := P) hPstat (U := cubeSet (originCube d n)) hY0_aemeas hY_cov
                (scaleTranslationShift n R)
    have hraw :
        IsBigO P (gammaSigma σ) (Zraw R) K := by
      have horigin :
          IsBigO P (gammaSigma σ) (Y (cubeSet (originCube d n))) K := by
        simpa [Y, μ0, restrictionCenteredOriginObservable] using! hX0
      have htail :=
        (isBigO_gammaSigma_iff_of_map_eq_map_aemeasurable
          (μ := P) (σ := σ) (A := K)
          hYR_aemeas hY0_aemeas hmap).2 horigin
      simpa [Zraw, Y] using htail
    exact (isBigO_congr_ae (μ := P) (Ψ := gammaSigma σ) (A := K)
      (hZraw_eq_Z R hR)).1 hraw
  have hY0_int : Integrable (Y (cubeSet (originCube d n))) P := by
    have hY0_tail :
        IsBigO P (gammaSigma σ) (Y (cubeSet (originCube d n))) K := by
      simpa [Y, μ0, restrictionCenteredOriginObservable] using! hX0
    have hY0_mom :=
      hasGammaMomentGrowthWith_of_isBigO_gammaSigma
        (μ := P) (X := Y (cubeSet (originCube d n))) (K := K) (σ := σ)
        hσ₀ hK hY0_aemeas hY0_tail
    have hY0_abs_int : Integrable (fun a => |Y (cubeSet (originCube d n)) a|) P := by
      simpa using
        (IndependentSums.gammaMomentGrowth_natCast_bound
          (μ := P) (X := Y (cubeSet (originCube d n))) (σ := σ)
          (M := gammaMomentConst σ * K) (n := 1) (by norm_num) hY0_mom).1
    have hY0_norm_int : Integrable (fun a => ‖Y (cubeSet (originCube d n)) a‖) P := by
      simpa [Real.norm_eq_abs] using hY0_abs_int
    exact
      (integrable_norm_iff hY0_aemeas.aestronglyMeasurable).1 hY0_norm_int
  have hX0_int : Integrable (X (cubeSet (originCube d n))) P := by
    have hX0_eq :
        (fun a => X (cubeSet (originCube d n)) a) =
          fun a => Y (cubeSet (originCube d n)) a + μ0 := by
      funext a
      simp [Y, μ0]
    simpa [hX0_eq] using hY0_int.add (integrable_const μ0)
  have hY0_mean : ∫ a, Y (cubeSet (originCube d n)) a ∂P = 0 := by
    calc
      ∫ a, Y (cubeSet (originCube d n)) a ∂P =
          ∫ a, X (cubeSet (originCube d n)) a ∂P - ∫ _a, μ0 ∂P := by
            simpa [Y] using integral_sub hX0_int (integrable_const μ0)
      _ = μ0 - μ0 := by simp [μ0]
      _ = 0 := by ring
  have hZraw_mean :
      ∀ R ∈ D, ∫ a, Zraw R a ∂P = 0 := by
    intro R hR
    have hscaleR : R.scale = n := by
      calc
        R.scale = Q.scale - Int.toNat (Q.scale - n) := by
          exact scale_eq_sub_of_mem_descendantsAtScale (Q := Q) hnQ (by simpa [D] using hR)
        _ = n := by
              rw [Int.toNat_of_nonneg (sub_nonneg.mpr hnQ)]
              ring
    have hshift :
        cubeSet R =
          translateSet (intVecToRealVec (scaleTranslationShift n R))
            (cubeSet (originCube d n)) := by
      have hscale_nonneg : 0 ≤ R.scale := by
        simpa [hscaleR] using hn
      calc
        cubeSet R =
            translateSet (intVecToRealVec (scaleTranslationShift R.scale R))
              (cubeSet (originCube d R.scale)) :=
          cubeSet_eq_translateSet_originCube_of_nonneg_scale hscale_nonneg
        _ =
            translateSet (intVecToRealVec (scaleTranslationShift n R))
              (cubeSet (originCube d n)) := by
              simp [hscaleR]
    have hint :
        ∫ a, Y (cubeSet R) a ∂P =
          ∫ a, Y (cubeSet (originCube d n)) a ∂P := by
      calc
        ∫ a, Y (cubeSet R) a ∂P =
            ∫ a,
              Y
                (translateSet (intVecToRealVec (scaleTranslationShift n R))
                  (cubeSet (originCube d n))) a ∂P := by
              rw [hshift]
        _ = ∫ a, Y (cubeSet (originCube d n)) a ∂P := by
              exact integral_eq_of_isRestrictionTranslationCovariant_of_stationary_aestronglyMeasurable
                (P := P) hPstat (U := cubeSet (originCube d n))
                hY0_aemeas.aestronglyMeasurable hY_cov (scaleTranslationShift n R)
    simpa [Zraw, Y] using hint.trans hY0_mean
  have hZ_mean :
      ∀ R ∈ D, ∫ a, Z R a ∂P = 0 := by
    intro R hR
    calc
      ∫ a, Z R a ∂P = ∫ a, Zraw R a ∂P :=
        integral_congr_ae (hZraw_eq_Z R hR).symm
      _ = 0 := hZraw_mean R hR
  have havg :=
    isBigO_gammaSigma_restrictionDescendantAverage_of_restrictionUnitRangeDependentLaw_aemeasurable
      (Q := Q) (k := n) (P := P) hnQ hPdep hσ₀ hσ₂ hK Z
      (by intro R hR; exact hZ_local R (by simpa [D] using hR))
      (by intro R hR; exact hZ_aemeas R (by simpa [D] using hR))
      (by intro R hR; exact hZ_tail R (by simpa [D] using hR))
      (by intro R hR; exact hZ_mean R (by simpa [D] using hR))
  have hcenter_eq :
      restrictionCenteredDescendantAverageOnCube P Q n X =ᵐ[P]
        fun a => ((descendantsAtScale Q n).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtScale Q n, Z R a := by
    have hAll : ∀ᵐ a ∂P, ∀ R ∈ D, Zraw R a = Z R a := by
      rw [Filter.eventually_all_finset]
      intro R hR
      exact hZraw_eq_Z R hR
    filter_upwards [hAll] with a hAll_a
    change
      ((D.card : ℝ)⁻¹ * ∑ R ∈ D, Zraw R a) =
        ((D.card : ℝ)⁻¹ * ∑ R ∈ D, Z R a)
    congr 1
    exact Finset.sum_congr rfl fun R hR => hAll_a R hR
  exact (isBigO_congr_ae (μ := P) (Ψ := gammaSigma σ)
    (A := gammaSigmaDescendantsAtScaleConst d n σ *
      (Real.sqrt ((descendantsAtScale Q n).card : ℝ) /
        ((descendantsAtScale Q n).card : ℝ)) * K)
    hcenter_eq).2 havg

end

end Ch04
end Book
end Homogenization
