/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageMoments.Rosenthal

/-! # Centered Average -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Restriction-carrier partition-average moment estimates: centered descendant averages
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- A descendant at a nonnegative scale is an integer translate of the origin cube at that scale. -/
theorem cubeSet_descendant_eq_translate_origin
    {d : ℕ} {n : ℤ} {Q R : TriadicCube d}
    (hn : 0 ≤ n) (hnQ : n ≤ Q.scale) (hR : R ∈ descendantsAtScale Q n) :
    cubeSet R =
      translateSet (intVecToRealVec (scaleTranslationShift n R))
        (cubeSet (originCube d n)) := by
  have hscaleR : R.scale = n := by
    calc
      R.scale = Q.scale - Int.toNat (Q.scale - n) := by
        exact scale_eq_sub_of_mem_descendantsAtScale (Q := Q) hnQ hR
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
  exact hshift

/-- A stationary restriction law gives equal pushforward laws for a covariant observable on an
integer-translated cube and its origin representative. Only the origin observable must be a.e.
measurable. -/
theorem restrictionCovariant_map_eq_of_cubeTranslation
    {d : ℕ} {n : ℤ} {R : TriadicCube d} {P : RestrictionCoeffLaw d}
    {Y : Set (Vec d) → RegCoeffField d → ℝ}
    (hPstat : RestrictionStationaryLaw P) (hY_cov : IsRestrictionTranslationCovariant Y)
    (hY0_aemeas : AEMeasurable (Y (cubeSet (originCube d n))) P)
    (hshift : cubeSet R =
      translateSet (intVecToRealVec (scaleTranslationShift n R))
        (cubeSet (originCube d n))) :
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

/-- Centered polynomial-moment fluctuation bound for restriction-centered
descendant averages of a translation-covariant cube observable. -/
theorem integral_abs_restrictionCenteredDescendantAverage_pow_rpow_inv_le_of_restrictionUnitRangeDependentLaw
    {d : ℕ} {n m : ℤ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {p : ℕ} {K : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : RestrictionStationaryLaw P) (hPdep : RestrictionUnitRangeDependentLaw P)
    (X : Set (Vec d) → RegCoeffField d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X (cubeSet R)))
    (hX_cov : IsRestrictionTranslationCovariant X)
    (hX0_aemeas : AEMeasurable (X (cubeSet (originCube d n))) P)
    (hX_desc_aemeas :
      ∀ R ∈ descendantsAtScale (originCube d m) n, AEMeasurable (X (cubeSet R)) P)
    (hp : 2 ≤ p) (hK_nonneg : 0 ≤ K)
    (hX0Lp_int :
      Integrable (fun a => |restrictionCenteredOriginObservable P n X a| ^ p) P)
    (hX0Lp :
      (∫ a, |restrictionCenteredOriginObservable P n X a| ^ p ∂P) ^
          (1 / (p : ℝ)) ≤ K) :
    (∫ a, |restrictionCenteredDescendantAverage P n m X a| ^ p ∂P) ^
        (1 / (p : ℝ)) ≤
      ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        (rosenthalDescendantsAtScaleLpConst d n p *
            ((descendantsAtScale (originCube d m) n).card : ℝ) ^
              (1 / (p : ℝ)) * K +
          rosenthalDescendantsAtScaleSqrtConst d n p *
            Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) * K) := by
  have hp_nat_ne_zero : p ≠ 0 := by omega
  let N : ℝ := ((descendantsAtScale (originCube d m) n).card : ℝ)
  let c : ℝ := N⁻¹
  let μ0 : ℝ := ∫ a, X (cubeSet (originCube d n)) a ∂P
  let Y : Set (Vec d) → RegCoeffField d → ℝ := fun U a => X U a - μ0
  have hdesc_nonempty : (descendantsAtScale (originCube d m) n).Nonempty := by
    exact descendantsAtScale_nonempty (originCube d m) hnm
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast hdesc_nonempty.card_pos
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hY_cov : IsRestrictionTranslationCovariant Y := by
    intro U z a
    simpa [Y] using congrArg (fun x : ℝ => x - μ0) (hX_cov U z a)
  have hY0_aemeas : AEMeasurable (Y (cubeSet (originCube d n))) P := by
    simpa [Y] using! hX0_aemeas.sub measurable_const.aemeasurable
  have hY0Lp_int :
      Integrable (fun a => |Y (cubeSet (originCube d n)) a| ^ p) P := by
    simpa [Y, μ0, restrictionCenteredOriginObservable] using hX0Lp_int
  have hY0Lp :
      (∫ a, |Y (cubeSet (originCube d n)) a| ^ p ∂P) ^
          (1 / (p : ℝ)) ≤ K := by
    simpa [Y, μ0, restrictionCenteredOriginObservable] using hX0Lp
  have hY0_memLp : MemLp (Y (cubeSet (originCube d n))) (p : ENNReal) P := by
    rw [← integrable_norm_rpow_iff
      hY0_aemeas.aestronglyMeasurable (by exact_mod_cast hp_nat_ne_zero) (by simp)]
    simpa [Real.norm_eq_abs] using hY0Lp_int
  have hY0_memL1 : MemLp (Y (cubeSet (originCube d n))) (1 : ENNReal) P := by
    exact hY0_memLp.mono_exponent (by exact_mod_cast (show 1 ≤ p by omega))
  have hY0_int : Integrable (Y (cubeSet (originCube d n))) P := by
    rwa [memLp_one_iff_integrable] at hY0_memL1
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
      _ = μ0 - μ0 := by
            simp [μ0]
      _ = 0 := by
            ring
  let Z : TriadicCube d → RegCoeffField d → ℝ := fun R a => X (cubeSet R) a - μ0
  have hZ_local :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (Z R) := by
    intro R hR
    simpa [Z] using (hX_local R hR).sub measurable_const
  have hZ_aemeas :
      ∀ R ∈ descendantsAtScale (originCube d m) n, AEMeasurable (Z R) P := by
    intro R hR
    simpa [Z] using! (hX_desc_aemeas R hR).sub measurable_const.aemeasurable
  have hZ_int :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        Integrable (fun a => |Z R a| ^ p) P := by
    intro R hR
    have hshift := cubeSet_descendant_eq_translate_origin hn hnm hR
    have hYR_aemeas : AEMeasurable (Y (cubeSet R)) P := by
      simpa [Y] using! (hX_desc_aemeas R hR).sub measurable_const.aemeasurable
    have hmap := restrictionCovariant_map_eq_of_cubeTranslation
      hPstat hY_cov hY0_aemeas hshift
    have hYR_int :
        Integrable (fun a => |Y (cubeSet R) a| ^ p) P := by
      exact integrable_abs_pow_of_map_eq_map_aemeasurable hYR_aemeas hY0_aemeas hmap hY0Lp_int
    simpa [Z, Y] using hYR_int
  have hZ_mean :
      ∀ R ∈ descendantsAtScale (originCube d m) n, ∫ a, Z R a ∂P = 0 := by
    intro R hR
    have hshift := cubeSet_descendant_eq_translate_origin hn hnm hR
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
    simpa [Z, Y] using hint.trans hY0_mean
  have hZ_bound :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        (∫ a, |Z R a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K := by
    intro R hR
    have hshift := cubeSet_descendant_eq_translate_origin hn hnm hR
    have hYR_aemeas : AEMeasurable (Y (cubeSet R)) P := by
      simpa [Y] using! (hX_desc_aemeas R hR).sub measurable_const.aemeasurable
    have hmap := restrictionCovariant_map_eq_of_cubeTranslation
      hPstat hY_cov hY0_aemeas hshift
    have hYR :
        (∫ a, |Y (cubeSet R) a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K := by
      have hint :
          ∫ a, |Y (cubeSet R) a| ^ p ∂P =
            ∫ a, |Y (cubeSet (originCube d n)) a| ^ p ∂P :=
        integral_abs_pow_eq_of_map_eq_map_aemeasurable hYR_aemeas hY0_aemeas hmap
      simpa [hint] using hY0Lp
    simpa [Z, Y] using hYR
  have hsum :=
    integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_uniform_descendantsAtScale_of_restrictionUnitRangeDependentLaw
      (Q := originCube d m) (k := n) (P := P)
      hPdep hp hK_nonneg Z hZ_local hZ_aemeas hZ_int hZ_mean hZ_bound
  let S : RegCoeffField d → ℝ :=
    fun a => ∑ R ∈ descendantsAtScale (originCube d m) n, Z R a
  have hS_aemeas : AEMeasurable S P := by
    have hsum : AEMeasurable
        (∑ R ∈ descendantsAtScale (originCube d m) n, Z R) P :=
      Finset.aemeasurable_sum _ (fun R hR => hZ_aemeas R hR)
    convert hsum using 1
    ext a
    simp [S]
  have hS_memLp : MemLp S (p : ENNReal) P := by
    dsimp [S]
    refine memLp_finsetSum _ ?_
    intro R hR
    refine (integrable_norm_rpow_iff
      (hZ_aemeas R hR).aestronglyMeasurable
      (by exact_mod_cast hp_nat_ne_zero) (by simp)).1 ?_
    simpa [Real.norm_eq_abs] using hZ_int R hR
  have hS_int : Integrable (fun a => |S a| ^ p) P := by
    simpa [S, Real.norm_eq_abs] using hS_memLp.integrable_norm_pow hp_nat_ne_zero
  let Aavg : RegCoeffField d → ℝ := c • S
  have hAavg_aemeas : AEMeasurable Aavg P := hS_aemeas.const_smul c
  have hAavg_memLp : MemLp Aavg (p : ENNReal) P := hS_memLp.const_smul c
  have hAavg_int : Integrable (fun a => |Aavg a| ^ p) P := by
    simpa [Aavg, S, Real.norm_eq_abs] using hAavg_memLp.integrable_norm_pow hp_nat_ne_zero
  have hS_toReal :
      ENNReal.toReal (eLpNorm S (p : ENNReal) P) =
        (∫ a, |S a| ^ p ∂P) ^ (1 / (p : ℝ)) := by
    exact toReal_eLpNorm_eq_integral_abs_pow_rpow_inv_aemeasurable (show 1 ≤ p by omega) hS_aemeas hS_int
  have hAavg_toReal :
      ENNReal.toReal (eLpNorm Aavg (p : ENNReal) P) =
        (∫ a, |Aavg a| ^ p ∂P) ^ (1 / (p : ℝ)) := by
    exact toReal_eLpNorm_eq_integral_abs_pow_rpow_inv_aemeasurable
      (show 1 ≤ p by omega) hAavg_aemeas hAavg_int
  have hscale :
      ENNReal.toReal (eLpNorm Aavg (p : ENNReal) P) =
        c * ENNReal.toReal (eLpNorm S (p : ENNReal) P) := by
    rw [show Aavg = c • S by rfl, eLpNorm_const_smul]
    rw [ENNReal.toReal_mul]
    simp [Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
  have hAavg_eq : Aavg = restrictionCenteredDescendantAverage P n m X := by
    funext a
    simp [Aavg, S, Z, restrictionCenteredDescendantAverage, μ0, c, N]
  calc
    (∫ a, |restrictionCenteredDescendantAverage P n m X a| ^ p ∂P) ^ (1 / (p : ℝ))
        = ENNReal.toReal (eLpNorm Aavg (p : ENNReal) P) := by
            rw [hAavg_toReal]
            simp [hAavg_eq]
    _ = c * ENNReal.toReal (eLpNorm S (p : ENNReal) P) := hscale
    _ = c * (∫ a, |S a| ^ p ∂P) ^ (1 / (p : ℝ)) := by
          rw [hS_toReal]
    _ ≤ c *
          (rosenthalDescendantsAtScaleLpConst d n p * N ^ (1 / (p : ℝ)) * K +
            rosenthalDescendantsAtScaleSqrtConst d n p * Real.sqrt N * K) := by
              exact mul_le_mul_of_nonneg_left (by simpa [S, N] using hsum) hc_nonneg
    _ = N⁻¹ *
          (rosenthalDescendantsAtScaleLpConst d n p * N ^ (1 / (p : ℝ)) * K +
            rosenthalDescendantsAtScaleSqrtConst d n p * Real.sqrt N * K) := by
              simp [c]
    _ = ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
          (rosenthalDescendantsAtScaleLpConst d n p *
              ((descendantsAtScale (originCube d m) n).card : ℝ) ^
                (1 / (p : ℝ)) * K +
            rosenthalDescendantsAtScaleSqrtConst d n p *
              Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) * K) := by
              simp [N]

end

end Ch04
end Book
end Homogenization
