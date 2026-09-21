/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceDescendantMoments
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceStationaryExpectations

/-!
# One-origin real-moment partition-average bounds

This module derives the real-exponent partition-average moment estimate on the
exact coarse source carrier from one local origin observable.
-/

namespace Homogenization.Book.Ch04

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The real-exponent moment of a centered source partition average is bounded
using only the centered moment of its one origin observable. -/
theorem integral_abs_sourceCenteredTranslatedDescendantAverage_rpow_rpow_inv_le_of_sourceUnitRangeDependentLaw
    {d : ℕ} {n m : ℤ} {P : SourceCoeffLaw d} [IsProbabilityMeasure P] {p : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : SourceStationaryLaw P) (hPdep : SourceUnitRangeDependentLaw P)
    (X : Source.Coarse.Carrier d → ℝ)
    (hX_local :
      IsSourceLocalRandomVariable (cubeSet (originCube d n))
        (measurableSet_cubeSet (originCube d n)) X)
    (hX_int : Integrable X P)
    (hp : 2 ≤ p)
    (hX0Lp_int :
      Integrable (fun a => |sourceCenteredObservable P X hX_int a| ^ p) P) :
    (∫ a, |sourceCenteredTranslatedDescendantAverage P n m hn hnm X hX_int a| ^ p ∂P) ^ p⁻¹ ≤
      ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        (rosenthalDescendantsAtScaleRpowLpConst d n p *
            ((descendantsAtScale (originCube d m) n).card : ℝ) ^ p⁻¹ +
          rosenthalDescendantsAtScaleRpowSqrtConst d n p *
            Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ)) *
          (∫ a, |sourceCenteredObservable P X hX_int a| ^ p ∂P) ^ p⁻¹ := by
  let D : Finset (TriadicCube d) := descendantsAtScale (originCube d m) n
  let N : ℝ := (D.card : ℝ)
  let c : ℝ := N⁻¹
  let μ0 : ℝ := ∫ a, X a ∂P
  let Y : TriadicCube d → Source.Coarse.Carrier d → ℝ :=
    fun R => sourceTranslatedObservable (scaleTranslationShift n R) X
  let Z : TriadicCube d → Source.Coarse.Carrier d → ℝ := fun R a => Y R a - μ0
  have hp_one : 1 ≤ p := le_trans (by norm_num) hp
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp_one
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp_one
  have hp_ennreal_ne_zero : ENNReal.ofReal p ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hp_pos]
  have hX_meas : Measurable X := hX_local.measurable
  have hX0_meas : Measurable (sourceCenteredObservable P X hX_int) :=
    hX_meas.sub measurable_const
  have hX0p_meas : Measurable (fun a => |sourceCenteredObservable P X hX_int a| ^ p) :=
    (Real.continuous_rpow_const hp_nonneg).measurable.comp
      (continuous_abs.measurable.comp hX0_meas)
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtScale_nonempty (originCube d m) hnm
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast hD_nonempty.card_pos
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hY_local :
      ∀ R ∈ D, IsSourceLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (Y R) := by
    intro R hR
    have hshift :=
      cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
        (d := d) hn hnm (by simpa [D] using hR)
    simpa only [Y, sourceTranslatedObservable, hshift] using
      (hX_local.comp_translate (scaleTranslationShift n R))
  have hY_int : ∀ R ∈ D, Integrable (Y R) P := by
    intro R hR
    simpa [Y, sourceTranslatedObservable] using
      (integrable_comp_sourceCarrier_translate_of_sourceStationaryLaw
        (P := P) hPstat (scaleTranslationShift n R) X hX_int)
  have hZ_local :
      ∀ R ∈ D, IsSourceLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (Z R) := by
    intro R hR
    simpa [Z] using (hY_local R hR).sub
      (IsSourceLocalRandomVariable.const (cubeSet R) (measurableSet_cubeSet R) μ0)
  have hZ_int : ∀ R ∈ D, Integrable (fun a => |Z R a| ^ p) P := by
    intro R hR
    simpa [Z, Y, μ0, sourceCenteredObservable, sourceTranslatedObservable, Function.comp_def] using
      (integrable_comp_sourceCarrier_translate_of_sourceStationaryLaw
        (P := P) hPstat (scaleTranslationShift n R)
        (fun a => |sourceCenteredObservable P X hX_int a| ^ p) hX0Lp_int)
  have hZ_mean : ∀ R ∈ D, ∫ a, Z R a ∂P = 0 := by
    intro R hR
    have hY_expect : ∫ a, Y R a ∂P = μ0 := by
      simpa [Y, μ0, sourceTranslatedObservable, Function.comp_def] using
        (integral_comp_sourceCarrier_translate_eq_of_sourceStationaryLaw
          (P := P) hPstat (scaleTranslationShift n R) X hX_meas)
    calc
      ∫ a, Z R a ∂P = ∫ a, Y R a ∂P - ∫ _a, μ0 ∂P := by
          simpa [Z] using integral_sub (hY_int R hR) (integrable_const μ0)
      _ = μ0 - μ0 := by rw [hY_expect]; simp
      _ = 0 := sub_self _
  have hZ_root :
      ∀ R ∈ D, (∫ a, |Z R a| ^ p ∂P) ^ p⁻¹ ≤
        (∫ a, |sourceCenteredObservable P X hX_int a| ^ p ∂P) ^ p⁻¹ := by
    intro R hR
    have hmoment_eq :
        ∫ a, |Z R a| ^ p ∂P =
          ∫ a, |sourceCenteredObservable P X hX_int a| ^ p ∂P := by
      simpa [Z, Y, μ0, sourceCenteredObservable, sourceTranslatedObservable, Function.comp_def] using
        (integral_comp_sourceCarrier_translate_eq_of_sourceStationaryLaw
          (P := P) hPstat (scaleTranslationShift n R)
          (fun a => |sourceCenteredObservable P X hX_int a| ^ p) hX0p_meas)
    rw [hmoment_eq]
  have hsum :=
    integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_uniform_descendantsAtScale_of_sourceUnitRangeDependentLaw
      (Q := originCube d m) (k := n) (P := P) hPdep hp
      (by positivity : 0 ≤ (∫ a, |sourceCenteredObservable P X hX_int a| ^ p ∂P) ^ p⁻¹)
      Z
      (fun R hR => hZ_local R (by simpa [D] using hR))
      (fun R hR => hZ_int R (by simpa [D] using hR))
      (fun R hR => hZ_mean R (by simpa [D] using hR))
      (fun R hR => hZ_root R (by simpa [D] using hR))
  let S : Source.Coarse.Carrier d → ℝ := fun a => ∑ R ∈ D, Z R a
  have hS_meas : Measurable S := by
    simpa [S] using Finset.measurable_sum D (fun R hR => (hZ_local R hR).measurable)
  have hS_int : Integrable (fun a => |S a| ^ p) P := by
    simpa [S] using
      (_root_.Homogenization.IndependentSums.integrable_abs_finsetSum_rpow
        (μ := P) (f := Z) (s := D) hp_one
        (fun R hR => (hZ_local R hR).measurable) hZ_int)
  have hS_memLp : MemLp S (ENNReal.ofReal p) P := by
    rw [← integrable_norm_rpow_iff hS_meas.aestronglyMeasurable hp_ennreal_ne_zero
      ENNReal.ofReal_ne_top]
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp_pos.le] using hS_int
  let Aavg : Source.Coarse.Carrier d → ℝ := c • S
  have hAavg_memLp : MemLp Aavg (ENNReal.ofReal p) P := hS_memLp.const_smul c
  have hAavg_int : Integrable (fun a => |Aavg a| ^ p) P := by
    have hint := hAavg_memLp.integrable_norm_rpow hp_ennreal_ne_zero ENNReal.ofReal_ne_top
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp_pos.le] using hint
  have hS_toReal :
      ENNReal.toReal (eLpNorm S (ENNReal.ofReal p) P) =
        (∫ a, |S a| ^ p ∂P) ^ p⁻¹ := by
    have hnonneg :
        0 ≤ (∫ a, ‖S a‖ ^ (ENNReal.ofReal p).toReal ∂P) ^
          (ENNReal.ofReal p).toReal⁻¹ := by positivity
    rw [hS_memLp.eLpNorm_eq_integral_rpow_norm hp_ennreal_ne_zero ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hnonneg]
    simp [Real.norm_eq_abs, ENNReal.toReal_ofReal hp_pos.le]
  have hAavg_toReal :
      ENNReal.toReal (eLpNorm Aavg (ENNReal.ofReal p) P) =
        (∫ a, |Aavg a| ^ p ∂P) ^ p⁻¹ := by
    have hnonneg :
        0 ≤ (∫ a, ‖Aavg a‖ ^ (ENNReal.ofReal p).toReal ∂P) ^
          (ENNReal.ofReal p).toReal⁻¹ := by positivity
    rw [hAavg_memLp.eLpNorm_eq_integral_rpow_norm hp_ennreal_ne_zero ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hnonneg]
    simp [Real.norm_eq_abs, ENNReal.toReal_ofReal hp_pos.le]
  have hscale :
      ENNReal.toReal (eLpNorm Aavg (ENNReal.ofReal p) P) =
        c * ENNReal.toReal (eLpNorm S (ENNReal.ofReal p) P) := by
    rw [show Aavg = c • S by rfl, eLpNorm_const_smul, ENNReal.toReal_mul]
    simp [Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
  have hAavg_eq : Aavg = sourceCenteredTranslatedDescendantAverage P n m hn hnm X hX_int := by
    funext a
    simp [Aavg, S, Z, Y, c, N, D, μ0, sourceCenteredTranslatedDescendantAverage]
  calc
    (∫ a, |sourceCenteredTranslatedDescendantAverage P n m hn hnm X hX_int a| ^ p ∂P) ^ p⁻¹ =
        ENNReal.toReal (eLpNorm Aavg (ENNReal.ofReal p) P) := by
          rw [hAavg_toReal]
          simp [hAavg_eq]
    _ = c * ENNReal.toReal (eLpNorm S (ENNReal.ofReal p) P) := hscale
    _ = c * (∫ a, |S a| ^ p ∂P) ^ p⁻¹ := by rw [hS_toReal]
    _ ≤ c *
          (rosenthalDescendantsAtScaleRpowLpConst d n p * N ^ p⁻¹ *
              (∫ a, |sourceCenteredObservable P X hX_int a| ^ p ∂P) ^ p⁻¹ +
            rosenthalDescendantsAtScaleRpowSqrtConst d n p * Real.sqrt N *
              (∫ a, |sourceCenteredObservable P X hX_int a| ^ p ∂P) ^ p⁻¹) := by
          exact mul_le_mul_of_nonneg_left (by simpa [S, D, N] using hsum) hc_nonneg
    _ = ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
          (rosenthalDescendantsAtScaleRpowLpConst d n p *
              ((descendantsAtScale (originCube d m) n).card : ℝ) ^ p⁻¹ +
            rosenthalDescendantsAtScaleRpowSqrtConst d n p *
              Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ)) *
            (∫ a, |sourceCenteredObservable P X hX_int a| ^ p ∂P) ^ p⁻¹ := by
          simp [c, N]
          ring

end

end Homogenization.Book.Ch04
