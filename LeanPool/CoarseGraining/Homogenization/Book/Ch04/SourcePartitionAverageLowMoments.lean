/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourcePartitionAverageMoments
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.MomentCalculus

/-!
# Finite-moment source partition-average bounds

This module derives the finite-moment `L¹` partition-average estimate on the
exact coarse source carrier.
-/

@[expose] public section

namespace Homogenization.Book.Ch04

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- A finite source `ξ`-moment controls the `L¹` fluctuation of its centered
partition average. -/
theorem integral_abs_sourceCenteredTranslatedDescendantAverage_le_of_sourceUnitRangeDependentLaw
    {d : ℕ} {n m : ℤ} {P : SourceCoeffLaw d} [IsProbabilityMeasure P] {ξ : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m)
    (hPstat : SourceStationaryLaw P) (hPdep : SourceUnitRangeDependentLaw P)
    (X : Source.Coarse.Carrier d → ℝ)
    (hX_local :
      IsSourceLocalRandomVariable (cubeSet (originCube d n))
        (measurableSet_cubeSet (originCube d n)) X)
    (hξ : 2 ≤ ξ)
    (hXξ_int : Integrable (fun a => |X a| ^ ξ) P) :
    let hX_int :=
      _root_.Homogenization.IndependentSums.integrable_of_integrable_abs_rpow
        (μ := P) (f := X) (le_trans (by norm_num) hξ) hX_local.measurable hXξ_int
    ∫ a, |sourceCenteredTranslatedDescendantAverage P n m hn hnm X hX_int a| ∂P ≤
      ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        (rosenthalDescendantsAtScaleRpowLpConst d n 2 *
            ((descendantsAtScale (originCube d m) n).card : ℝ) ^ (2 : ℝ)⁻¹ +
          rosenthalDescendantsAtScaleRpowSqrtConst d n 2 *
            Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ)) *
        (∫ a, |sourceCenteredObservable P X hX_int a| ^ ξ ∂P) ^ ξ⁻¹ := by
  let hX_int : Integrable X P :=
    _root_.Homogenization.IndependentSums.integrable_of_integrable_abs_rpow
      (μ := P) (f := X) (le_trans (by norm_num) hξ) hX_local.measurable hXξ_int
  have hξ_one : 1 ≤ ξ := le_trans (by norm_num) hξ
  have hX0_meas : Measurable (sourceCenteredObservable P X hX_int) :=
    hX_local.measurable.sub measurable_const
  have hX0ξ_int :
      Integrable (fun a => |sourceCenteredObservable P X hX_int a| ^ ξ) P := by
    simpa [sourceCenteredObservable] using
      (_root_.Homogenization.IndependentSums.integrable_abs_sub_integral_rpow_of_integrable_abs_rpow
        (μ := P) (f := X) hξ_one hX_local.measurable hXξ_int)
  have hX02_int :
      Integrable (fun a => |sourceCenteredObservable P X hX_int a| ^ (2 : ℝ)) P :=
    _root_.Homogenization.IndependentSums.integrable_abs_rpow_of_integrable_abs_rpow_of_le
      (μ := P) (f := sourceCenteredObservable P X hX_int) (q := 2) (p := ξ)
      (by norm_num) hξ hX0_meas hX0ξ_int
  let D : Finset (TriadicCube d) := descendantsAtScale (originCube d m) n
  let c : ℝ := (D.card : ℝ)⁻¹
  let Z : TriadicCube d → Source.Coarse.Carrier d → ℝ :=
    fun R a => sourceTranslatedObservable (scaleTranslationShift n R) X a - ∫ b, X b ∂P
  have hZ_local :
      ∀ R ∈ D, IsSourceLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (Z R) := by
    intro R hR
    have hshift :=
      cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
        (d := d) hn hnm (by simpa [D] using hR)
    have htranslated := hX_local.comp_translate (scaleTranslationShift n R)
    have hsub := htranslated.sub (IsSourceLocalRandomVariable.const _ _ (∫ b, X b ∂P))
    simpa only [Z, sourceTranslatedObservable, hshift] using
      hsub
  have hZ2_int : ∀ R ∈ D, Integrable (fun a => |Z R a| ^ (2 : ℝ)) P := by
    intro R hR
    simpa [Z, sourceCenteredObservable, sourceTranslatedObservable, Function.comp_def] using
      (integrable_comp_sourceCarrier_translate_of_sourceStationaryLaw
        (P := P) hPstat (scaleTranslationShift n R)
        (fun a => |sourceCenteredObservable P X hX_int a| ^ (2 : ℝ)) hX02_int)
  let S : Source.Coarse.Carrier d → ℝ := fun a => ∑ R ∈ D, Z R a
  have hS_meas : Measurable S := by
    simpa [S] using Finset.measurable_sum D (fun R hR => (hZ_local R hR).measurable)
  have hS2_int : Integrable (fun a => |S a| ^ (2 : ℝ)) P := by
    simpa [S] using
      (_root_.Homogenization.IndependentSums.integrable_abs_finsetSum_rpow
        (μ := P) (f := Z) (s := D) (p := 2) (by norm_num)
        (fun R hR => (hZ_local R hR).measurable) hZ2_int)
  let A : Source.Coarse.Carrier d → ℝ := fun a => c * S a
  have hA_meas : Measurable A := hS_meas.const_mul c
  have hA2_int : Integrable (fun a => |A a| ^ (2 : ℝ)) P := by
    convert hS2_int.const_mul (|c| ^ (2 : ℝ)) using 1
    funext a
    change |c * S a| ^ (2 : ℝ) = |c| ^ (2 : ℝ) * |S a| ^ (2 : ℝ)
    rw [abs_mul, Real.mul_rpow (abs_nonneg c) (abs_nonneg (S a))]
  have hA_eq : A = sourceCenteredTranslatedDescendantAverage P n m hn hnm X hX_int := by
    funext a
    simp [A, S, Z, c, D, sourceCenteredTranslatedDescendantAverage]
  have hA_l1_le_l2 :
      (∫ a, |A a| ∂P) ≤ (∫ a, |A a| ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹ := by
    simpa using
      (_root_.Homogenization.IndependentSums.integral_abs_rpow_rpow_inv_le_of_le
        (μ := P) (f := A) (q := 1) (p := 2) (by norm_num) (by norm_num) hA_meas hA2_int)
  have hmain :
      (∫ a, |A a| ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹ ≤
        ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
          (rosenthalDescendantsAtScaleRpowLpConst d n 2 *
              ((descendantsAtScale (originCube d m) n).card : ℝ) ^ (2 : ℝ)⁻¹ +
            rosenthalDescendantsAtScaleRpowSqrtConst d n 2 *
              Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ)) *
          (∫ a, |sourceCenteredObservable P X hX_int a| ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹ := by
    simpa [hA_eq] using
      (integral_abs_sourceCenteredTranslatedDescendantAverage_rpow_rpow_inv_le_of_sourceUnitRangeDependentLaw
        (P := P) (p := 2) hn hnm hPstat hPdep X hX_local hX_int (by norm_num) hX02_int)
  have hX0_l2_le_lξ :
      (∫ a, |sourceCenteredObservable P X hX_int a| ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹ ≤
        (∫ a, |sourceCenteredObservable P X hX_int a| ^ ξ ∂P) ^ ξ⁻¹ :=
    _root_.Homogenization.IndependentSums.integral_abs_rpow_rpow_inv_le_of_le
      (μ := P) (f := sourceCenteredObservable P X hX_int) (q := 2) (p := ξ)
      (by norm_num) hξ hX0_meas hX0ξ_int
  have hcoeff_nonneg :
      0 ≤ ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        (rosenthalDescendantsAtScaleRpowLpConst d n 2 *
            ((descendantsAtScale (originCube d m) n).card : ℝ) ^ (2 : ℝ)⁻¹ +
          rosenthalDescendantsAtScaleRpowSqrtConst d n 2 *
            Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ)) := by
    have hRB_nonneg : 0 ≤ rosenthalBennettIntegralConst := by
      dsimp [rosenthalBennettIntegralConst, IndependentSums.rosenthalBennettIntegralConst]
      positivity
    rw [rosenthalDescendantsAtScaleRpowLpConst,
      rosenthalDescendantsAtScaleRpowSqrtConst]
    positivity
  calc
    ∫ a, |sourceCenteredTranslatedDescendantAverage P n m hn hnm X hX_int a| ∂P =
        ∫ a, |A a| ∂P := by rw [hA_eq]
    _ ≤ (∫ a, |A a| ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹ := hA_l1_le_l2
    _ ≤ ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
          (rosenthalDescendantsAtScaleRpowLpConst d n 2 *
              ((descendantsAtScale (originCube d m) n).card : ℝ) ^ (2 : ℝ)⁻¹ +
            rosenthalDescendantsAtScaleRpowSqrtConst d n 2 *
              Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ)) *
          (∫ a, |sourceCenteredObservable P X hX_int a| ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹ := hmain
    _ ≤ ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
          (rosenthalDescendantsAtScaleRpowLpConst d n 2 *
              ((descendantsAtScale (originCube d m) n).card : ℝ) ^ (2 : ℝ)⁻¹ +
            rosenthalDescendantsAtScaleRpowSqrtConst d n 2 *
              Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ)) *
          (∫ a, |sourceCenteredObservable P X hX_int a| ^ ξ ∂P) ^ ξ⁻¹ :=
      mul_le_mul_of_nonneg_left hX0_l2_le_lξ hcoeff_nonneg

end

end Homogenization.Book.Ch04
