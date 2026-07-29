/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.GaussDigammaVerticalSqrtBound
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouQuadraticDecay
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Regularized Poitou Sqrt Weighted Integrable

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

private theorem sqrt_add_abs_mul_norm_poitouTransform_le_rpow
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) {t : ℝ} (ht : 1 ≤ |t|) :
    Real.sqrt (|σ - 1| + |t|) *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ ≤
      Real.sqrt (|σ - 1| + 1) *
        (∫ x : ℝ,
          ‖poitouVerticalProfileSecondDerivative
            (regularizedScaledTartar y δ)
            (regularizedScaledTartarDerivative y δ)
            (regularizedScaledTartarSecondDerivative y δ) σ x‖) *
        |t| ^ (-(3 : ℝ) / 2) := by
  let A : ℝ :=
    ∫ x : ℝ,
      ‖poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ x‖
  have htpos : 0 < |t| := zero_lt_one.trans_le ht
  have hsqrt :
      Real.sqrt (|σ - 1| + |t|) ≤
        Real.sqrt (|σ - 1| + 1) * Real.sqrt |t| := by
    rw [← Real.sqrt_mul (by positivity)]
    gcongr
    nlinarith [abs_nonneg (σ - 1)]
  have hquad :
      |t| ^ 2 *
          ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ ≤ A :=
    sq_abs_mul_norm_poitouTransform_regularized_le hδ y σ t
  have hnorm :
      ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ ≤
        A / |t| ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos htpos)).2 (by
      grind)
  calc
    Real.sqrt (|σ - 1| + |t|) *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ ≤
      (Real.sqrt (|σ - 1| + 1) * Real.sqrt |t|) *
        (A / |t| ^ 2) := by gcongr
    _ = Real.sqrt (|σ - 1| + 1) * A *
        (Real.sqrt |t| / |t| ^ 2) := by ring
    _ = _ := by
      rw [show Real.sqrt |t| / |t| ^ 2 = |t| ^ (-(3 : ℝ) / 2) by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
        rw [← Real.rpow_sub htpos]
        grind]

theorem integrable_sqrt_add_abs_mul_norm_poitouTransform_regularized
    {δ : ℝ} (hδ : 0 < δ) (y σ : ℝ) :
    Integrable (fun t : ℝ ↦
      Real.sqrt (|σ - 1| + |t|) *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖) := by
  let Φ : ℝ → ℂ := fun t ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I)
  let A : ℝ :=
    ∫ x : ℝ,
      ‖poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ x‖
  let C : ℝ := Real.sqrt (|σ - 1| + 1) * A
  have hΦ : Integrable Φ :=
    poitouTransform_regularizedScaledTartar_vertical_integrable hδ y σ
  have hcont : Continuous (fun t : ℝ ↦
      Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖) := by
    have hΦcont : Continuous Φ := by
      rw [continuous_iff_continuousAt]
      intro t
      have hin : ContinuousAt
          (fun u : ℝ ↦ (σ : ℂ) + u * I) t := by
        fun_prop
      have hout :
          ContinuousAt
            (poitouTransform (regularizedScaledTartar y δ))
            (σ + t * I) :=
        (analyticOnNhd_poitouTransform_regularizedScaledTartar
          hδ (σ + t * I) (mem_univ _)).continuousAt
      simpa only [Φ, ContinuousAt, Function.comp_def] using
        Filter.Tendsto.comp hout hin
    fun_prop
  have hpow :
      IntegrableOn (fun u : ℝ ↦ u ^ (-(3 : ℝ) / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hpos :
      IntegrableOn (fun t : ℝ ↦
        Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖) (Ioi 1) := by
    apply (hpow.const_mul C).mono'
    · exact hcont.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 1 < t at ht
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
      change
        Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖ ≤
          C * t ^ (-(3 : ℝ) / 2)
      simpa only [abs_of_pos (zero_lt_one.trans ht)] using
        sqrt_add_abs_mul_norm_poitouTransform_le_rpow
          hδ y σ (t := t) (by
            grind)
  have hnegMajor :
      IntegrableOn (fun t : ℝ ↦ C * (-t) ^ (-(3 : ℝ) / 2))
        (Iio (-1)) := by
    have hpowC :
        IntegrableOn (fun u : ℝ ↦ C * u ^ (-(3 : ℝ) / 2))
          (Ioi 1) :=
      (show Integrable (fun u : ℝ ↦ u ^ (-(3 : ℝ) / 2))
          (volume.restrict (Ioi 1)) from hpow).const_mul C
    have hpowC' :
        IntegrableOn (fun u : ℝ ↦ C * u ^ (-(3 : ℝ) / 2))
          (Ioi (-(-1 : ℝ))) := by simp_all
    exact hpowC'.comp_neg_Iio
  have hneg :
      IntegrableOn (fun t : ℝ ↦
        Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖) (Iio (-1)) := by
    apply hnegMajor.mono'
    · exact hcont.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
      change t < -1 at ht
      have htneg : t < 0 := ht.trans (by norm_num)
      have habs : |t| = -t := abs_of_neg htneg
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
      change
        Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖ ≤
          C * (-t) ^ (-(3 : ℝ) / 2)
      simpa only [habs] using
        sqrt_add_abs_mul_norm_poitouTransform_le_rpow
          hδ y σ (t := t) (by grind)
  have hmid :
      IntegrableOn (fun t : ℝ ↦
        Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖) (Icc (-1) 1) := by
    apply ((hΦ.norm.const_mul (Real.sqrt (|σ - 1| + 1))).integrableOn).mono'
    · exact hcont.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
      gcongr
      grind
  have huniv : Iio (-1 : ℝ) ∪ Icc (-1) 1 ∪ Ioi 1 = univ := by simp
  rw [← integrableOn_univ]
  change IntegrableOn
    (fun t : ℝ ↦ Real.sqrt (|σ - 1| + |t|) * ‖Φ t‖) univ
  rw [← huniv]
  exact (hneg.union hmid).union hpos

end NumberField.Odlyzko
