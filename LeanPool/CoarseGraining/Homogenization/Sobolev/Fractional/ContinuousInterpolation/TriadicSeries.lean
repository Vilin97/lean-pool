/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.TriadicScale

/-!
# Triadic sample series for the continuous `K`-energy

This module assembles the disjoint triadic scale intervals into an `ENNReal`
series.  The lower comparison is deliberately indexed from `j + 1`: the
continuous scale integral alone cannot recover the endpoint sample at `t = 1`.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal
open MeasureTheory

noncomputable section

/-- The canonical weighted triadic sample at `t_j = 3^{-j}`. -/
noncomputable def triadicContinuousKSampleTerm {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow (triadicContinuousKScale j).1 (-2 * s.1)) *
    ENNReal.ofReal (continuousKFunctional (triadicContinuousKScale j) F ^ 2)

/-- The canonical `ENNReal` triadic sampled energy.  Its weights are the
scale form of `3^(2 s j) K(3^{-j},F)^2`. -/
noncomputable def triadicContinuousKSampleEnergy {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  ∑' j : ℕ, triadicContinuousKSampleTerm s F j

/-- The shifted sampled energy, excluding only the endpoint sample at `t=1`. -/
noncomputable def triadicContinuousKShiftedSampleEnergy {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  ∑' j : ℕ, triadicContinuousKSampleTerm s F (j + 1)

/-- The explicit lower comparison constant for base-three intervals. -/
noncomputable def triadicContinuousKLowerSeriesConstant (s : FractionalOrder) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) / 3) * ENNReal.ofReal (Real.rpow 3 (-2 * s.1))

/-- The explicit upper comparison constant for base-three intervals. -/
noncomputable def triadicContinuousKUpperSeriesConstant (s : FractionalOrder) : ℝ≥0∞ :=
  ENNReal.ofReal 2 * ENNReal.ofReal (Real.rpow 3 (2 * s.1))

theorem continuousKSeminorm_lintegral_eq_tsum_triadicIntervals {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F t =
      ∑' j : ℕ, ∫⁻ t in triadicContinuousKInterval j,
        continuousKSeminormIntegrand s.1 F t := by
  rw [← iUnion_triadicContinuousKInterval]
  exact lintegral_iUnion measurableSet_triadicContinuousKInterval
    triadicContinuousKInterval_pairwiseDisjoint _

private theorem triadicContinuousKInterval_eq_diff_singleton (j : ℕ) :
    triadicContinuousKInterval j =
      Set.Ioc (triadicContinuousKScale (j + 1)).1 (triadicContinuousKScale j).1 \ {1} := by
  ext t
  simp only [triadicContinuousKInterval, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo,
    Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hpos, hone⟩
    exact ⟨⟨hlower, hupper⟩, ne_of_lt hone⟩
  · rintro ⟨⟨hlower, hupper⟩, hne⟩
    refine ⟨⟨hlower, hupper⟩, ?_, ?_⟩
    · exact (triadicContinuousKScale_pos (j + 1)).trans hlower
    · exact lt_of_le_of_ne (hupper.trans (triadicContinuousKScale_le_one j)) hne

private theorem volume_triadicContinuousKInterval (j : ℕ) :
    volume (triadicContinuousKInterval j) =
      ENNReal.ofReal ((2 : ℝ) / 3 * (triadicContinuousKScale j).1) := by
  rw [triadicContinuousKInterval_eq_diff_singleton, measure_sdiff_null Real.volume_singleton,
    Real.volume_Ioc, triadicContinuousKScale_succ]
  congr 1
  ring

private theorem triadicContinuousKUpper_scaleFactor (j : ℕ) :
    ENNReal.ofReal ((triadicContinuousKScale j).1)⁻¹ *
        volume (triadicContinuousKInterval j) = ENNReal.ofReal ((2 : ℝ) / 3) := by
  rw [volume_triadicContinuousKInterval, ← ENNReal.ofReal_mul]
  · congr 1
    field_simp [ne_of_gt (triadicContinuousKScale_pos j)]
  · exact inv_nonneg.mpr (triadicContinuousKScale_pos j).le

private theorem triadicContinuousKLower_scaleFactor (j : ℕ) :
    ENNReal.ofReal ((triadicContinuousKScale (j + 1)).1)⁻¹ *
        volume (triadicContinuousKInterval j) = ENNReal.ofReal 2 := by
  rw [volume_triadicContinuousKInterval, triadicContinuousKScale_succ,
    ← ENNReal.ofReal_mul]
  · congr 1
    field_simp [ne_of_gt (triadicContinuousKScale_pos j)]
  · exact inv_nonneg.mpr (by
      exact div_nonneg (triadicContinuousKScale_pos j).le (by norm_num))

private theorem triadicContinuousK_rpow_upper (s : FractionalOrder) (j : ℕ) :
    Real.rpow (triadicContinuousKScale j).1 (-2 * s.1) =
      Real.rpow 3 (-2 * s.1) *
        Real.rpow (triadicContinuousKScale (j + 1)).1 (-2 * s.1) := by
  have hscale : (triadicContinuousKScale j).1 =
      3 * (triadicContinuousKScale (j + 1)).1 := by
    rw [triadicContinuousKScale_succ]
    field_simp
  rw [hscale]
  exact Real.mul_rpow (by norm_num) (triadicContinuousKScale_pos (j + 1)).le

private theorem triadicContinuousK_rpow_lower (s : FractionalOrder) (j : ℕ) :
    Real.rpow (triadicContinuousKScale (j + 1)).1 (-2 * s.1) =
      Real.rpow 3 (2 * s.1) *
        Real.rpow (triadicContinuousKScale j).1 (-2 * s.1) := by
  rw [triadicContinuousKScale_succ,
    show (triadicContinuousKScale j).1 / 3 =
      (triadicContinuousKScale j).1 * 3⁻¹ by ring]
  calc
    Real.rpow ((triadicContinuousKScale j).1 * 3⁻¹) (-2 * s.1) =
        Real.rpow (triadicContinuousKScale j).1 (-2 * s.1) *
          Real.rpow 3⁻¹ (-2 * s.1) :=
      Real.mul_rpow (triadicContinuousKScale_pos j).le (by positivity)
    _ = Real.rpow 3 (2 * s.1) *
          Real.rpow (triadicContinuousKScale j).1 (-2 * s.1) := by
      have hthree : Real.rpow (3⁻¹ : ℝ) (-2 * s.1) = Real.rpow 3 (2 * s.1) := by
        calc
          Real.rpow (3⁻¹ : ℝ) (-2 * s.1) =
              (Real.rpow 3 (-2 * s.1))⁻¹ :=
            Real.inv_rpow (by norm_num) _
          _ = Real.rpow 3 (2 * s.1) := by
            rw [show -2 * s.1 = -(2 * s.1) by ring]
            have hneg : Real.rpow 3 (-(2 * s.1)) =
                (Real.rpow 3 (2 * s.1))⁻¹ :=
              Real.rpow_neg (by norm_num) _
            rw [hneg, inv_inv]
      rw [hthree]
      ring

private theorem triadicContinuousKLower_interval_bound {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (j : ℕ) :
    triadicContinuousKLowerSeriesConstant s *
        triadicContinuousKSampleTerm s F (j + 1) ≤
      ∫⁻ t in triadicContinuousKInterval j, continuousKSeminormIntegrand s.1 F t := by
  refine (le_of_eq ?_).trans (triadicContinuousKInterval_lintegral_bounds s F j).1
  unfold triadicContinuousKLowerSeriesConstant triadicContinuousKSampleTerm
    triadicContinuousKLowerSampleWeight
  have hpow : ENNReal.ofReal (Real.rpow (triadicContinuousKScale j).1 (-2 * s.1)) =
      ENNReal.ofReal (Real.rpow 3 (-2 * s.1)) *
        ENNReal.ofReal (Real.rpow (triadicContinuousKScale (j + 1)).1 (-2 * s.1)) := by
    rw [triadicContinuousK_rpow_upper s j]
    exact ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)
  rw [hpow]
  calc
    ENNReal.ofReal (2 / 3) * ENNReal.ofReal (Real.rpow 3 (-2 * s.1)) *
          (ENNReal.ofReal (Real.rpow (triadicContinuousKScale (j + 1)).1 (-2 * s.1)) *
            ENNReal.ofReal (continuousKFunctional (triadicContinuousKScale (j + 1)) F ^ 2)) =
        (ENNReal.ofReal (Real.rpow 3 (-2 * s.1)) *
            ENNReal.ofReal (Real.rpow (triadicContinuousKScale (j + 1)).1 (-2 * s.1)) *
            ENNReal.ofReal (continuousKFunctional (triadicContinuousKScale (j + 1)) F ^ 2)) *
          (ENNReal.ofReal ((triadicContinuousKScale j).1)⁻¹ *
            volume (triadicContinuousKInterval j)) := by
          rw [triadicContinuousKUpper_scaleFactor]
          ac_rfl
    _ = _ := by ac_rfl

private theorem triadicContinuousKUpper_interval_bound {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (j : ℕ) :
    (∫⁻ t in triadicContinuousKInterval j, continuousKSeminormIntegrand s.1 F t) ≤
      triadicContinuousKUpperSeriesConstant s * triadicContinuousKSampleTerm s F j := by
  refine (triadicContinuousKInterval_lintegral_bounds s F j).2.trans (le_of_eq ?_)
  unfold triadicContinuousKUpperSeriesConstant triadicContinuousKSampleTerm
    triadicContinuousKUpperSampleWeight
  have hpow : ENNReal.ofReal (Real.rpow (triadicContinuousKScale (j + 1)).1 (-2 * s.1)) =
      ENNReal.ofReal (Real.rpow 3 (2 * s.1)) *
        ENNReal.ofReal (Real.rpow (triadicContinuousKScale j).1 (-2 * s.1)) := by
    rw [triadicContinuousK_rpow_lower s j]
    exact ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)
  rw [hpow]
  calc
    (ENNReal.ofReal (Real.rpow 3 (2 * s.1)) *
          ENNReal.ofReal (Real.rpow (triadicContinuousKScale j).1 (-2 * s.1))) *
        ENNReal.ofReal (continuousKFunctional (triadicContinuousKScale j) F ^ 2) *
        ENNReal.ofReal ((triadicContinuousKScale (j + 1)).1)⁻¹ *
          volume (triadicContinuousKInterval j) =
      (ENNReal.ofReal (Real.rpow 3 (2 * s.1)) *
          ENNReal.ofReal (Real.rpow (triadicContinuousKScale j).1 (-2 * s.1)) *
          ENNReal.ofReal (continuousKFunctional (triadicContinuousKScale j) F ^ 2)) *
        (ENNReal.ofReal ((triadicContinuousKScale (j + 1)).1)⁻¹ *
          volume (triadicContinuousKInterval j)) := by ac_rfl
    _ =
      ENNReal.ofReal 2 * ENNReal.ofReal (Real.rpow 3 (2 * s.1)) *
        (ENNReal.ofReal (Real.rpow (triadicContinuousKScale j).1 (-2 * s.1)) *
          ENNReal.ofReal (continuousKFunctional (triadicContinuousKScale j) F ^ 2)) := by
        rw [triadicContinuousKLower_scaleFactor]
        ac_rfl
    _ = _ := by ac_rfl

/-- The continuum `K` energy dominates the shifted canonical triadic energy. -/
theorem triadicContinuousKLowerSeriesComparison {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    triadicContinuousKLowerSeriesConstant s * triadicContinuousKShiftedSampleEnergy s F ≤
      ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F t := by
  rw [continuousKSeminorm_lintegral_eq_tsum_triadicIntervals]
  rw [triadicContinuousKShiftedSampleEnergy, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum (triadicContinuousKLower_interval_bound s F)

/-- The continuum `K` energy is controlled by the canonical triadic sampled
energy with an explicit base-three constant. -/
theorem triadicContinuousKUpperSeriesComparison {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    (∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F t) ≤
      triadicContinuousKUpperSeriesConstant s * triadicContinuousKSampleEnergy s F := by
  rw [continuousKSeminorm_lintegral_eq_tsum_triadicIntervals]
  rw [triadicContinuousKSampleEnergy, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum (triadicContinuousKUpper_interval_bound s F)

/-- Square-root form of the shifted lower series comparison. -/
theorem triadicContinuousKLowerSeriesComparison_rpow {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    (triadicContinuousKLowerSeriesConstant s *
        triadicContinuousKShiftedSampleEnergy s F) ^ (1 / 2 : ℝ) ≤
      continuousKSeminorm s F := by
  rw [continuousKSeminorm_eq_lintegral]
  exact ENNReal.rpow_le_rpow (triadicContinuousKLowerSeriesComparison s F) (by norm_num)

/-- Square-root form of the upper series comparison. -/
theorem triadicContinuousKUpperSeriesComparison_rpow {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    continuousKSeminorm s F ≤
      (triadicContinuousKUpperSeriesConstant s *
        triadicContinuousKSampleEnergy s F) ^ (1 / 2 : ℝ) := by
  rw [continuousKSeminorm_eq_lintegral]
  exact ENNReal.rpow_le_rpow (triadicContinuousKUpperSeriesComparison s F) (by norm_num)

end

end Homogenization
