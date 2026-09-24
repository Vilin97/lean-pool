/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpExponents
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Cutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientForceUnconditional
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Slice Selected Gradient Force Holder

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

/-!
# Hölder conversion for the force-slot bound

A function `η` supported in a ball, bounded by `1`, carries an `L^q` bound on the ball
to an `L^{6/5}` bound on the whole space, with an explicit volume factor.
-/

/-- The `euclideanBall` is open, hence measurable. -/
private lemma euclideanBall_measurable (x₀ : Vec3) (ρ : ℝ) :
    MeasurableSet (euclideanBall x₀ ρ) := by
  have hopen : IsOpen (euclideanBall x₀ ρ) := by
    change IsOpen {y : Vec3 | euclideanSqDist y x₀ < ρ ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  exact hopen.measurableSet

/-- The extended-norm version: `η * g` has its `L^{6/5}` norm over ℝ³ bounded by the
`L^q` norm of `g` on the ball times the ball volume raised to `5/6 - 1/q`. -/
theorem eLpNorm_cutoff_mul_g_le
    {x₀ : Vec3} {ρ q : ℝ} (hρ : 0 < ρ) (hq : 6 / 5 ≤ q)
    {g : Vec3 → ℝ}
    (hg : MemLp g (ENNReal.ofReal q) (volume.restrict (euclideanBall x₀ ρ))) :
    eLpNorm (fun x => mollifiedBallCutoff x₀ hρ x * g x)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      eLpNorm g (ENNReal.ofReal q) (volume.restrict (euclideanBall x₀ ρ)) *
        volume (euclideanBall x₀ ρ) ^ (1 / (6 / 5 : ℝ) - 1 / q) := by
  set η := mollifiedBallCutoff x₀ hρ
  set B := euclideanBall x₀ ρ
  set p := ENNReal.ofReal (6 / 5 : ℝ)
  set q' := ENNReal.ofReal q
  have hpq : p ≤ q' := ENNReal.ofReal_le_ofReal hq
  have hball_meas : MeasurableSet B := euclideanBall_measurable x₀ ρ
  have hη_cont : Continuous η :=
    (mollifiedBallCutoff_smooth x₀ hρ).continuous
  have hη_bound : ∀ x, |η x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (mollifiedBallCutoff_nonneg x₀ hρ x)]
    exact mollifiedBallCutoff_le_one x₀ hρ x
  have hη_support : Function.support η ⊆ B := by
    intro x hx
    have hx' : η x ≠ 0 := hx
    by_contra hnot
    apply hx'
    have hηx : x ∈ tsupport η :=
      subset_tsupport (f := η) (Function.mem_support.mpr hx)
    have hzero : η x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := η) (fun hηx' => by
          have houter : x ∈ euclideanBall x₀ (3 * ρ / 4) := by
            apply mollifiedBallCutoff_tsupport_subset_outer x₀ hρ
            simpa only [η] using hηx'
          have houter_norm :=
            (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 houter
          apply hnot
          apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
          exact houter_norm.trans (by linarith only [hρ]))
    exact hzero
  have hηg_eq_indicator : (fun x => η x * g x) = B.indicator (fun x => η x * g x) := by
    ext x
    by_cases hx : x ∈ B
    · simp [Set.indicator_of_mem hx]
    · have hηx : η x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hηx'
        have houter : x ∈ euclideanBall x₀ (3 * ρ / 4) := by
          apply mollifiedBallCutoff_tsupport_subset_outer x₀ hρ
          simpa only [η] using hηx'
        have houter_norm :=
          (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 houter
        apply hx
        apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
        exact houter_norm.trans (by linarith only [hρ])
      simp [Set.indicator_of_notMem hx, hηx]
  -- Step 1: rewrite the L^{6/5} norm using the indicator
  have h_step1 : eLpNorm (fun x => η x * g x) p volume =
      eLpNorm (fun x => η x * g x) p (volume.restrict B) := by
    calc
      eLpNorm (fun x => η x * g x) p volume =
          eLpNorm (B.indicator (fun x => η x * g x)) p volume := by
            exact congrArg (fun F : Vec3 → ℝ => eLpNorm F p volume) hηg_eq_indicator
      _ = eLpNorm (fun x => η x * g x) p (volume.restrict B) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hball_meas
  -- Step 2: bound |η * g| ≤ |g| on the restricted measure
  have h_step2 : eLpNorm (fun x => η x * g x) p (volume.restrict B) ≤
      eLpNorm g p (volume.restrict B) := by
    have hη_meas_restrict : AEStronglyMeasurable η (volume.restrict B) :=
      hη_cont.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    have hg_meas_restrict : AEStronglyMeasurable g (volume.restrict B) :=
      hg.aestronglyMeasurable
    have hmul_meas : AEStronglyMeasurable (fun x => η x * g x) (volume.restrict B) :=
      hη_meas_restrict.mul hg_meas_restrict
    refine eLpNorm_mono_ae hmul_meas ?_
    filter_upwards [] with x
    have h_abs : |η x * g x| ≤ |g x| := by
      calc
        |η x * g x| = |η x| * |g x| := abs_mul (η x) (g x)
        _ ≤ 1 * |g x| := mul_le_mul_of_nonneg_right (hη_bound x) (abs_nonneg _)
        _ = |g x| := one_mul _
    simpa only [Real.norm_eq_abs] using h_abs
  -- Step 3: apply Hölder comparison on the finite-measure ball
  have h_step3 : eLpNorm g p (volume.restrict B) ≤
      eLpNorm g q' (volume.restrict B) *
        (volume.restrict B) Set.univ ^ (1 / p.toReal - 1 / q'.toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hg.aestronglyMeasurable
  have h_vol : (volume.restrict B) Set.univ = volume B := by
    rw [Measure.restrict_apply_univ]
  have h_exp : 1 / p.toReal - 1 / q'.toReal = 1 / (6 / 5 : ℝ) - 1 / q := by
    have hqpos : 0 ≤ q := by linarith only [hq]
    simp [p, q', ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6/5),
      ENNReal.toReal_ofReal hqpos]
  calc
    eLpNorm (fun x => η x * g x) p volume
        = eLpNorm (fun x => η x * g x) p (volume.restrict B) := h_step1
    _ ≤ eLpNorm g p (volume.restrict B) := h_step2
    _ ≤ eLpNorm g q' (volume.restrict B) *
        (volume.restrict B) Set.univ ^ (1 / p.toReal - 1 / q'.toReal) := h_step3
    _ = eLpNorm g q' (volume.restrict B) * volume B ^ (1 / p.toReal - 1 / q'.toReal) := by
      rw [h_vol]
    _ = eLpNorm g q' (volume.restrict B) *
        volume B ^ (1 / (6 / 5 : ℝ) - 1 / q) := by rw [h_exp]

end CKN.Core.Step4
