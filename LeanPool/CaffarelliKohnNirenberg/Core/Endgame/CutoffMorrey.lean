/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.MorreyScaling
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial

/-! # Quantitative cutoff multiplication for Morrey sources

A bounded multiplier supported in a prescribed set only uses the Morrey norm
of the source restricted to that set. Lowering the integrability exponent
then supplies the differentiated heat-source norm, including after truncation
to nonpositive times.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Endgame

/-- A bounded supported multiplier is controlled by the indicated source
norm. No measurability assumption is needed for this upper-integral bound. -/
theorem morrey_norm_mul_le_indicator (P τ C : ℝ) (hP : 0 < P) (hC : 0 ≤ C)
    (S : Set ParabolicPoint) (a f : ParabolicPoint → ℝ)
    (ha : ∀ z, |a z| ≤ C) (hsupp : ∀ z ∉ S, a z = 0) :
    morreyNorm P τ (fun z => a z * f z) ≤
      ENNReal.ofReal C * morreyNorm P τ (S.indicator f) := by
  have hmono : morreyNorm P τ (fun z => a z * f z) ≤
      morreyNorm P τ (fun z => C * S.indicator f z) := by
    apply morreyNorm_mono hP.le
    intro z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz, abs_mul, abs_mul, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha z) (abs_nonneg _)
    · rw [hsupp z hz, indicator_of_notMem hz, zero_mul, mul_zero]
  exact hmono.trans (by
    simpa only [abs_of_nonneg hC] using morreyNorm_const_mul_le hP C (S.indicator f))

/-- A bounded cutoff times an indicated `(3,25/3)` source has an explicit
`(6/5,25/3)` Morrey bound. -/
theorem cutoff_source_lower_integrability_bound (C : ℝ) (KU : ℝ≥0∞) (hC : 0 ≤ C)
    (S : Set ParabolicPoint) (a f : ParabolicPoint → ℝ)
    (ha : ∀ z, |a z| ≤ C) (hsupp : ∀ z ∉ S, a z = 0)
    (hf : AEMeasurable (S.indicator f) volume)
    (hN : morreyNorm 3 (25 / 3) (S.indicator f) ≤ KU) :
    morreyNorm (6 / 5) (25 / 3) (fun z => a z * f z) ≤
      ENNReal.ofReal C *
        (volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU) := by
  have hmul := morrey_norm_mul_le_indicator (6 / 5) (25 / 3) C
    (by norm_num) hC S a f ha hsupp
  have hlow := morreyNorm_lower_integrability (p' := 6 / 5) (p := 3) (q := 25 / 3)
    (by norm_num) (by norm_num) (by norm_num) hf
  have hbound := hlow.trans (mul_le_mul_of_nonneg_left hN (by positivity))
  have hbound' : morreyNorm (6 / 5) (25 / 3) (S.indicator f) ≤
      volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU := by
    convert hbound using 1
    norm_num
  exact hmul.trans (mul_le_mul_of_nonneg_left hbound' (by positivity))

/-- The past-time differentiated source `-2 ∂ⱼφ uᵢ` has the explicit
Morrey bound supplied by a past derivative bound and the initial velocity
component norm on the intermediate cylinder. -/
theorem past_derivative_source_morrey_le (C : ℝ) (KU : ℝ≥0∞) (hC : 0 ≤ C)
    (φ : ParabolicPoint → ℝ) (u : ParabolicPoint → Vec3) (j i : Fin 3)
    (hder : ∀ z : ParabolicPoint, z.2 ≤ 0 → |spatialPartial φ j z| ≤ C)
    (hsupp : ∀ z : ParabolicPoint, z.2 ≤ 0 →
      z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) → spatialPartial φ j z = 0)
    (hu : AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) volume)
    (hN : morreyNorm 3 (25 / 3) ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator
      (fun z => u z i)) ≤ KU) :
    morreyNorm (6 / 5) (25 / 3)
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator
        (fun z => -2 * spatialPartial φ j z * u z i)) ≤
      ENNReal.ofReal (2 * C) *
        (volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU) := by
  let a : ParabolicPoint → ℝ := {z : ParabolicPoint | z.2 ≤ 0}.indicator
    (fun z => -2 * spatialPartial φ j z)
  have ha : ∀ z, |a z| ≤ 2 * C := by
    intro z
    by_cases hz : z ∈ {z : ParabolicPoint | z.2 ≤ 0}
    · change |({z : ParabolicPoint | z.2 ≤ 0}.indicator
        (fun z => -2 * spatialPartial φ j z)) z| ≤ _
      rw [indicator_of_mem hz, abs_mul]
      rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left (hder z hz) (by norm_num)
    · simp only [a, indicator_of_notMem hz, abs_zero]
      exact mul_nonneg (by norm_num) hC
  have hasupp : ∀ z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8), a z = 0 := by
    intro z hz
    by_cases ht : z ∈ {z : ParabolicPoint | z.2 ≤ 0}
    · simp only [a, indicator_of_mem ht, hsupp z ht hz, mul_zero]
    · exact indicator_of_notMem ht _
  have heq : {z : ParabolicPoint | z.2 ≤ 0}.indicator
      (fun z => -2 * spatialPartial φ j z * u z i) = (fun z => a z * u z i) := by
    funext z
    by_cases ht : z ∈ {z : ParabolicPoint | z.2 ≤ 0}
    · simp only [a, indicator_of_mem ht]
    · simp only [a, indicator_of_notMem ht, zero_mul]
  rw [heq]
  exact cutoff_source_lower_integrability_bound (2 * C) KU (mul_nonneg (by norm_num) hC)
    (parabolicCylinder (0 : Vec3) 0 (5 / 8)) a (fun z => u z i) ha hasupp hu hN

end CKN.Core.Endgame
