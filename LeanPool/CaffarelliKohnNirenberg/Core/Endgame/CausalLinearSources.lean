/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CutoffMorrey
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Causal bounded multipliers for linear heat sources

Indicated input measurability suffices for a supported product after
truncation to the past. Uniform multiplier bounds control its Morrey norm.
The improved velocity exponent supplies the linear velocity terms, while
a cutoff of absolute value at most one preserves pressure-gradient bounds.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey


noncomputable section

namespace CKN.Core.Endgame

/-- A scalar product restricted to nonpositive times. -/
def pastMultiplierSource (a f : ParabolicPoint → ℝ) : ParabolicPoint → ℝ :=
  {z : ParabolicPoint | z.2 ≤ 0}.indicator (fun z => a z * f z)

/-- The support of the past product lies in the intermediate cylinder. -/
theorem pastMultiplierSource_zero_outside_intermediate
    {a f : ParabolicPoint → ℝ}
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) → a z = 0)
    {z : ParabolicPoint} (hz : z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8)) :
    pastMultiplierSource a f z = 0 := by
  unfold pastMultiplierSource
  by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
  · rw [indicator_of_mem ht, hsupp z ht hz, zero_mul]
  · exact indicator_of_notMem ht _

/-- The causal product is measurable without a global measurability
assumption on the original input. -/
theorem pastMultiplierSource_aemeasurable
    {a f : ParabolicPoint → ℝ}
    (ha : AEMeasurable a volume)
    (hf : AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator f) volume)
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) → a z = 0) :
    AEMeasurable (pastMultiplierSource a f) volume := by
  have hPast : MeasurableSet {z : ParabolicPoint | z.2 ≤ 0} :=
    (isClosed_le continuous_snd_parabolicPoint continuous_const).measurableSet
  have heq : pastMultiplierSource a f =
      {z : ParabolicPoint | z.2 ≤ 0}.indicator
        (fun z => a z * (parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator f z) := by
    funext z
    unfold pastMultiplierSource
    by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
    · rw [indicator_of_mem ht, indicator_of_mem ht]
      by_cases hz : z ∈ parabolicCylinder (0 : Vec3) 0 (5 / 8)
      · rw [indicator_of_mem hz]
      · rw [indicator_of_notMem hz, hsupp z ht hz, zero_mul, mul_zero]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht]
  rw [heq]
  exact (ha.mul hf).indicator hPast

/-- A bounded past multiplier preserves a Morrey exponent pair with its
explicit multiplier factor. -/
theorem pastMultiplierSource_morrey_le
    (P τ C : ℝ) (hP : 0 < P) (hC : 0 ≤ C)
    (a f : ParabolicPoint → ℝ)
    (hbound : ∀ z, z.2 ≤ 0 → |a z| ≤ C)
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) → a z = 0) :
    morreyNorm P τ (pastMultiplierSource a f) ≤
      ENNReal.ofReal C * morreyNorm P τ
        ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator f) := by
  let b := {z : ParabolicPoint | z.2 ≤ 0}.indicator a
  have hb : ∀ z, |b z| ≤ C := by
    intro z
    by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
    · simpa only [b, indicator_of_mem ht] using hbound z ht
    · simpa only [b, indicator_of_notMem ht, abs_zero] using hC
  have hbs : ∀ z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8), b z = 0 := by
    intro z hz
    by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
    · simpa only [b, indicator_of_mem ht] using hsupp z ht hz
    · exact indicator_of_notMem ht _
  have heq : pastMultiplierSource a f = fun z => b z * f z := by
    funext z
    by_cases ht : z ∈ {w : ParabolicPoint | w.2 ≤ 0}
    · simp only [pastMultiplierSource, b, indicator_of_mem ht]
    · simp only [pastMultiplierSource, b, indicator_of_notMem ht, zero_mul]
  rw [heq]
  exact morrey_norm_mul_le_indicator P τ C hP hC
    (parabolicCylinder (0 : Vec3) 0 (5 / 8)) b f hb hbs

private theorem pastMultiplierSource_zero_outside_unit
    {a f : ParabolicPoint → ℝ}
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) → a z = 0)
    (z : ParabolicPoint) (hz : z ∉ parabolicCylinder (0 : Vec3) 0 1) :
    pastMultiplierSource a f z = 0 := by
  apply pastMultiplierSource_zero_outside_intermediate hsupp
  intro hm
  exact hz (parabolicCylinder_mono (by norm_num) (by norm_num) hm)

/-- An improved `(3,25)` velocity input supplies each bounded linear
source at the paper heat-source exponents, with an explicit coefficient. -/
theorem causal_linear_velocity_source_morrey_le
    (q C : ℝ) (KU : ℝ≥0∞) (hq : 5 / 2 < q) (hC : 0 ≤ C)
    (a f : ParabolicPoint → ℝ)
    (ha : AEMeasurable a volume)
    (hf : AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator f) volume)
    (hbound : ∀ z, z.2 ≤ 0 → |a z| ≤ C)
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) → a z = 0)
    (hN : morreyNorm 3 25 ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator f) ≤ KU) :
    AEMeasurable (pastMultiplierSource a f) volume ∧
      morreyNorm (6 / 5) (min q (25 / 9 : ℝ)) (pastMultiplierSource a f) ≤
        ENNReal.ofReal C *
          (volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU) := by
  refine ⟨pastMultiplierSource_aemeasurable ha hf hsupp, ?_⟩
  have hlowerP := morreyNorm_lower_integrability (p' := (6 / 5 : ℝ))
    (p := (3 : ℝ)) (q := (25 : ℝ)) (by norm_num) (by norm_num) (by norm_num) hf
  have hinput : morreyNorm (6 / 5) 25
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator f) ≤
      volume (parabolicCylinder 0 0 1) ^ (5 / 6 - 1 / 3 : ℝ) * KU := by
    have hinput' := hlowerP.trans (mul_le_mul_of_nonneg_left hN (by positivity))
    convert hinput' using 1
    norm_num
  have hproduct := (pastMultiplierSource_morrey_le (6 / 5) 25 C (by norm_num)
    hC a f hbound hsupp).trans (mul_le_mul_of_nonneg_left hinput (by positivity))
  have hmin : (6 / 5 : ℝ) ≤ min q (25 / 9) :=
    le_min (by linarith only [hq]) (by norm_num)
  have hlower := morreyNorm_lower_morrey_exponent (p := (6 / 5 : ℝ)) (q := (25 : ℝ))
    (q' := min q (25 / 9 : ℝ)) (by norm_num) (by norm_num) hmin
    ((min_le_right _ _).trans (by norm_num)) (z₀ := ((0, 0) : ParabolicPoint))
    one_pos (pastMultiplierSource_zero_outside_unit (f := f) hsupp)
  simp only [ENNReal.ofReal_one, ENNReal.one_rpow, one_mul] at hlower
  exact hlower.trans hproduct

/-- A cutoff of absolute value at most one preserves the pressure-gradient
source exponent and its numerical bound. -/
theorem causal_linear_pressure_source_morrey_le
    (q : ℝ) (KP : ℝ≥0∞) (a f : ParabolicPoint → ℝ)
    (ha : AEMeasurable a volume)
    (hf : AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator f) volume)
    (hbound : ∀ z, z.2 ≤ 0 → |a z| ≤ 1)
    (hsupp : ∀ z, z.2 ≤ 0 → z ∉ parabolicCylinder (0 : Vec3) 0 (5 / 8) → a z = 0)
    (hN : morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
      ((parabolicCylinder (0 : Vec3) 0 (5 / 8)).indicator f) ≤ KP) :
    AEMeasurable (pastMultiplierSource a f) volume ∧
      morreyNorm (6 / 5) (min q (25 / 9 : ℝ)) (pastMultiplierSource a f) ≤ KP := by
  refine ⟨pastMultiplierSource_aemeasurable ha hf hsupp, ?_⟩
  have hproduct := pastMultiplierSource_morrey_le (6 / 5) (min q (25 / 9)) 1
    (by norm_num) (by norm_num) a f hbound hsupp
  simp only [ENNReal.ofReal_one, one_mul] at hproduct
  exact hproduct.trans hN

end CKN.Core.Endgame
