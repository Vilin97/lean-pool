/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceComponents
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalEquationRepresentation

/-! # The past-time convective heat source

The initial velocity exponent and initial gradient exponent give the
convective source estimate by scalar Morrey Hölder and the finite-sum
triangle inequality. Only the cutoff's nonpositive-time values are used.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3

noncomputable section
namespace CKN.Core.Endgame

/-- Component source bounds give the actual past convection source's
measurability and quantitative paper-exponent Morrey bound. -/
theorem bootstrap_past_convection_source_morrey_le (KU KD : ℝ≥0∞)
    (φ : ParabolicPoint → ℝ) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (i : Fin 3)
    (hφ : AEMeasurable φ volume)
    (hφbound : ∀ z : ParabolicPoint, z.2 ≤ 0 → |φ z| ≤ 1)
    (hφsupp : ∀ z : ParabolicPoint, z.2 ≤ 0 →
      z ∉ parabolicCylinder (0 : Vec3) 0 (11 / 16) → φ z = 0)
    (hu : ∀ j, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => u z j)) volume)
    (hDu : ∀ j, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => Du z i j)) volume)
    (hUN : ∀ j, morreyNorm 3 (25 / 3) ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => u z j)) ≤ KU)
    (hDN : ∀ j, morreyNorm 2 (25 / 8) ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator
      (fun z => Du z i j)) ≤ KD) :
    AEMeasurable ({z : ParabolicPoint | z.2 ≤ 0}.indicator
      (fun z => φ z * localizedConvection u Du z i)) volume ∧
    morreyNorm (6 / 5) ((25 / 11))
      ({z : ParabolicPoint | z.2 ≤ 0}.indicator
        (fun z => φ z * localizedConvection u Du z i)) ≤ 3 * KU * KD := by
  let S := parabolicCylinder (0 : Vec3) 0 (11 / 16)
  let U : Fin 3 → ParabolicPoint → ℝ := fun j => S.indicator (fun z => u z j)
  let D : Fin 3 → ParabolicPoint → ℝ := fun j => S.indicator (fun z => Du z i j)
  let B : ParabolicPoint → ℝ := fun z => ∑ j, U j z * D j z
  let a : ParabolicPoint → ℝ := {z : ParabolicPoint | z.2 ≤ 0}.indicator φ
  have hterm : ∀ j, AEMeasurable (fun z => U j z * D j z) volume :=
    fun j => (hu j).mul (hDu j)
  have hB : AEMeasurable B volume := by
    simpa [B, Fin.sum_univ_succ, Pi.add_def] using (hterm 0).add ((hterm 1).add (hterm 2))
  have ha : AEMeasurable a volume :=
    hφ.indicator (measurableSet_le measurable_snd measurable_const)
  have haone : ∀ z, |a z| ≤ 1 := by
    intro z
    by_cases hz : z ∈ {z : ParabolicPoint | z.2 ≤ 0}
    · simpa only [a, indicator_of_mem hz] using hφbound z hz
    · simp only [a, indicator_of_notMem hz, abs_zero, zero_le_one]
  have heq : {z : ParabolicPoint | z.2 ≤ 0}.indicator
      (fun z => φ z * localizedConvection u Du z i) = (fun z => a z * B z) := by
    funext z
    by_cases hz : z ∈ {z : ParabolicPoint | z.2 ≤ 0}
    · by_cases hzS : z ∈ S
      · simp only [a, B, U, D, indicator_of_mem hz, indicator_of_mem hzS, localizedConvection]
      · simp only [a, indicator_of_mem hz, hφsupp z hz hzS, zero_mul]
    · simp only [a, indicator_of_notMem hz, zero_mul]
  have hprod : ∀ j, morreyNorm (6 / 5) (25 / 11) (fun z => U j z * D j z) ≤ KU * KD := by
    intro j
    have h := morreyNorm_holder (p := 6 / 5) (p₁ := 3) (p₂ := 2)
      (q := 25 / 11) (q₁ := 25 / 3) (q₂ := 25 / 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (hu j) (hDu j)
    exact h.trans (mul_le_mul (hUN j) (hDN j) (by positivity) (by positivity))
  have h12 := (morrey_norm_add_le (τ := 25 / 11) (by norm_num : (1 : ℝ) ≤ 6 / 5)
    (hterm 1) (hterm 2)).trans (add_le_add (hprod 1) (hprod 2))
  have hsum := (morrey_norm_add_le (τ := 25 / 11) (by norm_num : (1 : ℝ) ≤ 6 / 5)
    (hterm 0) ((hterm 1).add (hterm 2))).trans (add_le_add (hprod 0) h12)
  have hBN : morreyNorm (6 / 5) (25 / 11) B ≤ 3 * KU * KD := by
    have hthree : KU * KD + (KU * KD + KU * KD) = 3 * KU * KD := by ring
    simpa [B, Fin.sum_univ_succ, hthree] using hsum
  have hmul : morreyNorm (6 / 5) (25 / 11) (fun z => a z * B z) ≤
      morreyNorm (6 / 5) (25 / 11) B := by
    apply morreyNorm_mono (by norm_num)
    intro z
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (haone z) (abs_nonneg (B z))
  rw [heq]
  exact ⟨ha.mul hB, hmul.trans hBN⟩

end CKN.Core.Endgame
