/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyBounds

/-!
# Splitting the two-reflection energy integral

This module isolates the `ENNReal` integral algebra from concrete energy
densities.  The resulting theorem is applied only after the density has been
made opaque at the use site.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace CKN

private theorem seeleyReflectionOne_measurable :
    Measurable (seeleyReflectionOne : Vec 3 → Vec 3) := by
  have hsq : Measurable (fun x : Vec 3 => vecNormSq x) :=
    (contDiff_vecNormSq (d := 3)).continuous.measurable
  change Measurable (fun x : Vec 3 => (vecNormSq x)⁻¹ • x)
  exact hsq.inv.smul measurable_id

private theorem seeleyReflectionTwo_measurable :
    Measurable (seeleyReflectionTwo : Vec 3 → Vec 3) := by
  have hnorm : Continuous (vecEuclideanNorm (d := 3)) := by
    change Continuous (fun x : Vec 3 => Real.sqrt (vecNormSq x))
    exact (contDiff_vecNormSq (d := 3)).continuous.sqrt
  have hden : Continuous (fun x : Vec 3 =>
      (2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x) := by
    fun_prop
  change Measurable (fun x : Vec 3 =>
    ((2 * vecEuclideanNorm x - 1) * vecEuclideanNorm x)⁻¹ • x)
  exact hden.measurable.inv.smul measurable_id

theorem lintegral_reflection_split_coeff {A : Set (Vec 3)}
    (_ : MeasurableSet A) (a b : ℝ≥0∞) (g : Vec 3 → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ y in A,
        a * g (seeleyReflectionOne y) +
          b * g (seeleyReflectionTwo y) ∂volume =
      a * ∫⁻ y in A, g (seeleyReflectionOne y) ∂volume +
        b * ∫⁻ y in A, g (seeleyReflectionTwo y) ∂volume := by
  have h₁ : Measurable (fun y => g (seeleyReflectionOne y)) := by
    exact hg.comp seeleyReflectionOne_measurable
  have h₂ : Measurable (fun y => g (seeleyReflectionTwo y)) := by
    exact hg.comp seeleyReflectionTwo_measurable
  rw [lintegral_add_left (h₁.const_mul a)]
  rw [lintegral_const_mul a h₁, lintegral_const_mul b h₂]

theorem lintegral_reflection_split {A : Set (Vec 3)}
    (hA : MeasurableSet A) (g : Vec 3 → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y in A,
        (18 : ℝ≥0∞) * g (seeleyReflectionOne y) +
          (8 : ℝ≥0∞) * g (seeleyReflectionTwo y) ∂volume =
      18 * ∫⁻ y in A, g (seeleyReflectionOne y) ∂volume +
        8 * ∫⁻ y in A, g (seeleyReflectionTwo y) ∂volume := by
  exact lintegral_reflection_split_coeff hA 18 8 g hg

end CKN
