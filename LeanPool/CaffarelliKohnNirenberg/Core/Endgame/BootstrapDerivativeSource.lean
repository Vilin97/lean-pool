/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.BootstrapSourceBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CausalDerivativeSource

/-! # The first bootstrap's differentiated cutoff source

The initial velocity exponent controls the actual differentiated source
without lowering integrability. Unit-cylinder support then lowers only the
outer Morrey exponent, with numerical factor one.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Core.Step3

noncomputable section
namespace CKN.Core.Endgame

/-- The literal differentiated source has the first-bootstrap exponents
and an explicit bound from the initial velocity and cutoff derivatives. -/
theorem bootstrap_derivative_source_of_suitableWeakSolution
    (C : ℝ) (KU : ℝ≥0∞) (hC : 0 ≤ C)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {φ : Vec3 × ℝ → ℝ}
    {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hsupp : ∀ z ∈ tsupport φ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 (11 / 16))
    (hder : ∀ z : Vec3 × ℝ, z.2 ≤ 0 → ∀ j, |spatialPartial φ j z| ≤ C)
    (hN : ∀ i, morreyNorm 3 (25 / 3)
      ((parabolicCylinder (0 : Vec3) 0 (11 / 16)).indicator (fun z => u z i)) ≤ KU) :
    ∀ j i, AEMeasurable (causalDerivativeComponent φ u j i) volume ∧
      morreyNorm 3 (25 / 6) (causalDerivativeComponent φ u j i) ≤
        ENNReal.ofReal (2 * C) * KU := by
  obtain ⟨hu, _, _, _⟩ := bootstrap_indicated_components_aemeasurable hsol hdom
  intro j i
  let a : ParabolicPoint → ℝ := fun z => -2 * spatialPartial φ j z
  have ha : AEMeasurable a volume := aemeasurable_const.mul
    (((spatialPartial_contDiff hφ.1 j).continuous.comp
      continuous_parabolicPoint_to_prod).measurable.aemeasurable)
  have hs : ∀ z : ParabolicPoint, z.2 ≤ 0 →
      z ∉ parabolicCylinder (0 : Vec3) 0 (11 / 16) → a z = 0 := by
    intro z ht hz
    change -2 * spatialPartial φ j z = 0
    rw [(bootstrap_cutoff_coefficients_zero hφ.1 hsupp ht hz).2.2.1 j, mul_zero]
  have hb : ∀ z : ParabolicPoint, z.2 ≤ 0 → |a z| ≤ 2 * C := by
    intro z ht
    change |-2 * spatialPartial φ j z| ≤ 2 * C
    rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (hder z ht j) (by norm_num)
  have heq : causalDerivativeComponent φ u j i = pastMultiplierSource a (fun z => u z i) := rfl
  rw [heq]
  refine ⟨bootstrap_pastMultiplierSource_aemeasurable ha (hu i) hs, ?_⟩
  have hbase := (bootstrap_pastMultiplierSource_morrey_le 3 (25 / 3) (2 * C)
    (by norm_num) (mul_nonneg (by norm_num) hC) a (fun z => u z i) hb hs).trans
    (mul_le_mul_of_nonneg_left (hN i) (by positivity))
  have hunit : ∀ z ∉ parabolicCylinder (0 : Vec3) 0 1,
      pastMultiplierSource a (fun z => u z i) z = 0 := by
    intro z hz
    apply bootstrap_pastMultiplierSource_zero_outside_intermediate hs
    exact fun hm => hz (parabolicCylinder_mono (by norm_num) (by norm_num) hm)
  have hlow := morreyNorm_lower_morrey_exponent (p := (3 : ℝ))
    (q := (25 / 3 : ℝ)) (q' := (25 / 6 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (z₀ := ((0, 0) : ParabolicPoint)) one_pos hunit
  simpa only [ENNReal.ofReal_one, ENNReal.one_rpow, one_mul] using hlow.trans
    (mul_le_mul_of_nonneg_left hbase (by positivity))

end CKN.Core.Endgame
