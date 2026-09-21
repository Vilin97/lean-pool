/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.OmnificInteger
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Cuts
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.NormalForm
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.NormalForm

/-!
# Native cut and normal-form criteria for the omnific-integer class

The class predicate defined using raw ZFC game codes is exactly fixedness under the class-valued
singleton Conway cut. Equivalently, its canonical Conway normal form has nonnegative support and
an integral constant coefficient. These are the cut and normal-form presentations of Conway's
omnific integers recalled in LM24, Section 1.1; the exponent orientation here is unsigned.
-/

universe u

public noncomputable section

namespace ZFSet.Surreal

/-- A class value is omnific exactly when it equals its singleton cut at distance one. -/
theorem isOmnificInteger_iff_cut (x : Surreal.{u}) :
    x.IsOmnificInteger ↔ x = !{{x - 1} | {x + 1}}'(by
      simp only [Set.mem_singleton_iff]
      rintro _ rfl _ rfl
      simp [sub_eq_add_neg]) := by
  rw [isOmnificInteger_iff, _root_.Surreal.isOmnificInteger_iff,
    ← toSurreal_injective.eq_iff, toSurreal_ofSets, _root_.Surreal.omnificIntegerCut_eq]
  simp only [Set.image_singleton, toSurreal_sub, toSurreal_add, toSurreal_one]

/-- Nonnegativity of every Conway support exponent is unchanged by evaluation. -/
theorem support_subset_Ici_zero_iff_toSurreal (x : Surreal.{u}) :
    support x ⊆ Set.Ici 0 ↔ (toSurreal x).support ⊆ Set.Ici 0 := by
  rw [← image_support, Set.image_subset_iff]
  simp only [Set.subset_def, Set.mem_preimage, Set.mem_Ici,
    ← toSurreal_zero, toSurreal_le_toSurreal]

/-- A class value is omnific exactly when its Conway support is nonnegative and its constant
coefficient is an integer, with the coefficient on the left of the equality. -/
theorem isOmnificInteger_iff_normalForm (x : Surreal.{u}) :
    x.IsOmnificInteger ↔
      support x ⊆ Set.Ici 0 ∧ ∃ z : ℤ, coeff x 0 = (z : ℝ) := by
  rw [isOmnificInteger_iff, _root_.Surreal.isOmnificInteger_iff_normalForm,
    ← support_subset_Ici_zero_iff_toSurreal, coeff_eq_toSurreal, toSurreal_zero]
  constructor
  · rintro ⟨hs, z, hz⟩
    exact ⟨hs, z, hz.symm⟩
  · rintro ⟨hs, z, hz⟩
    exact ⟨hs, z, hz.symm⟩

end ZFSet.Surreal
