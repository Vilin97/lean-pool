/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.FiniteClassReduction
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OneRow

/-!
# Checks for finite support classes

These clients distinguish the support-class set from two nearby wrong definitions: discarding
the zero class, and asking that the support itself be finite. The series `2 + t⁻¹` meets both the
zero and nonzero real classes. Berarducci's row has infinite support but meets just one class.
The zero-series check is only an interface boundary check.
-/

public noncomputable section

open HahnSeries HahnSeries.Nonpositive
open scoped HahnSeries

namespace Tests.FiniteClassReduction

/-- Zero meets no class, rather than meeting the zero class. -/
theorem zero_support_classes : supportArchimedeanClasses (0 : Nonpositive ℝ ℝ) = ∅ :=
  supportArchimedeanClasses_zero

/-- A nonzero ordinary constant meets the zero class. -/
theorem constant_support_classes :
    supportArchimedeanClasses (Nonpositive.single (0 : ℝ) (3 : ℝ) le_rfl) = {⊤} := by
  ext c
  simp [mem_supportArchimedeanClasses, eq_comm]

/-- The two-class fixture `2 + t⁻¹`. -/
def twoClassSeries : Nonpositive ℝ ℝ :=
  Nonpositive.single 0 2 le_rfl + Nonpositive.single (-1) 1 (by norm_num)

/-- The zero exponent contributes a second class even though all nonzero real exponents are
Archimedean-equivalent. -/
theorem twoClass_support_classes :
    supportArchimedeanClasses twoClassSeries = {ArchimedeanClass.mk (-1 : ℝ), ⊤} := by
  have hs : (twoClassSeries : ℝ⟦ℝ⟧).support = {0, -1} := by
    ext g
    by_cases hg0 : g = 0 <;> by_cases hg1 : g = -1 <;>
      simp [HahnSeries.mem_support, twoClassSeries, hg0, hg1]
  ext c
  rw [mem_supportArchimedeanClasses, hs]
  simp [eq_comm, or_comm]

/-- Berarducci's row has infinitely many exponents. -/
theorem oneRow_support_infinite :
    (Berarducci.OneRow.withoutConstant (K := ℝ) : ℝ⟦ℝ⟧).support.Infinite := by
  rw [Berarducci.OneRow.withoutConstant_support]
  exact Set.infinite_range_of_injective Berarducci.OneRow.exponentEmbedding.injective

/-- The same infinite support meets just one Archimedean class. -/
theorem oneRow_support_classes :
    supportArchimedeanClasses (Berarducci.OneRow.withoutConstant (K := ℝ)) =
      {ArchimedeanClass.mk (-1 : ℝ)} := by
  ext c
  rw [mem_supportArchimedeanClasses, Set.mem_singleton_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg0 : g ≠ 0 := by
      intro hzero
      subst g
      exact (HahnSeries.mem_support _ _).mp hg Berarducci.OneRow.withoutConstant_coeff_zero
    exact ArchimedeanClass.mk_eq_mk_of_archimedean hg0 (by norm_num)
  · rintro rfl
    refine ⟨-1, ?_, rfl⟩
    rw [HahnSeries.mem_support]
    have hcoeff := Berarducci.OneRow.withoutConstant_coeff_exponent (K := ℝ) 0
    norm_num [Berarducci.OneRow.exponent_apply] at hcoeff
    rw [hcoeff]
    exact one_ne_zero

end Tests.FiniteClassReduction
