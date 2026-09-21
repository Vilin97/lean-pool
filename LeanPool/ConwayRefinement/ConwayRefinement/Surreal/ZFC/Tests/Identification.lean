/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Identification

/-!
# Imported checks of native class omnific criteria

The positive monomial `ω` excludes a definition restricted to ordinary integers. The reciprocal
of two excludes unrestricted constant coefficients, while a negative support exponent violates
the unsigned Conway-support criterion. The native singleton-cut and coefficient formulas below
exercise their exported interfaces without unfolding project definitions.
-/

universe u

public noncomputable section

namespace Tests.ClassOmnificIdentification

example (x : ZFSet.Surreal.{u}) :
    x.IsOmnificInteger ↔ x = !{{x - 1} | {x + 1}}'(by
      simp only [Set.mem_singleton_iff]
      rintro _ rfl _ rfl
      simp [sub_eq_add_neg]) :=
  ZFSet.Surreal.isOmnificInteger_iff_cut x

example (x : ZFSet.Surreal.{u}) :
    x.IsOmnificInteger ↔
      ZFSet.Surreal.support x ⊆ Set.Ici 0 ∧
        ∃ z : ℤ, ZFSet.Surreal.coeff x 0 = (z : ℝ) :=
  ZFSet.Surreal.isOmnificInteger_iff_normalForm x

/-- A negative Conway support exponent rules out the class omnific predicate. -/
theorem not_isOmnificInteger_of_negative_support (x i : ZFSet.Surreal.{u})
    (hi : i ∈ ZFSet.Surreal.support x) (hneg : i < 0) : ¬ x.IsOmnificInteger := by
  intro hx
  exact (not_le_of_gt hneg) (((ZFSet.Surreal.isOmnificInteger_iff_normalForm x).1 hx).1 hi)

/-- The class value with normal form `ω` is an omnific integer. -/
theorem omega_isOmnificInteger :
    (ZFSet.Surreal.equiv.symm (ω^ (1 : Surreal.{u}))).IsOmnificInteger := by
  rw [ZFSet.Surreal.isOmnificInteger_iff_normalForm]
  constructor
  · rw [ZFSet.Surreal.support_subset_Ici_zero_iff_toSurreal,
      ← ZFSet.Surreal.equiv_apply, ZFSet.Surreal.equiv.apply_symm_apply]
    simp
  · refine ⟨0, ?_⟩
    rw [ZFSet.Surreal.coeff_eq_toSurreal, ZFSet.Surreal.toSurreal_zero,
      ← ZFSet.Surreal.equiv_apply, ZFSet.Surreal.equiv.apply_symm_apply]
    simp

/-- The class reciprocal of two is not an omnific integer. -/
theorem two_inv_not_isOmnificInteger :
    ¬ ((2 : ZFSet.Surreal.{u})⁻¹).IsOmnificInteger := by
  rw [ZFSet.Surreal.isOmnificInteger_iff]
  have h := Surreal.two_inv_not_mem_omnificIntegers.{u}
  rw [Surreal.mem_omnificIntegers] at h
  simpa only [← ZFSet.Surreal.ringEquiv_apply, map_inv₀, map_ofNat] using h

end Tests.ClassOmnificIdentification
