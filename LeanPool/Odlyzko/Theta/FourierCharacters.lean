/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.TorusPeriodization

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

namespace NumberField.Odlyzko

variable {ι : Type*} [Fintype ι]

theorem mFourier_torusQuotientMap
    (n : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier n (torusQuotientMap x) =
      Complex.exp (2 * Real.pi * Complex.I *
        ∑ i, (n i : ℂ) * (x i : ℂ)) := by
  simp only [UnitAddTorus.mFourier, torusQuotientMap,
    ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  push_cast
  rw [Finset.mul_sum]
  ring_nf

theorem mFourier_neg_torusQuotientMap
    (n : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier (-n) (torusQuotientMap x) =
      Complex.exp (-2 * Real.pi * Complex.I *
        ∑ i, (n i : ℂ) * (x i : ℂ)) := by
  rw [mFourier_torusQuotientMap]
  simp

@[simp]
theorem norm_mFourier_torusQuotientMap
    (n : ι → ℤ) (x : ι → ℝ) :
    ‖UnitAddTorus.mFourier n (torusQuotientMap x)‖ = 1 := by
  simp only [UnitAddTorus.mFourier, torusQuotientMap,
    ContinuousMap.coe_mk, norm_prod, fourier_coe_apply]
  apply Finset.prod_eq_one
  intro i _
  rw [Complex.norm_exp]
  simp

end NumberField.Odlyzko
