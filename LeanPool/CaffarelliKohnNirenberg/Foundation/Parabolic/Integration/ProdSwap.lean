/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Prod Swap

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open CKN.Foundation.Parabolic
open scoped ENNReal


noncomputable section

namespace CKN.Foundation.Parabolic.Integration

/-- Tonelli's theorem for set integrals on a product of a spatial set `S ⊆ Vec3`
and a time interval `T ⊆ ℝ`: the integral of a nonnegative measurable function over
the cylinder `S ×ˢ T` equals the iterated integral with the time variable outermost,
using the product Lebesgue measure on `Vec3 × ℝ`. -/
theorem prod_lintegral_swap_cyl {S : Set Vec3} {T : Set ℝ}
    {F : Vec3 × ℝ → ℝ≥0∞}
    (hF : AEMeasurable F ((volume.restrict S).prod (volume.restrict T))) :
    (∫⁻ z in S ×ˢ T, F z) = ∫⁻ s in T, ∫⁻ y in S, F (y, s) := by
  rw [show (volume : Measure (Vec3 × ℝ)) =
      (volume : Measure Vec3).prod (volume : Measure ℝ) from
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict]
  calc
    _ = ∫⁻ y : Vec3, ∫⁻ s : ℝ, F (y, s)
        ∂(volume.restrict T) ∂(volume.restrict S) :=
      MeasureTheory.lintegral_prod F hF
    _ = _ := MeasureTheory.lintegral_lintegral_swap (by
      change AEMeasurable F ((volume.restrict S).prod (volume.restrict T))
      exact hF)

end CKN.Foundation.Parabolic.Integration
