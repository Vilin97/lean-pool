/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.Geometry
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Mean subtraction for ball estimates

Adapted from CoarseGraining (LeanIntoHomogenization, 2026) with the author's
permission.  These identities separate the average bookkeeping from the
analytic segment estimate.
-/

public section

namespace CKN

theorem sub_integralAverage_eq_volumeAverage_sub
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeOn U)]
    {u : Vec d → ℝ} (hu : MeasureTheory.IntegrableOn u U) (x : Vec d)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    u x - integralAverage U u =
      (MeasureTheory.volume U).toReal⁻¹ *
        ∫ y in U, (u x - u y) ∂MeasureTheory.volume := by
  have hμ_ne : (MeasureTheory.volume U).toReal ≠ 0 := ne_of_gt hvol
  have hconstInt : MeasureTheory.IntegrableOn (fun _ : Vec d => u x) U := by
    simp [MeasureTheory.IntegrableOn]
  have hconst :
      ∫ y in U, (u x : ℝ) ∂MeasureTheory.volume =
        (MeasureTheory.volume U).toReal * u x := by
    rw [MeasureTheory.integral_const, smul_eq_mul]
    have hμ₁ :
        (MeasureTheory.volume.restrict U).real Set.univ =
          MeasureTheory.volume.real U := by
      exact MeasureTheory.measureReal_restrict_apply_univ (μ := MeasureTheory.volume) U
    rw [hμ₁]
    rfl
  let I : ℝ := ∫ y in U, u y ∂MeasureTheory.volume
  have hscale :
      u x - (MeasureTheory.volume U).toReal⁻¹ * I =
        (MeasureTheory.volume U).toReal⁻¹ *
          ((MeasureTheory.volume U).toReal * u x - I) := by
    field_simp [hμ_ne]
  calc
    u x - integralAverage U u =
        u x - (MeasureTheory.volume U).toReal⁻¹ * I := by
          rw [integralAverage, MeasureTheory.setAverage_eq]
          change u x - (MeasureTheory.volume U).toReal⁻¹ *
              (∫ y in U, u y ∂MeasureTheory.volume) =
            u x - (MeasureTheory.volume U).toReal⁻¹ * I
          rfl
    _ = (MeasureTheory.volume U).toReal⁻¹ *
          ((MeasureTheory.volume U).toReal * u x - I) := hscale
    _ = (MeasureTheory.volume U).toReal⁻¹ *
          ((∫ y in U, u x ∂MeasureTheory.volume) - I) := by
            rw [← hconst]
    _ = (MeasureTheory.volume U).toReal⁻¹ *
          ∫ y in U, (u x - u y) ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_sub hconstInt.integrable hu.integrable]

theorem norm_sub_integralAverage_le_volumeAverage_integral_norm_sub
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeOn U)]
    {u : Vec d → ℝ} (hu : MeasureTheory.IntegrableOn u U) (x : Vec d)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    ‖u x - integralAverage U u‖ ≤
      (MeasureTheory.volume U).toReal⁻¹ *
        ∫ y in U, ‖u x - u y‖ ∂MeasureTheory.volume := by
  have hμinv_nonneg : 0 ≤ (MeasureTheory.volume U).toReal⁻¹ := by
    positivity
  calc
    ‖u x - integralAverage U u‖ =
        ‖(MeasureTheory.volume U).toReal⁻¹ *
          ∫ y in U, (u x - u y) ∂MeasureTheory.volume‖ := by
            rw [sub_integralAverage_eq_volumeAverage_sub hu x hvol]
    _ = (MeasureTheory.volume U).toReal⁻¹ *
          ‖∫ y in U, (u x - u y) ∂MeasureTheory.volume‖ := by
            rw [norm_mul, Real.norm_of_nonneg hμinv_nonneg]
    _ ≤ (MeasureTheory.volume U).toReal⁻¹ *
          ∫ y in U, ‖u x - u y‖ ∂MeasureTheory.volume := by
            gcongr
            exact MeasureTheory.norm_integral_le_integral_norm (fun y => u x - u y)

end CKN
