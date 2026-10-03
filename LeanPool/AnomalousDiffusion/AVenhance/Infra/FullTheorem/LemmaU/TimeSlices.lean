/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LemmaU.ModeCoefficients
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lemma U: time slices of space-time integrable functions

Fubini bookkeeping for the space-time cell `(0,1) × (0,1)²`: integrals over `timeCube` are iterated
interval/cell integrals, the slice integral is interval integrable, and a.e. time slice of an
integrable function is integrable.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization

namespace AVenhance.Infra.FullTheorem.LemmaU

theorem timeCube_measure_eq_product :
    (volume.restrict AVenhance.timeCube) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume.restrict AVenhance.unitCube) := by
  rw [AVenhance.timeCube, Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (Vec 2)]

theorem timeMeasure_Ioo_eq_Ioc :
    volume.restrict (Set.Ioo (0 : ℝ) 1) = volume.restrict (Set.Ioc (0 : ℝ) 1) :=
  Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc

theorem integral_timeCube_eq_interval_cell {F : ℝ × Vec 2 → ℝ}
    (hF : Integrable F (volume.restrict AVenhance.timeCube)) :
    ∫ p in AVenhance.timeCube, F p =
      ∫ t in (0 : ℝ)..1, ∫ x in AVenhance.unitCube, F (t, x) := by
  have hproduct : Integrable F
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume.restrict AVenhance.unitCube)) := by
    rwa [← timeCube_measure_eq_product]
  calc
    ∫ p in AVenhance.timeCube, F p =
        ∫ t, ∫ x, F (t, x) ∂(volume.restrict AVenhance.unitCube)
        ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
            rw [timeCube_measure_eq_product, integral_prod F hproduct]
    _ = ∫ t, ∫ x, F (t, x) ∂(volume.restrict AVenhance.unitCube)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
            rw [timeMeasure_Ioo_eq_Ioc]
    _ = ∫ t in (0 : ℝ)..1, ∫ x in AVenhance.unitCube, F (t, x) := by
            symm
            exact intervalIntegral.integral_of_le (by norm_num)

theorem intervalIntegrable_cell_of_timeCube {F : ℝ × Vec 2 → ℝ}
    (hF : Integrable F (volume.restrict AVenhance.timeCube)) :
    IntervalIntegrable (fun t => ∫ x in AVenhance.unitCube, F (t, x)) volume 0 1 := by
  have hproduct : Integrable F
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume.restrict AVenhance.unitCube)) := by
    rwa [← timeCube_measure_eq_product]
  have htime : Integrable (fun t => ∫ x, F (t, x) ∂(volume.restrict AVenhance.unitCube))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := hproduct.integral_prod_left
  have htime' : Integrable (fun t => ∫ x, F (t, x) ∂(volume.restrict AVenhance.unitCube))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [← timeMeasure_Ioo_eq_Ioc]
    exact htime
  rw [intervalIntegrable_iff, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact htime'

/-- A.e. time slice of a space-time integrable function is integrable on the cell. -/
theorem section_integrable_ae {F : ℝ × Vec 2 → ℝ}
    (hF : Integrable F (volume.restrict AVenhance.timeCube)) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      Integrable (fun x => F (t, x)) (volume.restrict AVenhance.unitCube) := by
  have hproduct : Integrable F
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume.restrict AVenhance.unitCube)) := by
    rwa [← timeCube_measure_eq_product]
  have hsections := hproduct.prod_right_ae
  rw [← timeMeasure_Ioo_eq_Ioc]
  exact hsections

end AVenhance.Infra.FullTheorem.LemmaU

end
