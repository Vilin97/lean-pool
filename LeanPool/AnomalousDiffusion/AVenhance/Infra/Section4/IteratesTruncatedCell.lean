/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability

/-! Terminal-time cells and monotonicity of actual nonnegative energies. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual open time cell up to a specified terminal time. -/
def iterateTruncatedCell (s : ℝ) : Set AmnrSpace := Set.Ioo (0 : ℝ) s ×ˢ unitCube

/-- The terminal cell is open for the actual positive-time calculus. -/
theorem iterateTruncatedCell_isOpen (s : ℝ) : IsOpen (iterateTruncatedCell s) := by
  unfold iterateTruncatedCell unitCube
  exact isOpen_Ioo.prod (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo))

/-- Every terminal time in the interval gives a subcell. -/
theorem iterateTruncatedCell_subset {s : ℝ} (hs : s ≤ 1) :
    iterateTruncatedCell s ⊆ timeCube := by
  intro z hz
  exact ⟨⟨hz.1.1, lt_of_lt_of_le hz.1.2 hs⟩, hz.2⟩

/-- Continuous actual fields are integrable on every nonnegative terminal cell. -/
theorem iterate_truncated_cell_integrable {f : AmnrSpace → ℝ}
    (hf : ContinuousOn f (Set.Ici (0 : ℝ) ×ˢ Set.univ)) {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn f (iterateTruncatedCell s) := by
  have hi := iterate_time_cell_integrable_of_continuousOn hf hs
  rw [Measure.prod_restrict] at hi
  change IntegrableOn f (Set.uIoc 0 s ×ˢ unitCube) at hi
  apply hi.mono_set
  intro z hz
  rw [Set.uIoc_of_le hs]
  exact ⟨⟨hz.1.1, hz.1.2.le⟩, hz.2⟩

/-- Nonnegative energy on a terminal cell is bounded by full-cell energy.
This applies to energies, not signed pairings. -/
theorem iterate_truncated_nonnegative_integral_le {f : AmnrSpace → ℝ}
    (hi : IntegrableOn f timeCube) (hf : ∀ z, 0 ≤ f z) {s : ℝ} (hs : s ≤ 1) :
    (∫ z in iterateTruncatedCell s, f z) ≤ ∫ z in timeCube, f z := by
  exact setIntegral_mono_set hi (Filter.Eventually.of_forall hf)
    (Filter.Eventually.of_forall (iterateTruncatedCell_subset hs))

/-- Fubini identifies each terminal cell with the actual time integral. -/
theorem iterate_truncated_integral_eq_interval {f : AmnrSpace → ℝ}
    (hf : ContinuousOn f (Set.Ici (0 : ℝ) ×ˢ Set.univ)) {s : ℝ} (hs : 0 ≤ s) :
    (∫ z in iterateTruncatedCell s, f z) = ∫ t in 0..s, ∫ x in unitCube, f (t, x) := by
  have hi := iterate_time_cell_integrable_of_continuousOn hf hs
  rw [Set.uIoc_of_le hs] at hi
  unfold iterateTruncatedCell
  rw [Measure.volume_eq_prod ℝ (Vec 2), ← Measure.prod_restrict,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc, integral_prod _ hi,
    intervalIntegral.integral_of_le hs]

/-- A terminal signed integral is controlled by the full integral of the
 absolute value; no cancellation in the full signed integral is used. -/
theorem iterate_truncated_integral_abs_le {f : AmnrSpace → ℝ}
    (hi : IntegrableOn f timeCube) {s : ℝ} (hs : s ≤ 1) :
    |∫ z in iterateTruncatedCell s, f z| ≤ ∫ z in timeCube, |f z| := by
  exact abs_integral_le_integral_abs.trans
    (iterate_truncated_nonnegative_integral_le hi.abs (fun _ => abs_nonneg _) hs)

/-- Fubini also applies to actual positive-time pairings with an integrable
 initial-time representative, without initial-time continuity of the pairing. -/
theorem iterate_truncated_integral_eq_interval_of_integrable {f : AmnrSpace → ℝ}
    (hf : IntegrableOn f timeCube) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ z in iterateTruncatedCell s, f z) = ∫ t in 0..s, ∫ x in unitCube, f (t, x) := by
  have hi := hf.mono_set (iterateTruncatedCell_subset hs1)
  rw [IntegrableOn, iterateTruncatedCell, Measure.volume_eq_prod ℝ (Vec 2),
    ← Measure.prod_restrict, Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hi
  unfold iterateTruncatedCell
  rw [Measure.volume_eq_prod ℝ (Vec 2), ← Measure.prod_restrict,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc, integral_prod _ hi,
    intervalIntegral.integral_of_le hs]

end AVenhance.Infra.Section4
