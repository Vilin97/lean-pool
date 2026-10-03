/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedCell

/-! # Iterates Terminal Signed Pairing

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Fubini preserves the two signed terms of the actual energy identity. -/
theorem iterate_terminal_signed_pairing_identity {f g : AmnrSpace → ℝ}
    (hf : ContinuousOn f (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hg : ContinuousOn g (Set.Ici (0 : ℝ) ×ˢ Set.univ)) {s : ℝ} (hs : 0 ≤ s) :
    (∫ t in 0..s, -(∫ x in unitCube, f (t, x)) - (∫ x in unitCube, g (t, x))) =
      -(∫ z in iterateTruncatedCell s, f z) - (∫ z in iterateTruncatedCell s, g z) := by
  have hfi := iterate_time_cell_integrable_of_continuousOn hf hs
  have hgi := iterate_time_cell_integrable_of_continuousOn hg hs
  have hft : IntervalIntegrable (fun t => ∫ x in unitCube, f (t, x)) volume 0 s :=
    intervalIntegrable_iff.mpr hfi.integral_prod_left
  have hgt : IntervalIntegrable (fun t => ∫ x in unitCube, g (t, x)) volume 0 s :=
    intervalIntegrable_iff.mpr hgi.integral_prod_left
  have he := intervalIntegral.integral_sub hft.neg hgt
  dsimp only [Pi.neg_apply] at he
  rw [he, intervalIntegral.integral_neg,
    ← iterate_truncated_integral_eq_interval hf hs,
    ← iterate_truncated_integral_eq_interval hg hs]

end AVenhance.Infra.Section4
