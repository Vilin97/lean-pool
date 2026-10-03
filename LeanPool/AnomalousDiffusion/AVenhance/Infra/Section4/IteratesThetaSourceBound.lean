/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesNormComponents
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesComponentEnergy

/-! # Iterates Theta Source Bound

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Component energies can be extracted without taking a supremum or
assuming an energy identity. -/
theorem iterate_norm_le_energy_components {e g κ H : ℝ}
    (he : 0 ≤ e) (hg : 0 ≤ g) (hκ : 0 ≤ κ) (hH : 0 ≤ H)
    (hbound : Real.sqrt e + Real.sqrt κ * Real.sqrt g ≤ H) :
    e ≤ H ^ 2 ∧ κ * g ≤ H ^ 2 := by
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt e + Real.sqrt κ * Real.sqrt g) hH).mpr hbound
  exact iterate_norm_sq_components he hg hκ hs

end AVenhance.Infra.Section4
