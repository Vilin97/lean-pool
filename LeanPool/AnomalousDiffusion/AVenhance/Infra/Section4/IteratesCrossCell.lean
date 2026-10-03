/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCrossIntegrability
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedCell

/-! # Iterates Cross Cell

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual material cross pairing is integrable on the full open time cell. -/
theorem iterate_material_cross_timeCube_integrable {u v : ℝ → Vec 2 → ℝ}
    {b : ℝ → Vec 2 → Vec 2}
    (hb : ContinuousOn (fun z : AmnrSpace => b z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContinuousOn (fun z : AmnrSpace => u z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ 1 (fun z : AmnrSpace => v z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    IntegrableOn (fun z : AmnrSpace => u z.1 z.2 * amnrMaterial b v z.1 z.2) timeCube := by
  have hi := iterate_material_cross_pairing_integrable hb hu hv (T := 1) (by norm_num)
  rw [Measure.prod_restrict] at hi
  change IntegrableOn (fun z : AmnrSpace => u z.1 z.2 * amnrMaterial b v z.1 z.2)
    (Set.uIoc 0 1 ×ˢ unitCube) at hi
  apply hi.mono_set
  intro z hz
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact ⟨⟨hz.1.1, hz.1.2.le⟩, hz.2⟩

end AVenhance.Infra.Section4
