/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowAverageSourceBounds

/-! Time energy tools below the AMNR facade, avoiding a reverse import. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

theorem TemperatureTimeEnergy.amnr_time_cell_integrable {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f unitCube := by
  let K : Set (Vec 2) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc
  apply (hf.continuousOn.integrableOn_compact hK).mono_set
  intro x hx i hi
  exact ⟨(hx i hi).1.le, (hx i hi).2.le⟩

end AVenhance.Infra.Section4
