/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureSpatialWords

/-! The energy inequality with the actual spatial drift commutator retained. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4
open AVenhance

theorem TemperatureForcedEnergy.amnr_cell_integrable {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f unitCube := by
  let K : Set (Vec 2) := Set.pi univ fun _ => Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc
  apply (hf.continuousOn.integrableOn_compact hK).mono_set
  intro x hx i hi
  exact ⟨(hx i hi).1.le, (hx i hi).2.le⟩

theorem TemperatureForcedEnergy.amnr_normSq_continuous {a : Vec 2 → Vec 2} (ha : Continuous a) :
    Continuous (fun x => vecNormSq (a x)) := by
  unfold vecNormSq vecDot
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp ha).mul ((continuous_apply i).comp ha)

end AVenhance.Infra.Section4
