/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.DriftCommutatorExpansion

/-! Integrability of the actual energy pairings, including the initial boundary. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set Filter
open scoped Topology
namespace AVenhance.Infra.Section4
open AVenhance

/-- A field continuous up to the initial time is integrable on every bounded
physical time-cell product. The actual open spatial cell is retained. -/
theorem amnr_time_cell_product_integrable {g : AmnrSpace → ℝ}
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ univ)) {T : ℝ} (hT : 0 ≤ T) :
    Integrable g ((volume.restrict (uIoc 0 T)).prod (volume.restrict unitCube)) := by
  let Q : Set (Vec 2) := Set.pi univ fun _ => Icc (0 : ℝ) 1
  have hQ : IsCompact Q := isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc
  have hK : IsCompact (Icc (0 : ℝ) T ×ˢ Q) := isCompact_Icc.prod hQ
  have hsub : Icc (0 : ℝ) T ×ˢ Q ⊆ Ici (0 : ℝ) ×ˢ univ :=
    fun z hz => ⟨hz.1.1, mem_univ z.2⟩
  have hi := (hg.mono hsub).integrableOn_compact (μ := volume) hK
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (Vec 2)]
  apply hi.mono_set
  intro z hz
  rw [uIoc_of_le hT] at hz
  refine ⟨⟨hz.1.1.le, hz.1.2⟩, ?_⟩
  intro i hι
  exact ⟨(hz.2 i hι).1.le, (hz.2 i hι).2.le⟩

end AVenhance.Infra.Section4
