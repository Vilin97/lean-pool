/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCrossIntegrability
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedCell

/-! Natural material-square integrability from actual initial-time carriers. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The material square has a continuous within-derivative representative;
no two-sided initial-time derivative is assumed. -/
theorem iterate_material_square_time_integrable {u : ℝ → Vec 2 → ℝ}
    {b : ℝ → Vec 2 → Vec 2}
    (hb : ContinuousOn (fun z : AmnrSpace => b z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ 1 (fun z : AmnrSpace => u z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun z : AmnrSpace => (amnrMaterial b u z.1 z.2) ^ 2)
      ((volume.restrict (Set.uIoc 0 s)).prod (volume.restrict unitCube)) := by
  let S : Set AmnrSpace := Set.Ici (0 : ℝ) ×ˢ Set.univ
  let f : AmnrSpace → ℝ := fun z => u z.1 z.2
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hd : ContinuousOn (fderivWithin ℝ f S) S :=
    hu.continuousOn_fderivWithin hS (by norm_num)
  have hc : ContinuousOn (fun z : AmnrSpace =>
      (fderivWithin ℝ f S z (1, b z.1 z.2)) ^ 2) S :=
    (hd.clm_apply (continuousOn_const.prodMk hb)).pow 2
  have hi := iterate_time_cell_integrable_of_continuousOn hc hs
  rw [Measure.prod_restrict] at hi ⊢
  change IntegrableOn (fun z : AmnrSpace => (fderivWithin ℝ f S z (1, b z.1 z.2)) ^ 2)
    (Set.uIoc 0 s ×ˢ unitCube) at hi
  change IntegrableOn (fun z : AmnrSpace => (amnrMaterial b u z.1 z.2) ^ 2)
    (Set.uIoc 0 s ×ˢ unitCube)
  apply hi.congr_fun _ (measurableSet_uIoc.prod
    (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).measurableSet)
  intro z hz
  rw [Set.uIoc_of_le hs] at hz
  have hn : S ∈ nhds z := prod_mem_nhds (Ici_mem_nhds hz.1.1) Filter.univ_mem
  have hf := (hu.contDiffAt hn).differentiableAt (by simp)
  have he : fderiv ℝ f z (1, b z.1 z.2) = amnrMaterial b u z.1 z.2 :=
    amnrOp_material (b := fun z : AmnrSpace => b z.1 z.2) hf
  dsimp only
  rw [fderivWithin_of_mem_nhds (𝕜 := ℝ) (f := f) hn, he]

/-- Actual material squares are naturally integrable on the open cell. -/
theorem iterate_material_square_integrable {u : ℝ → Vec 2 → ℝ}
    {b : ℝ → Vec 2 → Vec 2}
    (hb : ContinuousOn (fun z : AmnrSpace => b z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ 1 (fun z : AmnrSpace => u z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    IntegrableOn (fun z : AmnrSpace => (amnrMaterial b u z.1 z.2) ^ 2) timeCube := by
  have hi := iterate_material_square_time_integrable hb hu (by norm_num : (0 : ℝ) ≤ 1)
  rw [Measure.prod_restrict] at hi
  change IntegrableOn (fun z : AmnrSpace => (amnrMaterial b u z.1 z.2) ^ 2)
    (Set.uIoc 0 1 ×ˢ unitCube) at hi
  apply hi.mono_set
  intro z hz
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact ⟨⟨hz.1.1, hz.1.2.le⟩, hz.2⟩

end AVenhance.Infra.Section4
