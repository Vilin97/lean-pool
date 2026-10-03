/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergyIntegrability

/-! Cross temporal pairings inherit integrability from the actual C1 carrier. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Natural temporal cross-pairing integrability requires only continuity of
the first factor and C1 up to zero of the differentiated factor. -/
theorem iterate_time_cross_pairing_integrable {u v : ℝ → Vec 2 → ℝ}
    (hu : ContinuousOn (fun z : AmnrSpace => u z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ 1 (fun z : AmnrSpace => v z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun z : AmnrSpace => u z.1 z.2 * deriv (fun s => v s z.2) z.1)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube)) := by
  let S : Set AmnrSpace := Set.Ici (0 : ℝ) ×ˢ Set.univ
  let f : AmnrSpace → ℝ := fun z => v z.1 z.2
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hd : ContinuousOn (fderivWithin ℝ f S) S :=
    hv.continuousOn_fderivWithin hS (by norm_num)
  have hc : ContinuousOn (fun z : AmnrSpace => u z.1 z.2 *
      fderivWithin ℝ f S z (1, 0)) S :=
    hu.mul (hd.clm_apply continuousOn_const)
  have hi := iterate_time_cell_integrable_of_continuousOn hc hT
  rw [Measure.prod_restrict] at hi ⊢
  change IntegrableOn (fun z : AmnrSpace => u z.1 z.2 * fderivWithin ℝ f S z (1, 0))
    (Set.uIoc 0 T ×ˢ unitCube) at hi
  change IntegrableOn (fun z : AmnrSpace => u z.1 z.2 * deriv (fun s => v s z.2) z.1)
    (Set.uIoc 0 T ×ˢ unitCube)
  apply hi.congr_fun _
    ((measurableSet_uIoc).prod (isOpen_set_pi Set.finite_univ
      (fun _ _ => isOpen_Ioo)).measurableSet)
  intro z hz
  rw [Set.uIoc_of_le hT] at hz
  have ht : 0 < z.1 := hz.1.1
  have hn : S ∈ nhds z := prod_mem_nhds (Ici_mem_nhds ht) Filter.univ_mem
  have hf := (hv.contDiffAt hn).differentiableAt (by simp)
  have htime := hf.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
  have he : deriv (fun s => v s z.2) z.1 = fderiv ℝ f z (1, 0) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] using htime.hasDerivAt.deriv
  change u z.1 z.2 * fderivWithin ℝ f S z (1, 0) =
    u z.1 z.2 * deriv (fun s => v s z.2) z.1
  rw [fderivWithin_of_mem_nhds (𝕜 := ℝ) (f := f) hn, he]

/-- Material cross-pairing integrability follows from the same within-derivative
representative and the actual continuous drift. -/
theorem iterate_material_cross_pairing_integrable {u v : ℝ → Vec 2 → ℝ}
    {b : ℝ → Vec 2 → Vec 2}
    (hb : ContinuousOn (fun z : AmnrSpace => b z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContinuousOn (fun z : AmnrSpace => u z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ 1 (fun z : AmnrSpace => v z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun z : AmnrSpace => u z.1 z.2 * amnrMaterial b v z.1 z.2)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube)) := by
  let S : Set AmnrSpace := Set.Ici (0 : ℝ) ×ˢ Set.univ
  let f : AmnrSpace → ℝ := fun z => v z.1 z.2
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hd : ContinuousOn (fderivWithin ℝ f S) S :=
    hv.continuousOn_fderivWithin hS (by norm_num)
  have hc : ContinuousOn (fun z : AmnrSpace => u z.1 z.2 *
      fderivWithin ℝ f S z (1, b z.1 z.2)) S :=
    hu.mul (hd.clm_apply (continuousOn_const.prodMk hb))
  have hi := iterate_time_cell_integrable_of_continuousOn hc hT
  rw [Measure.prod_restrict] at hi ⊢
  change IntegrableOn (fun z : AmnrSpace => u z.1 z.2 * fderivWithin ℝ f S z (1, b z.1 z.2))
    (Set.uIoc 0 T ×ˢ unitCube) at hi
  change IntegrableOn (fun z : AmnrSpace => u z.1 z.2 * amnrMaterial b v z.1 z.2)
    (Set.uIoc 0 T ×ˢ unitCube)
  apply hi.congr_fun _
    ((measurableSet_uIoc).prod (isOpen_set_pi Set.finite_univ
      (fun _ _ => isOpen_Ioo)).measurableSet)
  intro z hz
  rw [Set.uIoc_of_le hT] at hz
  have ht : 0 < z.1 := hz.1.1
  have hn : S ∈ nhds z := prod_mem_nhds (Ici_mem_nhds ht) Filter.univ_mem
  have hf := (hv.contDiffAt hn).differentiableAt (by simp)
  have he : fderiv ℝ f z (1, b z.1 z.2) = amnrMaterial b v z.1 z.2 := by
    exact amnrOp_material (b := fun z : AmnrSpace => b z.1 z.2) hf
  change u z.1 z.2 * fderivWithin ℝ f S z (1, b z.1 z.2) =
    u z.1 z.2 * amnrMaterial b v z.1 z.2
  rw [fderivWithin_of_mem_nhds (𝕜 := ℝ) (f := f) hn, he]

end AVenhance.Infra.Section4
