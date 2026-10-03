/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordRegularity

/-! # Iterates C1Spatial Continuity

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem iterate_spatial_partial_continuous_up_to_initial
    {f : AmnrSpace → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (i : Fin 2) :
    ContinuousOn
      (fun z : AmnrSpace => spaceGrad (fun y => f (z.1, y)) z.2 i)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  let S : Set AmnrSpace := Set.Ici (0 : ℝ) ×ˢ Set.univ
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hd : ContinuousOn (fderivWithin ℝ f S) S :=
    hf.continuousOn_fderivWithin hS (by norm_num)
  have he : ContinuousOn
      (fun z => fderivWithin ℝ f S z (0, basisVec i)) S :=
    hd.clm_apply continuousOn_const
  apply he.congr
  intro z hz
  have hdf := (hf.differentiableOn (by simp) z hz).hasFDerivWithinAt
  have hmaps : Set.MapsTo (fun y : Vec 2 => (z.1, y)) Set.univ S :=
    fun y _ => ⟨hz.1, Set.mem_univ y⟩
  have hc := hdf.comp z.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2).hasFDerivWithinAt hmaps
  have hderiv := hc.hasFDerivAt_of_univ.fderiv
  change fderiv ℝ (fun y : Vec 2 => f (z.1, y)) z.2 = _ at hderiv
  unfold spaceGrad
  change fderiv ℝ (fun y : Vec 2 => f (z.1, y)) z.2 (basisVec i) = fderivWithin ℝ f S z (0,
      basisVec i)
  rw [hderiv]
  rfl

end AVenhance.Infra.Section4
