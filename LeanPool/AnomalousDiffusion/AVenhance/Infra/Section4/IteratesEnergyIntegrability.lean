/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTime

/-! Natural energy integrability follows from actual smoothness up to time zero.
Within derivatives provide continuous representatives at the initial boundary. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Continuous fields on the closed nonnegative-time domain are integrable
on every bounded time interval times the torus cell. -/
theorem iterate_time_cell_integrable_of_continuousOn
    {f : AmnrSpace → ℝ}
    (hf : ContinuousOn f (Set.Ici (0 : ℝ) ×ˢ Set.univ)) {T : ℝ} (hT : 0 ≤ T) :
    Integrable f ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube)) := by
  let K : Set (Vec 2) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc
  have hC : IsCompact (Set.Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  have hc : ContinuousOn f (Set.Icc (0 : ℝ) T ×ˢ K) := hf.mono (by
    intro z hz; exact ⟨hz.1.1, Set.mem_univ z.2⟩)
  have hi : IntegrableOn f (Set.Icc (0 : ℝ) T ×ˢ K) volume :=
    hc.integrableOn_compact hC
  rw [Measure.prod_restrict]
  change IntegrableOn f (Set.uIoc 0 T ×ˢ unitCube)
  apply hi.mono_set
  intro z hz
  rw [Set.uIoc_of_le hT] at hz
  refine ⟨⟨hz.1.1.le, hz.1.2⟩, ?_⟩
  intro i hi
  exact ⟨(hz.2 i hi).1.le, (hz.2 i hi).2.le⟩

/-- Both the actual time-energy pairing and Dirichlet energy are integrable.
The ordinary time derivative is only identified at positive times, which
suffices on uIoc(0,T); no ambient derivative at zero is required. -/
theorem iterate_smooth_energy_integrability
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun p : AmnrSpace => u p.1 p.2 * deriv (fun s => u s p.2) p.1)
      ((volume.restrict (Set.uIoc 0 T)).prod (volume.restrict unitCube)) ∧
    IntervalIntegrable (fun t => ∫ x in unitCube, vecNormSq (spaceGrad (u t) x)) volume 0 T := by
  let S : Set AmnrSpace := Set.Ici (0 : ℝ) ×ˢ Set.univ
  let f : AmnrSpace → ℝ := fun z => u z.1 z.2
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderivWithin ℝ f S) S :=
    hu.fderivWithin hS (by simp)
  have hc : ContinuousOn (fun z : AmnrSpace => u z.1 z.2 *
      fderivWithin ℝ f S z (1, 0)) S :=
    hu.continuousOn.mul (hd.clm_apply contDiffOn_const).continuousOn
  have hi := iterate_time_cell_integrable_of_continuousOn hc hT
  have hg : ContinuousOn (fun z : AmnrSpace => vecNormSq (spaceGrad (u z.1) z.2)) S := by
    unfold vecNormSq vecDot
    apply continuousOn_finsetSum
    intro i _
    have hp := (iterate_spatial_partial_smooth_up_to_initial hu i).continuousOn
    exact hp.mul hp
  have hgi := iterate_time_cell_integrable_of_continuousOn hg hT
  refine ⟨?_, intervalIntegrable_iff.mpr hgi.integral_prod_left⟩
  rw [Measure.prod_restrict] at hi ⊢
  change IntegrableOn (fun z : AmnrSpace => u z.1 z.2 * fderivWithin ℝ f S z (1, 0))
    (Set.uIoc 0 T ×ˢ unitCube) at hi
  change IntegrableOn (fun z : AmnrSpace => u z.1 z.2 * deriv (fun s => u s z.2) z.1)
    (Set.uIoc 0 T ×ˢ unitCube)
  apply hi.congr_fun _
    ((measurableSet_uIoc).prod (isOpen_set_pi Set.finite_univ
      (fun _ _ => isOpen_Ioo)).measurableSet)
  intro z hz
  rw [Set.uIoc_of_le hT] at hz
  have ht : 0 < z.1 := hz.1.1
  have hn : S ∈ nhds z := prod_mem_nhds (Ici_mem_nhds ht) Filter.univ_mem
  have hf := (hu.contDiffAt hn).differentiableAt (by simp)
  have htime := hf.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
  have he : deriv (fun s => u s z.2) z.1 = fderiv ℝ f z (1, 0) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] using htime.hasDerivAt.deriv
  change u z.1 z.2 * fderivWithin ℝ f S z (1, 0) =
    u z.1 z.2 * deriv (fun s => u s z.2) z.1
  rw [fderivWithin_of_mem_nhds (𝕜 := ℝ) (f := f) hn, he]

end AVenhance.Infra.Section4
