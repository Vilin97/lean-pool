/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Defs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.TimeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceTimeGradNormSq

/-! # Time slicing and continuity of spatial integrals (for `e.ergodic.break.up`)

Source: `enhance.tex` 8305–8394.  The joint spatial gradient of a function smooth up to `t = 0`
is continuous there, `‖∇θ‖²_{L²((0,1)×𝕋²)}` is the iterated integral of the slice energies, and
spatial integrals over the unit cube of jointly continuous integrands are continuous in time. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance

/-- The closed unit square, a compact set carrying the open cube up to a null set. -/
def Slicing.closedCube : Set (Vec 2) := Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

theorem Slicing.isCompact_closedCube : IsCompact Slicing.closedCube :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem Slicing.unitCube_subset_closedCube : unitCube ⊆ Slicing.closedCube :=
  Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self

theorem Slicing.unitCube_ae_eq_closedCube :
    unitCube =ᵐ[(volume : Measure (Vec 2))] Slicing.closedCube := by
  simpa [volume_pi, unitCube, Slicing.closedCube] using
    (Measure.univ_pi_Ioo_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ))
      (g := fun _ : Fin 2 => (1 : ℝ)))

theorem continuous_vecNormSq_two : Continuous (fun v : Vec 2 => vecNormSq v) := by
  unfold vecNormSq vecDot
  fun_prop

/-- Continuous functions are integrable over the open unit cube. -/
theorem integrableOn_unitCube_of_continuous {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f unitCube :=
  (hf.continuousOn.integrableOn_compact Slicing.isCompact_closedCube).mono_set
      Slicing.unitCube_subset_closedCube

/-- The slice derivative of a function smooth up to `t = 0` is the within-derivative of the
joint function in the spatial direction. -/
theorem fderiv_slice_eq_fderivWithin {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) (x v : Vec 2) :
    fderiv ℝ (T t) x v =
      fderivWithin ℝ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, x)
        (0, v) := by
  have hp : (t, x) ∈ Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) := ⟨ht, mem_univ _⟩
  have hdiff : DifferentiableWithinAt ℝ (fun p : ℝ × Vec 2 => T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, x) :=
    (hT.differentiableOn (by simp)) _ hp
  have hmaps : MapsTo (fun y : Vec 2 => (t, y)) Set.univ (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    fun y _ => ⟨ht, mem_univ _⟩
  have hcomp := hdiff.hasFDerivWithinAt.comp x (hasFDerivAt_prodMk_right t x).hasFDerivWithinAt
    hmaps
  have hat : HasFDerivAt (T t)
      ((fderivWithin ℝ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2))) x :=
    hcomp.hasFDerivAt Filter.univ_mem
  rw [hat.fderiv]
  simp

/-- The joint spatial gradient of a function smooth up to `t = 0`. -/
theorem spaceGrad_continuousOn {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hs : UniqueDiffOn ℝ (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    UniqueDiffOn.prod (uniqueDiffOn_Ici 0) uniqueDiffOn_univ
  have hc := hT.continuousOn_fderivWithin hs (by simp)
  refine continuousOn_pi.mpr fun i => ?_
  have hi := hc.clm_apply (continuousOn_const (c := ((0 : ℝ), basisVec i)))
  refine hi.congr ?_
  intro p hp
  exact fderiv_slice_eq_fderivWithin hT hp.1 p.2 (basisVec i)

/-- `‖∇θ‖²_{L²((0,1)×𝕋²)}` as an iterated integral of the slice energies. -/
theorem spaceTimeGradNormSq_eq_intervalIntegral {V : ℝ → Vec 2 → Vec 2}
    (hV : ContinuousOn (fun p : ℝ × Vec 2 => V p.1 p.2) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) :
    spaceTimeGradNormSq V = ∫ t in (0 : ℝ)..1, ∫ x in unitCube, vecNormSq (V t x) := by
  unfold spaceTimeGradNormSq timeCube
  have hmaps : MapsTo (fun p : ℝ × Vec 2 => p) (Set.Icc (0 : ℝ) 1 ×ˢ Slicing.closedCube)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := fun p hp => ⟨hp.1, mem_univ _⟩
  have hcont : ContinuousOn (fun p : ℝ × Vec 2 => vecNormSq (V p.1 p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Slicing.closedCube) :=
    continuous_vecNormSq_two.comp_continuousOn (hV.mono (fun p hp => ⟨hp.1, mem_univ _⟩))
  have hint : IntegrableOn (fun p : ℝ × Vec 2 => vecNormSq (V p.1 p.2))
      (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube) volume :=
    (hcont.integrableOn_compact (isCompact_Icc.prod Slicing.isCompact_closedCube)).mono_set
      (Set.prod_mono Set.Ioo_subset_Icc_self Slicing.unitCube_subset_closedCube)
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [setIntegral_prod _ hint, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

/-- Spatial integrals over the unit cube of jointly continuous integrands are continuous on
`[0,1]`. -/
theorem continuousOn_integral_unitCube {h : ℝ → Vec 2 → ℝ}
    (hh : ContinuousOn (fun p : ℝ × Vec 2 => h p.1 p.2) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) :
    ContinuousOn (fun t => ∫ x in unitCube, h t x) (Set.Icc (0 : ℝ) 1) := by
  have hcongr : ∀ t, ∫ x in unitCube, h t x = ∫ x in Slicing.closedCube, h t x :=
    fun t => setIntegral_congr_set Slicing.unitCube_ae_eq_closedCube
  simp_rw [hcongr]
  rw [continuousOn_iff_continuous_domRestrict]
  have hcont : Continuous (fun q : Set.Icc (0 : ℝ) 1 × Vec 2 => h q.1.1 q.2) := by
    have hmap : Continuous (fun q : Set.Icc (0 : ℝ) 1 × Vec 2 => (q.1.1, q.2)) := by fun_prop
    exact hh.comp_continuous hmap (fun q => ⟨q.1.2, mem_univ _⟩)
  exact continuous_parametric_integral_of_continuous
    (f := fun (s : Set.Icc (0 : ℝ) 1) (y : Vec 2) => h s.1 y) hcont Slicing.isCompact_closedCube

end AVenhance.Infra.Section5.LeftToShow

end
