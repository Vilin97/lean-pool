/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFilteredFluxEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesVelocitySmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesComponentEnergy

/-! Actual material-error energy from positive velocity jets and scalar energies. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual material error has an all-order squared-energy bound involving
 only positive velocity orders and strictly lower scalar gradient orders. -/
theorem iterate_material_error_energy_bound
    {b : ℝ → Vec 2 → Vec 2} {v : ℝ → Vec 2 → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) (D E : ℕ → ℝ)
    (hjet : ∀ t x p, p ∈ (iterateSpatialSplits w).filter (fun p => decide (1 ≤ p.1.length)) → ∀ j,
      |iterateSpatialWord p.1 (fun y => b t y j) x| ≤ D p.1.length)
    (hE : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => decide (1 ≤ p.1.length)),
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (v t))) ≤ E p.2.length) :
    (∫ z in timeCube, iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => v z.1 z.2) z ^ 2) ≤
      8 * ∑ j ∈ Finset.range (w.length + 1), if 1 ≤ j then
        (Nat.choose w.length j : ℝ) ^ 2 * (2 : ℝ) ^ j * D j ^ 2 * E (w.length - j) else 0 := by
  let P := (iterateSpatialSplits w).filter (fun p => decide (1 ≤ p.1.length))
  let A := fun t y => (fun (_ : Fin 2) j => b t y j : Matrix (Fin 2) (Fin 2) ℝ)
  have hP : (iterateSpatialSplits w).filter (fun p => !p.1.isEmpty) = P := by
    congr 1
    funext p
    cases p with
    | mk l r => cases l <;> simp
  have hc : ∀ p ∈ P, ContinuousOn (fun z : AmnrSpace => iterateMatrixWord (A z.1) p.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro p _
    apply continuousOn_pi.mpr
    intro _
    apply continuousOn_pi.mpr
    intro j
    exact (iterateSpatialWord_smooth_up_to_initial (u := fun t x => b t x j)
      (contDiffOn_pi.mp hb j) p.1).continuousOn
  have hflux := iterate_filtered_flux_energy_bound hv w (fun j => decide (1 ≤ j)) hc D E
    (fun t x p hp _ j => hjet t x p hp j) hE
  have hmono : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) ⊆
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun z hz => ⟨(show 0 < z.1 from hz.1).le, hz.2⟩
  have he : (fun z : AmnrSpace => iterateWordMaterialError (fun z : AmnrSpace => b z.1 z.2) w
      (fun z => v z.1 z.2) z ^ 2) =ᵐ[volume.restrict timeCube]
      (fun z => iterateVelocitySplit P (b z.1) (v z.1) z.2 ^ 2) := by
    apply (ae_restrict_mem iterate_timeCube_isOpen.measurableSet).mono
    intro z hz
    change iterateWordMaterialError _ w _ (z.1, z.2) ^ 2 = _
    rw [iterateWordMaterialError_lower_velocity (hb.mono hmono) (hv.mono hmono) hz.1.1, hP]
    rfl
  rw [integral_congr_ae he]
  have hi := iterate_timeCube_integrable_of_continuousOn
    ((iterateVelocitySplit_continuousOn hb hv P).pow 2)
  have hfi := iterate_timeCube_integrable_of_continuousOn
    ((iterate_vecNormSq_continuous continuous_id).comp_continuousOn
      (iterateSplitFlux_continuousOn_of_jets P hc hv))
  have ht := integral_mono hi hfi (fun z =>
    iterate_component_sq_le_normSq (iterateSplitFlux P (A z.1) (v z.1) z.2) 0)
  dsimp only [Function.comp_def, id_eq, Pi.pow_apply] at ht
  change (∫ z in timeCube, iterateVelocitySplit P (b z.1) (v z.1) z.2 ^ 2) ≤
    spaceTimeGradNormSq (fun t => iterateSplitFlux P (A t) (v t)) at ht
  exact ht.trans (by simpa only [decide_eq_true_eq] using hflux)

end AVenhance.Infra.Section4
