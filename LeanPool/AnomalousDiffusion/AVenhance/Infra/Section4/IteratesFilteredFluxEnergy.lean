/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFilteredGrouping

/-! Actual selected flux square from scalar gradient energies. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The integrated differentiated flux is controlled directly by lower
scalar L2 gradient energies. A pointwise scalar analytic bound is unnecessary. -/
theorem iterate_filtered_flux_energy_bound
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) (q : ℕ → Bool)
    (hcoef : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => q p.1.length),
      ContinuousOn (fun z : AmnrSpace => iterateMatrixWord (A z.1) p.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (D E : ℕ → ℝ)
    (hD : ∀ t x p, p ∈ (iterateSpatialSplits w).filter (fun p => q p.1.length) → ∀ j k,
      |iterateMatrixWord (A t) p.1 x j k| ≤ D p.1.length)
    (hE : ∀ p ∈ (iterateSpatialSplits w).filter (fun p => q p.1.length),
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (v t))) ≤ E p.2.length) :
    spaceTimeGradNormSq (fun t => iterateSplitFlux ((iterateSpatialSplits w).filter (fun p => q
        p.1.length)) (A t) (v t)) ≤
      8 * ∑ j ∈ Finset.range (w.length + 1),
        (if q j then (Nat.choose w.length j : ℝ) ^ 2 * (2 : ℝ) ^ j * (D j) ^ 2 * E (w.length - j)
            else 0) := by
  have hc := iterateSplitFlux_continuousOn_of_jets ((iterateSpatialSplits w).filter (fun p => q
      p.1.length)) hcoef hv
  have ha : IntegrableOn (fun z : AmnrSpace =>
      vecNormSq (iterateSplitFlux ((iterateSpatialSplits w).filter (fun p => q p.1.length)) (A
          z.1) (v z.1) z.2)) timeCube :=
    iterate_timeCube_integrable_of_continuousOn ((iterate_vecNormSq_continuous
        continuous_id).comp_continuousOn hc)
  have h := iterate_split_flux_spacetime_pairing_bound ((iterateSpatialSplits w).filter (fun p =>
      q p.1.length)) A v
    (fun t => iterateSplitFlux ((iterateSpatialSplits w).filter (fun p => q p.1.length)) (A t) (v
        t))
    (fun p => iterateYoungWeight 4 w.length p.1.length) (fun p => D p.1.length)
    (fun p hp => iterateYoungWeight_pos (by norm_num) w (List.mem_filter.mp hp).1) hD ha
    (fun p _ => iterate_word_gradient_energy_integrable hv p.2) ha
  change |spaceTimeGradNormSq (fun t => iterateSplitFlux ((iterateSpatialSplits w).filter (fun p
      => q p.1.length)) (A t) (v t))| ≤ _ at h
  have hn : 0 ≤ spaceTimeGradNormSq (fun t => iterateSplitFlux ((iterateSpatialSplits w).filter
      (fun p => q p.1.length)) (A t) (v t)) := by
    exact integral_nonneg (fun _ => vecNormSq_nonneg _)
  rw [abs_of_nonneg hn] at h
  have hr := iterate_filtered_remainder_group_bound (by norm_num : (0 : ℝ) < 4) w q D E
    (fun r => spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord r (v t)))) hE
  have hs := mul_le_mul_of_nonneg_right
    (iterateYoungWeight_filtered_sum_le (by norm_num : (0 : ℝ) < 4) w q) hn
  norm_num at hr hs
  linarith only [h, hr, hs]

end AVenhance.Infra.Section4
