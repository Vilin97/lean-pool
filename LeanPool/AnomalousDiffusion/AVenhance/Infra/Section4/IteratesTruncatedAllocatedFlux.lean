/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedContinuousFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedGrouping

/-! Actual integrated forcing with dissipation absorbed uniformly in order. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual all-order flux pairing has a uniform dissipation allocation
and an explicit binomial-square sum of preceding gradient energies. -/
theorem iterate_truncated_allocated_word_flux_bound
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {u v : ℝ → Vec 2 → ℝ}
    {s : ℝ} (hs1 : s ≤ 1)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2))
    (hcoef : ∀ p ∈ iterateSpatialSplits w,
      ContinuousOn (fun z : AmnrSpace => iterateMatrixWord (A z.1) p.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {κ : ℝ} (hκ : 0 < κ) (D E : ℕ → ℝ)
    (hD : ∀ t x p, p ∈ iterateSpatialSplits w → ∀ j k,
      |iterateMatrixWord (A t) p.1 x j k| ≤ D p.1.length)
    (hE : ∀ p ∈ iterateSpatialSplits w,
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (v t))) ≤ E p.2.length) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      (iterateWordFlux (A z.1) (v z.1) w z.2)| ≤
      κ / 8 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))) +
      16 / κ * ∑ j ∈ Finset.range (w.length + 1),
        (Nat.choose w.length j : ℝ) ^ 2 * (2 : ℝ) ^ j * (D j) ^ 2 * E (w.length - j) := by
  have h := iterate_truncated_flux_pairing_bound_of_continuous_jets hs1
    (iterateSpatialSplits w) hu hv hcoef w
    (fun p => iterateYoungWeight κ w.length p.1.length) (fun p => D p.1.length)
    (fun p hp => iterateYoungWeight_pos hκ w hp) hD
  have hg : 0 ≤ spaceTimeGradNormSq
      (fun t => spaceGrad (iterateSpatialWord w (u t))) := by
    unfold spaceTimeGradNormSq
    apply integral_nonneg
    intro z
    exact vecNormSq_nonneg _
  have hr := iterate_weighted_remainder_group_bound hκ w D E
    (fun r => spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord r (v t)))) hE
  exact h.trans (add_le_add
    (mul_le_mul_of_nonneg_right (iterateYoungWeight_sum_le hκ.le w) hg) hr)

end AVenhance.Infra.Section4
