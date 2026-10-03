/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedCell

/-! Exact integration of the actual finite Leibniz flux. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Integrating the actual selected flux preserves every ordered split. -/
theorem iterate_truncated_split_flux_pairing_integral
    (P : List (List (Fin 2) × List (Fin 2)))
    {A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {u v : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hA : ∀ p ∈ P, ContinuousOn
      (fun z : AmnrSpace => iterateMatrixWord (A z.1) p.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) {s : ℝ} (hs1 : s ≤ 1) (w : List (Fin 2)) :
    (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      (iterateSplitFlux P (A z.1) (v z.1) z.2)) =
      (P.map (fun p => ∫ z in iterateTruncatedCell s,
        vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
          ((iterateMatrixWord (A z.1) p.1 z.2).mulVec
            (spaceGrad (iterateSpatialWord p.2 (v z.1)) z.2)))).sum := by
  have ha := (iterate_word_gradient_smooth_up_to_initial hu w).continuousOn
  induction P with
  | nil => simp [iterateSplitFlux, vecDot]
  | cons p P ih =>
    have ht : ∀ q ∈ P, ContinuousOn
        (fun z : AmnrSpace => iterateMatrixWord (A z.1) q.1 z.2)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun q hq => hA q (List.mem_cons_of_mem p hq)
    have hp := (iterate_matrix_pairing_integrable ha
      (iterate_word_gradient_smooth_up_to_initial hv p.2).continuousOn (hA p
          List.mem_cons_self)).mono_set
        (iterateTruncatedCell_subset hs1)
    have htail := iterateSplitFlux_continuousOn_of_jets P ht hv
    have hi : IntegrableOn (fun z : AmnrSpace =>
        vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
          (iterateSplitFlux P (A z.1) (v z.1) z.2)) (iterateTruncatedCell s) := by
      apply (iterate_timeCube_integrable_of_continuousOn ?_).mono_set (iterateTruncatedCell_subset
          hs1)
      unfold vecDot
      exact continuousOn_finsetSum Finset.univ (fun j _ =>
        ((continuous_apply j).comp_continuousOn ha).mul
          ((continuous_apply j).comp_continuousOn htail))
    have he (z : AmnrSpace) :
        vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
          (iterateSplitFlux (p :: P) (A z.1) (v z.1) z.2) =
        vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
          ((iterateMatrixWord (A z.1) p.1 z.2).mulVec
            (spaceGrad (iterateSpatialWord p.2 (v z.1)) z.2)) +
        vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
          (iterateSplitFlux P (A z.1) (v z.1) z.2) := by
      rw [iterateSplitFlux_eq_sum, List.map_cons, List.sum_cons, ← iterateSplitFlux_eq_sum]
      simp [vecDot, mul_add, Finset.sum_add_distrib]
    simp only [he, List.map_cons, List.sum_cons]
    rw [integral_add hp hi, ih ht]

end AVenhance.Infra.Section4
