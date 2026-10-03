/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedFirstFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamOrders

/-! Exact first and high stream order split at each terminal time. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual stream energy flux has no principal contribution; its first
and high parts retain all multiplicities exactly. -/
theorem iterate_truncated_stream_pairing_order_split
    {φ u : ℝ → Vec 2 → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => φ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) {s : ℝ} (hs1 : s ≤ 1) (w : List (Fin 2)) :
    (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      (iterateWordFlux (fun y => φ z.1 y • sigmaMat) (u z.1) w z.2)) =
    (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      (iterateSplitFlux ((iterateSpatialSplits w).filter (fun p => p.1.length == 1))
        (fun y => φ z.1 y • sigmaMat) (u z.1) z.2)) +
    (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      (iterateSplitFlux ((iterateSpatialSplits w).filter (fun p => decide (2 ≤ p.1.length)))
        (fun y => φ z.1 y • sigmaMat) (u z.1) z.2)) := by
  change (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      (iterateSplitFlux (iterateSpatialSplits w) (fun y => φ z.1 y • sigmaMat) (u z.1) z.2)) = _
  rw [iterate_truncated_split_flux_pairing_integral _ hu hu
    (A := fun t y => φ t y • sigmaMat)
    (fun p _ => iterate_stream_matrix_word_continuousOn hφ p.1) hs1 w,
    iterate_three_order_list_sum _ (fun p => p.1.length)]
  have hz : (iterateSpatialSplits w).filter (fun p => p.1.length == 0) = [([], w)] := by
    have he : (fun p : List (Fin 2) × List (Fin 2) => p.1.length == 0) =
        fun p => p.1.isEmpty := by
      funext p
      cases p.1 <;> simp
    rw [he, iterateSpatialSplits_nil_left]
  rw [hz]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hprincipal : (∫ z in iterateTruncatedCell s,
      vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
        ((iterateMatrixWord (fun y => φ z.1 y • sigmaMat) [] z.2).mulVec
          (spaceGrad (iterateSpatialWord w (u z.1)) z.2))) = 0 := by
    have he (z : AmnrSpace) : vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
        ((iterateMatrixWord (fun y => φ z.1 y • sigmaMat) [] z.2).mulVec
          (spaceGrad (iterateSpatialWord w (u z.1)) z.2)) = 0 := by
      simp [iterateMatrixWord, iterateSpatialWord, sigmaMat, vecDot,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    simp only [he, integral_zero]
  rw [hprincipal, zero_add]
  rw [iterate_truncated_split_flux_pairing_integral _ hu hu
    (A := fun t y => φ t y • sigmaMat)
    (fun p _ => iterate_stream_matrix_word_continuousOn hφ p.1) hs1 w,
    iterate_truncated_split_flux_pairing_integral _ hu hu
    (A := fun t y => φ t y • sigmaMat)
    (fun p _ => iterate_stream_matrix_word_continuousOn hφ p.1) hs1 w]

end AVenhance.Infra.Section4
