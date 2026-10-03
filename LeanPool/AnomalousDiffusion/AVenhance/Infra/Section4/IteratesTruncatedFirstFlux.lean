/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedFluxIntegral
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedFirstStream
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamCoefficient

/-! The first stream radius gain for the actual selected vector flux. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Exact first-order multiplicity and radius gain in the energy's actual flux. -/
theorem iterate_truncated_first_stream_flux_analytic_bound
    {φ u : ℝ → Vec 2 → ℝ} {H B L d : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => φ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hφp : ∀ t, 0 < t → IsZ2Periodic (φ t))
    (hup : ∀ t, 0 < t → IsZ2Periodic (u t)) (j : Fin 2) (w : List (Fin 2)) (i : ℕ)
    (hjet : ∀ t x j k, |spaceGrad (fun y => spaceGrad (φ t) y j) x k| ≤ H)
    (hM : ∀ q : List (Fin 2), q.length = w.length →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord q (u t))) ≤
        B ^ 2 * (((w.length + 2 * i).factorial : ℝ) * L ^ w.length) ^ 2 * d ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord (j :: w) (u z.1)) z.2)
      (iterateSplitFlux ((iterateSpatialSplits (j :: w)).filter (fun p => p.1.length == 1))
        (fun y => φ z.1 y • sigmaMat) (u z.1) z.2)| ≤
      2 * H * B ^ 2 / L ^ 2 *
        (((w.length + 1 + 2 * i).factorial : ℝ) * L ^ (w.length + 1)) ^ 2 * d ^ 2 := by
  rw [iterate_truncated_split_flux_pairing_integral
    ((iterateSpatialSplits (j :: w)).filter (fun p => p.1.length == 1))
    (A := fun t y => φ t y • sigmaMat) hu hu
    (fun p _ => iterate_stream_matrix_word_continuousOn hφ p.1) hs1 (j :: w)]
  have he : ∀ p : List (Fin 2) × List (Fin 2),
      (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord (j :: w) (u z.1)) z.2)
        ((iterateMatrixWord (fun y => φ z.1 y • sigmaMat) p.1 z.2).mulVec
          (spaceGrad (iterateSpatialWord p.2 (u z.1)) z.2))) =
      (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord (j :: w) (u z.1)) z.2)
        ((iterateSpatialWord p.1 (φ z.1) z.2 • sigmaMat).mulVec
          (spaceGrad (iterateSpatialWord p.2 (u z.1)) z.2))) := by
    intro p
    apply setIntegral_congr_fun (iterateTruncatedCell_isOpen s).measurableSet
    intro z hz
    have hs : ContDiff ℝ (⊤ : ℕ∞) (φ z.1) :=
      hφ.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (z.1, y)))
        (fun _ => ⟨hz.1.1.le, Set.mem_univ _⟩)
    dsimp only
    rw [iterateMatrixWord_stream hs]
  simp only [he]
  exact iterate_truncated_first_stream_time_analytic_bound hH hL hφ hu hs0 hs1 hφp hup j w i hjet hM

end AVenhance.Infra.Section4
