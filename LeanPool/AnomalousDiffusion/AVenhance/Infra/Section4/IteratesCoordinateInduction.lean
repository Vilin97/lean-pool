/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCoordinateProfile

/-! # Iterates Coordinate Induction

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Structural induction over the finite increment index and every coordinate
order. The step is applied only to previously established scalar energies;
this helper does not claim a PDE estimate for the family. -/
theorem iterate_coordinate_two_index_induction
    {u : ℕ → ℝ → Vec 2 → ℝ} {κ N L η : ℝ} {K : ℕ} (hκ : 0 < κ)
    (hbase : iterateCoordinateEnergyProfile (u 0) κ N L 0)
    (hstep : ∀ i, 1 ≤ i → i ≤ K →
      (∀ j, j < i → iterateCoordinateEnergyProfile (u j) κ (N * iterateAmplitude η j) L j) →
      ∀ w : List (Fin 2),
      (∀ p : List (Fin 2), p.length < w.length →
        spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p (u i t))) ≤
          (N * iterateAmplitude η i / Real.sqrt κ) ^ 2 * iterateAnalyticWeight p.length i L ^ 2) →
      ∀ s, 0 ≤ s → s ≤ 1 →
      (Real.sqrt (l2NormSq (iterateSpatialWord w (u i s))) + Real.sqrt κ *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u i t))))) ^ 2 ≤
      N ^ 2 * iterateAmplitude η i ^ 2 * iterateAnalyticWeight w.length i L ^ 2 / 4) :
    ∀ i, i ≤ K → iterateCoordinateEnergyProfile (u i) κ (N * iterateAmplitude η i) L i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst i
      simpa [iterateAmplitude] using hbase
    · have hip : 1 ≤ i := by omega
      have hpast : ∀ j, j < i →
          iterateCoordinateEnergyProfile (u j) κ (N * iterateAmplitude η j) L j := by
        intro j hj
        exact ih j hj (by omega)
      have horders : ∀ n : ℕ, ∀ w : List (Fin 2), w.length = n → ∀ s, 0 ≤ s → s ≤ 1 →
          (Real.sqrt (l2NormSq (iterateSpatialWord w (u i s))) + Real.sqrt κ *
            Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u i t))))) ^
                2 ≤
          N ^ 2 * iterateAmplitude η i ^ 2 * iterateAnalyticWeight w.length i L ^ 2 := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ihn =>
          intro w hw s hs hs1
          have hlower (p : List (Fin 2)) (hp : p.length < w.length) :
              spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p (u i t))) ≤
                (N * iterateAmplitude η i / Real.sqrt κ) ^ 2 * iterateAnalyticWeight p.length i L
                    ^ 2 := by
            have hb := ihn p.length (by omega) p rfl 0 (by norm_num) (by norm_num)
            have he : 0 ≤ l2NormSq (iterateSpatialWord p (u i 0)) :=
              integral_nonneg (fun _ => sq_nonneg _)
            have hg : 0 ≤ spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p (u i t)))
                := by
              apply integral_nonneg
              intro z
              unfold vecNormSq vecDot
              exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
            exact iterate_norm_sq_gradient_bound he hg hκ hb
          have hb := hstep i hip hi hpast w hlower s hs hs1
          have hnonneg : 0 ≤ N ^ 2 * iterateAmplitude η i ^ 2 * iterateAnalyticWeight w.length i L
              ^ 2 := by
            positivity
          linarith only [hb, hnonneg]
      apply iterate_coordinate_profile_of_word_norm hκ
      intro w s hs hs1
      simpa only [mul_pow] using horders w.length w rfl s hs hs1

end AVenhance.Infra.Section4
