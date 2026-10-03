/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAnalyticWeightOrder
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesNormComponents

/-! # Iterates Coordinate Profile

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Scalar coordinate energies at every order, with the common prefactor
outside the increment amplitude. The homogeneous base has only positive-order
scalar energies; its order-zero input is the integrated gradient. -/
def iterateCoordinateEnergyProfile (u : ℝ → Vec 2 → ℝ) (κ N L : ℝ) (i : ℕ) : Prop :=
  (∀ w : List (Fin 2), 1 ≤ w.length ∨ 1 ≤ i → ∀ s, 0 ≤ s → s ≤ 1 →
    l2NormSq (iterateSpatialWord w (u s)) ≤ N ^ 2 * iterateAnalyticWeight w.length i L ^ 2) ∧
  (∀ w : List (Fin 2), spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))) ≤
    (N / Real.sqrt κ) ^ 2 * iterateAnalyticWeight w.length i L ^ 2)

/-- A proved squared norm estimate supplies the two energies used by the
next increment equation. -/
theorem iterate_coordinate_profile_of_word_norm
    {u : ℝ → Vec 2 → ℝ} {κ N L : ℝ} {i : ℕ} (hκ : 0 < κ)
    (hnorm : ∀ w : List (Fin 2), ∀ s, 0 ≤ s → s ≤ 1 →
      (Real.sqrt (l2NormSq (iterateSpatialWord w (u s))) + Real.sqrt κ *
        Real.sqrt (spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))))) ^ 2 ≤
      N ^ 2 * iterateAnalyticWeight w.length i L ^ 2) :
    iterateCoordinateEnergyProfile u κ N L i := by
  have he (w : List (Fin 2)) (s : ℝ) : 0 ≤ l2NormSq (iterateSpatialWord w (u s)) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hg (w : List (Fin 2)) : 0 ≤ spaceTimeGradNormSq
      (fun t => spaceGrad (iterateSpatialWord w (u t))) := by
    apply integral_nonneg
    intro z
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  constructor
  · intro w _hw s hs hs1
    exact (iterate_norm_sq_components (he w s) (hg w) hκ.le (hnorm w s hs hs1)).1
  · intro w
    have hb := iterate_norm_sq_gradient_bound (N := N) (A := 1)
      (W := iterateAnalyticWeight w.length i L) (he w 0) (hg w) hκ
      (by simpa only [one_pow, mul_one] using hnorm w 0 (by norm_num) (by norm_num))
    simpa only [mul_one] using hb

end AVenhance.Infra.Section4
