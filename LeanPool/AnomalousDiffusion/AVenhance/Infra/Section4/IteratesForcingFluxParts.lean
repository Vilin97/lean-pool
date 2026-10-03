/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordCoefficientSplit

/-! # Iterates Forcing Flux Parts

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- The actual forcing separates its centered time oscillation, mean
 diffusivity mismatch, and spatial flow correction at every word order. -/
theorem iterate_TForcing_word_flux_three_parts {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm κprev t : ℝ)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (I.sMat hΦ m κm t))
    (v : Vec 2 → ℝ) (w : List (Fin 2)) (x : Vec 2) :
    iterateWordFlux (fun y => I.Kmat κm m t -
      κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm t y) v w x =
      (I.Kmat κm m t - timeAvgMat (I.Kmat κm m)).mulVec
        (spaceGrad (iterateSpatialWord w v) x) +
      (timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ)).mulVec
        (spaceGrad (iterateSpatialWord w v) x) +
      iterateWordFlux (I.sMat hΦ m κm t) v w x := by
  rw [iterateWordFlux_TForcing_coefficient I hΦ m κm κprev t hs v w x]
  have he : I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      (I.Kmat κm m t - timeAvgMat (I.Kmat κm m)) +
        (timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by abel
  rw [he, Matrix.add_mulVec]

end AVenhance.Infra.Section4
