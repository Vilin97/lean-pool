/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCoefficientWords
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability

/-! Exact actual stream-matrix coefficient words and their continuity. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Every matrix word of the skew stream coefficient is the same scalar
 stream word times the fixed matrix. -/
theorem iterateMatrixWord_stream {φ : Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (w : List (Fin 2)) (x : Vec 2) :
    iterateMatrixWord (fun y => φ y • sigmaMat) w x = iterateSpatialWord w φ x • sigmaMat := by
  ext i j
  change iterateSpatialWord w (fun y => φ y * sigmaMat i j) x =
    iterateSpatialWord w φ x * sigmaMat i j
  have he : (fun y => φ y * sigmaMat i j) = fun y => sigmaMat i j * φ y := by
    funext y; ring
  rw [he, iterateSpatialWord_const_mul hφ]
  ring

/-- All actual stream coefficient words are continuous jointly up to time
 zero, as required by the selected-flux space-time bound. -/
theorem iterate_stream_matrix_word_continuousOn {φ : ℝ → Vec 2 → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => φ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    ContinuousOn (fun z : AmnrSpace => iterateMatrixWord
      (fun y => φ z.1 y • sigmaMat) w z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hs := (iterateSpatialWord_smooth_up_to_initial hφ w).continuousOn
  have hc : ContinuousOn (fun z : AmnrSpace => iterateSpatialWord w (φ z.1) z.2 • sigmaMat)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hs.smul continuousOn_const
  apply hc.congr
  intro z hz
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (φ z.1) :=
    hφ.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (z.1, y)))
      (fun _ => ⟨hz.1, Set.mem_univ _⟩)
  exact iterateMatrixWord_stream hslice w z.2

end AVenhance.Infra.Section4
