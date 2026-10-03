/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesScalarMaterialEnergy

/-! Scalar diffusion energies from actual one-higher gradient energies. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The scalar diffusion square uses exactly the two one-higher word gradients. -/
theorem iterate_word_laplacian_sq_le {u : Vec 2 → ℝ} (w : List (Fin 2)) (x : Vec 2) :
    (spaceLap (iterateSpatialWord w u) x) ^ 2 ≤
      2 * ∑ k : Fin 2, vecNormSq (spaceGrad (iterateSpatialWord (k :: w) u) x) := by
  simp only [spaceLap, iterateSpatialWord, vecNormSq, vecDot, Fin.sum_univ_two]
  nlinarith only [sq_nonneg (spaceGrad (fun y => spaceGrad (iterateSpatialWord w u) y 0) x 0 -
      spaceGrad (fun y => spaceGrad (iterateSpatialWord w u) y 1) x 1),
    sq_nonneg (spaceGrad (fun y => spaceGrad (iterateSpatialWord w u) y 0) x 1),
    sq_nonneg (spaceGrad (fun y => spaceGrad (iterateSpatialWord w u) y 1) x 0)]

/-- Full scalar diffusion energy is derived from actual scalar gradients. -/
theorem iterate_word_laplacian_energy_bound {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) {G : ℝ}
    (hE : ∀ k : Fin 2,
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord (k :: w) (u t))) ≤ G ^ 2) :
    (∫ z in timeCube, (spaceLap (iterateSpatialWord w (u z.1)) z.2) ^ 2) ≤ 4 * G ^ 2 := by
  have hi := iterate_timeCube_integrable_of_continuousOn
    ((iterate_word_laplacian_continuousOn hu w).pow 2)
  have hg (k : Fin 2) := iterate_word_gradient_energy_integrable hu (k :: w)
  have hs := integrable_finsetSum Finset.univ (fun k _ => hg k)
  have ht := integral_mono hi (hs.const_mul 2) (fun z => iterate_word_laplacian_sq_le w z.2)
  dsimp only [Pi.pow_apply] at ht
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun k _ => hg k)] at ht
  change (∫ z in timeCube, (spaceLap (iterateSpatialWord w (u z.1)) z.2) ^ 2) ≤
    2 * (∑ k : Fin 2, spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord (k :: w) (u
        t)))) at ht
  simp only [Fin.sum_univ_two] at ht
  linarith only [ht, hE 0, hE 1]

end AVenhance.Infra.Section4
