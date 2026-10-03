/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesComponentEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability

/-! Actual differentiated diffusion energy from two higher scalar gradients. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The Laplacian of an actual gradient is the sum of two twice-differentiated
 scalar gradients. The order is retained explicitly for the increment induction. -/
theorem iterate_word_laplacian_gradient_formula {v : Vec 2 → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (w : List (Fin 2)) (x : Vec 2) (j : Fin 2) :
    spaceLap (fun y => spaceGrad (iterateSpatialWord w v) y j) x =
      ∑ k : Fin 2, spaceGrad (iterateSpatialWord (k :: k :: w) v) x j := by
  rw [← iterate_gradient_laplacian_commute (iterateSpatialWord_smooth hv w)]
  unfold spaceLap
  rw [show (fun y => ∑ k : Fin 2,
      spaceGrad (fun z => spaceGrad (iterateSpatialWord w v) z k) y k) =
      (fun y => ∑ k : Fin 2, iterateSpatialWord (k :: k :: w) v y) by rfl]
  have he := iterateSpatialWord_sum Finset.univ
    (fun k : Fin 2 => iterateSpatialWord (k :: k :: w) v)
    (fun k _ => iterateSpatialWord_smooth hv (k :: k :: w)) [j]
  exact congrFun he x

/-- The actual vector diffusion square is controlled by higher gradient squares. -/
theorem iterate_word_laplacian_gradient_sq_bound {v : Vec 2 → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (w : List (Fin 2)) (x : Vec 2) :
    vecNormSq (fun j => spaceLap (fun y => spaceGrad (iterateSpatialWord w v) y j) x) ≤
      2 * ∑ k : Fin 2, vecNormSq (spaceGrad (iterateSpatialWord (k :: k :: w) v) x) := by
  simp only [vecNormSq, vecDot, iterate_word_laplacian_gradient_formula hv,
    Fin.sum_univ_two]
  nlinarith only [sq_nonneg (spaceGrad (iterateSpatialWord (0 :: 0 :: w) v) x 0 -
      spaceGrad (iterateSpatialWord (1 :: 1 :: w) v) x 0),
    sq_nonneg (spaceGrad (iterateSpatialWord (0 :: 0 :: w) v) x 1 -
      spaceGrad (iterateSpatialWord (1 :: 1 :: w) v) x 1)]

/-- Actual differentiated diffusion has continuous initial-time coefficients. -/
theorem iterate_word_laplacian_gradient_continuousOn {v : ℝ → Vec 2 → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    ContinuousOn (fun z : AmnrSpace => fun j : Fin 2 =>
      spaceLap (fun y => spaceGrad (iterateSpatialWord w (v z.1)) y j) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hc : ContinuousOn (fun z : AmnrSpace => ∑ k : Fin 2,
      spaceGrad (iterateSpatialWord (k :: k :: w) (v z.1)) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    continuousOn_finsetSum Finset.univ (fun k _ =>
      (iterate_word_gradient_smooth_up_to_initial hv (k :: k :: w)).continuousOn)
  apply hc.congr
  intro z hz
  funext j
  have hs : ContDiff ℝ (⊤ : ℕ∞) (v z.1) :=
    hv.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (z.1, x)))
      (fun _ => ⟨hz.1, Set.mem_univ _⟩)
  simpa only [Finset.sum_apply] using iterate_word_laplacian_gradient_formula hs w z.2 j

/-- Actual higher scalar gradient energies bound the differentiated diffusion
 energy. All natural integrability follows from the actual smooth carrier. -/
theorem iterate_word_laplacian_gradient_energy_bound {v : ℝ → Vec 2 → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) {G : ℝ}
    (hE : ∀ k : Fin 2,
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord (k :: k :: w) (v t))) ≤ G ^ 2) :
    spaceTimeGradNormSq (fun t x j =>
      spaceLap (fun y => spaceGrad (iterateSpatialWord w (v t)) y j) x) ≤ 4 * G ^ 2 := by
  have hc := iterate_word_laplacian_gradient_continuousOn hv w
  have hsq : ContinuousOn (fun z : AmnrSpace => vecNormSq
      (fun j => spaceLap (fun y => spaceGrad (iterateSpatialWord w (v z.1)) y j) z.2))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    unfold vecNormSq vecDot
    exact continuousOn_finsetSum Finset.univ (fun j _ =>
      ((continuous_apply j).comp_continuousOn hc).mul ((continuous_apply j).comp_continuousOn hc))
  have hgi (k : Fin 2) := iterate_word_gradient_energy_integrable hv (k :: k :: w)
  have hsum := integrable_finsetSum Finset.univ (fun k _ => hgi k)
  have ht := integral_mono_ae (iterate_timeCube_integrable_of_continuousOn hsq)
    (hsum.const_mul 2) (by
      apply (ae_restrict_mem iterate_timeCube_isOpen.measurableSet).mono
      intro z hz
      have hs : ContDiff ℝ (⊤ : ℕ∞) (v z.1) :=
        hv.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (z.1, x)))
          (fun _ => ⟨hz.1.1.le, Set.mem_univ _⟩)
      exact iterate_word_laplacian_gradient_sq_bound hs w z.2)
  simp only [integral_const_mul, integral_finsetSum Finset.univ (fun k _ => hgi k)] at ht
  change spaceTimeGradNormSq (fun t x j => spaceLap
    (fun y => spaceGrad (iterateSpatialWord w (v t)) y j) x) ≤ 2 * (∑ k : Fin 2, spaceTimeGradNormSq
    (fun t => spaceGrad (iterateSpatialWord (k :: k :: w) (v t)))) at ht
  have he := add_le_add (hE 0) (hE 1)
  simp only [Fin.sum_univ_two] at ht
  linarith only [ht, he]

end AVenhance.Infra.Section4
