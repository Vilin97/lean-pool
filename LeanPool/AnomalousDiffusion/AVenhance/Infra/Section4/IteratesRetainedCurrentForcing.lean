/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedWordCurrent

/-! # Iterates Retained Current Forcing

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem iterate_terminal_current_word_pairing_retained_forcing
    {s : ℝ} (hs1 : s ≤ 1)
    {b : ℝ → Vec 2 → Vec 2} {κ D : ℝ} {F u v : ℝ → Vec 2 → ℝ}
    {u₀ : Vec 2 → ℝ} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hsol : IsClassicalSol b κ F u₀ u) (w : List (Fin 2)) (hκ : 0 < κ)
    (hQ : ∀ t i j, |Q t i j| ≤ D)
    (hv : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvp : ∀ t, 0 < t → IsZ2Periodic (v t))
    (hF : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (F t))
    (huI : IntegrableOn (fun p : ℝ × Vec 2 => vecNormSq (spaceGrad (iterateSpatialWord w (u p.1))
        p.2)) timeCube)
    (hvLap : IntegrableOn (fun p : ℝ × Vec 2 =>
      vecNormSq (fun j => spaceLap (fun y => spaceGrad (v p.1) y j) p.2)) timeCube)
    (hL : IntegrableOn (fun p : ℝ × Vec 2 => vecDot
      (fun i => spaceLap (fun y => spaceGrad (iterateSpatialWord w (u p.1)) y i) p.2)
      ((Q p.1).mulVec (spaceGrad (v p.1) p.2))) timeCube)
    (hR : IntegrableOn (fun p : ℝ × Vec 2 => vecDot (spaceGrad (iterateSpatialWord w (u p.1)) p.2)
      ((Q p.1).mulVec (fun j => spaceLap (fun y => spaceGrad (v p.1) y j) p.2))) timeCube)
    (hFP : IntegrableOn (fun p : ℝ × Vec 2 => vecDot (spaceGrad (iterateSpatialWord w (F p.1)) p.2)
      ((Q p.1).mulVec (spaceGrad (v p.1) p.2))) timeCube) :
    |∫ p in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (amnrMaterial b u
        p.1)) p.2)
      ((Q p.1).mulVec (spaceGrad (v p.1) p.2))| ≤
      κ / 24 * spaceTimeGradNormSq (fun t x => spaceGrad (iterateSpatialWord w (u t)) x) +
      24 * κ * D ^ 2 * spaceTimeGradNormSq
        (fun t x j => spaceLap (fun y => spaceGrad (v t) y j) x) +
      |∫ p in iterateTruncatedCell s, vecDot
        (spaceGrad (iterateSpatialWord w (F p.1)) p.2)
        ((Q p.1).mulVec (spaceGrad (v p.1) p.2))| := by
  have hu (t : ℝ) (ht : 0 < t) : ContDiff ℝ (⊤ : ℕ∞) (iterateSpatialWord w (u t)) := by
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) := by fun_prop
    exact iterateSpatialWord_smooth
      (hsol.1.comp_contDiff hm (fun _ => ⟨ht.le, Set.mem_univ _⟩)) w
  have hdiff := iterate_truncated_current_diffusion_pairing_bound hs1
    (a := fun t x => spaceGrad (iterateSpatialWord w (u t)) x) (b := fun t x => spaceGrad (v t) x)
    (Q := Q) (D := D) hκ hQ
    (fun t ht => iterate_gradient_smooth (hu t ht))
    (fun t ht => iterate_gradient_smooth (hv t ht))
    (fun t ht => iterate_gradient_periodic ((hu t ht).of_le (by simp)) (iterateSpatialWord_periodic
      (hsol.1.comp_contDiff (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
        (fun _ => ⟨ht.le, Set.mem_univ _⟩)) (hsol.2.1 t ht.le) w))
    (fun t ht => iterate_gradient_periodic ((hv t ht).of_le (by simp)) (hvp t ht))
    hL hR huI hvLap le_rfl
  have heq : (∫ p in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (amnrMaterial
      b u p.1)) p.2)
      ((Q p.1).mulVec (spaceGrad (v p.1) p.2))) =
      κ * (∫ p in iterateTruncatedCell s, vecDot
        (fun i => spaceLap (fun y => spaceGrad (iterateSpatialWord w (u p.1)) y i) p.2)
        ((Q p.1).mulVec (spaceGrad (v p.1) p.2))) +
      (∫ p in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (F p.1)) p.2)
        ((Q p.1).mulVec (spaceGrad (v p.1) p.2))) := by
    have hp : (fun p : ℝ × Vec 2 => vecDot (spaceGrad (iterateSpatialWord w (amnrMaterial b u
        p.1)) p.2)
        ((Q p.1).mulVec (spaceGrad (v p.1) p.2))) =ᵐ[volume.restrict (iterateTruncatedCell s)]
        (fun p => κ * vecDot
          (fun i => spaceLap (fun y => spaceGrad (iterateSpatialWord w (u p.1)) y i) p.2)
          ((Q p.1).mulVec (spaceGrad (v p.1) p.2)) +
          vecDot (spaceGrad (iterateSpatialWord w (F p.1)) p.2) ((Q p.1).mulVec (spaceGrad (v p.1)
              p.2))) := by
      apply (ae_restrict_mem ((iterateTruncatedCell_isOpen s).measurableSet)).mono
      intro p hp
      have ht : 0 < p.1 := hp.1.1
      simp only [vecDot, iterate_classical_word_material_gradient_equation hsol ht (hF p.1 ht) w
          p.2, add_mul, Finset.sum_add_distrib,
        mul_assoc, ← Finset.mul_sum]
    rw [integral_congr_ae hp]
    have hs := integral_add ((hL.mono_set (iterateTruncatedCell_subset hs1)).const_mul κ)
      (hFP.mono_set (iterateTruncatedCell_subset hs1))
    rw [hs, integral_const_mul]
  rw [heq]
  have habs := abs_add_le
    (κ * (∫ p in iterateTruncatedCell s, vecDot
      (fun i => spaceLap (fun y => spaceGrad (iterateSpatialWord w (u p.1)) y i) p.2)
      ((Q p.1).mulVec (spaceGrad (v p.1) p.2))))
    (∫ p in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (F p.1)) p.2)
      ((Q p.1).mulVec (spaceGrad (v p.1) p.2)))
  rw [abs_mul, abs_of_pos hκ] at habs
  exact habs.trans (add_le_add hdiff le_rfl)

end AVenhance.Infra.Section4
