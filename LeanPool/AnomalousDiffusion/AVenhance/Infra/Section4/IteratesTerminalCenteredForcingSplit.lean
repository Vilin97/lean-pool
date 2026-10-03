/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCenteredRemainderGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCenteredForcingRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMeanCorrectionRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordForcingContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixContinuity

/-! # Iterates Terminal Centered Forcing Split

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual first-increment forcing pairing splits into the exact
centered cancellation and small remainder, with all integrability proved. -/
theorem iterate_terminal_centered_forcing_pairing_split {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (hN : 1 ≤ Nstar β)
    {m : ℕ} {κm κprev : ℝ} (hm : 1 ≤ m) (hκm : 0 < κm)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) {s : ℝ} (hs : 0 ≤ s) :
    (∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (iterateSpatialWord w (I.TForcing hΦ m κm κprev u z.1)) z.2)
      ((iterateKmatPrimitive I κm m z.1).mulVec (spaceGrad (iterateSpatialWord w (u z.1)) z.2))) =
    (∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (fun y => ∑ j : Fin 2, ∑ k : Fin 2,
        (I.Kmat κm m z.1 j k - timeAvgMat (I.Kmat κm m) j k) *
          iterateSpatialWord (j :: k :: w) (u z.1) y) z.2)
      ((iterateKmatPrimitive I κm m z.1).mulVec (spaceGrad (iterateSpatialWord w (u z.1)) z.2))) +
    (∫ z in iterateTruncatedCell s, vecDot
      (spaceGrad (iterateSpatialWord w (vecDiv (fun y =>
        (timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          I.sMat hΦ m κm z.1 y).mulVec (spaceGrad (u z.1) y)))) z.2)
      ((iterateKmatPrimitive I κm m z.1).mulVec (spaceGrad (iterateSpatialWord w (u z.1)) z.2)))
          := by
  have hSM (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (I.sMat hΦ m κm t) :=
    AVenhance.Infra.Section5.sMat_spatial_contDiff I hΦ m hm κm t
      (fun l => (hflow l).comp
        (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x))))
  have hR (t : ℝ) (_ : 0 ≤ t) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) := contDiff_const.add (hSM t)
  have hRc := iterate_word_forcing_gradient_continuousOn hu hR
    (iterate_mean_correction_word_continuousOn I hΦ hm hκm κprev hflow) w
  have hCc := iterate_centered_hessian_forcing_gradient_continuousOn I hN hm hκm hu w
  have hQc : ContinuousOn (fun z : AmnrSpace => iterateKmatPrimitive I κm m z.1)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k
    exact (iterateKmatPrimitive_entry_joint_contDiff I hκm hm j k).continuous.continuousOn
  have hB := (iterate_word_gradient_smooth_up_to_initial hu w).continuousOn
  have hCI := iterate_truncated_cell_integrable (iterate_matrix_pairing_continuousOn hCc hB hQc) hs
  have hRI := iterate_truncated_cell_integrable (iterate_matrix_pairing_continuousOn hRc hB hQc) hs
  have heq := integral_add hCI hRI
  rw [← heq]
  apply integral_congr_ae
  apply (ae_restrict_mem (iterateTruncatedCell_isOpen s).measurableSet).mono
  intro z hz
  have hus : ContDiff ℝ (⊤ : ℕ∞) (u z.1) := hu.comp_contDiff
    (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (z.1, x)))
    (fun _ => ⟨hz.1.1.le, Set.mem_univ _⟩)
  dsimp only
  rw [iterate_TForcing_word_gradient_centered_remainder I hΦ m κm κprev z.1 u
    (hSM z.1) hus w z.2]
  simp only [vecDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

end AVenhance.Infra.Section4
