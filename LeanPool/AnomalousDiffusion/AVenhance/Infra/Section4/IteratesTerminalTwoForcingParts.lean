/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingFluxParts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFluxPairingContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingCoefficients
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedCell
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMeanCorrectionRegularity

/-! # Iterates Terminal Two Forcing Parts

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Exact terminal forcing decomposition into the centered oscillation and
mean-plus-spatial remainder. This permits a common small remainder budget. -/
theorem iterate_terminal_TForcing_pairing_two_parts {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} (hm : 1 ≤ m) (hκm : 0 < κm)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    {u v : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) {s : ℝ} (hs : 0 ≤ s) :
    (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      (iterateWordFlux (fun y => I.Kmat κm m z.1 -
        κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm z.1 y) (v z.1) w z.2)) =
    (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      ((I.Kmat κm m z.1 - timeAvgMat (I.Kmat κm m)).mulVec
        (spaceGrad (iterateSpatialWord w (v z.1)) z.2))) +
    (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      (iterateWordFlux (fun y => timeAvgMat (I.Kmat κm m) -
        κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm z.1 y) (v z.1) w z.2)) := by
  have hSM (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (I.sMat hΦ m κm t) :=
    AVenhance.Infra.Section5.sMat_spatial_contDiff I hΦ m hm κm t
      (fun l => (hflow l).comp
        (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x))))
  have he (z : AmnrSpace) : iterateWordFlux
      (fun y => I.Kmat κm m z.1 - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm z.1 y)
      (v z.1) w z.2 =
      (I.Kmat κm m z.1 - timeAvgMat (I.Kmat κm m)).mulVec
        (spaceGrad (iterateSpatialWord w (v z.1)) z.2) +
      iterateWordFlux (fun y => timeAvgMat (I.Kmat κm m) -
        κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm z.1 y) (v z.1) w z.2 := by
    rw [iterate_TForcing_word_flux_three_parts I hΦ m κm κprev z.1 (hSM z.1),
      iterateWordFlux_add contDiff_const (hSM z.1), iterateWordFlux_constant]
    exact add_assoc _ _ _
  have hK : ContinuousOn (fun z : AmnrSpace => I.Kmat κm m z.1 - timeAvgMat (I.Kmat κm m))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (((AVenhance.Infra.Section3.Kmat_contDiff I hm hκm).continuous.comp continuous_fst).sub
      continuous_const).continuousOn
  have h1 := iterate_truncated_cell_integrable
    (iterate_matrix_pairing_continuousOn
      (iterate_word_gradient_smooth_up_to_initial hu w).continuousOn
      (iterate_word_gradient_smooth_up_to_initial hv w).continuousOn hK) hs
  have h2 := iterate_truncated_cell_integrable (iterate_word_flux_pairing_continuousOn
    (A := fun t y => timeAvgMat (I.Kmat κm m) -
      κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm t y) hu hv w
    (fun p _ => iterate_mean_correction_word_continuousOn I hΦ hm hκm κprev hflow p.1)) hs
  simp only [he, vecDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have ht := integral_add h1 h2
  simpa only [vecDot] using ht

end AVenhance.Infra.Section4
