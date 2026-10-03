/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFluxPairingContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingCoefficients
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamCoefficient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalSignedPairing

/-! # Iterates Actual Terminal Energy

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The differentiated actual increment has an exact terminal energy identity
on the same truncated cell used by the quantitative forcing estimates. -/
theorem iterate_increment_terminal_word_energy_identity {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (hflowp : ∀ t, 0 < t → ∀ l : ℤ, IsZ2Periodic (I.flowGrad hΦ m l t))
    (hm : 1 ≤ m) (hκm : 0 < κm) (i : ℕ) (hi : i + 1 ≤ Nstar β)
    (w : List (Fin 2)) {s : ℝ} (hs : 0 ≤ s) :
    l2NormSq (iterateSpatialWord w (iterateIncrement T (i + 1) s)) / 2 +
      κprev * (∫ z in iterateTruncatedCell s, vecNormSq
        (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) z.1)) z.2)) =
      -(∫ z in iterateTruncatedCell s, vecDot
        (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) z.1)) z.2)
        (iterateWordFlux (fun y => I.Kmat κm m z.1 -
          κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm z.1 y)
          (iterateIncrement T i z.1) w z.2)) -
      (∫ z in iterateTruncatedCell s, vecDot
        (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) z.1)) z.2)
        (iterateWordFlux (fun y => Φ (m - 1) z.1 y • sigmaMat)
          (iterateIncrement T (i + 1) z.1) w z.2)) := by
  have hu := iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 hi
  have hv := iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 (by omega : i ≤ Nstar β)
  obtain ⟨hφ, _⟩ := hΦ.2 m hm
  have hFc := iterate_word_flux_pairing_continuousOn
    (A := fun t y => I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm t y)
        hu hv w
    (fun p _ => iterate_TForcing_coefficient_word_continuousOn I hΦ hm hκm κprev hflow p.1)
  have hSc := iterate_word_flux_pairing_continuousOn
    (A := fun t y => Φ (m - 1) t y • sigmaMat) hu hu w
    (fun p _ => iterate_stream_matrix_word_continuousOn hφ.1.contDiffOn p.1)
  have hGc := iterate_word_gradient_smooth_up_to_initial hu w
  have hEc : ContinuousOn (fun z : AmnrSpace => vecNormSq
      (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) z.1)) z.2))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    unfold vecNormSq vecDot
    exact continuousOn_finsetSum Finset.univ (fun j _ =>
      ((continuous_apply j).comp_continuousOn hGc.continuousOn).mul
        ((continuous_apply j).comp_continuousOn hGc.continuousOn))
  have he := iterate_increment_word_flux_time_energy_identity I hΦ hT hθ
    (fun t _ l => (hflow l).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x))))
    hflowp hm i hi w hs
  rw [iterate_terminal_signed_pairing_identity hFc hSc hs,
    ← iterate_truncated_integral_eq_interval hEc hs] at he
  exact he

end AVenhance.Infra.Section4
