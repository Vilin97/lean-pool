/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalSmallAnalyticFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMeanCorrectionRegularity

/-! # Iterates Actual Small Remainder Flux

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Actual mean and flow coefficient jets yield the uniformly small terminal
remainder flux. No bound on the forcing pairing is assumed. -/
theorem iterate_terminal_mean_correction_small_flux_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} (hm : 1 ≤ m) (hκm : 0 < κm) (hκ : 0 < κprev)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    {u v : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) (a : ℕ)
    {C B ρ r L s : ℝ} (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2) (hs1 : s ≤ 1)
    (hcoef : ∀ t x p, ∀ j k, |iterateMatrixWord
      (fun y => timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) p x j k| ≤
          κprev * C * ρ * (p.length.factorial : ℝ) * r ^ p.length)
    (hE : ∀ p ∈ iterateSpatialSplits w,
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p.2 (v t))) ≤
        B ^ 2 * (((p.2.length + a).factorial : ℝ) * L ^ p.2.length) ^ 2) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      (iterateWordFlux (fun y => timeAvgMat (I.Kmat κm m) -
        κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm z.1 y) (v z.1) w z.2)| ≤
      κprev / 8 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))) +
      32 * κprev * C ^ 2 * ρ ^ 2 * B ^ 2 *
        (((w.length + a).factorial : ℝ) * L ^ w.length) ^ 2 := by
  exact iterate_terminal_small_analytic_word_flux_bound
    (A := fun t y => timeAvgMat (I.Kmat κm m) - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      I.sMat hΦ m κm t y) hs1 hu hv w
    (fun p _ => iterate_mean_correction_word_continuousOn I hΦ hm hκm κprev hflow p.1)
    hκ hL hg a (fun t x p _ j k => hcoef t x p.1 j k) hE

end AVenhance.Infra.Section4
