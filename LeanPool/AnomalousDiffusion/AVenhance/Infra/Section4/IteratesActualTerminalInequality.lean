/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualTerminalEnergy

/-! # Iterates Actual Terminal Inequality

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem iterate_increment_terminal_word_energy_inequality {β : ℝ} (I : Ingredients β)
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
        (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) z.1)) z.2)) ≤
      |∫ z in iterateTruncatedCell s, vecDot
        (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) z.1)) z.2)
        (iterateWordFlux (fun y => I.Kmat κm m z.1 -
          κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm z.1 y)
          (iterateIncrement T i z.1) w z.2)| +
      |∫ z in iterateTruncatedCell s, vecDot
        (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) z.1)) z.2)
        (iterateWordFlux (fun y => Φ (m - 1) z.1 y • sigmaMat)
          (iterateIncrement T (i + 1) z.1) w z.2)| := by
  rw [iterate_increment_terminal_word_energy_identity I hΦ hT hθ hflow hflowp hm hκm i hi w hs]
  have hf := neg_le_abs (∫ z in iterateTruncatedCell s, vecDot
    (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) z.1)) z.2)
    (iterateWordFlux (fun y => I.Kmat κm m z.1 -
      κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm z.1 y)
      (iterateIncrement T i z.1) w z.2))
  have hg := neg_le_abs (∫ z in iterateTruncatedCell s, vecDot
    (spaceGrad (iterateSpatialWord w (iterateIncrement T (i + 1) z.1)) z.2)
    (iterateWordFlux (fun y => Φ (m - 1) z.1 y • sigmaMat)
      (iterateIncrement T (i + 1) z.1) w z.2))
  linarith only [hf, hg]

end AVenhance.Infra.Section4
