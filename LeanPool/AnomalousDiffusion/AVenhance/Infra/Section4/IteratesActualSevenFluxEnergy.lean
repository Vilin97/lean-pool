/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualOscillatoryFiveParts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalTwoForcingParts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesActualTerminalInequality
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesSevenFluxTriangle

/-! # Iterates Actual Seven Flux Energy

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Complete differentiated energy inequality for the actual increment.
Every flux is exposed in the form used by its independently proved bound. -/
theorem iterate_increment_terminal_seven_flux_energy_inequality {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2))
    (hflowp : ∀ t, 0 < t → ∀ l : ℤ, IsZ2Periodic (I.flowGrad hΦ m l t))
    (hm : 1 ≤ m) (hκm : 0 < κm) (i : ℕ) (hi : i + 1 ≤ Nstar β)
    (w : List (Fin 2)) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    let u := fun t => iterateSpatialWord w (iterateIncrement T (i + 1) t)
    let v := fun t => iterateSpatialWord w (iterateIncrement T i t)
    let b := streamVel (Φ (m - 1))
    let Q := iterateKmatPrimitive I κm m
    l2NormSq (u s) / 2 + κprev *
      (∫ z in iterateTruncatedCell s, vecNormSq (spaceGrad (u z.1) z.2)) ≤
      |∫ x in unitCube, vecDot (spaceGrad (u s) x) ((Q s).mulVec (spaceGrad (v s) x))| +
      |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (u z.1) z.2)
        ((Q z.1).mulVec (spaceGrad (amnrMaterial b v z.1) z.2))| +
      |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (amnrMaterial b u z.1) z.2)
        ((Q z.1).mulVec (spaceGrad (v z.1) z.2))| +
      |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (u z.1) z.2)
        ((Q z.1).mulVec ((gradMatrix (b z.1) z.2).mulVec (spaceGrad (v z.1) z.2)))| +
      |∫ z in iterateTruncatedCell s, vecDot
        ((gradMatrix (b z.1) z.2).mulVec (spaceGrad (u z.1) z.2))
        ((Q z.1).mulVec (spaceGrad (v z.1) z.2))| +
      |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (u z.1) z.2)
        (iterateWordFlux (fun y => timeAvgMat (I.Kmat κm m) -
          κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm z.1 y)
          (iterateIncrement T i z.1) w z.2)| +
      |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (u z.1) z.2)
        (iterateWordFlux (fun y => Φ (m - 1) z.1 y • sigmaMat)
          (iterateIncrement T (i + 1) z.1) w z.2)| := by
  dsimp only
  have he := iterate_increment_terminal_word_energy_inequality I hΦ hT hθ hflow hflowp
    hm hκm i hi w hs
  have hu := iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 hi
  have hv := iterateIncrement_smooth_up_to_initial I hΦ hT hθ.1 (by omega : i ≤ Nstar β)
  rw [iterate_terminal_TForcing_pairing_two_parts I hΦ hm hκm hflow hu hv w hs,
    iterate_increment_oscillatory_flux_five_parts I hΦ hT hθ hm hκm i hi w hs hs1] at he
  exact he.trans (iterate_seven_flux_triangle _ _ _ _ _ _ _)

end AVenhance.Infra.Section4
