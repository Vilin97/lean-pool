/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHomogeneousGradientMaterial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHomogeneousPreviousScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalPreviousMaterial

/-! # Iterates Homogeneous Previous Material

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The actual homogeneous PDE supplies the exceptional first previous-material
term at q squared from conditional scalar analytic energies. -/
theorem iterate_homogeneous_terminal_previous_material_squared_gain
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {u v : ℝ → Vec 2 → ℝ} {v₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ (fun _ _ => 0) v₀ v)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2))
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hQc : ContinuousOn (fun z : AmnrSpace => Q z.1) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {B N r L Cv Cs D q s : ℝ} (hB : 0 ≤ B) (hr : 0 ≤ r) (hCv : 0 ≤ Cv)
    (hκ : 0 < κ) (hL : 0 < L) (hg : 2 * (r / L) ^ 2 ≤ 1 / 2)
    (hvelocity : B * r ≤ Cv * κ * L ^ 2)
    (hjet : ∀ t x (p : List (Fin 2)), 1 ≤ p.length → ∀ j,
      |iterateSpatialWord p (fun y => b t y j) x| ≤ B * (p.length.factorial : ℝ) * r ^ p.length)
    (hE : ∀ p : List (Fin 2), p.length ≤ w.length + 2 →
      spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord p (v t))) ≤
        (N / Real.sqrt κ) ^ 2 * ((p.length.factorial : ℝ) * L ^ p.length) ^ 2)
    (hD : 0 ≤ D) (hCs : 0 ≤ Cs) (hq : 0 ≤ q)
    (hQ : ∀ t j k, |Q t j k| ≤ D) (hscale : D * L ^ 2 ≤ Cs * q) (hs1 : s ≤ 1) :
    |∫ z in iterateTruncatedCell s, vecDot (spaceGrad (iterateSpatialWord w (u z.1)) z.2)
      ((Q z.1).mulVec (spaceGrad (amnrMaterial b (fun t => iterateSpatialWord w (v t)) z.1) z.2))| ≤
      κ / 24 * spaceTimeGradNormSq (fun t => spaceGrad (iterateSpatialWord w (u t))) +
      24 * Cs ^ 2 * (8 + 544 * Cv ^ 2) * q ^ 2 * N ^ 2 *
        (((w.length + 2).factorial : ℝ) * L ^ w.length) ^ 2 := by
  have hFc := (iterate_word_gradient_smooth_up_to_initial
    (u := fun _ _ => (0 : ℝ)) contDiffOn_const w).continuousOn
  have hp := iterate_terminal_previous_material_pairing_bound hsol hb hu w hFc hQc hQ hκ hs1
  have he := iterate_homogeneous_gradient_material_energy_bound hsol hb w 0
    hB hr hCv hκ hL hg hvelocity
    hjet (fun p hp => by simpa only [Nat.add_zero] using hE p hp)
  simp only [Nat.add_zero] at he
  have hs := iterate_homogeneous_previous_material_scale_bound w.length
    (H := 8 + 544 * Cv ^ 2) (N := N) hκ hD hL hCs hq (by positivity) hscale
  exact hp.trans ((add_le_add le_rfl (mul_le_mul_of_nonneg_left he
    (by positivity : 0 ≤ 24 * D ^ 2 / κ))).trans (add_le_add le_rfl hs))

end AVenhance.Infra.Section4
