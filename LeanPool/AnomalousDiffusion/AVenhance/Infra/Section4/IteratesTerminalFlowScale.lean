/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalFlowPairing

/-! # Iterates Terminal Flow Scale

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

theorem iterate_terminal_flow_pairings_bound_of_previous_energy
    {s : ℝ} (hs1 : s ≤ 1)
    {flow a b : ℝ → Vec 2 → Vec 2} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {κ D B C ρ E : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hQ : ∀ t i j, |Q t i j| ≤ D)
    (hG : ∀ t x i j, |gradMatrix (flow t) x i j| ≤ B)
    (hscale : D * B ≤ C * κ * ρ)
    (ha : IntegrableOn (fun p : ℝ × Vec 2 => vecNormSq (a p.1 p.2)) timeCube)
    (hb : IntegrableOn (fun p : ℝ × Vec 2 => vecNormSq (b p.1 p.2)) timeCube)
    (hp₁ : IntegrableOn (fun p : ℝ × Vec 2 => vecDot (a p.1 p.2)
      ((Q p.1).mulVec ((gradMatrix (flow p.1) p.2).mulVec (b p.1 p.2)))) timeCube)
    (hp₂ : IntegrableOn (fun p : ℝ × Vec 2 => vecDot
      ((gradMatrix (flow p.1) p.2).mulVec (a p.1 p.2))
      ((Q p.1).mulVec (b p.1 p.2))) timeCube)
    (hprevious : κ * spaceTimeGradNormSq b ≤ E) :
    |∫ p in iterateTruncatedCell s, vecDot (a p.1 p.2)
      ((Q p.1).mulVec ((gradMatrix (flow p.1) p.2).mulVec (b p.1 p.2)))| +
    |∫ p in iterateTruncatedCell s, vecDot ((gradMatrix (flow p.1) p.2).mulVec (a p.1 p.2))
      ((Q p.1).mulVec (b p.1 p.2))| ≤
      κ / 24 * spaceTimeGradNormSq a + 384 * C ^ 2 * ρ ^ 2 * E := by
  have h := iterate_terminal_flow_commutator_pairings_bound hs1 hκ hQ hG ha hb hp₁ hp₂
  have hD : 0 ≤ D := (abs_nonneg _).trans (hQ 0 0 0)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hG 0 0 0 0)
  have hs : (D * B) ^ 2 ≤ (C * κ * ρ) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hD hB) (by positivity)).mpr hscale
  have henergy : 0 ≤ spaceTimeGradNormSq b := by
    apply integral_nonneg
    intro p
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hcoeff : 384 * D ^ 2 * B ^ 2 / κ ≤ 384 * C ^ 2 * ρ ^ 2 * κ := by
    apply (div_le_iff₀ hκ).mpr
    nlinarith only [hs]
  have hterm := mul_le_mul_of_nonneg_right hcoeff henergy
  have hprev := mul_le_mul_of_nonneg_left hprevious
    (by positivity : 0 ≤ 384 * C ^ 2 * ρ ^ 2)
  have he : 384 * D ^ 2 * B ^ 2 / κ * spaceTimeGradNormSq b ≤
      384 * C ^ 2 * ρ ^ 2 * E := by
    calc
      _ ≤ (384 * C ^ 2 * ρ ^ 2 * κ) * spaceTimeGradNormSq b := hterm
      _ = (384 * C ^ 2 * ρ ^ 2) * (κ * spaceTimeGradNormSq b) := by ring
      _ ≤ _ := hprev
  exact h.trans (add_le_add_right he _)

end AVenhance.Infra.Section4
