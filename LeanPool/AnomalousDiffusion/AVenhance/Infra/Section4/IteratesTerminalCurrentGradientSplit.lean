/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalGradientMaterialSplit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixIntegralSum

/-! # Iterates Terminal Current Gradient Split

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The current coordinatewise material-gradient term has the same exact
flow commutator after transpose reversal of its scalar pairing. -/
theorem iterate_terminal_current_gradient_material_pairing_split
    {b : ℝ → Vec 2 → Vec 2} {u v : ℝ → Vec 2 → ℝ}
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQc : ContinuousOn (fun z : AmnrSpace => Q z.1) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {s : ℝ} (hs1 : s ≤ 1) :
    (∫ z in iterateTruncatedCell s, vecDot
      (fun j => amnrMaterial b (fun t x => spaceGrad (u t) x j) z.1 z.2)
      ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) =
      (∫ z in iterateTruncatedCell s, vecDot (spaceGrad (amnrMaterial b u z.1) z.2)
        ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) -
      (∫ z in iterateTruncatedCell s, vecDot
        ((gradMatrix (b z.1) z.2).mulVec (spaceGrad (u z.1) z.2))
        ((Q z.1).mulVec (spaceGrad (v z.1) z.2))) := by
  have hQt : ContinuousOn (fun z : AmnrSpace => (Q z.1).transpose)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k
    exact (continuous_apply j).comp_continuousOn
      ((continuous_apply k).comp_continuousOn hQc)
  have ht := iterate_terminal_gradient_material_pairing_split
    (u := v) (v := u) (Q := fun t => (Q t).transpose) hb hv hu hQt hs1
  simpa only [iterate_matrix_pairing_transpose] using ht

end AVenhance.Infra.Section4
