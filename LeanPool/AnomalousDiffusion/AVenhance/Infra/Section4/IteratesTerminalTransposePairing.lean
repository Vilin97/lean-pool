/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixContinuity

/-! # Iterates Terminal Transpose Pairing

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Reverse the matrix pairing before Young allocation, preserving the
 desired scalar dissipation factor and proving natural integrability. -/
theorem iterate_terminal_transpose_pairing_bound_of_continuity
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {a b : ℝ → Vec 2 → Vec 2}
    {σ D s : ℝ} (hs1 : s ≤ 1) (hσ : 0 < σ)
    (ha : ContinuousOn (fun z : AmnrSpace => a z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hb : ContinuousOn (fun z : AmnrSpace => b z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQc : ContinuousOn (fun z : AmnrSpace => Q z.1) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQ : ∀ t j k, |Q t j k| ≤ D) :
    |∫ z in iterateTruncatedCell s, vecDot (a z.1 z.2) ((Q z.1).mulVec (b z.1 z.2))| ≤
      σ * spaceTimeGradNormSq b + D ^ 2 / σ * spaceTimeGradNormSq a := by
  have hQt : ContinuousOn (fun z : AmnrSpace => (Q z.1).transpose)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k
    exact (continuous_apply j).comp_continuousOn
      ((continuous_apply k).comp_continuousOn hQc)
  have hp := iterate_matrix_pairing_integrable hb ha hQt
  have hn (v : AmnrSpace → Vec 2) (hv : ContinuousOn v (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
      ContinuousOn (fun z => vecNormSq (v z)) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    unfold vecNormSq vecDot
    exact continuousOn_finsetSum Finset.univ (fun j _ =>
      ((continuous_apply j).comp_continuousOn hv).mul
        ((continuous_apply j).comp_continuousOn hv))
  have ht := iterate_truncated_matrix_pairing_bound
    (A := fun t _ => (Q t).transpose) (a := b) (b := a) hs1 hσ
    (fun t _ j k => hQ t k j)
    (iterate_timeCube_integrable_of_continuousOn (hn _ hb))
    (iterate_timeCube_integrable_of_continuousOn (hn _ ha)) hp
  have he : (fun z : AmnrSpace => vecDot (b z.1 z.2) ((Q z.1).transpose.mulVec (a z.1 z.2))) =
      fun z => vecDot (a z.1 z.2) ((Q z.1).mulVec (b z.1 z.2)) := by
    funext z
    simp only [vecDot, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two]
    ring
  rw [he] at ht
  exact ht

end AVenhance.Infra.Section4
