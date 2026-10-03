/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTerminalFlowScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixContinuity

/-! # Iterates Terminal Flow Regularity

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Actual continuous flow and gradient carriers discharge every natural
integrability premise in the two terminal flow commutator pairings. -/
theorem iterate_terminal_flow_pairings_bound_of_continuity
    {flow a b : ℝ → Vec 2 → Vec 2} {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {κ D B C ρ E s : ℝ} (hs1 : s ≤ 1) (hκ : 0 < κ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (ha : ContinuousOn (fun z : AmnrSpace => a z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hb : ContinuousOn (fun z : AmnrSpace => b z.1 z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQc : ContinuousOn (fun z : AmnrSpace => Q z.1) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hGc : ContinuousOn (fun z : AmnrSpace => gradMatrix (flow z.1) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hQ : ∀ t i j, |Q t i j| ≤ D)
    (hG : ∀ t x i j, |gradMatrix (flow t) x i j| ≤ B)
    (hscale : D * B ≤ C * κ * ρ)
    (hprevious : κ * spaceTimeGradNormSq b ≤ E) :
    |∫ p in iterateTruncatedCell s, vecDot (a p.1 p.2)
      ((Q p.1).mulVec ((gradMatrix (flow p.1) p.2).mulVec (b p.1 p.2)))| +
    |∫ p in iterateTruncatedCell s, vecDot
      ((gradMatrix (flow p.1) p.2).mulVec (a p.1 p.2))
      ((Q p.1).mulVec (b p.1 p.2))| ≤
      κ / 24 * spaceTimeGradNormSq a + 384 * C ^ 2 * ρ ^ 2 * E := by
  have hn (v : AmnrSpace → Vec 2) (hv : ContinuousOn v (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
      ContinuousOn (fun z => vecNormSq (v z)) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    unfold vecNormSq vecDot
    exact continuousOn_finsetSum Finset.univ (fun j _ =>
      ((continuous_apply j).comp_continuousOn hv).mul
        ((continuous_apply j).comp_continuousOn hv))
  have hA1 := hQc.mul hGc
  have hGt : ContinuousOn (fun z : AmnrSpace => (gradMatrix (flow z.1) z.2).transpose)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (continuous_apply i).comp_continuousOn
      ((continuous_apply j).comp_continuousOn hGc)
  have hA2 := hGt.mul hQc
  have hp1 := iterate_matrix_pairing_integrable ha hb hA1
  have hp2 := iterate_matrix_pairing_integrable ha hb hA2
  have he1 : (fun z : AmnrSpace => vecDot (a z.1 z.2)
      ((Q z.1 * gradMatrix (flow z.1) z.2).mulVec (b z.1 z.2))) =
      (fun z => vecDot (a z.1 z.2)
        ((Q z.1).mulVec ((gradMatrix (flow z.1) z.2).mulVec (b z.1 z.2)))) := by
    funext z
    rw [Matrix.mulVec_mulVec]
  have he2 : (fun z : AmnrSpace => vecDot (a z.1 z.2)
      (((gradMatrix (flow z.1) z.2).transpose * Q z.1).mulVec (b z.1 z.2))) =
      (fun z => vecDot ((gradMatrix (flow z.1) z.2).mulVec (a z.1 z.2))
        ((Q z.1).mulVec (b z.1 z.2))) := by
    funext z
    simp only [vecDot, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two]
    ring
  dsimp only [Pi.mul_apply] at hp1 hp2
  rw [he1] at hp1
  rw [he2] at hp2
  exact iterate_terminal_flow_pairings_bound_of_previous_energy hs1 hκ hC hρ hQ hG hscale
    (iterate_timeCube_integrable_of_continuousOn (hn _ ha))
    (iterate_timeCube_integrable_of_continuousOn (hn _ hb)) hp1 hp2 hprevious

end AVenhance.Infra.Section4
