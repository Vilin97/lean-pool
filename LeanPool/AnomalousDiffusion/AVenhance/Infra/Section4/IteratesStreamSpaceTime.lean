/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamPairing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability

/-! Spatial skew transfer on the full space-time cell. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem IteratesStreamSpaceTime.stream_pairing_continuous
    {ψ u v : ℝ → Vec 2 → ℝ}
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => ψ z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => v z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun z : AmnrSpace => vecDot (spaceGrad (u z.1) z.2)
      ((ψ z.1 z.2 • sigmaMat).mulVec (spaceGrad (v z.1) z.2)))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
    ContinuousOn (fun z : AmnrSpace => u z.1 z.2 * vecDot
      (sigmaMat.mulVec (spaceGrad (ψ z.1) z.2)) (spaceGrad (v z.1) z.2))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hgu := (iterate_word_gradient_smooth_up_to_initial hu []).continuousOn
  have hgv := (iterate_word_gradient_smooth_up_to_initial hv []).continuousOn
  have hgψ := (iterate_word_gradient_smooth_up_to_initial hψ []).continuousOn
  have hp := hψ.continuousOn
  have hc := hu.continuousOn
  constructor
  · unfold vecDot Matrix.mulVec dotProduct
    apply continuousOn_finsetSum Finset.univ
    intro i _
    exact ((continuous_apply i).comp_continuousOn hgu).mul
      (continuousOn_finsetSum Finset.univ (fun j _ =>
        (hp.mul_const (sigmaMat i j)).mul ((continuous_apply j).comp_continuousOn hgv)))
  · unfold vecDot Matrix.mulVec dotProduct
    apply hc.mul
    apply continuousOn_finsetSum Finset.univ
    intro i _
    exact (continuousOn_finsetSum Finset.univ (fun j _ =>
      continuousOn_const.mul ((continuous_apply j).comp_continuousOn hgψ))).mul
      ((continuous_apply i).comp_continuousOn hgv)

end AVenhance.Infra.Section4
