/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordDiffusion
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Calculus.TangentCone.Prod

/-! Ordered spatial derivatives remain smooth up to the initial time.
At the boundary the proof uses the within derivative, not an unsupported
ambient derivative of the extension to negative times. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Differentiate only in space on the closed nonnegative-time domain. -/
theorem iterate_spatial_partial_smooth_up_to_initial
    {f : AmnrSpace → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (i : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => spaceGrad (fun y => f (z.1, y)) z.2 i)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  let S : Set AmnrSpace := Set.Ici (0 : ℝ) ×ˢ Set.univ
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderivWithin ℝ f S) S :=
    hf.fderivWithin hS (by simp)
  have he : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => fderivWithin ℝ f S z (0, basisVec i)) S :=
    hd.clm_apply contDiffOn_const
  apply he.congr
  intro z hz
  have hdf := (hf.differentiableOn (by simp) z hz).hasFDerivWithinAt
  have hmaps : Set.MapsTo (fun y : Vec 2 => (z.1, y)) Set.univ S :=
    fun y _ => ⟨hz.1, Set.mem_univ y⟩
  have hc := hdf.comp z.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2).hasFDerivWithinAt hmaps
  have hderiv := hc.hasFDerivAt_of_univ.fderiv
  change fderiv ℝ (fun y : Vec 2 => f (z.1, y)) z.2 = _ at hderiv
  unfold spaceGrad
  rw [hderiv]
  rfl

/-- All ordered spatial derivatives of the actual scalar retain joint
smoothness on the closed time domain, including their initial trace. -/
theorem iterateSpatialWord_smooth_up_to_initial
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (w : List (Fin 2)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => iterateSpatialWord w (u z.1) z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  induction w with
  | nil => exact hu
  | cons i w ih => exact iterate_spatial_partial_smooth_up_to_initial ih i

/-- The initial trace of a spatial word is the corresponding initial-data
word. This uses a function equality, without ambient derivatives at time zero. -/
theorem iterate_classical_word_initial
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ F u₀ u) (w : List (Fin 2)) :
    iterateSpatialWord w (u 0) = iterateSpatialWord w u₀ := by
  have heq : u 0 = u₀ := by funext x; exact hsol.2.2.1 x
  rw [heq]

end AVenhance.Infra.Section4
