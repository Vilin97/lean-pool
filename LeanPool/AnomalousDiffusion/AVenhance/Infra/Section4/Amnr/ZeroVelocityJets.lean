/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.StreamVelocityConstants

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocityNonemptySpatial

/-! Actual zero-stream base cases for the higher material induction. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

theorem amnr_streamVelocity_zero {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ) :
    (fun y : AmnrSpace => AVenhance.streamVel (Φ 0) y.1 y.2) = 0 := by
  funext y p
  rw [hΦ.1]
  rw [AVenhance.streamVel_spatialConstant]
  rfl

theorem amnr_streamVelocity_zero_word {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (w : List (Option (Fin 2))) (i : Fin 2) :
    amnrWord (fun y => AVenhance.streamVel (Φ 0) y.1 y.2) w
      (fun y => AVenhance.streamVel (Φ 0) y.1 y.2 i) = 0 := by
  have hi : (fun y : AmnrSpace => AVenhance.streamVel (Φ 0) y.1 y.2 i) = 0 := by
    funext y
    exact congrFun (congrFun (amnr_streamVelocity_zero I hΦ) y) i
  rw [hi, amnrWord_zero]

theorem amnr_streamGradient_zero_word {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (w : List (Option (Fin 2))) (i p : Fin 2) :
    amnrWord (fun y => AVenhance.streamVel (Φ 0) y.1 y.2) w
      (amnrVelocityGradient (fun y => AVenhance.streamVel (Φ 0) y.1 y.2) i p) = 0 := by
  rw [amnr_streamVelocity_zero I hΦ]
  have hg : amnrVelocityGradient (0 : AmnrSpace → Vec 2) i p = 0 := by
    funext y
    simp [amnrVelocityGradient, AVenhance.spaceGrad]
  rw [hg, amnrWord_zero]

end AVenhance.Infra.Section4
