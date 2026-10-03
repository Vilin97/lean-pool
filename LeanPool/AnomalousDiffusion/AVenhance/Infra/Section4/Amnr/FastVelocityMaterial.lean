/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StreamGradientMaterial

/-! Material cancellation and bounds for the actual fast velocity increment. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Rotation of the actual spatial gradient commutes with subtracting
smooth scalar streams. -/
theorem amnr_streamVel_sub {φ ψ : ℝ → Vec 2 → ℝ} (t : ℝ) (x : Vec 2)
    (hφ : DifferentiableAt ℝ (φ t) x) (hψ : DifferentiableAt ℝ (ψ t) x) :
    AVenhance.streamVel (fun t x => φ t x - ψ t x) t x =
      AVenhance.streamVel φ t x - AVenhance.streamVel ψ t x := by
  have hgrad : AVenhance.spaceGrad (fun y => φ t y - ψ t y) x =
      AVenhance.spaceGrad (φ t) x - AVenhance.spaceGrad (ψ t) x := by
    funext i
    unfold AVenhance.spaceGrad
    rw [fderiv_fun_sub hφ hψ]
    rfl
  unfold AVenhance.streamVel
  rw [hgrad, Matrix.mulVec_sub]

/-- Smoothness of the actual scalar stream increment comes from the defining
admissibility of its two streams. -/
theorem amnr_streamIncrement_contDiff {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => Φ m z.1 z.2 - Φ (m - 1) z.1 z.2) :=
  (AVenhance.streamSeq_isAdmissible hΦ m).1.sub
    (AVenhance.streamSeq_isAdmissible hΦ (m - 1)).1

/-- The actual fast velocity is the rotated spatial gradient of the actual
stream increment, in the source's two coordinate conventions. -/
theorem amnr_fastVelocity_component {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (i : Fin 2) :
    (fun z : AmnrSpace => AVenhance.streamVel (Φ m) z.1 z.2 i -
      AVenhance.streamVel (Φ (m - 1)) z.1 z.2 i) =
      (if i = 0 then (-1 : ℝ) else 1) •
        amnrOp (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) (some (if i = 0 then 1 else 0))
          (fun z => Φ m z.1 z.2 - Φ (m - 1) z.1 z.2) := by
  have hf := amnr_streamIncrement_contDiff I hΦ m
  funext z
  have hφ : DifferentiableAt ℝ (Φ m z.1) z.2 :=
    (((AVenhance.streamSeq_isAdmissible hΦ m).1.comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) z.2
  have hψ : DifferentiableAt ℝ (Φ (m - 1) z.1) z.2 :=
    (((AVenhance.streamSeq_isAdmissible hΦ (m - 1)).1.comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) z.2
  have hh := congrArg (fun v : Vec 2 => v i) (amnr_streamVel_sub z.1 z.2 hφ hψ)
  simp only [Pi.sub_apply] at hh
  rw [← hh]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [amnrOp_space (hf.differentiable (by simp) z)]
  fin_cases i <;> simp [AVenhance.streamVel, AVenhance.sigmaMat, dotProduct, Fin.sum_univ_two]

/-- Abstract real conversion from the stream amplitude to its gradient rate. -/
theorem amnr_amplitude_gradient_scale {E β : ℝ} (hE : 0 < E) :
    E ^ (β - 2) * E = E ^ (β - 1) := by
  calc
    _ = E ^ (β - 2) * E ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hE]; congr 1; ring

end AVenhance.Infra.Section4
