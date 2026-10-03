/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.StreamIncrement
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.StreamAdmissible

/-! The stream recursion gives the exact perpendicular-gradient
velocity increment used in the Section 5 operator split. -/

@[expose] public section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5

open AVenhance

theorem StreamVelocityIncrement.admissibleStream_spatialSlice_contDiff
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (φ t) := by
  let E : Vec 2 → ℝ × Vec 2 := fun x => (t, x)
  have hE : ContDiff ℝ (⊤ : ℕ∞) E := by fun_prop
  have hcomp := hφ.1.comp hE
  have heq : Function.uncurry φ ∘ E = φ t := by
    funext x
    rfl
  rw [heq] at hcomp
  exact hcomp

/-- The scalar recursion coefficient is differentiable in space because it
is the difference of the two admissible stream slices. -/
theorem streamSeq_psiTilde_differentiableAt
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (t : ℝ) (x : Vec 2) :
    DifferentiableAt ℝ (psiTilde I hΦ m t) x := by
  obtain ⟨hcurrent, _⟩ := hΦ.2 (m + 1) (by omega)
  have hprevious : IsAdmissibleStream (Φ (m - 1)) := hΦ.adm_pred m
  have hcurrentSmooth : Differentiable ℝ (Φ m t) :=
    (StreamVelocityIncrement.admissibleStream_spatialSlice_contDiff hcurrent t).differentiable (by
        simp)
  have hpreviousSmooth : Differentiable ℝ (Φ (m - 1) t) :=
    (StreamVelocityIncrement.admissibleStream_spatialSlice_contDiff hprevious t).differentiable
        (by simp)
  have hcurrentDiff : DifferentiableAt ℝ (Φ m t) x := hcurrentSmooth.differentiableAt
  have hpreviousDiff : DifferentiableAt ℝ (Φ (m - 1) t) x := hpreviousSmooth.differentiableAt
  have hpsiFun : psiTilde I hΦ m t =
      fun y => Φ m t y - Φ (m - 1) t y := by
    funext y
    have hpoint := streamSeq_increment_eq_psiTilde I hΦ m hm t y
    linarith
  rw [hpsiFun]
  exact hcurrentDiff.sub hpreviousDiff

/-- For every `m ≥ 1`, differentiating the stream recursion in space
gives `b_m - b_{m-1} = σ ∇ψTilde_m`. The current stream's smoothness is read from
the next recursive witness in `IsStreamSeq`, while the previous stream is
the one supplied by the `m`-th step. -/
theorem streamSeq_velocity_increment_eq_psiTilde
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (t : ℝ) (x : Vec 2) :
    streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x =
      sigmaMat.mulVec (spaceGrad (psiTilde I hΦ m t) x) := by
  obtain ⟨hcurrent, _⟩ := hΦ.2 (m + 1) (by omega)
  have hprevious : IsAdmissibleStream (Φ (m - 1)) := hΦ.adm_pred m
  have hcurrentSmooth : Differentiable ℝ (Φ m t) :=
    (StreamVelocityIncrement.admissibleStream_spatialSlice_contDiff hcurrent t).differentiable (by
        simp)
  have hpreviousSmooth : Differentiable ℝ (Φ (m - 1) t) :=
    (StreamVelocityIncrement.admissibleStream_spatialSlice_contDiff hprevious t).differentiable
        (by simp)
  have hcurrentDiff : DifferentiableAt ℝ (Φ m t) x :=
    hcurrentSmooth.differentiableAt
  have hpreviousDiff : DifferentiableAt ℝ (Φ (m - 1) t) x :=
    hpreviousSmooth.differentiableAt
  have hrec : (Φ m t) = fun y => Φ (m - 1) t y + psiTilde I hΦ m t y := by
    funext y
    have hpoint := streamSeq_increment_eq_psiTilde I hΦ m hm t y
    linarith
  have hpsiDiff := streamSeq_psiTilde_differentiableAt I hΦ m hm t x
  have hgrad :
      spaceGrad (Φ m t) x =
        spaceGrad (Φ (m - 1) t) x + spaceGrad (psiTilde I hΦ m t) x := by
    ext i
    change fderiv ℝ (Φ m t) x (basisVec i) = _
    have hfderiv : fderiv ℝ (Φ m t) x =
        fderiv ℝ (Φ (m - 1) t + psiTilde I hΦ m t) x :=
      congrArg (fun f : Vec 2 → ℝ => fderiv ℝ f x) hrec
    rw [hfderiv, fderiv_add hpreviousDiff hpsiDiff]
    rfl
  change sigmaMat.mulVec (spaceGrad (Φ m t) x) -
      sigmaMat.mulVec (spaceGrad (Φ (m - 1) t) x) = _
  rw [hgrad]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

end AVenhance.Infra.Section5
