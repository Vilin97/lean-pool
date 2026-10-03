/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaDifferentiated
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaTimeEnergy
public import Mathlib.Analysis.Calculus.TangentCone.Prod

/-! Spatial derivatives of a classical solution remain smooth and continuous
down to the initial time. The derivatives are taken within the closed
nonnegative-time half-space, so their boundary values are the derivatives of
the initial trace. -/

@[expose] public section

open Homogenization
open MeasureTheory
open Filter
open scoped Topology

noncomputable section

namespace AVenhance.Infra.Section4

/-- Joint time-space domain with nonnegative time, including the initial trace. -/
def ThetaTimeSpatialTrace.thetaNonnegativeJointDomain : Set (ℝ × Vec 2) :=
  Set.Ici (0 : ℝ) ×ˢ Set.univ

theorem ThetaTimeSpatialTrace.thetaNonnegativeJointDomain_uniqueDiff :
    UniqueDiffOn ℝ ThetaTimeSpatialTrace.thetaNonnegativeJointDomain := by
  exact (uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ

/-- Spatial coordinate direction embedded in the joint temperature domain. -/
def ThetaTimeSpatialTrace.thetaSpatialDirection (i : Fin 2) : ℝ × Vec 2 :=
  (0, Homogenization.basisVec i)

/-- Iterate spatial directional derivatives within the nonnegative-time domain. -/
def ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin : List (Fin 2) →
    (ℝ × Vec 2 → ℝ) → ℝ × Vec 2 → ℝ
  | [], f => f
  | i :: w, f => fun p =>
      fderivWithin ℝ (ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin w f)
        ThetaTimeSpatialTrace.thetaNonnegativeJointDomain p
            (ThetaTimeSpatialTrace.thetaSpatialDirection i)

theorem ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin_contDiffOn
    {f : ℝ × Vec 2 → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f ThetaTimeSpatialTrace.thetaNonnegativeJointDomain) :
    ∀ w, ContDiffOn ℝ (⊤ : ℕ∞)
      (ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin w f)
          ThetaTimeSpatialTrace.thetaNonnegativeJointDomain := by
  intro w
  induction w with
  | nil => exact hf
  | cons i w ih =>
      have htail := ih
      have hderiv : ContDiffOn ℝ (⊤ : ℕ∞)
          (fderivWithin ℝ (ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin w f)
            ThetaTimeSpatialTrace.thetaNonnegativeJointDomain)
                ThetaTimeSpatialTrace.thetaNonnegativeJointDomain :=
        (contDiffOn_infty_iff_fderivWithin
            ThetaTimeSpatialTrace.thetaNonnegativeJointDomain_uniqueDiff).1
          htail |>.2
      have hdir : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun _ : ℝ × Vec 2 => ThetaTimeSpatialTrace.thetaSpatialDirection i)
          ThetaTimeSpatialTrace.thetaNonnegativeJointDomain := contDiffOn_const
      simpa [ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin] using hderiv.clm_apply hdir

theorem ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin_eq_slice
    {f : ℝ × Vec 2 → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f ThetaTimeSpatialTrace.thetaNonnegativeJointDomain) :
    ∀ w (t : ℝ), 0 ≤ t → ∀ x : Vec 2,
      ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin w f (t, x) =
        classicalWordDerivative w (fun y => f (t, y)) x := by
  intro w
  induction w with
  | nil =>
      intro t ht x
      rfl
  | cons i w ih =>
      intro t ht x
      have htailSmooth := ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin_contDiffOn hf w
      have hp : (t, x) ∈ ThetaTimeSpatialTrace.thetaNonnegativeJointDomain := by
        exact ⟨ht, Set.mem_univ x⟩
      have hAt := htailSmooth.contDiffWithinAt hp
      have hderiv := hAt.differentiableWithinAt (by simp)
      have hwithin := hderiv.hasFDerivWithinAt
      let slice : Vec 2 → ℝ × Vec 2 := fun y => (t, y)
      have hslice : HasFDerivAt slice
          (ContinuousLinearMap.prod (0 : Vec 2 →L[ℝ] ℝ)
            (ContinuousLinearMap.id ℝ (Vec 2))) x := by
        exact (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk
          (hasFDerivAt_id (𝕜 := ℝ) x)
      have hmem : ∀ᶠ y in 𝓝 x,
          slice y ∈ ThetaTimeSpatialTrace.thetaNonnegativeJointDomain := by
        filter_upwards with y
        exact ⟨ht, Set.mem_univ y⟩
      have hcomp := hwithin.comp_hasFDerivAt x hslice hmem
      have hcomponent :
          fderiv ℝ (fun y => ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin w f (t, y)) x
            (Homogenization.basisVec i) =
          fderivWithin ℝ (ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin w f)
            ThetaTimeSpatialTrace.thetaNonnegativeJointDomain (t, x)
                (ThetaTimeSpatialTrace.thetaSpatialDirection i) := by
        have hcompDeriv := hcomp.fderiv
        change fderiv ℝ
            (fun y => ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin w f (t, y)) x =
          fderivWithin ℝ (ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin w f)
            ThetaTimeSpatialTrace.thetaNonnegativeJointDomain (t, x) ∘SL
              ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ (Vec 2)) at hcompDeriv
        have h := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (Homogenization.basisVec i))
            hcompDeriv
        simpa [ThetaTimeSpatialTrace.thetaSpatialDirection, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.prod_apply] using h
      have htailEq :
          (fun y => ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin w f (t, y)) =
            classicalWordDerivative w (fun y => f (t, y)) := by
        funext y
        exact ih t ht y
      rw [htailEq] at hcomponent
      change fderivWithin ℝ (ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin w f)
          ThetaTimeSpatialTrace.thetaNonnegativeJointDomain (t, x)
              (ThetaTimeSpatialTrace.thetaSpatialDirection i) =
        AVenhance.spaceGrad (classicalWordDerivative w (fun y => f (t, y))) x i
      exact hcomponent.symm

theorem theta_classical_word_joint_contDiffOn_nonneg
    {θ : ℝ → Vec 2 → ℝ}
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ∀ w, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => classicalWordDerivative w (θ p.1) p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  intro w
  let F : ℝ × Vec 2 → ℝ := Function.uncurry θ
  have hθ' : ContDiffOn ℝ (⊤ : ℕ∞) F ThetaTimeSpatialTrace.thetaNonnegativeJointDomain := by
    simpa [F, ThetaTimeSpatialTrace.thetaNonnegativeJointDomain] using hθ
  have hwithin := ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin_contDiffOn (f := F) hθ' w
  have heq : ∀ p ∈ ThetaTimeSpatialTrace.thetaNonnegativeJointDomain,
      classicalWordDerivative w (θ p.1) p.2 =
        ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin w F p := by
    intro p hp
    rcases p with ⟨t, x⟩
    have ht : 0 ≤ t := by simpa [ThetaTimeSpatialTrace.thetaNonnegativeJointDomain] using hp.1
    exact (ThetaTimeSpatialTrace.thetaJointWordDerivativeWithin_eq_slice (f := F) hθ' w t ht x).symm
  have hwithin' := hwithin.congr heq
  simpa [ThetaTimeSpatialTrace.thetaNonnegativeJointDomain, F, Function.uncurry] using hwithin'

theorem theta_classical_word_slice_contDiff_nonneg
    {θ : ℝ → Vec 2 → ℝ}
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ∀ w, ∀ t : ℝ, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞)
      (classicalWordDerivative w (θ t)) := by
  intro w t ht
  have hmap : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => (t, x)) Set.univ :=
    contDiffOn_const.prodMk contDiffOn_id
  have hmem : ∀ x : Vec 2, (t, x) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
    intro x
    exact ⟨ht, Set.mem_univ x⟩
  have hcomp := hθ.comp hmap (fun x hx => hmem x)
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (θ t) :=
    contDiffOn_univ.mp (by
      simpa [Function.uncurry, Function.comp_def] using hcomp)
  exact classicalWordDerivative_contDiff w (θ t) hslice

end AVenhance.Infra.Section4
