/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SigmaMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatZetaML
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ZetaMK
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Psi
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.LIdx
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsHolderClass
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SmoothField
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.LIdxConsequences
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVel

/-! Infrastructure for the §2 construction. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Infra.Construction

theorem fderiv_slice {φ : ℝ → Vec 2 → ℝ} (h : IsAdmissibleStream φ) (t : ℝ) (x v : Vec 2) :
    fderiv ℝ (φ t) x v = fderiv ℝ (Function.uncurry φ) (t, x) (0, v) := by
  have hF : DifferentiableAt ℝ (Function.uncurry φ) (t, x) :=
    (h.1.differentiable (by simp)) _
  have hg : HasFDerivAt (fun y : Vec 2 => (t, y))
      ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have := (hF.hasFDerivAt.comp x hg).fderiv
  change fderiv ℝ (fun y => Function.uncurry φ (t, y)) x = _ at this
  have e : (fun y => Function.uncurry φ (t, y)) = φ t := rfl
  rw [e] at this
  rw [this]
  simp

theorem contDiff_partial {φ : ℝ → Vec 2 → ℝ} (h : IsAdmissibleStream φ) (v : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => fderiv ℝ (Function.uncurry φ) p (0, v)) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry φ)) :=
    h.1.fderiv_right (by simp)
  exact h1.clm_apply contDiff_const

theorem streamVel_apply {φ : ℝ → Vec 2 → ℝ} (h : IsAdmissibleStream φ) (t : ℝ) (x : Vec 2) :
    streamVel φ t x = ![-(fderiv ℝ (Function.uncurry φ) (t, x) (0, basisVec 1)),
      fderiv ℝ (Function.uncurry φ) (t, x) (0, basisVec 0)] := by
  ext i
  fin_cases i <;>
    simp [streamVel, sigmaMat, spaceGrad, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      fderiv_slice h]

/-- The velocity of an admissible stream is a smooth jointly periodic field. -/
theorem smoothPeriodic_streamVel {φ : ℝ → Vec 2 → ℝ} (h : IsAdmissibleStream φ) :
    Infra.Flow.SmoothPeriodicField (streamVel φ) := by
  refine ⟨?_, ?_⟩
  · have : Function.uncurry (streamVel φ) = fun p : ℝ × Vec 2 =>
        ![-(fderiv ℝ (Function.uncurry φ) p (0, basisVec 1)),
          fderiv ℝ (Function.uncurry φ) p (0, basisVec 0)] := by
      funext p
      exact streamVel_apply h p.1 p.2
    rw [this]
    refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · exact (contDiff_partial h _).neg
    · exact contDiff_partial h _
  · intro n k t x
    have hper : (fun y => φ (t + (n : ℝ)) (y + latticeShift k)) = φ t := by
      funext y; exact h.2 n k t y
    have hd : ∀ v, fderiv ℝ (φ (t + (n : ℝ))) (x + latticeShift k) v = fderiv ℝ (φ t) x v := by
      intro v
      rw [← hper, fderiv_comp_add_right]
    ext i
    fin_cases i <;>
      simp [streamVel, sigmaMat, spaceGrad, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd]

end Infra.Construction

end AVenhance
