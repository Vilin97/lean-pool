/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerState
import LeanPool.NavierStokesAndEuler.Euler.ParentPacketHessianSymmetry
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-! The scalar pressure of a finite packet evolution is spatially smooth
because its actual gradient is smooth. Its curvature operator is therefore
symmetric, as required by the particle-map vorticity transport argument. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace EulerSmoothLimit
open scoped ContDiff

variable {A : Parent} (E : Evolution A)

theorem pressure_contDiff (t : Icc (0 : ℝ) A.T) :
    ContDiff ℝ ∞ (fun x => E.pressure (t,x)) := by
  apply contDiff_infty_iff_fderiv.mpr
  refine ⟨E.pressure_differentiable t,?_⟩
  have he : fderiv ℝ (fun x => E.pressure (t,x)) = (toDual ℝ Space) ∘ E.force t := by
    funext x
    rw [Function.comp_apply,← E.pressure_gradient t x,toDual_gradient]
  rw [he]
  exact (toDual ℝ Space).contDiff.comp (E.force_smooth t)

include E in
theorem curvature_symmetric (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.curvature.field t x).IsSymmetric := by
  rw [E.curvature_eq]
  have hf : E.force t = gradient (fun y => E.pressure (t,y)) :=
    funext (fun y => (E.pressure_gradient t y).symm)
  rw [hf]
  exact hessian_isSymmetric _ ((E.pressure_contDiff t).of_le (by simp)) _

end EulerParentPacketFrames.Evolution
