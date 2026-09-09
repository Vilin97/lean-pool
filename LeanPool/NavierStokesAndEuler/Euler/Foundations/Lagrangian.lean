/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Measurability.Init

/-!
# Lagrangian
-/

@[expose] public section

noncomputable section

namespace EulerLagrangian

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The unforced Euler momentum residual, with space-time derivative and the
canonical real gradient. -/
def momentumResidual (u : ℝ × E → E) (p : ℝ × E → ℝ) (z : ℝ × E) : E :=
  fderiv ℝ u z (1, u z) + gradient (fun x => p (z.1, x)) z.2

omit [CompleteSpace E] in
theorem material_derivative (w : ℝ × E → E) (X : ℝ → E) (t : ℝ)
    (U : E) (D : (ℝ × E) →L[ℝ] E)
    (hX : HasDerivAt X U t) (hw : HasFDerivAt w D (t, X t)) :
    HasDerivAt (fun s => w (s, X s)) (D (1, U)) t :=
  hw.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hX)

theorem gradient_add (f g : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y + g y) x = gradient f x + gradient g x := by
  have hs : HasFDerivAt (fun y => f y + g y) (fderiv ℝ f x + fderiv ℝ g x) x :=
    hf.hasFDerivAt.add hg.hasFDerivAt
  simp only [gradient, hs.fderiv, map_add]

theorem momentum_perturbation (u w : ℝ × E → E) (p q : ℝ × E → ℝ)
    (z : ℝ × E) (Du Dw : (ℝ × E) →L[ℝ] E)
    (hu : HasFDerivAt u Du z) (hw : HasFDerivAt w Dw z)
    (hp : DifferentiableAt ℝ (fun x => p (z.1, x)) z.2)
    (hq : DifferentiableAt ℝ (fun x => q (z.1, x)) z.2) :
    momentumResidual (fun y => u y + w y) (fun y => p y + q y) z =
      momentumResidual u p z + Dw (1, u z) + Du (0, w z) + Dw (0, w z) +
        gradient (fun x => q (z.1, x)) z.2 := by
  have hsplit : ((1 : ℝ), u z + w z) = (1, u z) + (0, w z) := by simp
  have hs : HasFDerivAt (fun y => u y + w y) (Du + Dw) z := hu.add hw
  simp only [momentumResidual, hs.fderiv, hu.fderiv,
    add_apply, hsplit, map_add,
    gradient_add _ _ _ hp hq]
  abel

theorem euler_perturbation_along_flow (u w : ℝ × E → E)
    (p q : ℝ × E → ℝ) (X : ℝ → E) (t : ℝ)
    (Du Dw : (ℝ × E) →L[ℝ] E) (V : E)
    (hX : HasDerivAt X (u (t, X t)) t)
    (hu : HasFDerivAt u Du (t, X t)) (hw : HasFDerivAt w Dw (t, X t))
    (hW : HasDerivAt (fun s => w (s, X s)) V t)
    (hp : DifferentiableAt ℝ (fun x => p (t, x)) (X t))
    (hq : DifferentiableAt ℝ (fun x => q (t, x)) (X t))
    (hparent : momentumResidual u p (t, X t) = 0) :
    momentumResidual (fun y => u y + w y) (fun y => p y + q y) (t, X t) =
      V + Du (0, w (t, X t)) + Dw (0, w (t, X t)) +
        gradient (fun x => q (t, x)) (X t) := by
  have hV := hW.unique (material_derivative w X t _ Dw hX hw)
  rw [momentum_perturbation u w p q (t, X t) Du Dw hu hw hp hq, hparent,
    zero_add, ← hV]

omit [CompleteSpace E] in
theorem deformation_acceleration (F M H : ℝ → E →L[ℝ] E) (t : ℝ)
    (hF : HasDerivAt F ((M t).comp (F t)) t)
    (hM : HasDerivAt M (-((M t).comp (M t)) - H t) t) :
    HasDerivAt (fun s => (M s).comp (F s)) (-((H t).comp (F t))) t := by
  convert hM.clm_comp hF using 1
  ext v
  simp only [add_apply, sub_apply, neg_apply, ContinuousLinearMap.comp_apply]
  abel

omit [CompleteSpace E] in
theorem derivative_pullback_inverse (f X : E → E) (F : E ≃L[ℝ] E) (x : E)
    (hX : HasFDerivAt X F.toContinuousLinearMap x)
    (hf : DifferentiableAt ℝ f (X x)) :
    fderiv ℝ f (X x) = (fderiv ℝ (f ∘ X) x).comp F.symm.toContinuousLinearMap := by
  rw [(hf.hasFDerivAt.comp x hX).fderiv]
  ext v
  simp

theorem gradient_pullback (f : E → ℝ) (X : E → E) (F : E →L[ℝ] E) (x : E)
    (hX : HasFDerivAt X F x) (hf : DifferentiableAt ℝ f (X x)) :
    gradient (f ∘ X) x = F.adjoint (gradient f (X x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left,
    (hf.hasFDerivAt.comp x hX).fderiv]
  rfl

theorem gradient_pullback_inverse (f : E → ℝ) (X : E → E) (F : E ≃L[ℝ] E) (x : E)
    (hX : HasFDerivAt X F.toContinuousLinearMap x)
    (hf : DifferentiableAt ℝ f (X x)) :
    gradient f (X x) = F.symm.toContinuousLinearMap.adjoint (gradient (f ∘ X) x) := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left, gradient_pullback f X _ x hX hf,
    ContinuousLinearMap.adjoint_inner_left]
  simp

end EulerLagrangian
