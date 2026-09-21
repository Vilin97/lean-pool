/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.BoundedInverseRealization
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CoerciveUnit
import Mathlib.Tactic

/-!
# Bounded resolvent produced by a coercive form operator

A convenient Hilbert-space version of the form method is encoded by a dense
continuous embedding `j : V → H` and a bounded positive coercive self-adjoint
operator `A : V → V` representing the form.  The variational solution is

`u = A⁻¹ j* f`,

and the ambient solution operator is

`R = j A⁻¹ j*`.

This file constructs `R`, proves the variational identity, positivity,
self-adjointness, and injectivity, then invokes `BoundedInverseRealization` to
produce the associated positive self-adjoint unbounded operator.

The free-beam specialization takes `V` to be an `H²` form space and `A` to
represent the shifted bending form.

The scalar field is an arbitrary `RCLike` `𝕜`, so the whole form method is
available over `ℝ` as well as over `ℂ`.
-/

open scoped InnerProductSpace

namespace TauCeti

open TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Abstract

noncomputable section

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V]

/-- Data for a coercive symmetric form represented by a bounded operator on a
form Hilbert space. -/
structure CoerciveFormData where
  /-- The continuous, injective, dense embedding of the form space into the ambient Hilbert
  space. -/
  embed : V →L[𝕜] H
  embed_injective : Function.Injective embed
  embed_dense : DenseRange embed
  embed_adjoint_injective : Function.Injective embed.adjoint
  /-- The bounded self-adjoint operator representing the coercive form on its Hilbert space. -/
  formOperator : V →L[𝕜] V
  form_selfAdjoint : IsSelfAdjoint formOperator
  /-- The positive constant in the quadratic coercivity lower bound. -/
  coercivityConstant : ℝ
  coercivity_pos : 0 < coercivityConstant
  coercive : ∀ u : V,
    coercivityConstant * ‖u‖ ^ 2 ≤
      RCLike.re ⟪formOperator u, u⟫_𝕜

namespace CoerciveFormData

/-- Coercivity makes the form operator invertible in the bounded-operator
algebra. -/
theorem formOperator_isUnit (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    IsUnit D.formOperator :=
  ContinuousLinearMap.isUnit_of_coercive D.coercivity_pos D.coercive

/-- Bounded inverse of the represented form operator. -/
noncomputable def formInverse (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    V →L[𝕜] V :=
  Ring.inverse D.formOperator

/-- Variational solution map from ambient forcing to the form space. -/
noncomputable def solutionOperator
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    H →L[𝕜] V :=
  D.formInverse ∘L D.embed.adjoint

/-- Ambient bounded resolvent produced by the form method. -/
noncomputable def resolvent
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    H →L[𝕜] H :=
  D.embed ∘L D.solutionOperator

/-- The solution operator of a coercive form, unfolded. -/
@[simp] theorem solutionOperator_apply
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (f : H) :
    D.solutionOperator f = D.formInverse (D.embed.adjoint f) := rfl

/-- The form's inverse, unfolded.  **Note this is `A⁻¹`, not a resolvent at a spectral
parameter** -- it is unrelated to `TauCeti.LinearPMap.resolvent` despite the name. -/
@[simp] theorem resolvent_apply
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (f : H) :
    D.resolvent f = D.embed (D.solutionOperator f) := rfl

/-- Applying the form operator to the variational solution returns the adjoint
embedding of the forcing. -/
theorem formOperator_solutionOperator
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (f : H) :
    D.formOperator (D.solutionOperator f) = D.embed.adjoint f := by
  have hmul : D.formOperator * Ring.inverse D.formOperator = 1 :=
    Ring.mul_inverse_cancel D.formOperator D.formOperator_isUnit
  have happ := DFunLike.congr_fun hmul (D.embed.adjoint f)
  simpa [solutionOperator, formInverse] using happ

/-- The solution operator is injective because the adjoint embedding is
injective. -/
theorem solutionOperator_injective
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    Function.Injective D.solutionOperator := by
  intro f g hfg
  apply D.embed_adjoint_injective
  rw [← D.formOperator_solutionOperator f,
    ← D.formOperator_solutionOperator g, hfg]

/-- Variational identity in inner-product form. -/
theorem variational_identity
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V))
    (f : H) (v : V) :
    ⟪D.formOperator (D.solutionOperator f), v⟫_𝕜 =
      ⟪f, D.embed v⟫_𝕜 := by
  rw [D.formOperator_solutionOperator]
  exact ContinuousLinearMap.adjoint_inner_left D.embed v f

/-- The ambient form resolvent is injective. -/
theorem resolvent_injective
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    Function.Injective D.resolvent := by
  intro f g hfg
  apply D.solutionOperator_injective
  apply D.embed_injective
  exact hfg

/-- The ambient form resolvent is symmetric. -/
theorem resolvent_isSymmetric
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    D.resolvent.IsSymmetric := by
  intro f g
  let u := D.solutionOperator f
  let v := D.solutionOperator g
  calc
    ⟪D.resolvent f, g⟫_𝕜 = ⟪u, D.embed.adjoint g⟫_𝕜 := by
      rw [resolvent_apply]
      simpa [u] using
        (ContinuousLinearMap.adjoint_inner_right D.embed u g).symm
    _ = ⟪u, D.formOperator v⟫_𝕜 := by
      rw [D.formOperator_solutionOperator g]
    _ = ⟪D.formOperator u, v⟫_𝕜 := by
      exact D.form_selfAdjoint.isSymmetric u v |>.symm
    _ = ⟪D.embed.adjoint f, v⟫_𝕜 := by
      rw [D.formOperator_solutionOperator f]
    _ = ⟪f, D.resolvent g⟫_𝕜 := by
      rw [resolvent_apply]
      exact ContinuousLinearMap.adjoint_inner_left D.embed v f

/-- The ambient form resolvent is self-adjoint. -/
theorem resolvent_isSelfAdjoint
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    IsSelfAdjoint D.resolvent :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr D.resolvent_isSymmetric

/-- The resolvent quadratic form is the represented form energy of its
variational solution. -/
theorem resolvent_energy_identity
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (f : H) :
    ⟪D.resolvent f, f⟫_𝕜 =
      ⟪D.formOperator (D.solutionOperator f), D.solutionOperator f⟫_𝕜 := by
  calc
    ⟪D.resolvent f, f⟫_𝕜 =
        ⟪D.solutionOperator f, D.embed.adjoint f⟫_𝕜 := by
      rw [resolvent_apply]
      exact (ContinuousLinearMap.adjoint_inner_right D.embed
        (D.solutionOperator f) f).symm
    _ = ⟪D.solutionOperator f,
        D.formOperator (D.solutionOperator f)⟫_𝕜 := by
      rw [D.formOperator_solutionOperator]
    _ = ⟪D.formOperator (D.solutionOperator f),
        D.solutionOperator f⟫_𝕜 := by
      exact D.form_selfAdjoint.isSymmetric _ _ |>.symm

/-- The ambient form resolvent is positive. -/
theorem resolvent_nonnegative
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (f : H) :
    0 ≤ RCLike.re ⟪D.resolvent f, f⟫_𝕜 := by
  rw [D.resolvent_energy_identity]
  exact le_trans
    (mul_nonneg D.coercivity_pos.le (sq_nonneg ‖D.solutionOperator f‖))
    (D.coercive (D.solutionOperator f))

/-- Closed positive self-adjoint operator associated to the coercive form. -/
noncomputable def associatedOperator
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    H →ₗ.[𝕜] H :=
  inversePartialMap D.resolvent D.resolvent_isSelfAdjoint
    D.resolvent_injective

/-- The associated unbounded operator is self-adjoint. -/
theorem associatedOperator_isSelfAdjoint
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    _root_.IsSelfAdjoint D.associatedOperator :=
  inversePartialMap_isSelfAdjoint
    D.resolvent D.resolvent_isSelfAdjoint D.resolvent_injective
    D.resolvent_nonnegative

/-- The form resolvent is the inverse of the associated operator on its domain. -/
 theorem associatedOperator_resolvent
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) (f : H) :
    D.associatedOperator
      ⟨D.resolvent f,
        LinearMap.mem_range_self D.resolvent.toLinearMap f⟩ = f := by
  exact inversePartialMap_apply_R
    D.resolvent D.resolvent_isSelfAdjoint D.resolvent_injective f

end CoerciveFormData

end

end Abstract
end FreeBeam
end DavisKahan
end TauCeti
