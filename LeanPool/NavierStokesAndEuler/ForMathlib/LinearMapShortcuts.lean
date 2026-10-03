/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Shortcut instances for applying continuous linear maps and linear isometries

Applying a continuous (semi)linear map or a (semi)linear isometry to an argument asks for its
coercion to a function, and rewriting with `map_add`, `map_sub` or `map_zero` asks for its
homomorphism classes. Both are found through the generic function-like hierarchy, which first
tries the other kinds of maps and, for a map between concrete function spaces, re-derives
structures on the two spaces along the way. The search is slowest when the spaces are not yet
known, as for a bundled operator whose implicit arguments are determined only by its argument.

The instances below answer these queries from the shape of the map type alone. Each is the
instance that resolution already finds, registered with high priority.
-/

public section

namespace NavierStokesAndEuler

section ContinuousLinearMap

variable {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {M N : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [TopologicalSpace N] [AddCommMonoid N] [Module S N]

/-- Shortcut for the coercion of a continuous semilinear map to a function. -/
instance (priority := high) ContinuousLinearMapShortcut.instCoeFun :
    CoeFun (M →SL[σ] N) fun _ => M → N := inferInstance

instance (priority := high) ContinuousLinearMapShortcut.instAddMonoidHomClass :
    AddMonoidHomClass (M →SL[σ] N) M N := inferInstance

instance (priority := high) ContinuousLinearMapShortcut.instAddHomClass :
    AddHomClass (M →SL[σ] N) M N := inferInstance

instance (priority := high) ContinuousLinearMapShortcut.instZeroHomClass :
    ZeroHomClass (M →SL[σ] N) M N := inferInstance

end ContinuousLinearMap

section ContinuousLinearMapLinear

variable {R : Type*} [Semiring R] {M N : Type*} [TopologicalSpace M] [AddCommMonoid M]
  [Module R M] [TopologicalSpace N] [AddCommMonoid N] [Module R N]

instance (priority := high) ContinuousLinearMapShortcut.instMulActionHomClass :
    MulActionHomClass (M →L[R] N) R M N := inferInstance

end ContinuousLinearMapLinear

section LinearIsometry

variable {R R₂ : Type*} [Semiring R] [Semiring R₂] {σ₁₂ : R →+* R₂}
  {E E₂ : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂]
  [Module R E] [Module R₂ E₂]

/-- Shortcut for the coercion of a semilinear isometry to a function. -/
instance (priority := high) LinearIsometryShortcut.instCoeFun :
    CoeFun (E →ₛₗᵢ[σ₁₂] E₂) fun _ => E → E₂ := inferInstance

instance (priority := high) LinearIsometryShortcut.instAddMonoidHomClass :
    AddMonoidHomClass (E →ₛₗᵢ[σ₁₂] E₂) E E₂ := inferInstance

instance (priority := high) LinearIsometryShortcut.instZeroHomClass :
    ZeroHomClass (E →ₛₗᵢ[σ₁₂] E₂) E E₂ := inferInstance

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- Shortcut for the coercion of a semilinear isometric equivalence to a function. -/
instance (priority := high) LinearIsometryEquivShortcut.instCoeFun :
    CoeFun (E ≃ₛₗᵢ[σ₁₂] E₂) fun _ => E → E₂ := inferInstance

instance (priority := high) LinearIsometryEquivShortcut.instAddMonoidHomClass :
    AddMonoidHomClass (E ≃ₛₗᵢ[σ₁₂] E₂) E E₂ := inferInstance

instance (priority := high) LinearIsometryEquivShortcut.instZeroHomClass :
    ZeroHomClass (E ≃ₛₗᵢ[σ₁₂] E₂) E E₂ := inferInstance

end LinearIsometry

end NavierStokesAndEuler

end
