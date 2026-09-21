/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.BaseChangeNormTrace
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.FiniteProductNormTrace
/-!
# Degree, norm, and trace through a tensor-product decomposition

These are the purely linear-algebraic implications for a finite product decomposition.
They deliberately state the product terms as the components of a supplied
algebra equivalence.  A tensor-product decomposition identifies those components
with the canonical images in `L_w`; no compatibility theorem is assumed
here.
-/

noncomputable section

namespace ValuationTheory
namespace Completion

universe u v w

open scoped TensorProduct

/-- Finite rank is the sum of the ranks of the factors in a finite
dependent-product decomposition after scalar extension. -/
theorem baseChange_pi_finrank_eq_sum
    {K : Type u} {A : Type v} {L : Type w}
    [Field K] [Field A] [Field L] [Algebra K A] [Algebra K L]
    [FiniteDimensional K L]
    {I : Type*} [Fintype I]
    (B : I → Type*) [∀ i, Field (B i)] [∀ i, Algebra A (B i)]
    [∀ i, Module.Finite A (B i)]
    (e : A ⊗[K] L ≃ₐ[A] ∀ i, B i) :
    Module.finrank K L = ∑ i, Module.finrank A (B i) := by
  calc
    Module.finrank K L = Module.finrank A (A ⊗[K] L) :=
      Module.finrank_baseChange.symm
    _ = Module.finrank A (∀ i, B i) := e.toLinearEquiv.finrank_eq
    _ = ∑ i, Module.finrank A (B i) := Module.finrank_pi_fintype A

/-- The base-changed global norm is the product of the norms of the
components under a finite dependent-product decomposition. -/
theorem baseChange_pi_norm_eq_prod
    {K : Type u} {A : Type v} {L : Type w}
    [Field K] [Field A] [Field L] [Algebra K A] [Algebra K L]
    [FiniteDimensional K L]
    {I : Type*} [Fintype I]
    (B : I → Type*) [∀ i, Field (B i)] [∀ i, Algebra A (B i)]
    [∀ i, Module.Finite A (B i)]
    (e : A ⊗[K] L ≃ₐ[A] ∀ i, B i) (x : L) :
    algebraMap K A (Algebra.norm K x) =
      ∏ i, Algebra.norm A (e (1 ⊗ₜ[K] x) i) := by
  calc
    algebraMap K A (Algebra.norm K x) =
        Algebra.norm A (1 ⊗ₜ[K] x) :=
      (algebra_norm_baseChange_tmul (A := A) x).symm
    _ = Algebra.norm A (e (1 ⊗ₜ[K] x)) :=
      (Algebra.norm_eq_of_algEquiv e (1 ⊗ₜ[K] x)).symm
    _ = ∏ i, Algebra.norm A (e (1 ⊗ₜ[K] x) i) :=
      algebra_norm_pi_apply B _

/-- The base-changed global trace is the sum of the traces of the
components under a finite dependent-product decomposition. -/
theorem baseChange_pi_trace_eq_sum
    {K : Type u} {A : Type v} {L : Type w}
    [Field K] [Field A] [Field L] [Algebra K A] [Algebra K L]
    [FiniteDimensional K L]
    {I : Type*} [Fintype I]
    (B : I → Type*) [∀ i, Field (B i)] [∀ i, Algebra A (B i)]
    [∀ i, Module.Finite A (B i)]
    (e : A ⊗[K] L ≃ₐ[A] ∀ i, B i) (x : L) :
    algebraMap K A (Algebra.trace K L x) =
      ∑ i, Algebra.trace A (B i) (e (1 ⊗ₜ[K] x) i) := by
  calc
    algebraMap K A (Algebra.trace K L x) =
        Algebra.trace A (A ⊗[K] L) (1 ⊗ₜ[K] x) :=
      (algebra_trace_baseChange_tmul (A := A) x).symm
    _ = Algebra.trace A (∀ i, B i) (e (1 ⊗ₜ[K] x)) :=
      (Algebra.trace_eq_of_algEquiv e (1 ⊗ₜ[K] x)).symm
    _ = ∑ i, Algebra.trace A (B i) (e (1 ⊗ₜ[K] x) i) :=
      algebra_trace_pi_apply B _

end Completion
end ValuationTheory

end
