/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.TensorProductDecomposition
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.TensorProductProductFormulas
/-!
# Compatibility of local degree, norm, and trace

The canonical decomposition of the completion tensor-product decomposition gives the sum of the
  local
degrees and the product/sum formulas for norm and trace.  Since the global
norm and trace lie in `K`, their Lean statements are mapped into `K_v`.
-/

noncomputable section

open scoped BigOperators TensorProduct
open ValuationTheory.Completion

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

/-- Every local completion is finite-dimensional over `K_v`.  This is
derived from the completion tensor-product decomposition by projecting from its finite product. -/
theorem completionModuleFinite
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    Module.Finite vK.Completion w.1.Completion := by
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Module.Finite vK.Completion (vK.Completion ⊗[K] L) :=
    inferInstance
  let : Module.Finite vK.Completion
      (∀ w : AbsoluteValueExtension vK L, w.1.Completion) :=
    Module.Finite.equiv (completionTensorDecompositionLeft vK hvK).toLinearEquiv
  exact moduleFiniteOfPi
    (fun w : AbsoluteValueExtension vK L ↦ w.1.Completion) w

/-- the local degree, norm, and trace formulas, degree formula. -/
theorem completionDegreeNormTrace_degree
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w ↦ completionModuleFinite vK hvK w
    Module.finrank K L =
      ∑ w : AbsoluteValueExtension vK L,
        Module.finrank vK.Completion w.1.Completion := by
  let := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w ↦ completionModuleFinite vK hvK w
  exact baseChange_pi_finrank_eq_sum
    (fun w : AbsoluteValueExtension vK L ↦ w.1.Completion)
    (completionTensorDecompositionLeft vK hvK)

/-- the local degree, norm, and trace formulas, norm formula, written in `K_v`. -/
theorem completionDegreeNormTrace_norm
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) (x : L) :
    letI := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w ↦ completionModuleFinite vK hvK w
    algebraMap K vK.Completion (Algebra.norm K x) =
      ∏ w : AbsoluteValueExtension vK L,
        Algebra.norm vK.Completion
          (AbsoluteValue.toCompletionAlgHom (K := K) w.1 x) := by
  let := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w ↦ completionModuleFinite vK hvK w
  simpa using baseChange_pi_norm_eq_prod
    (fun w : AbsoluteValueExtension vK L ↦ w.1.Completion)
    (completionTensorDecompositionLeft vK hvK) x

/-- the local degree, norm, and trace formulas, trace formula, written in `K_v`. -/
theorem completionDegreeNormTrace_trace
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) (x : L) :
    letI := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w ↦ completionModuleFinite vK hvK w
    algebraMap K vK.Completion (Algebra.trace K L x) =
      ∑ w : AbsoluteValueExtension vK L,
        Algebra.trace vK.Completion w.1.Completion
          (AbsoluteValue.toCompletionAlgHom (K := K) w.1 x) := by
  let := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w ↦ completionModuleFinite vK hvK w
  simpa using baseChange_pi_trace_eq_sum
    (fun w : AbsoluteValueExtension vK L ↦ w.1.Completion)
    (completionTensorDecompositionLeft vK hvK) x

/-- **the local degree, norm, and trace formulas.**  The degree, norm, and trace formulas obtained
simultaneously from the canonical decomposition of the completion tensor-product decomposition. -/
theorem completionDegreeNormTrace
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    letI := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w ↦ completionModuleFinite vK hvK w
    (Module.finrank K L =
      ∑ w : AbsoluteValueExtension vK L,
        Module.finrank vK.Completion w.1.Completion) ∧
    (∀ x : L,
      algebraMap K vK.Completion (Algebra.norm K x) =
        ∏ w : AbsoluteValueExtension vK L,
          Algebra.norm vK.Completion
            (AbsoluteValue.toCompletionAlgHom (K := K) w.1 x)) ∧
    (∀ x : L,
      algebraMap K vK.Completion (Algebra.trace K L x) =
        ∑ w : AbsoluteValueExtension vK L,
          Algebra.trace vK.Completion w.1.Completion
            (AbsoluteValue.toCompletionAlgHom (K := K) w.1 x)) := by
  let := completionTensorDecompositionExtensionFintype (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w ↦ completionModuleFinite vK hvK w
  exact ⟨completionDegreeNormTrace_degree (K := K) (L := L) vK hvK,
    fun x ↦ completionDegreeNormTrace_norm (K := K) (L := L) vK hvK x,
    fun x ↦ completionDegreeNormTrace_trace (K := K) (L := L) vK hvK x⟩

end Valuations
end AlgebraicNumberTheory

end
