/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.ExtendingAbsoluteValue
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalNorm
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Local norm as a product over completions

The tensor algebra `K_v ⊗[K] L` is a product of the completions of `L` at
the absolute values above `v`.  Its determinant norm is the product of the
norms of those components.  The theorem exposes the decomposition and norm
formula using only Mathlib objects and the public extension index type.
-/

open scoped BigOperators TensorProduct

noncomputable section

namespace ClassFieldTheory

universe u v

/-- A separable finite extension decomposes after completion, and its
determinant norm is the product of the norms of all completion components. -/
theorem completionTensorNormDecomposition
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) :
    ∃ hfin : Fintype (ExtendingAbsoluteValue vK L),
      letI := hfin
      ∃ halg : ∀ w : ExtendingAbsoluteValue vK L,
          Algebra vK.Completion w.1.Completion,
        letI := halg
        ∃ hmodule : ∀ w : ExtendingAbsoluteValue vK L,
            Module.Finite vK.Completion w.1.Completion,
          letI := hmodule
          ∃ e : vK.Completion ⊗[K] L ≃ₐ[vK.Completion]
              ∀ w : ExtendingAbsoluteValue vK L, w.1.Completion,
            ∀ z : vK.Completion ⊗[K] L,
              Algebra.norm vK.Completion z =
                ∏ w : ExtendingAbsoluteValue vK L,
                  Algebra.norm vK.Completion (e z w) := by
  classical
  refine ⟨
    AlgebraicNumberTheory.Valuations.completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK,
    (fun w => AbsoluteValue.completionAlgebra vK w.1 w.2),
    (fun w => AlgebraicNumberTheory.Valuations.completionModuleFinite vK hvK w),
    AlgebraicNumberTheory.Valuations.completionTensorDecomposition_left
      (K := K) (L := L) vK hvK,
    ?_⟩
  intro z
  exact RelativeIdeleGroup.localNorm_eq_prod vK hvK z

end ClassFieldTheory
