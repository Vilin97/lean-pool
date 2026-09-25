/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.ExtendingAbsoluteValue
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalNorm
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.TensorProductDecomposition
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Canonical evaluation in the completion tensor decomposition

The finite product decomposition sends a pure tensor to the product of its
two canonical images in each completion. This specifies the same algebra
equivalence that appears in the determinant-norm product formula.
-/

@[expose] public section

open scoped BigOperators TensorProduct

noncomputable
section

namespace ClassFieldTheory

universe u v

/-- The completion tensor algebra decomposes canonically into the completions
above `vK`: on pure tensors each coordinate is standard multiplication, and
the determinant norm is the product of the coordinate norms. -/
theorem completionTensorNormDecomposition_canonical
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
            (∀ (b : vK.Completion) (a : L)
                (w : ExtendingAbsoluteValue vK L),
              e (b ⊗ₜ[K] a) w =
                algebraMap vK.Completion w.1.Completion b *
                  algebraMap L w.1.Completion a) ∧
            ∀ z : vK.Completion ⊗[K] L,
              Algebra.norm vK.Completion z =
                ∏ w : ExtendingAbsoluteValue vK L,
                  Algebra.norm vK.Completion (e z w) := by
  classical
  refine ⟨
    AlgebraicNumberTheory.Valuations.completionTensorDecompositionExtensionFintype
      (K := K) (L := L) vK hvK,
    (fun w => AbsoluteValue.completionAlgebra vK w.1 w.2),
    (fun w => AlgebraicNumberTheory.Valuations.completionModuleFinite vK hvK w),
    AlgebraicNumberTheory.Valuations.completionTensorDecompositionLeft
      (K := K) (L := L) vK hvK,
    ?_, ?_⟩
  · intro b a w
    let : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    calc
      _ = algebraMap vK.Completion w.1.Completion b *
            AbsoluteValue.toCompletionAlgHom (K := K) w.1 a :=
        AlgebraicNumberTheory.Valuations.completionTensorDecomposition_left_tmul_apply
          vK hvK b a w
      _ = algebraMap vK.Completion w.1.Completion b *
            algebraMap L w.1.Completion a := by
        have hcomp : AbsoluteValue.toCompletionAlgHom (K := K) w.1 a =
            algebraMap L w.1.Completion a := by
          change AbsoluteValue.toCompletion w.1 a =
            algebraMap L w.1.Completion a
          exact AbsoluteValue.toCompletion_eq_algebraMap w.1 a
        exact congrArg (fun y : w.1.Completion =>
          algebraMap vK.Completion w.1.Completion b * y) hcomp
  · intro z
    exact RelativeIdeleGroup.localNorm_eq_prod vK hvK z

end ClassFieldTheory
