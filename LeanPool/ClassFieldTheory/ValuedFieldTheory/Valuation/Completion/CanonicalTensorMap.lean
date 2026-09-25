/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.FiniteLocalization
public import Mathlib.Algebra.Algebra.Pi
/-!
# The canonical tensor map to all completions

For every exact extension `w | v`, multiplication in `L_w` gives the map
`K_v ⊗_K L → L_w`.  Taking all components produces the canonical map
which occurs in the tensor-product decomposition over a completion.  This construction is
independent of the factorisation argument later used to prove bijectivity.
-/

@[expose] public section

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

open scoped TensorProduct

/-- The product of the component maps `K_v ⊗_K L → L_w`. -/
noncomputable def completionTensorMapLeftCanonicalHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    vK.Completion ⊗[K] L →ₐ[vK.Completion]
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion := by
  letI : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  exact AlgHom.pi fun w ↦
    absoluteValueExtensionLocalizationTensorHom vK w

@[simp]
theorem completionTensorMap_leftCanonicalHom_tmul_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (b : vK.Completion) (a : L)
    (w : AbsoluteValueExtension vK L) :
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    completionTensorMapLeftCanonicalHom vK (b ⊗ₜ[K] a) w =
      algebraMap vK.Completion w.1.Completion b *
        AbsoluteValue.toCompletionAlgHom (K := K) w.1 a := by
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  exact absoluteValueExtension_localizationTensorHom_tmul vK w b a

/-- The canonical `K_v`-algebra map in the chosen tensor-factor order
`L ⊗_K K_v`. -/
noncomputable def completionTensorMapCanonicalHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) :
    letI := Algebra.TensorProduct.rightAlgebra
      (R := K) (A := L) (B := vK.Completion)
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    L ⊗[K] vK.Completion →ₐ[vK.Completion]
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion := by
  letI := Algebra.TensorProduct.rightAlgebra
    (R := K) (A := L) (B := vK.Completion)
  letI : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let e := Algebra.TensorProduct.comm K L vK.Completion
  let h : vK.Completion ⊗[K] L →ₐ[vK.Completion]
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion :=
    completionTensorMapLeftCanonicalHom vK
  exact
    { toRingHom := h.toRingHom.comp e.toRingEquiv.toRingHom
      commutes' := fun b ↦ by
        change h (e (algebraMap vK.Completion
          (L ⊗[K] vK.Completion) b)) = _
        rw [Algebra.TensorProduct.right_algebraMap_apply,
          Algebra.TensorProduct.comm_tmul]
        exact h.commutes b }

@[simp]
theorem completionTensorMap_canonicalHom_tmul_apply
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (a : L) (b : vK.Completion)
    (w : AbsoluteValueExtension vK L) :
    letI := Algebra.TensorProduct.rightAlgebra
      (R := K) (A := L) (B := vK.Completion)
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    completionTensorMapCanonicalHom vK (a ⊗ₜ[K] b) w =
      AbsoluteValue.toCompletionAlgHom (K := K) w.1 a *
        algebraMap vK.Completion w.1.Completion b := by
  let := Algebra.TensorProduct.rightAlgebra
    (R := K) (A := L) (B := vK.Completion)
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  simp only [completionTensorMapCanonicalHom]
  change completionTensorMapLeftCanonicalHom (L := L) vK
      (Algebra.TensorProduct.comm K L vK.Completion (a ⊗ₜ[K] b)) w = _
  rw [Algebra.TensorProduct.comm_tmul,
    completionTensorMap_leftCanonicalHom_tmul_apply, mul_comm]

end Valuations
end AlgebraicNumberTheory

end
