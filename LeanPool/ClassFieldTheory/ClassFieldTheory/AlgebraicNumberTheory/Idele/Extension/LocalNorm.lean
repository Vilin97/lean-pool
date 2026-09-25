/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.DegreeNormTrace
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.FiniteProductNormTrace
/-!
# Local components of the idele norm

The local algebra at a place of the base field is a finite product of the
completions above it. This file proves that the determinant norm on a finite
product is the product of the norms of its factors. The last theorem applies
this calculation to the canonical completion decomposition.
-/

@[expose] public section

open scoped BigOperators TensorProduct

noncomputable section


namespace RelativeIdeleGroup

open AlgebraicNumberTheory.Valuations
open ValuationTheory.Completion

universe u v

/-- At one place of the base field, under the
canonical isomorphism

`K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w`,

the determinant norm of an arbitrary local component is the product of
the field norms of its components above `v`. -/
theorem localNorm_eq_prod
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (z : vK.Completion ⊗[K] L) :
    letI :=
      completionTensorDecompositionExtensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w ↦ completionModuleFinite vK hvK w
    _root_.Algebra.norm vK.Completion z =
      ∏ w : AbsoluteValueExtension vK L,
        _root_.Algebra.norm vK.Completion
          (completionTensorDecompositionLeft
            (K := K) (L := L) vK hvK z w) := by
  classical
  let :=
    completionTensorDecompositionExtensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Free vK.Completion w.1.Completion :=
    fun w ↦ Module.Free.of_divisionRing
      vK.Completion w.1.Completion
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w ↦ completionModuleFinite vK hvK w
  let e :=
    completionTensorDecompositionLeft
      (K := K) (L := L) vK hvK
  calc
    _root_.Algebra.norm vK.Completion z =
        _root_.Algebra.norm vK.Completion (e z) :=
      (_root_.Algebra.norm_eq_of_algEquiv e z).symm
    _ = ∏ w : AbsoluteValueExtension vK L,
        _root_.Algebra.norm vK.Completion (e z w) :=
      algebra_norm_pi_apply
        (R := vK.Completion)
        (fun w : AbsoluteValueExtension vK L ↦
          w.1.Completion) (e z)

/-- The unit-valued version of `localNorm_eq_prod`, which is the formula
used for local components of ideles. -/
theorem localNorm_units_eq_prod
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (z : (vK.Completion ⊗[K] L)ˣ) :
    letI :=
      completionTensorDecompositionExtensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w ↦ completionModuleFinite vK hvK w
    ((Units.map (_root_.Algebra.norm vK.Completion) z :
        vK.Completionˣ) : vK.Completion) =
      ∏ w : AbsoluteValueExtension vK L,
        _root_.Algebra.norm vK.Completion
          (completionTensorDecompositionLeft
            (K := K) (L := L) vK hvK (z : _) w) := by
  exact localNorm_eq_prod vK hvK (z : vK.Completion ⊗[K] L)

end RelativeIdeleGroup
