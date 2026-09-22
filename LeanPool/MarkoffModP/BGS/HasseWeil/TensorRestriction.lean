/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Tensor restriction maps

This file packages the bilinear maps used in the Stepanov restriction step.
For submodules `R`, `S`, and `T` of a commutative `K`-algebra `L`, an algebra
endomorphism `φ` gives the two twisted products
`x * φ y` and `φ x * y`.  An explicit containment hypothesis promotes either
product to a linear map from `R ⊗[K] S` into `T`.

The final lemmas record the finite-generation and finrank consequences that
are needed when such a tensor restriction map is used as a target map in a
rank-nullity argument.
-/

namespace BGS.HasseWeil

open scoped TensorProduct

variable {K L : Type*} [Field K] [CommRing L] [Algebra K L]
variable {R S T : Submodule K L}

/-- The tensor restriction map induced by the twisted product
`(x, y) ↦ x * φ y`, with codomain restricted by `hmul`. -/
def tensorRestriction
    (φ : L →ₐ[K] L)
    (hmul : ∀ x : R, ∀ y : S, (x : L) * φ (y : L) ∈ T) :
    R ⊗[K] S →ₗ[K] T :=
  TensorProduct.lift <|
    LinearMap.mk₂ K
      (fun x y ↦ ⟨(x : L) * φ (y : L), hmul x y⟩)
      (fun x₁ x₂ y ↦ by
        apply Subtype.ext
        change ((x₁ : L) + (x₂ : L)) * φ (y : L) =
          (x₁ : L) * φ (y : L) + (x₂ : L) * φ (y : L)
        rw [add_mul])
      (fun c x y ↦ by
        apply Subtype.ext
        change (c • (x : L)) * φ (y : L) =
          c • ((x : L) * φ (y : L))
        rw [smul_mul_assoc])
      (fun x y₁ y₂ ↦ by
        apply Subtype.ext
        change (x : L) * φ ((y₁ : L) + (y₂ : L)) =
          (x : L) * φ (y₁ : L) + (x : L) * φ (y₂ : L)
        rw [map_add, mul_add])
      (fun c x y ↦ by
        apply Subtype.ext
        change (x : L) * φ (c • (y : L)) =
          c • ((x : L) * φ (y : L))
        rw [map_smul, mul_smul_comm])

@[simp]
theorem tensorRestriction_tmul
    (φ : L →ₐ[K] L)
    (hmul : ∀ x : R, ∀ y : S, (x : L) * φ (y : L) ∈ T)
    (x : R) (y : S) :
    tensorRestriction φ hmul (x ⊗ₜ[K] y) =
      ⟨(x : L) * φ (y : L), hmul x y⟩ :=
  rfl

/-- The swapped tensor restriction map induced by the twisted product
`(x, y) ↦ φ x * y`, with codomain restricted by `hmul`. -/
def swappedTensorRestriction
    (φ : L →ₐ[K] L)
    (hmul : ∀ x : R, ∀ y : S, φ (x : L) * (y : L) ∈ T) :
    R ⊗[K] S →ₗ[K] T :=
  TensorProduct.lift <|
    LinearMap.mk₂ K
      (fun x y ↦ ⟨φ (x : L) * (y : L), hmul x y⟩)
      (fun x₁ x₂ y ↦ by
        apply Subtype.ext
        change φ ((x₁ : L) + (x₂ : L)) * (y : L) =
          φ (x₁ : L) * (y : L) + φ (x₂ : L) * (y : L)
        rw [map_add, add_mul])
      (fun c x y ↦ by
        apply Subtype.ext
        change φ (c • (x : L)) * (y : L) =
          c • (φ (x : L) * (y : L))
        rw [map_smul, smul_mul_assoc])
      (fun x y₁ y₂ ↦ by
        apply Subtype.ext
        change φ (x : L) * ((y₁ : L) + (y₂ : L)) =
          φ (x : L) * (y₁ : L) + φ (x : L) * (y₂ : L)
        rw [mul_add])
      (fun c x y ↦ by
        apply Subtype.ext
        change φ (x : L) * (c • (y : L)) =
          c • (φ (x : L) * (y : L))
        rw [mul_smul_comm])

@[simp]
theorem swappedTensorRestriction_tmul
    (φ : L →ₐ[K] L)
    (hmul : ∀ x : R, ∀ y : S, φ (x : L) * (y : L) ∈ T)
    (x : R) (y : S) :
    swappedTensorRestriction φ hmul (x ⊗ₜ[K] y) =
      ⟨φ (x : L) * (y : L), hmul x y⟩ :=
  rfl

/-- A tensor product of finite modules is finite.  This named bridge keeps
downstream restriction arguments independent of the tensor-product instance
search details. -/
theorem moduleFinite_tensorProduct
    [Module.Finite K R] [Module.Finite K S] :
    Module.Finite K (R ⊗[K] S) :=
  Module.Finite.tensorProduct K R S

/-- The range of a linear map out of a tensor product of finite modules is
finite. -/
theorem moduleFinite_range_tensorProductMap
    {U : Type*} [AddCommGroup U] [Module K U]
    [Module.Finite K R] [Module.Finite K S]
    (f : R ⊗[K] S →ₗ[K] U) :
    Module.Finite K (LinearMap.range f) := by
  let : Module.Finite K (R ⊗[K] S) :=
    moduleFinite_tensorProduct
  exact Module.Finite.range f

/-- The range of a linear map out of `R ⊗ S` has finrank at most the product
of the two input finranks. -/
theorem finrank_range_tensorProductMap_le
    {U : Type*} [AddCommGroup U] [Module K U]
    [Module.Finite K R] [Module.Finite K S]
    (f : R ⊗[K] S →ₗ[K] U) :
    Module.finrank K (LinearMap.range f) ≤
      Module.finrank K R * Module.finrank K S := by
  let : Module.Finite K (R ⊗[K] S) :=
    moduleFinite_tensorProduct
  calc
    Module.finrank K (LinearMap.range f) ≤
        Module.finrank K (R ⊗[K] S) :=
      LinearMap.finrank_range_le f
    _ = Module.finrank K R * Module.finrank K S :=
      Module.finrank_tensorProduct

/-- A surjective linear map out of `R ⊗ S` makes its target finite. -/
theorem moduleFinite_of_surjective_tensorProductMap
    {U : Type*} [AddCommGroup U] [Module K U]
    [Module.Finite K R] [Module.Finite K S]
    (f : R ⊗[K] S →ₗ[K] U) (hf : Function.Surjective f) :
    Module.Finite K U := by
  let : Module.Finite K (R ⊗[K] S) :=
    moduleFinite_tensorProduct
  exact Module.Finite.of_surjective f hf

/-- A surjective linear map out of `R ⊗ S` bounds the target finrank by the
product of the two input finranks. -/
theorem finrank_le_mul_of_surjective_tensorProductMap
    {U : Type*} [AddCommGroup U] [Module K U]
    [Module.Finite K R] [Module.Finite K S]
    (f : R ⊗[K] S →ₗ[K] U) (hf : Function.Surjective f) :
    Module.finrank K U ≤ Module.finrank K R * Module.finrank K S := by
  let : Module.Finite K (R ⊗[K] S) :=
    moduleFinite_tensorProduct
  calc
    Module.finrank K U ≤ Module.finrank K (R ⊗[K] S) :=
      LinearMap.finrank_le_finrank_of_surjective hf
    _ = Module.finrank K R * Module.finrank K S :=
      Module.finrank_tensorProduct

end BGS.HasseWeil
