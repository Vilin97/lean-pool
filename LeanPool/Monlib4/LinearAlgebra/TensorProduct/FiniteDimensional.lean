/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Star.TensorProduct
import Mathlib.RingTheory.TensorProduct.Finite
import LeanPool.Monlib4.LinearAlgebra.IsReal
import LeanPool.Monlib4.LinearAlgebra.Ips.OpUnop
import LeanPool.Monlib4.LinearAlgebra.Ips.MulOp
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.BasicLemmas
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.Lemmas

/-!

# Tensor products of finite-dimensional star modules

This file defines the star operation on a tensor product of finite-dimensional
star modules and proves compatibility lemmas for tensor-product maps.

-/


open scoped TensorProduct BigOperators

section

variable {𝕜 E F G : Type _}
  [Field 𝕜] [StarRing 𝕜]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
  [StarAddMonoid E] [StarAddMonoid F] [StarAddMonoid G]
  [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]
  [StarModule 𝕜 G]
  [Module.Finite 𝕜 E] [Module.Finite 𝕜 F]
  [Module.Finite 𝕜 G]

omit [StarModule 𝕜 G] [Module.Finite 𝕜 E] [Module.Finite 𝕜 F]
  [Module.Finite 𝕜 G] in
/-- Compatibility name for the tensor-product star instance now provided by Mathlib. -/
noncomputable abbrev TensorProduct.Star [StarModule 𝕜 E] [StarModule 𝕜 F] :
    Star (E ⊗[𝕜] F) :=
  inferInstance

omit [StarModule 𝕜 G] [Module.Finite 𝕜 E] [Module.Finite 𝕜 F]
  [Module.Finite 𝕜 G] in
/-- Compatibility name for the tensor-product involutive-star instance. -/
noncomputable abbrev TensorProduct.InvolutiveStar [StarModule 𝕜 E] [StarModule 𝕜 F] :
    InvolutiveStar (E ⊗[𝕜] F) :=
  inferInstance

omit [StarModule 𝕜 G] [Module.Finite 𝕜 E] [Module.Finite 𝕜 F]
  [Module.Finite 𝕜 G] in
/-- Compatibility name for the tensor-product star-additive instance. -/
noncomputable abbrev TensorProduct.starAddMonoid [StarModule 𝕜 E] [StarModule 𝕜 F] :
    StarAddMonoid (E ⊗[𝕜] F) :=
  inferInstance

omit [StarModule 𝕜 G] [Module.Finite 𝕜 E] [Module.Finite 𝕜 F]
  [Module.Finite 𝕜 G] in
/-- Compatibility name for the tensor-product star-module instance. -/
theorem TensorProduct.starModule [StarModule 𝕜 E] [StarModule 𝕜 F] :
    StarModule 𝕜 (E ⊗[𝕜] F) :=
  inferInstance

omit [Module.Finite 𝕜 E] [Module.Finite 𝕜 F] in
/-- Tensor-product star is additive. -/
theorem TensorProduct.star_add
    [StarModule 𝕜 E] [StarModule 𝕜 F] (x y : E ⊗[𝕜] F) :
    star (x + y) = star x + star y :=
  StarAddMonoid.star_add x y

omit [Module.Finite 𝕜 E] [Module.Finite 𝕜 F] in
/-- Tensor-product star is involutive. -/
theorem TensorProduct.star_is_involutive [StarModule 𝕜 E] [StarModule 𝕜 F] :
    Function.Involutive (star : E ⊗[𝕜] F → E ⊗[𝕜] F) :=
  fun a => star_star a

theorem TensorProduct.map_real {A B E F : Type _} [AddCommGroup A] [AddCommGroup B] [AddCommGroup E]
    [AddCommGroup F] [StarAddMonoid A] [StarAddMonoid B] [StarAddMonoid E] [StarAddMonoid F]
    [Module 𝕜 A] [Module 𝕜 B] [Module 𝕜 E] [Module 𝕜 F] [StarModule 𝕜 A] [StarModule 𝕜 B]
    [StarModule 𝕜 E] [StarModule 𝕜 F] [Module.Finite 𝕜 A] [Module.Finite 𝕜 B]
    [Module.Finite 𝕜 E] [Module.Finite 𝕜 F] (f : E →ₗ[𝕜] F) (g : A →ₗ[𝕜] B) :
    (TensorProduct.map f g).real = TensorProduct.map f.real g.real :=
  by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.real_apply, TensorProduct.star_tmul, TensorProduct.map_tmul]


variable (A : Type _) [Ring A] [Module 𝕜 A] [StarRing A] [StarModule 𝕜 A] [SMulCommClass 𝕜 A A]
  [IsScalarTower 𝕜 A A] [Module.Finite 𝕜 A]

omit [Module.Finite 𝕜 A] in
theorem LinearMap.mul'_real :
    (LinearMap.mul' 𝕜 A).real = LinearMap.mul' 𝕜 A ∘ₗ (TensorProduct.comm 𝕜 A A).toLinearMap :=
  by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.real_apply, TensorProduct.star_tmul,
    LinearEquiv.coe_coe, LinearMap.comp_apply, TensorProduct.comm_tmul, LinearMap.mul'_apply,
    star_mul, star_star]

variable [StarModule 𝕜 E] [StarModule 𝕜 F]

omit [Module.Finite 𝕜 E] [Module.Finite 𝕜 F] [Module.Finite 𝕜 G] in
theorem TensorProduct.assoc_real :
    (TensorProduct.assoc 𝕜 E F G : (E ⊗[𝕜] F) ⊗[𝕜] G →ₗ[𝕜] E ⊗[𝕜] (F ⊗[𝕜] G)).real =
      TensorProduct.assoc 𝕜 E F G :=
  by
  apply TensorProduct.ext_threefold
  intro a b c
  simp only [LinearMap.real_apply, TensorProduct.star_tmul, LinearEquiv.coe_coe,
    TensorProduct.assoc_tmul, star_star]

omit [Module.Finite 𝕜 E] [Module.Finite 𝕜 F] in
theorem TensorProduct.comm_real :
    (TensorProduct.comm 𝕜 E F : E ⊗[𝕜] F →ₗ[𝕜] F ⊗[𝕜] E).real = TensorProduct.comm 𝕜 E F :=
  by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.real_apply, TensorProduct.star_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, star_star]

omit [Module.Finite 𝕜 E] in
theorem TensorProduct.lid_real :
    (TensorProduct.lid 𝕜 E : 𝕜 ⊗[𝕜] E →ₗ[𝕜] E).real = TensorProduct.lid 𝕜 E :=
  by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.real_apply, TensorProduct.star_tmul, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul, star_star, star_smul]

omit [Module.Finite 𝕜 E] in
theorem TensorProduct.rid_real :
    (TensorProduct.rid 𝕜 E : E ⊗[𝕜] 𝕜 →ₗ[𝕜] E).real = TensorProduct.rid 𝕜 E :=
  by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.real_apply, TensorProduct.star_tmul, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul, star_star, star_smul]

omit [Module.Finite 𝕜 E] in
theorem tensor_op_star_apply (x : E) (y : Eᵐᵒᵖ) :
    star (x ⊗ₜ[𝕜] y) = star x ⊗ₜ[𝕜] (op 𝕜) (star (unop 𝕜 y)) :=
  by
  simp only [TensorProduct.star_tmul]
  rfl

omit [Module.Finite 𝕜 E] in
theorem tenSwap_star (x : E ⊗[𝕜] Eᵐᵒᵖ) : star (tenSwap 𝕜 x) = tenSwap 𝕜 (star x) :=
x.induction_on
  (by simp only [star_zero, map_zero])
  (fun _ _ => by
    simp only [tenSwap_apply, tensor_op_star_apply, unop_apply, op_apply, MulOpposite.unop_op])
  (fun z w hz hw => by simp only [map_add, StarAddMonoid.star_add, hz, hw])

end

/-- Build a star algebra equivalence from a tensor-product linear equivalence. -/
noncomputable def starAlgEquivOfLinearEquivTensorProduct
  {R A B C : Type*} [RCLike R] [Ring A]
  [StarAddMonoid A]
  [Algebra R A] [StarModule R A]
  [Ring B] [StarAddMonoid B] [Algebra R B] [StarModule R B]
  [Semiring C] [Algebra R C] [StarAddMonoid C]
  (f : TensorProduct R A B ≃ₗ[R] C)
  (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B),
    f ((a₁ * a₂) ⊗ₜ[R] (b₁ * b₂)) = f (a₁ ⊗ₜ[R] b₁) * f (a₂ ⊗ₜ[R] b₂))
  (h_one : f (1 ⊗ₜ[R] 1) = 1)
  (h_star : ∀ (x : A) (y : B), f (star (x ⊗ₜ[R] y)) = star (f (x ⊗ₜ[R] y))) :
  TensorProduct R A B ≃⋆ₐ[R] C :=
StarAlgEquiv.ofAlgEquiv
  (Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct f h_mul h_one)
  (fun x => x.induction_on (by simp only [star_zero, map_zero])
    h_star
    (fun _ _ h1 h2 => by simp only [star_add, map_add, h1, h2]))

/-- Tensor a pair of star algebra equivalences. -/
noncomputable def StarAlgEquiv.TensorProduct.map {R A B C D : Type*} [RCLike R]
  [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  [StarAddMonoid A] [StarAddMonoid B] [StarAddMonoid C] [StarAddMonoid D]
  [StarModule R A] [StarModule R B] [StarModule R C] [StarModule R D]
  (f : A ≃⋆ₐ[R] B) (g : C ≃⋆ₐ[R] D) :
  TensorProduct R A C ≃⋆ₐ[R] TensorProduct R B D :=
StarAlgEquiv.ofAlgEquiv
  (AlgEquiv.TensorProduct.map f.toAlgEquiv g.toAlgEquiv)
  (fun x => x.induction_on
    (by simp only [star_zero, map_zero])
    (fun _ _ => by simp only [TensorProduct.star_tmul, AlgEquiv.TensorProduct.map_tmul,
      coe_toAlgEquiv, map_star])
    (fun _ _ h1 h2 => by simp only [star_add, map_add, h1, h2]))

theorem StarAlgEquiv.TensorProduct.map_tmul {R A B C D : Type*} [RCLike R]
  [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  [StarAddMonoid A] [StarAddMonoid B] [StarAddMonoid C] [StarAddMonoid D]
  [StarModule R A] [StarModule R B] [StarModule R C] [StarModule R D]
  (f : A ≃⋆ₐ[R] B) (g : C ≃⋆ₐ[R] D) (x : A) (y : C) :
  (StarAlgEquiv.TensorProduct.map f g) (x ⊗ₜ[R] y) = f x ⊗ₜ g y :=
rfl
theorem StarAlgEquiv.TensorProduct.map_symm_tmul {R A B C D : Type*} [RCLike R]
  [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  [StarAddMonoid A] [StarAddMonoid B] [StarAddMonoid C] [StarAddMonoid D]
  [StarModule R A] [StarModule R B] [StarModule R C] [StarModule R D]
  (f : A ≃⋆ₐ[R] B) (g : C ≃⋆ₐ[R] D) (x : B) (y : D) :
  (StarAlgEquiv.TensorProduct.map f g).symm (x ⊗ₜ[R] y) = f.symm x ⊗ₜ g.symm y :=
rfl


/-- Tensor a star algebra equivalence on the left by a fixed algebra. -/
noncomputable def StarAlgEquiv.lTensor {R A B : Type*} (C : Type*) [RCLike R]
  [Ring A]
  [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
  [StarAddMonoid A] [StarAddMonoid B] [StarAddMonoid C]
  [StarModule R A] [StarModule R B] [StarModule R C]
  (f : A ≃⋆ₐ[R] B) :
  (C ⊗[R] A) ≃⋆ₐ[R] (C ⊗[R] B) :=
StarAlgEquiv.ofAlgEquiv
  (AlgEquiv.lTensor C f.toAlgEquiv)
  (fun x => x.induction_on
    (by simp only [star_zero, map_zero])
    (fun _ _ => by
      simp only [AlgEquiv.lTensor_tmul, TensorProduct.star_tmul, coe_toAlgEquiv, map_star])
    (fun _ _ h1 h2 => by simp only [star_add, map_add, h1, h2]))

lemma StarAlgEquiv.lTensor_tmul {R A B C : Type*}
  [RCLike R]
  [Ring A]
  [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
  [StarAddMonoid A] [StarAddMonoid B] [StarAddMonoid C]
  [StarModule R A] [StarModule R B] [StarModule R C]
  (f : A ≃⋆ₐ[R] B) (x : C) (y : A) :
  (StarAlgEquiv.lTensor C f) (x ⊗ₜ[R] y) = x ⊗ₜ f (y) :=
by
  simpa [StarAlgEquiv.lTensor] using AlgEquiv.lTensor_tmul (C := C) f.toAlgEquiv x y
lemma StarAlgEquiv.lTensor_symm_tmul {R A B C : Type*} [RCLike R]
  [Ring A]
  [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
  [StarAddMonoid A] [StarAddMonoid B] [StarAddMonoid C]
  [StarModule R A] [StarModule R B] [StarModule R C]
  (f : A ≃⋆ₐ[R] B) (x : C) (y : B) :
  (StarAlgEquiv.lTensor C f).symm (x ⊗ₜ[R] y) = x ⊗ₜ f.symm (y) :=
by
  simpa [StarAlgEquiv.lTensor, StarAlgEquiv.toAlgEquiv_symm] using
    AlgEquiv.lTensor_symm_tmul (C := C) f.toAlgEquiv x y
