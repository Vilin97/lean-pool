/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Order.Filter.Germ.Basic

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Linear maps on filter germs

A linear map acts pointwise on germs of functions at a filter. Pointwise pure tensors also
induce a canonical linear map from a tensor product with a germ space to a germ space with
tensor-product values. Over a field that canonical map is injective: a kernel element expanded
along a basis of the second factor has germ coordinates that are killed by the dual coordinate
functionals, applied pointwise.
-/

open Filter
open scoped TensorProduct

universe u v w

namespace Filter.Germ

public section

variable {R : Type u} {M : Type v} {N : Type w}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]
variable {α : Type*} {l : Filter α}

instance instIsScalarTower {S : Type*} [SMul S R] [SMul S M] [IsScalarTower S R M] :
    IsScalarTower S R (Germ l M) where
  smul_assoc s r x := by
    induction x using inductionOn with
    | _ x =>
        rw [← coe_smul, ← coe_smul, ← coe_smul]
        exact EventuallyEq.germ_eq <| Eventually.of_forall fun a ↦ smul_assoc s r (x a)

instance instSMulCommClass {S : Type*} [SMul S M] [SMulCommClass S R M] :
    SMulCommClass S R (Germ l M) where
  smul_comm s r x := by
    induction x using inductionOn with
    | _ x =>
        rw [← coe_smul, ← coe_smul, ← coe_smul, ← coe_smul]
        exact EventuallyEq.germ_eq <| Eventually.of_forall fun a ↦ smul_comm s r (x a)

/-- The pointwise action of a linear map on germs at a filter. -/
def mapLinear (f : M →ₗ[R] N) : Germ l M →ₗ[R] Germ l N where
  toFun := map f
  map_add' x y := by
    induction x using inductionOn with
    | _ x =>
        induction y using inductionOn with
        | _ y =>
            rw [← coe_add, map_coe, map_coe, map_coe]
            exact EventuallyEq.germ_eq <| Eventually.of_forall fun a ↦ f.map_add (x a) (y a)
  map_smul' c x := by
    induction x using inductionOn with
    | _ x =>
        rw [← coe_smul, map_coe, map_coe]
        exact EventuallyEq.germ_eq <| Eventually.of_forall fun a ↦ f.map_smul c (x a)

/-- Pointwise evaluation of `mapLinear` on a representative. -/
@[simp]
theorem mapLinear_coe (f : M →ₗ[R] N) (g : α → M) :
    mapLinear f (g : Germ l M) = (f ∘ g : α → N) :=
  (rfl)

/-- `mapLinear` is functorial. -/
theorem mapLinear_comp {P : Type*} [AddCommMonoid P] [Module R P] (f : M →ₗ[R] N)
    (g : N →ₗ[R] P) (x : Germ l M) :
    mapLinear g (mapLinear f x) = mapLinear (g.comp f) x := by
  induction x using inductionOn with
  | _ x => rfl

/-- The zero map acts as zero on germs. -/
theorem mapLinear_zero_apply (x : Germ l M) : mapLinear (0 : M →ₗ[R] N) x = 0 := by
  induction x using inductionOn with
  | _ x =>
      rw [mapLinear_coe]
      exact EventuallyEq.germ_eq <| Eventually.of_forall fun a ↦ rfl

/-- An injective linear map acts injectively on germs. -/
theorem mapLinear_injective (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (mapLinear (l := l) f) := by
  intro x y hxy
  induction x using inductionOn with
  | _ x =>
      induction y using inductionOn with
      | _ y =>
          rw [mapLinear_coe, mapLinear_coe, coe_eq] at hxy
          rw [coe_eq]
          exact hxy.mono fun _ hx ↦ hf hx

section TensorProduct

variable {K : Type u} {V : Type v} {E : Type w}
variable [CommSemiring K] [AddCommMonoid V] [AddCommMonoid E]
variable [Module K V] [Module K E]

/-- The bilinear pointwise pure-tensor map on germs. -/
def tensorBilinear :
    Germ l V →ₗ[K] E →ₗ[K] Germ l (V ⊗[K] E) :=
  LinearMap.mk₂ K
    (fun g e ↦ mapLinear ((TensorProduct.mk K V E).flip e) g)
    (fun g₁ g₂ e ↦ (mapLinear ((TensorProduct.mk K V E).flip e)).map_add g₁ g₂)
    (fun c g e ↦ (mapLinear ((TensorProduct.mk K V E).flip e)).map_smul c g)
    (by
      intro g e₁ e₂
      induction g using inductionOn with
      | _ g =>
          rw [mapLinear_coe, mapLinear_coe, mapLinear_coe, ← coe_add, coe_eq]
          exact Eventually.of_forall fun x ↦ by simp)
    (by
      intro c g e
      induction g using inductionOn with
      | _ g =>
          rw [mapLinear_coe, mapLinear_coe, ← coe_smul, coe_eq]
          exact Eventually.of_forall fun x ↦ by simp)

/-- Pointwise tensoring of a germ with a fixed vector, extended linearly over a tensor product. -/
def tensorProduct :
    Germ l V ⊗[K] E →ₗ[K] Germ l (V ⊗[K] E) :=
  TensorProduct.lift tensorBilinear

/-- On a pure tensor, `tensorProduct` is represented by pointwise pure tensors. -/
@[simp]
theorem tensorProduct_tmul (g : Germ l V) (e : E) :
    tensorProduct (l := l) (g ⊗ₜ[K] e) =
      mapLinear ((TensorProduct.mk K V E).flip e) g := by
  rw [tensorProduct, TensorProduct.lift.tmul]
  rfl

/-- Contraction of the right tensor factor against a functional. -/
private def tensorRightContraction (lambda : E →ₗ[K] K) : V ⊗[K] E →ₗ[K] V :=
  (TensorProduct.rid K V).toLinearMap.comp (lambda.lTensor V)

@[simp]
private theorem tensorRightContraction_tmul (lambda : E →ₗ[K] K) (v : V) (e : E) :
    tensorRightContraction lambda (v ⊗ₜ[K] e) = lambda e • v := by
  simp [tensorRightContraction]

private theorem mapLinear_tensorRightContraction_tensorProduct (lambda : E →ₗ[K] K)
    (T : Germ l V ⊗[K] E) :
    mapLinear (tensorRightContraction lambda) (tensorProduct (l := l) T) =
      tensorRightContraction lambda T := by
  induction T with
  | zero => simp
  | tmul g e =>
      rw [tensorProduct_tmul, tensorRightContraction_tmul]
      induction g using inductionOn with
      | _ f =>
          rw [mapLinear_coe, mapLinear_coe]
          rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end TensorProduct

section Injective

variable {K : Type u} {V : Type v} {E : Type w}
variable [Field K] [AddCommGroup V] [AddCommGroup E]
variable [Module K V] [Module K E]

/-- Over a field, the canonical map `Germ(V) ⊗[K] E → Germ(V ⊗[K] E)` is injective. -/
theorem tensorProduct_injective :
    Function.Injective (tensorProduct (l := l) (K := K) (V := V) (E := E)) := by
  let C := Module.Free.chooseBasis K E
  rw [← LinearMap.ker_eq_bot]
  refine eq_bot_iff.mpr fun T hT ↦ ?_
  change T = 0
  change tensorProduct (l := l) T = 0 at hT
  let c := TensorProduct.equivFinsuppOfBasisRight C T
  have hc : c = 0 := by
    apply Finsupp.ext
    intro i
    have hcontract := congrArg (mapLinear (tensorRightContraction (C.coord i))) hT
    rw [mapLinear_tensorRightContraction_tensorProduct, map_zero] at hcontract
    simpa [c, tensorRightContraction, TensorProduct.equivFinsuppOfBasisRight_apply] using hcontract
  apply (TensorProduct.equivFinsuppOfBasisRight C).injective
  simp [c, hc]

end Injective

end

end Filter.Germ
