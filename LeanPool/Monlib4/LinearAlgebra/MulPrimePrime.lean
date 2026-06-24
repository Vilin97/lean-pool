/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Algebra.Bilinear
import LeanPool.Monlib4.LinearAlgebra.KroneckerToTensor
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.BasicLemmas
import LeanPool.Monlib4.LinearAlgebra.Nacgor
import LeanPool.Monlib4.LinearAlgebra.Ips.TensorHilbert

/-!

# linear_map.mul''

this defines the multiplication map $M_{n\times n} \to M_n$

-/


open Matrix

open scoped Matrix Kronecker BigOperators

section

variable {R A B : Type _} [CommSemiring R]

theorem commutes_with_unit_iff [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (f : A →ₗ[R] B) :
    f ∘ₗ Algebra.linearMap R A = Algebra.linearMap R B ↔ f 1 = 1 := by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, _root_.map_smul]
  refine ⟨fun h => ?_, fun h x => by rw [h]⟩
  simpa using h 1

theorem commutes_with_mul'_iff [NonUnitalNonAssocSemiring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A]
    [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
    (f : A →ₗ[R] B) :
    LinearMap.mul' R B ∘ₗ TensorProduct.map f f = f ∘ₗ LinearMap.mul' R A ↔
      ∀ x y : A, f (x * y) = f x * f y := by
  simp_rw [TensorProduct.ext_iff', LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.mul'_apply, eq_comm]

end

theorem LinearMap.adjoint_commutes_with_mul_adjoint_iff {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroupOfRing X] [NormedAddCommGroupOfRing Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y] [SMulCommClass 𝕜 X X]
    [SMulCommClass 𝕜 Y Y] [IsScalarTower 𝕜 X X] [IsScalarTower 𝕜 Y Y]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y] (f : X →ₗ[𝕜] Y) :
    (TensorProduct.map (LinearMap.adjoint f) (LinearMap.adjoint f)) ∘ₗ
        (LinearMap.adjoint (LinearMap.mul' 𝕜 Y))
      = (LinearMap.adjoint (LinearMap.mul' 𝕜 X)) ∘ₗ LinearMap.adjoint f
    ↔
      ∀ x y : X, f (x * y) = f x * f y := by
  simp_rw [← TensorProduct.map_adjoint, ← LinearMap.adjoint_comp, ← commutes_with_mul'_iff]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  apply_fun LinearMap.adjoint at h
  simpa only [LinearMap.adjoint_adjoint] using h

lemma LinearMap.commutes_with_mul_adjoint_iff {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroupOfRing X] [NormedAddCommGroupOfRing Y] [InnerProductSpace 𝕜 X]
    [InnerProductSpace 𝕜 Y] [SMulCommClass 𝕜 X X] [SMulCommClass 𝕜 Y Y]
    [IsScalarTower 𝕜 X X] [IsScalarTower 𝕜 Y Y] [FiniteDimensional 𝕜 X]
    [FiniteDimensional 𝕜 Y] (f : X →ₗ[𝕜] Y) :
    (TensorProduct.map f f) ∘ₗ (LinearMap.adjoint (LinearMap.mul' 𝕜 X))
      = (LinearMap.adjoint (LinearMap.mul' 𝕜 Y)) ∘ₗ f
    ↔
      ∀ x y : Y, (adjoint f) (x * y) = (adjoint f) x * (adjoint f) y := by
  simp_rw [← commutes_with_mul'_iff]
  constructor <;>
  · intro h
    apply_fun LinearMap.adjoint at h
    simpa only [adjoint_comp, TensorProduct.map_adjoint, adjoint_adjoint] using h

lemma LinearIsometryEquiv.commutes_with_mul_adjoint_iff_of_surjective_isometry
    {𝕜 X Y : Type*} [RCLike 𝕜] [NormedAddCommGroupOfRing X]
    [NormedAddCommGroupOfRing Y] [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y]
    [SMulCommClass 𝕜 X X] [SMulCommClass 𝕜 Y Y] [IsScalarTower 𝕜 X X]
    [IsScalarTower 𝕜 Y Y] [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (f : X ≃ₗᵢ[𝕜] Y) :
    (TensorProduct.map (f.toLinearMap : X →ₗ[𝕜] Y) (f.toLinearMap : X →ₗ[𝕜] Y)) ∘ₗ
        (LinearMap.adjoint (LinearMap.mul' 𝕜 X))
      = (LinearMap.adjoint (LinearMap.mul' 𝕜 Y)) ∘ₗ f.toLinearMap
    ↔
      ∀ x y : X, f (x * y) = f x * f y := by
  simp_rw [LinearMap.commutes_with_mul_adjoint_iff]
  haveI : CompleteSpace X := FiniteDimensional.complete 𝕜 _
  haveI : CompleteSpace Y := FiniteDimensional.complete 𝕜 _
  have : LinearMap.adjoint f.toLinearMap = f.symm.toLinearMap := by
    calc
      LinearMap.adjoint f.toLinearMap =
          ContinuousLinearMap.adjoint
            (LinearIsometry.toContinuousLinearMap f.toLinearIsometry) := rfl
      _ = LinearIsometry.toContinuousLinearMap f.symm.toLinearIsometry := by
        simp only [ContinuousLinearMap.coe_inj]
        exact adjoint_eq_symm _
      _ = f.symm.toLinearMap := rfl
  rw [this]
  constructor
  · intro h x y
    specialize h (f x) (f y)
    simp only [LinearEquiv.coe_coe, coe_toLinearEquiv, symm_apply_apply] at h
    rw [← h, apply_symm_apply]
  · intro h x y
    specialize h (f.symm x) (f.symm y)
    simp only [LinearEquiv.coe_coe, coe_toLinearEquiv, apply_symm_apply] at h ⊢
    rw [← h, symm_apply_apply]

-- MOVE:
theorem Matrix.KroneckerProduct.ext_iff {R P n₁ n₂ : Type _} [Finite n₁] [Finite n₂]
    [CommSemiring R] [AddCommMonoid P] [Module R P]
    {g h : Matrix (n₁ × n₂) (n₁ × n₂) R →ₗ[R] P} :
    g = h ↔ ∀ (x : Matrix n₁ n₁ R) (y : Matrix n₂ n₂ R), g (x ⊗ₖ y) = h (x ⊗ₖ y) := by
  classical
  letI := Fintype.ofFinite n₁
  letI := Fintype.ofFinite n₂
  refine ⟨fun h x y => by rw [h], fun h => ?_⟩
  rw [LinearMap.ext_iff]
  intro x
  rw [Matrix.kmul_representation x]
  simp_rw [map_sum, _root_.map_smul, h _ _]

private def mul_map_aux (𝕜 X : Type _) [RCLike 𝕜] [NormedAddCommGroupOfRing X] [NormedSpace 𝕜 X]
    [SMulCommClass 𝕜 X X] [IsScalarTower 𝕜 X X] [FiniteDimensional 𝕜 X] : X →ₗ[𝕜] X →L[𝕜] X
    where
  toFun x :=
    { toFun := LinearMap.mul 𝕜 X x
      map_add' := map_add _
      map_smul' := map_smul _ }
  map_add' x y := by
    ext
    simp_rw [map_add, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.add_apply, _root_.add_apply]
    rfl
  map_smul' r x := by
    ext
    simp_rw [_root_.map_smul, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, _root_.smul_apply]
    rfl

namespace LinearMap

/-- Multiplication as a continuous bilinear map, curried as a continuous linear map. -/
def mulToClm (𝕜 X : Type _) [RCLike 𝕜] [NormedAddCommGroupOfRing X] [NormedSpace 𝕜 X]
    [SMulCommClass 𝕜 X X] [IsScalarTower 𝕜 X X] [FiniteDimensional 𝕜 X] : X →L[𝕜] X →L[𝕜] X
    where
  toFun := mul_map_aux 𝕜 X
  map_add' := map_add _
  map_smul' := _root_.map_smul _
  cont := map_continuous _

theorem mulToClm_apply {𝕜 X : Type _} [RCLike 𝕜] [NormedAddCommGroupOfRing X]
    [NormedSpace 𝕜 X] [SMulCommClass 𝕜 X X] [IsScalarTower 𝕜 X X] [FiniteDimensional 𝕜 X]
    (x y : X) : mulToClm 𝕜 X x y = x * y :=
  rfl

end LinearMap
