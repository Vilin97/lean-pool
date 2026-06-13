/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Basic
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Schur Product Operator

This file ports the definition of the upstream `Monlib.LinearAlgebra.QuantumSet.SchurMul`
operator.  The deeper upstream Schur-product theorem stack depends on the finite-dimensional
Hilbert-algebra coalgebra instance and tensor-product infrastructure that are not yet recovered
in the current monlib4 slice.
-/

open scoped TensorProduct BigOperators

local notation "m" x => LinearMap.mul' ℂ x
local notation x " ⊗ₘ " y => TensorProduct.map x y

open Coalgebra

/-- Schur product `x •ₛ y := m ∘ (x ⊗ y) ∘ comul`. -/
@[simps]
noncomputable def schurMul {B C : Type*}
    [AddCommMonoid B] [NonUnitalNonAssocSemiring C]
    [Module ℂ B] [Module ℂ C] [CoalgebraStruct ℂ B]
    [SMulCommClass ℂ C C] [IsScalarTower ℂ C C] :
    (B →ₗ[ℂ] C) →ₗ[ℂ] (B →ₗ[ℂ] C) →ₗ[ℂ] (B →ₗ[ℂ] C) where
  toFun x :=
    { toFun := fun y => (m C) ∘ₗ (x ⊗ₘ y) ∘ₗ comul
      map_add' := fun _ _ => by
        simp only [TensorProduct.map_add_right, LinearMap.add_comp, LinearMap.comp_add]
      map_smul' := fun _ _ => by
        simp only [TensorProduct.map_smul_right, LinearMap.smul_comp, LinearMap.comp_smul,
          RingHom.id_apply] }
  map_add' x y := by
    simp only [TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add,
      LinearMap.ext_iff, LinearMap.add_apply, LinearMap.coe_mk]
    intro _ _
    rfl
  map_smul' r x := by
    simp only [TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul,
      LinearMap.ext_iff, LinearMap.smul_apply, LinearMap.coe_mk, RingHom.id_apply]
    intro _ _
    rfl

@[inherit_doc schurMul]
notation3:80 (name := schurMulNotation) x:81 " •ₛ " y:80 => schurMul x y

theorem nonUnitalAlgHom_comp_mul {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (f : A →ₙₐ[R] B) :
    (LinearMapClass.linearMap f) ∘ₗ LinearMap.mul' R A =
      (LinearMap.mul' R B) ∘ₗ
        ((LinearMapClass.linearMap f) ⊗ₘ (LinearMapClass.linearMap f)) := by
  rw [TensorProduct.ext_iff']
  intro a b
  simp only [LinearMap.comp_apply, LinearMap.mul'_apply, TensorProduct.map_tmul]
  exact NonUnitalAlgHom.map_mul f a b

theorem algHom_comp_mul {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    f.toLinearMap ∘ₗ LinearMap.mul' R A =
      (LinearMap.mul' R B) ∘ₗ (f.toLinearMap ⊗ₘ f.toLinearMap) := by
  change (LinearMapClass.linearMap f.toNonUnitalAlgHom) ∘ₗ LinearMap.mul' R A =
    (LinearMap.mul' R B) ∘ₗ
      ((LinearMapClass.linearMap f.toNonUnitalAlgHom) ⊗ₘ
        (LinearMapClass.linearMap f.toNonUnitalAlgHom))
  exact nonUnitalAlgHom_comp_mul f.toNonUnitalAlgHom

attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass

variable {A B : Type*}
  [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
  [InnerProductSpace ℂ A] [InnerProductSpace ℂ B]
  [SMulCommClass ℂ A A] [SMulCommClass ℂ B B]
  [IsScalarTower ℂ A A] [IsScalarTower ℂ B B]
  [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]

omit [FiniteDimensional ℂ B] in
theorem schurMul.apply_rankOne (a c : B) (b d : A) :
    (rankOne ℂ a b).toLinearMap •ₛ (rankOne ℂ c d).toLinearMap =
      (rankOne ℂ (a * c) (b * d) : A →L[ℂ] B).toLinearMap := by
  rw [schurMul, LinearMap.ext_iff]
  intro x
  apply ext_inner_right ℂ
  intro u
  simp only [ContinuousLinearMap.coe_coe, LinearMap.coe_mk, AddHom.coe_mk,
    rankOne_apply, LinearMap.comp_apply]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (Coalgebra.comul x : A ⊗[ℂ] A)
  rw [← h]
  simp_rw [map_sum, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    rankOne_apply, LinearMap.mul'_apply, smul_mul_smul_comm,
    ← TensorProduct.inner_tmul, ← Finset.sum_smul, ← inner_sum, h,
    Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_inner_right,
    LinearMap.mul'_apply]

omit [FiniteDimensional ℂ B] in
theorem schurMul.apply_ket (a b : B) :
    (ket ℂ a) •ₛ (ket ℂ b) = (ket ℂ (a * b)).toLinearMap := by
  simp only [schurMul_apply_apply, QuantumSet.complex_comul]
  ext
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    TensorProduct.lid_symm_apply, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    ket_apply_apply, one_smul, LinearMap.mul'_apply]

section TensorRankOne

variable {𝕜 B C : Type*} [RCLike 𝕜] [NormedAddCommGroup B] [NormedAddCommGroup C]
  [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C]
  [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C]

omit [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] in
theorem bra_tmul (a : B) (b : C) :
    (bra 𝕜 (a ⊗ₜ[𝕜] b)).toLinearMap =
      (TensorProduct.lid 𝕜 _).toLinearMap ∘ₗ
        TensorProduct.map (bra 𝕜 a).toLinearMap (bra 𝕜 b).toLinearMap := by
  ext
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    innerSL_apply_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    TensorProduct.inner_tmul, TensorProduct.lid_tmul]
  rfl

omit [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] in
theorem bra_map_bra (a : B) (b : C) :
    TensorProduct.map (bra 𝕜 a).toLinearMap (bra 𝕜 b).toLinearMap =
      (TensorProduct.lid 𝕜 _).symm.toLinearMap ∘ₗ
        (bra 𝕜 (a ⊗ₜ[𝕜] b)).toLinearMap := by
  rw [bra_tmul, ← LinearMap.comp_assoc]
  simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.id_comp]

omit [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] in
theorem ket_tmul (a : B) (b : C) :
    (ket 𝕜 (a ⊗ₜ[𝕜] b)).toLinearMap =
      TensorProduct.map (ket 𝕜 a).toLinearMap (ket 𝕜 b).toLinearMap ∘ₗ
        (TensorProduct.lid 𝕜 _).symm.toLinearMap := by
  ext
  simp only [ContinuousLinearMap.coe_coe, ket_one_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.lid_symm_apply,
    TensorProduct.map_tmul]

omit [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] in
theorem ket_map_ket (a : B) (b : C) :
    TensorProduct.map (ket 𝕜 a).toLinearMap (ket 𝕜 b).toLinearMap =
      (ket 𝕜 (a ⊗ₜ[𝕜] b)).toLinearMap ∘ₗ (TensorProduct.lid 𝕜 _).toLinearMap := by
  rw [ket_tmul, LinearMap.comp_assoc]
  simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.comp_id]

end TensorRankOne

theorem bra_comp_linearMap {𝕜 E₁ E₂ : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂]
    [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂]
    (x : E₂) (f : E₁ →ₗ[𝕜] E₂) :
    (bra 𝕜 x).toLinearMap.comp f = (bra 𝕜 (LinearMap.adjoint f x)).toLinearMap :=
  letI := FiniteDimensional.complete 𝕜 E₁
  letI := FiniteDimensional.complete 𝕜 E₂
  calc
    (bra 𝕜 x).toLinearMap ∘ₗ f =
        ((bra 𝕜 x) ∘L LinearMap.toContinuousLinearMap f).toLinearMap := rfl
    _ =
        (bra 𝕜
          (ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap f) x)).toLinearMap := by
          rw [bra_comp_continuousLinearMap]
    _ = (bra 𝕜 (LinearMap.adjoint f x)).toLinearMap := rfl

theorem linearMap_comp_ket {𝕜 E₁ E₂ : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂]
    [InnerProductSpace 𝕜 E₂] (x : E₁) (f : E₁ →ₗ[𝕜] E₂) :
    f ∘ₗ (ket 𝕜 x).toLinearMap = (ket 𝕜 (f x)).toLinearMap := by
  ext
  simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
    ket_apply_apply, one_smul]

theorem mul_comp_lid_symm {R : Type*} [CommSemiring R] :
    LinearMap.mul' R R ∘ₗ (TensorProduct.lid R R).symm.toLinearMap = LinearMap.id := by
  aesop

theorem schurMul.apply_bra (a b : B) :
    (bra ℂ a) •ₛ (bra ℂ b) = (bra ℂ (a * b)).toLinearMap := by
  rw [schurMul_apply_apply, bra_map_bra, LinearMap.comp_assoc, bra_comp_linearMap,
    Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_adjoint, LinearMap.mul'_apply,
    ← LinearMap.comp_assoc, mul_comp_lid_symm]
  rfl

omit [FiniteDimensional ℂ B] in
theorem schurMul.comp_apply_of {C : Type*}
    [NormedAddCommGroupOfRing C] [InnerProductSpace ℂ C] [SMulCommClass ℂ C C]
    [IsScalarTower ℂ C C] [FiniteDimensional ℂ C] (δ : ℂ)
    (hAδ : Coalgebra.comul ∘ₗ LinearMap.mul' ℂ A = δ • LinearMap.id)
    (a b : A →ₗ[ℂ] B) (c d : C →ₗ[ℂ] A) :
    (a •ₛ b) ∘ₗ (c •ₛ d) = δ • ((a ∘ₗ c) •ₛ (b ∘ₗ d)) := by
  calc
    (a •ₛ b) ∘ₗ (c •ₛ d) =
        (m _) ∘ₗ (a ⊗ₘ b) ∘ₗ (Coalgebra.comul ∘ₗ (m A)) ∘ₗ (c ⊗ₘ d) ∘ₗ
          Coalgebra.comul := by
          simp_rw [schurMul_apply_apply, LinearMap.comp_assoc]
    _ = δ • (m _) ∘ₗ ((a ⊗ₘ b) ∘ₗ (c ⊗ₘ d)) ∘ₗ Coalgebra.comul := by
          simp_rw [hAδ, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp,
            LinearMap.comp_assoc]
    _ = δ • (a ∘ₗ c) •ₛ (b ∘ₗ d) := by
          rw [← TensorProduct.map_comp]
          rfl

theorem schurMul_one_one_right (x : A →ₗ[ℂ] B) :
    x •ₛ (rankOne ℂ (1 : B) (1 : A)).toLinearMap = x := by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
  simp_rw [map_sum, LinearMap.sum_apply, schurMul.apply_rankOne, mul_one]

theorem schurMul_one_one_left (x : A →ₗ[ℂ] B) :
    (rankOne ℂ (1 : B) (1 : A)).toLinearMap •ₛ x = x := by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
  simp_rw [map_sum, schurMul.apply_rankOne, one_mul]

theorem schurMul_one_right_rankOne (a b : A) :
    (rankOne ℂ a b).toLinearMap •ₛ (1 : A →ₗ[ℂ] A) =
      lmul a ∘ₗ LinearMap.adjoint (lmul b) := by
  let e := stdOrthonormalBasis ℂ A
  calc
    (rankOne ℂ a b).toLinearMap •ₛ (1 : A →ₗ[ℂ] A)
        = (rankOne ℂ a b).toLinearMap •ₛ
            (∑ i, (rankOne ℂ (e i) (e i)).toLinearMap) := by
          rw [rankOne.sum_orthonormalBasis_eq_id_lm e]
    _ = ∑ i, (rankOne ℂ (a * e i) (b * e i)).toLinearMap := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [schurMul.apply_rankOne]
    _ = ∑ i, lmul a ∘ₗ
          ((rankOne ℂ (e i) (e i)).toLinearMap ∘ₗ LinearMap.adjoint (lmul b)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [LinearMap.rankOne_comp', LinearMap.comp_rankOne]
          rfl
    _ = lmul a ∘ₗ
          ((∑ i, (rankOne ℂ (e i) (e i)).toLinearMap) ∘ₗ
            LinearMap.adjoint (lmul b)) := by
          rw [← LinearMap.comp_sum, ← LinearMap.sum_comp]
    _ = lmul a ∘ₗ LinearMap.adjoint (lmul b) := by
          rw [rankOne.sum_orthonormalBasis_eq_id_lm e]
          ext x
          rfl

theorem schurMul_one_left_rankOne (a b : A) :
    (1 : A →ₗ[ℂ] A) •ₛ (rankOne ℂ a b).toLinearMap =
      rmul a ∘ₗ LinearMap.adjoint (rmul b) := by
  let e := stdOrthonormalBasis ℂ A
  calc
    (1 : A →ₗ[ℂ] A) •ₛ (rankOne ℂ a b).toLinearMap
        = (∑ i, (rankOne ℂ (e i) (e i)).toLinearMap) •ₛ
            (rankOne ℂ a b).toLinearMap := by
          rw [rankOne.sum_orthonormalBasis_eq_id_lm e]
    _ = ∑ i, (rankOne ℂ (e i * a) (e i * b)).toLinearMap := by
          rw [map_sum, LinearMap.sum_apply]
          apply Finset.sum_congr rfl
          intro i _
          rw [schurMul.apply_rankOne]
    _ = ∑ i, rmul a ∘ₗ
          ((rankOne ℂ (e i) (e i)).toLinearMap ∘ₗ LinearMap.adjoint (rmul b)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [LinearMap.rankOne_comp', LinearMap.comp_rankOne]
          rfl
    _ = rmul a ∘ₗ
          ((∑ i, (rankOne ℂ (e i) (e i)).toLinearMap) ∘ₗ
            LinearMap.adjoint (rmul b)) := by
          rw [← LinearMap.comp_sum, ← LinearMap.sum_comp]
    _ = rmul a ∘ₗ LinearMap.adjoint (rmul b) := by
          rw [rankOne.sum_orthonormalBasis_eq_id_lm e]
          ext x
          rfl

theorem schurMul_adjoint (x y : A →ₗ[ℂ] B) :
    LinearMap.adjoint (x •ₛ y) = LinearMap.adjoint x •ₛ LinearMap.adjoint y := by
  simp_rw [schurMul, Coalgebra.comul_eq_mul_adjoint]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint, TensorProduct.map_adjoint, LinearMap.comp_assoc]

theorem schurMul_real {A B : Type*} [starAlgebra A] [starAlgebra B]
    [QuantumSet A] [QuantumSet B] (x y : A →ₗ[ℂ] B) :
    LinearMap.real (x •ₛ y : A →ₗ[ℂ] B) =
      LinearMap.real y •ₛ LinearMap.real x := by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
  obtain ⟨γ, ζ, rfl⟩ := LinearMap.exists_sum_rankOne y
  simp only [map_sum, LinearMap.real_sum, LinearMap.sum_apply, schurMul.apply_rankOne]
  simp_rw [rankOne_real, schurMul.apply_rankOne, ← map_mul, ← StarMul.star_mul]
  rw [Finset.sum_comm]

theorem Psi.schurMul {A B : Type*} [starAlgebra A] [starAlgebra B]
    [hA : QuantumSet A] [QuantumSet B] (r₁ r₂ : ℝ) (f g : A →ₗ[ℂ] B) :
    hA.Psi r₁ r₂ (f •ₛ g) = hA.Psi r₁ r₂ f * hA.Psi r₁ r₂ g := by
  suffices ∀ (a c : B) (b d : A),
      hA.Psi r₁ r₂ ((rankOne ℂ a b).toLinearMap •ₛ (rankOne ℂ c d).toLinearMap) =
        hA.Psi r₁ r₂ (rankOne ℂ a b).toLinearMap *
          hA.Psi r₁ r₂ (rankOne ℂ c d).toLinearMap by
    obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne f
    obtain ⟨γ, δ, rfl⟩ := LinearMap.exists_sum_rankOne g
    simp only [map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact this (α j) (γ i) (β j) (δ i)
  intro a c b d
  rw [schurMul.apply_rankOne]
  repeat rw [QuantumSet.Psi_apply]
  repeat rw [QuantumSet.PsiToFun_apply]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, map_mul, star_mul]
  rfl

theorem schurMul_assoc {A B : Type*} [starAlgebra A] [starAlgebra B]
    [hA : QuantumSet A] [QuantumSet B] (f g h : A →ₗ[ℂ] B) :
    (f •ₛ g) •ₛ h = f •ₛ (g •ₛ h) := by
  apply_fun hA.Psi 0 0 using LinearEquiv.injective _
  simp_rw [Psi.schurMul, mul_assoc]

theorem comul_comp_nonUnitalAlgHom_adjoint (f : A →ₙₐ[ℂ] B) :
    Coalgebra.comul ∘ₗ LinearMap.adjoint (LinearMapClass.linearMap f) =
      ((LinearMap.adjoint (LinearMapClass.linearMap f)) ⊗ₘ
        (LinearMap.adjoint (LinearMapClass.linearMap f))) ∘ₗ Coalgebra.comul := by
  simp_rw [Coalgebra.comul_eq_mul_adjoint, ← TensorProduct.map_adjoint,
    ← LinearMap.adjoint_comp, nonUnitalAlgHom_comp_mul f]

theorem comul_comp_algHom_adjoint (f : A →ₐ[ℂ] B) :
    Coalgebra.comul ∘ₗ LinearMap.adjoint f.toLinearMap =
      ((LinearMap.adjoint f.toLinearMap) ⊗ₘ (LinearMap.adjoint f.toLinearMap)) ∘ₗ
        Coalgebra.comul := by
  change Coalgebra.comul ∘ₗ
      LinearMap.adjoint (LinearMapClass.linearMap f.toNonUnitalAlgHom) =
    ((LinearMap.adjoint (LinearMapClass.linearMap f.toNonUnitalAlgHom)) ⊗ₘ
      (LinearMap.adjoint (LinearMapClass.linearMap f.toNonUnitalAlgHom))) ∘ₗ
        Coalgebra.comul
  exact comul_comp_nonUnitalAlgHom_adjoint f.toNonUnitalAlgHom

theorem schurMul_nonUnitalAlgHom_comp_coalgHom {C D : Type*}
    [Semiring C] [Semiring D]
    [Module ℂ C] [Module ℂ D]
    [SMulCommClass ℂ C C] [SMulCommClass ℂ D D]
    [IsScalarTower ℂ C C] [IsScalarTower ℂ D D]
    (g : C →ₙₐ[ℂ] D) (f : A →ₗc[ℂ] B) (x y : B →ₗ[ℂ] C) :
    ((LinearMapClass.linearMap g) ∘ₗ x ∘ₗ f.toLinearMap) •ₛ
        ((LinearMapClass.linearMap g) ∘ₗ y ∘ₗ f.toLinearMap) =
      (LinearMapClass.linearMap g) ∘ₗ (x •ₛ y) ∘ₗ f.toLinearMap := by
  simp_rw [schurMul_apply_apply, ← LinearMap.comp_assoc, nonUnitalAlgHom_comp_mul,
    LinearMap.comp_assoc, ← f.map_comp_comul]
  congr 1
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp_rw [TensorProduct.map_comp]

theorem schurMul_algHom_comp_coalgHom {C D : Type*}
    [Semiring C] [Semiring D]
    [Module ℂ C] [Module ℂ D]
    [SMulCommClass ℂ C C] [SMulCommClass ℂ D D]
    [IsScalarTower ℂ C C] [IsScalarTower ℂ D D]
    (g : C →ₐ[ℂ] D) (f : A →ₗc[ℂ] B) (x y : B →ₗ[ℂ] C) :
    (g.toLinearMap ∘ₗ x ∘ₗ f.toLinearMap) •ₛ (g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap) =
      g.toLinearMap ∘ₗ (x •ₛ y) ∘ₗ f.toLinearMap := by
  change ((LinearMapClass.linearMap g.toNonUnitalAlgHom) ∘ₗ x ∘ₗ f.toLinearMap) •ₛ
      ((LinearMapClass.linearMap g.toNonUnitalAlgHom) ∘ₗ y ∘ₗ f.toLinearMap) =
    (LinearMapClass.linearMap g.toNonUnitalAlgHom) ∘ₗ (x •ₛ y) ∘ₗ f.toLinearMap
  exact schurMul_nonUnitalAlgHom_comp_coalgHom g.toNonUnitalAlgHom f x y

theorem schurMul_nonUnitalAlgHom_comp_nonUnitalAlgHom_adjoint {C D : Type*}
    [Semiring C] [Semiring D]
    [Module ℂ C] [Module ℂ D]
    [SMulCommClass ℂ C C] [SMulCommClass ℂ D D]
    [IsScalarTower ℂ C C] [IsScalarTower ℂ D D]
    (g : C →ₙₐ[ℂ] D) (f : B →ₙₐ[ℂ] A) (x y : B →ₗ[ℂ] C) :
    ((LinearMapClass.linearMap g) ∘ₗ x ∘ₗ
        (LinearMap.adjoint (LinearMapClass.linearMap f))) •ₛ
      ((LinearMapClass.linearMap g) ∘ₗ y ∘ₗ
        (LinearMap.adjoint (LinearMapClass.linearMap f))) =
      (LinearMapClass.linearMap g) ∘ₗ (x •ₛ y) ∘ₗ
        LinearMap.adjoint (LinearMapClass.linearMap f) := by
  simp_rw [schurMul_apply_apply, ← LinearMap.comp_assoc, nonUnitalAlgHom_comp_mul,
    LinearMap.comp_assoc, comul_comp_nonUnitalAlgHom_adjoint]
  congr 1
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp_rw [TensorProduct.map_comp]

theorem schurMul_algHom_comp_algHom_adjoint {C D : Type*}
    [Semiring C] [Semiring D]
    [Module ℂ C] [Module ℂ D]
    [SMulCommClass ℂ C C] [SMulCommClass ℂ D D]
    [IsScalarTower ℂ C C] [IsScalarTower ℂ D D]
    (g : C →ₐ[ℂ] D) (f : B →ₐ[ℂ] A) (x y : B →ₗ[ℂ] C) :
    (g.toLinearMap ∘ₗ x ∘ₗ LinearMap.adjoint f.toLinearMap) •ₛ
    (g.toLinearMap ∘ₗ y ∘ₗ LinearMap.adjoint f.toLinearMap) =
      g.toLinearMap ∘ₗ (x •ₛ y) ∘ₗ LinearMap.adjoint f.toLinearMap := by
  change ((LinearMapClass.linearMap g.toNonUnitalAlgHom) ∘ₗ x ∘ₗ
        LinearMap.adjoint (LinearMapClass.linearMap f.toNonUnitalAlgHom)) •ₛ
      ((LinearMapClass.linearMap g.toNonUnitalAlgHom) ∘ₗ y ∘ₗ
        LinearMap.adjoint (LinearMapClass.linearMap f.toNonUnitalAlgHom)) =
    (LinearMapClass.linearMap g.toNonUnitalAlgHom) ∘ₗ (x •ₛ y) ∘ₗ
      LinearMap.adjoint (LinearMapClass.linearMap f.toNonUnitalAlgHom)
  exact schurMul_nonUnitalAlgHom_comp_nonUnitalAlgHom_adjoint
    g.toNonUnitalAlgHom f.toNonUnitalAlgHom x y

protected lemma QuantumSet.schurMul_algHom_comp_algHom_adjoint {A B C D : Type*}
    [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
    [starAlgebra C] [starAlgebra D] [QuantumSet C] [QuantumSet D]
    (g : C →ₐ[ℂ] D) (f : B →ₐ[ℂ] A) (x y : B →ₗ[ℂ] C) :
    (g.toLinearMap ∘ₗ x ∘ₗ LinearMap.adjoint f.toLinearMap) •ₛ
      (g.toLinearMap ∘ₗ y ∘ₗ LinearMap.adjoint f.toLinearMap) =
        g.toLinearMap ∘ₗ (x •ₛ y) ∘ₗ LinearMap.adjoint f.toLinearMap :=
  schurMul_nonUnitalAlgHom_comp_nonUnitalAlgHom_adjoint
    g.toNonUnitalAlgHom f.toNonUnitalAlgHom x y

theorem schurMul_one_iff_one_schurMul_of_isReal {A B : Type*}
    [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
    {x y z : A →ₗ[ℂ] B}
    (hx : LinearMap.IsReal x) (hy : LinearMap.IsReal y) (hz : LinearMap.IsReal z) :
    x •ₛ y = z ↔ y •ₛ x = z := by
  rw [LinearMap.real_inj_eq, schurMul_real, x.isReal_iff.mp hx, y.isReal_iff.mp hy,
    z.isReal_iff.mp hz]

theorem schurMul_reflexive_of_isReal {A : Type*} [starAlgebra A] [QuantumSet A]
    {x : A →ₗ[ℂ] A} (hx : LinearMap.IsReal x) :
    x •ₛ 1 = 1 ↔ 1 •ₛ x = 1 :=
  schurMul_one_iff_one_schurMul_of_isReal hx LinearMap.isRealOne LinearMap.isRealOne

theorem schurMul_irreflexive_of_isReal {A : Type*} [starAlgebra A] [QuantumSet A]
    {x : A →ₗ[ℂ] A} (hx : LinearMap.IsReal x) :
    x •ₛ 1 = 0 ↔ 1 •ₛ x = 0 :=
  schurMul_one_iff_one_schurMul_of_isReal hx LinearMap.isRealOne LinearMap.isRealZero

lemma schurIdempotent_iff_Psi_isIdempotentElem {A B : Type*}
    [starAlgebra A] [starAlgebra B] [hA : QuantumSet A] [QuantumSet B]
    (f : A →ₗ[ℂ] B) (t r : ℝ) :
    f •ₛ f = f ↔ IsIdempotentElem (hA.Psi t r f) := by
  simp_rw [IsIdempotentElem, ← Psi.schurMul,
    Function.Injective.eq_iff (LinearEquiv.injective _)]
