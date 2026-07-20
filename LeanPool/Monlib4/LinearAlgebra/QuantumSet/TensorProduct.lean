/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Basic
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.OrthonormalBasis

/-!
# Tensor Products of Quantum Sets

This file restores the upstream tensor-product quantum-set instance and the
fourfold tensor-shuffle lemmas used by later quantum-graph files.
-/

variable {A : Type*} [ha : starAlgebra A]
  {B : Type*} [hb : starAlgebra B]

open scoped TensorProduct

noncomputable instance tensorStarAlgebra
    :
    starAlgebra (A ⊗[ℂ] B) where
  star_mul x y := x.induction_on (by simp only [zero_mul, star_zero, mul_zero])
    (y.induction_on
      (by simp only [mul_zero, star_zero, TensorProduct.star_tmul, zero_mul,
        implies_true])
      (fun _ _ _ _ => by simp only [Algebra.TensorProduct.tmul_mul_tmul,
        TensorProduct.star_tmul, star_mul])
      (fun _ _ h1 h2 _ _ => by simp only [mul_add, star_add, h1, h2, add_mul]))
    (fun _ _ h1 h2 => by simp only [star_add, add_mul, mul_add, h1, h2])
  star_add := star_add
  modAut r := AlgEquiv.TensorProduct.map (ha.modAut r) (hb.modAut r)
  modAut_trans r s := by
    simp_rw [AlgEquiv.ext_iff, ← AlgEquiv.toLinearMap_apply, ← LinearMap.ext_iff]
    apply TensorProduct.ext'
    intro _ _
    simp only [AlgEquiv.trans_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.TensorProduct.map_tmul,
      QuantumSet.modAut_apply_modAut, add_comm]
  modAut_star _ x := x.induction_on (by simp only [map_zero, star_zero])
    (fun _ _ => by
      simp only [AlgEquiv.TensorProduct.map_tmul, TensorProduct.star_tmul,
        starAlgebra.modAut_star])
    (fun _ _ h1 h2 => by simp only [map_add, star_add, h1, h2])

lemma modAut_tensor (r : ℝ) :
    tensorStarAlgebra.modAut r = AlgEquiv.TensorProduct.map (ha.modAut r) (hb.modAut r) :=
  rfl

lemma modAut_tensor_tmul (r : ℝ) (x : A)
    (y : B) :
    tensorStarAlgebra.modAut r (x ⊗ₜ[ℂ] y) = (ha.modAut r x) ⊗ₜ[ℂ] (hb.modAut r y) :=
  rfl

noncomputable instance
    [InnerProductAlgebra A] [InnerProductAlgebra B]
    :
    InnerProductAlgebra (A ⊗[ℂ] B) where
  norm_smul_le := norm_smul_le
  norm_sq_eq_inner _ := norm_sq_eq_re_inner (𝕜 := ℂ) _
  conj_symm x y := inner_conj_symm (𝕜 := ℂ) x y
  add_left := inner_add_left
  smul_left r x y := inner_smul_left (𝕜 := ℂ) r x y

noncomputable instance QuantumSet.tensorProduct
    [hA : QuantumSet A] [hB : QuantumSet B] [h : Fact (hA.k = hB.k)] :
    QuantumSet (A ⊗[ℂ] B) where
  modAut_isSymmetric r _ _ := by
    simp_rw [← AlgEquiv.toLinearMap_apply, modAut_tensor, AlgEquiv.TensorProduct.map_toLinearMap]
    nth_rw 1 [← @modAut_isSelfAdjoint A]
    nth_rw 1 [← @modAut_isSelfAdjoint B]
    simp_rw [LinearMap.star_eq_adjoint, ← TensorProduct.map_adjoint]
    exact LinearMap.adjoint_inner_left _ _ _
  k := hA.k
  inner_star_left a b c := a.induction_on
    (by simp only [zero_mul, inner_zero_left, star_zero, map_zero, inner_zero_right])
    (b.induction_on
      (by simp only [mul_zero, inner_zero_left, TensorProduct.star_tmul, implies_true])
      (c.induction_on
        (by simp only [Algebra.TensorProduct.tmul_mul_tmul, inner_zero_right,
          TensorProduct.star_tmul, mul_zero, implies_true])
        (fun _ _ _ _ _ _ => by
          simp only [TensorProduct.star_tmul, modAut_tensor,
            Algebra.TensorProduct.tmul_mul_tmul, QuantumSet.inner_star_left,
            TensorProduct.inner_tmul, AlgEquiv.TensorProduct.map_tmul]
          rw [h.out])
        (fun _ _ h1 h2 _ _ _ _ => by
          simp only [inner_add_right, h1, h2, mul_add]))
      (fun _ _ h1 h2 _ _ => by
        simp only [mul_add, inner_add_left, h1, h2]))
    (fun _ _ h1 h2 => by
      simp only [add_mul, inner_add_left, inner_add_right, h1, h2, star_add,
        map_add])
  inner_conj_left a b c := a.induction_on
    (by simp only [zero_mul, inner_zero_left])
    (b.induction_on
      (by simp only [mul_zero, inner_zero_left, star_zero, map_zero, inner_zero_right,
        implies_true])
      (c.induction_on
        (by simp only [Algebra.TensorProduct.tmul_mul_tmul, inner_zero_right,
          TensorProduct.star_tmul, zero_mul, implies_true])
        (fun _ _ _ _ _ _ => by
          simp_rw [TensorProduct.star_tmul, modAut_tensor_tmul,
            Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.inner_tmul,
            QuantumSet.inner_conj_left]
          rw [h.out])
        (fun _ _ h1 h2 _ _ _ _ => by
          simp only [inner_add_right, add_mul, h1, h2]))
      (fun _ _ h1 h2 _ _ => by
        simp only [mul_add, inner_add_left, inner_add_right, star_add, map_add, h1, h2]))
    (fun _ _ h1 h2 => by
      simp only [add_mul, inner_add_left, h1, h2])
  n := _
  nIsFintype := _
  onb := hA.onb.tensorProduct hB.onb
  nIsDecidableEq := inferInstance

theorem QuantumSet.tensorProduct.k_eq₁ [hA : QuantumSet A] [hB : QuantumSet B]
    [Fact (hA.k = hB.k)] :
    (QuantumSet.tensorProduct : QuantumSet (A ⊗[ℂ] B)).k = hA.k :=
  rfl

theorem QuantumSet.tensorProduct.k_eq₂ [hA : QuantumSet A] [hB : QuantumSet B]
    [h : Fact (hA.k = hB.k)] :
    (QuantumSet.tensorProduct : QuantumSet (A ⊗[ℂ] B)).k = hB.k := by
  rw [← h.out]
  rfl

theorem comul_real [hA : QuantumSet A] :
    (Coalgebra.comul : A →ₗ[ℂ] A ⊗[ℂ] A).real =
      (TensorProduct.comm ℂ A A).toLinearMap ∘ₗ Coalgebra.comul := by
  letI := Fact.mk (rfl : hA.k = hA.k)
  letI : starAlgebra (A ⊗[ℂ] A) := by infer_instance
  letI : QuantumSet (A ⊗[ℂ] A) := QuantumSet.tensorProduct
  rw [Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_real_eq (f := LinearMap.mul' ℂ A),
    LinearMap.mul'_real, LinearMap.adjoint_comp, TensorProduct.comm_adjoint,
    LinearMap.comp_assoc, ← LinearMap.comp_assoc, modAut_tensor,
    AlgEquiv.TensorProduct.map_toLinearMap,
    ← TensorProduct.comm_symm_map, ← Coalgebra.comul_eq_mul_adjoint]
  simp_rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ (TensorProduct.map _ _),
    (QuantumSet.modAut_isCoalgHom _).2, LinearMap.comp_assoc, ← AlgEquiv.trans_toLinearMap,
    starAlgebra.modAut_trans, neg_sub_left, add_comm,
    QuantumSet.tensorProduct.k_eq₁, neg_add_cancel, starAlgebra.modAut_zero]
  rfl

/-- Swap the two middle factors in a fourfold tensor product. -/
noncomputable def swapMiddleTensor
    (R : Type*) [CommSemiring R] (A B C D : Type*)
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
    [Module R A] [Module R B] [Module R C] [Module R D] :
    (A ⊗[R] B) ⊗[R] (C ⊗[R] D) ≃ₗ[R] (A ⊗[R] C) ⊗[R] (B ⊗[R] D) :=
  ((TensorProduct.assoc R (A ⊗[R] B) C D).symm.trans
      (LinearEquiv.rTensor D
        (((TensorProduct.assoc R A B C).trans
          ((LinearEquiv.lTensor A (TensorProduct.comm R B C)))).trans
            (TensorProduct.assoc R A C B).symm))).trans
    (TensorProduct.assoc R (A ⊗[R] C) _ _)

@[simp]
lemma swapMiddleTensor_tmul_apply
    {R : Type*} [CommSemiring R] {A B C D : Type*}
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    (x : A) (y : B) (z : C) (w : D) :
    swapMiddleTensor R A B C D ((x ⊗ₜ[R] y) ⊗ₜ[R] (z ⊗ₜ[R] w)) =
      (x ⊗ₜ z) ⊗ₜ (y ⊗ₜ w) :=
  rfl

@[simp]
lemma swapMiddleTensor_symm
    {R : Type*} [CommSemiring R] {A B C D : Type*}
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
    [Module R A] [Module R B] [Module R C] [Module R D] :
    (swapMiddleTensor R A B C D).symm = swapMiddleTensor R A C B D :=
  rfl

lemma swapMiddleTensor_comp_map
    {R : Type*} [CommSemiring R] {A B C D E F G H : Type*}
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid G] [AddCommMonoid H]
    [Module R E] [Module R F] [Module R G] [Module R H]
    (f : A →ₗ[R] B) (g : C →ₗ[R] D)
    (h : E →ₗ[R] F) (k : G →ₗ[R] H) :
    (swapMiddleTensor R B D F H).toLinearMap ∘ₗ
        (TensorProduct.map (TensorProduct.map f g) (TensorProduct.map h k)) =
      (TensorProduct.map (TensorProduct.map f h) (TensorProduct.map g k)) ∘ₗ
        (swapMiddleTensor R A C E G).toLinearMap := by
  apply TensorProduct.ext_fourfold'
  simp

lemma LinearMap.mul'_tensorProduct {R A B : Type*}
    [CommSemiring R] [NonUnitalNonAssocSemiring A]
    [NonUnitalNonAssocSemiring B] [Module R A] [Module R B]
    [SMulCommClass R A A] [SMulCommClass R B B] [IsScalarTower R A A]
    [IsScalarTower R B B] :
    LinearMap.mul' R (A ⊗[R] B) =
      (TensorProduct.map (LinearMap.mul' R A) (LinearMap.mul' R B)) ∘ₗ
        (swapMiddleTensor R A B A B).toLinearMap := by
  apply TensorProduct.ext_fourfold'
  simp

lemma swapMiddleTensor_map_conj {R A B C D E F G H : Type*} [CommSemiring R]
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid G] [AddCommMonoid H]
    [Module R E] [Module R F] [Module R G] [Module R H]
    (f : A →ₗ[R] B) (g : C →ₗ[R] D)
    (h : E →ₗ[R] F) (k : G →ₗ[R] H) :
    (swapMiddleTensor R B D F H).toLinearMap ∘ₗ
        (TensorProduct.map (TensorProduct.map f g) (TensorProduct.map h k)) ∘ₗ
          (swapMiddleTensor R A C E G).symm.toLinearMap =
      TensorProduct.map (TensorProduct.map f h) (TensorProduct.map g k) := by
  apply TensorProduct.ext_fourfold'
  simp

lemma swapMiddleTensor_adjoint
    {𝕜 E F G H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
    [InnerProductSpace 𝕜 G] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H] :
    LinearMap.adjoint (swapMiddleTensor 𝕜 E F G H).toLinearMap =
      (swapMiddleTensor 𝕜 E F G H).symm.toLinearMap := by
  apply TensorProduct.ext_fourfold'
  intros x y z w
  rw [TensorProduct.inner_ext_fourfold_iff']
  simp [LinearMap.adjoint_inner_left, mul_mul_mul_comm]
