/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.QuantumGraph.Basic
import LeanPool.Monlib4.QuantumGraph.Degree

/-!
# LeanPool.Monlib4.QuantumGraph.Grad

Imported Lean Pool material for `LeanPool.Monlib4.QuantumGraph.Grad`.
-/

variable {B : Type*} [starAlgebra B] [QuantumSet B]

open scoped TensorProduct

local notation "lT" => LinearMap.lTensor
local notation "rT" => LinearMap.rTensor
local notation "η" => Algebra.linearMap ℂ
local notation "τ" => TensorProduct.lid ℂ
local notation "τ'" => TensorProduct.rid ℂ

/-- Gradient map associated to a quantum graph adjacency operator. -/
noncomputable def QuantumGraph.Grad :
    (B →ₗ[ℂ] B) →+ (B →ₗ[ℂ] B ⊗[ℂ] B) where
  toFun f := (rT _ (LinearMap.adjoint f) - lT _ f) ∘ₗ Coalgebra.comul
  map_add' _ _ := by simp_rw [LinearMap.lTensor_add, map_add, LinearMap.rTensor_add,
    add_sub_add_comm, LinearMap.add_comp]
  map_zero' := by simp only [map_zero, LinearMap.rTensor_zero, LinearMap.lTensor_zero, sub_self,
    LinearMap.zero_comp]

lemma QuantumGraph.Grad_apply (A : B →ₗ[ℂ] B) :
  QuantumGraph.Grad A = (rT _ (LinearMap.adjoint A) - lT _ A) ∘ₗ Coalgebra.comul :=
rfl

private noncomputable def grad_phiMap :
    (B →ₗ[ℂ] B) →+ (B →ₗ[ℂ] B ⊗[ℂ] B) where
  toFun A := ((PhiMap (LinearMap.real A)).1 ∘ₗ (rT _ (η _)) ∘ₗ (τ _).symm.toLinearMap)
    - (PhiMap A).1 ∘ₗ (lT _ (η _)) ∘ₗ (τ' _).symm.toLinearMap
  map_add' _ _ := by simp only [LinearMap.real_add, map_add,
    LinearMap.IsBimoduleMaps.coe_add, add_sub_add_comm, LinearMap.add_comp]
  map_zero' := by simp only [map_zero, LinearMap.real_zero, LinearMap.IsBimoduleMaps.coe_zero,
    sub_self, LinearMap.zero_comp]
private lemma grad_phiMap_apply (A : B →ₗ[ℂ] B) :
  grad_phiMap A = ((PhiMap (LinearMap.real A)).1 ∘ₗ (rT _ (η _)) ∘ₗ (τ _).symm.toLinearMap)
    - (PhiMap A).1 ∘ₗ (lT _ (η _)) ∘ₗ (τ' _).symm.toLinearMap :=
rfl

theorem QuantumGraph.Grad_eq (gns : k B = 0) (A : B →ₗ[ℂ] B) :
  QuantumGraph.Grad A
    = ((PhiMap (LinearMap.real A)).1 ∘ₗ (rT _ (η _)) ∘ₗ (τ _).symm.toLinearMap)
      - (PhiMap A).1 ∘ₗ (lT _ (η _)) ∘ₗ (τ' _).symm.toLinearMap :=
by
  rw [← grad_phiMap_apply]
  revert A
  rw [← AddMonoidHom.ext_iff]
  apply AddMonoidHom.ext_of_rank_one'
  intro x y
  ext a
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := ℂ) (Coalgebra.comul a)
  apply (TensorProduct.inner_ext_iff' _ _).mpr
  intro c d
  simp only [grad_phiMap_apply, QuantumGraph.Grad_apply]
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_right,
    map_sub, LinearMap.rTensor_adjoint, LinearMap.lTensor_adjoint,
    LinearMap.adjoint_adjoint, LinearMap.sub_apply,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    ← LinearMap.adjoint_inner_right, Coalgebra.comul_eq_mul_adjoint,
    LinearMap.adjoint_adjoint, map_sub]
  simp_rw [LinearMap.mul'_apply]
  simp only [LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.lid_symm_apply,
    TensorProduct.rid_symm_apply,
    LinearMap.rTensor_tmul, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
    one_smul, LinearMap.sub_apply,
    PhiMap.apply_real gns, PhiMap_rankOne, TensorProduct.map_adjoint,
    LinearMap.adjoint_adjoint, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
    inner_sub_left, TensorProduct.inner_tmul, rmul_apply, one_mul, mul_one,
    inner_sub_right, LinearMap.adjoint_inner_left, lmul_apply]
  simp only [ContinuousLinearMap.linearMap_adjoint, rankOne_adjoint,
    ContinuousLinearMap.coe_coe, rankOne_apply, smul_mul_assoc, inner_smul_right,
    mul_smul_comm, mul_comm]

theorem QuantumGraph.Grad_apply' (gns : k B = 0) (A : B →ₗ[ℂ] B) (x : B) :
  QuantumGraph.Grad A x = (PhiMap (LinearMap.real A)).1 (1 ⊗ₜ x) - (PhiMap A).1 (x ⊗ₜ 1) :=
by
  simp_rw [Grad_eq gns, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe,
    TensorProduct.lid_symm_apply, TensorProduct.rid_symm_apply,
    LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
    Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, one_smul]

theorem QuantumGraph.Real.range_grad_le_range_phiMap
  (gns : k B = 0) {A : B →ₗ[ℂ] B} (hA : QuantumGraph.Real _ A) :
    LinearMap.range (QuantumGraph.Grad A) ≤ LinearMap.range (PhiMap A).1 :=
by
  have : IsIdempotentElem (PhiMap A).1 :=
  by
    rw [IsIdempotentElem, PhiMap_apply, ← schurMul_Upsilon_toBimodule, hA.1]
  apply (IsIdempotentElem.comp_idempotent_iff this (p := QuantumGraph.Grad A)).mp
  rw [QuantumGraph.Grad_eq gns, LinearMap.comp_sub]
  simp_rw [← LinearMap.comp_assoc, LinearMap.real_of_isReal hA.2,
    ← Module.End.mul_eq_comp, this.eq]

theorem Upsilon_symm_grad_apply_apply (gns : k B = 0) (A : B →ₗ[ℂ] B) (x : B) :
  Upsilon.symm (QuantumGraph.Grad A x)
    = rmul x ∘ₗ LinearMap.real A - A ∘ₗ rmul x :=
by
  suffices ∀ a b : B, Upsilon.symm (QuantumGraph.Grad (rankOne ℂ a b) x)
    = rmul x ∘ₗ LinearMap.real (rankOne ℂ a b) - rankOne ℂ a b ∘ₗ rmul x by
    obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne A
    simp only [map_sum, LinearMap.sum_apply, this, LinearMap.real_sum,
      LinearMap.comp_sum, LinearMap.sum_comp, Finset.sum_sub_distrib]
  intro a b
  rw [QuantumGraph.Grad_eq gns, PhiMap.apply_real gns, PhiMap_rankOne,
    TensorProduct.map_adjoint, LinearMap.adjoint_adjoint]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.lid_symm_apply, TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul,
    LinearMap.rTensor_tmul, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, one_smul,
    TensorProduct.map_tmul, map_sub, Upsilon_symm_tmul,
    lmul_adjoint, rmul_adjoint, lmul_apply, rmul_apply, mul_one, one_mul,
    rankOne_real, LinearMap.comp_rankOne, LinearMap.rankOne_comp,
    gns, neg_zero, mul_zero, zero_sub, starAlgebra.modAut_zero,
    star_mul, map_mul, starAlgebra.modAut_star, starAlgebra.modAut_apply_modAut,
    star_star, add_neg_cancel]
  rfl

theorem QuantumGraph.grad_adjoint_comp_grad (gns : k B = 0) (A : B →ₗ[ℂ] B) :
  LinearMap.adjoint (Grad A) ∘ₗ Grad A
    = outDegree (A •ₛ LinearMap.real A)
      - A •ₛ A
      - LinearMap.adjoint (A •ₛ A)
      + inDegree (LinearMap.real A •ₛ A) :=
by
  rw [Grad_apply, LinearMap.adjoint_comp, Coalgebra.comul_eq_mul_adjoint,
    map_sub, LinearMap.rTensor_adjoint, LinearMap.lTensor_adjoint]
  simp_rw [LinearMap.adjoint_adjoint, ← Coalgebra.comul_eq_mul_adjoint]
  rw [LinearMap.comp_assoc]
  nth_rw 2 [← LinearMap.comp_assoc]
  simp only [← Module.End.mul_eq_comp, sub_mul, mul_sub,
    ← LinearMap.rTensor_mul, ← LinearMap.lTensor_mul]
  simp only [Module.End.mul_eq_comp,
    LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.rTensor, LinearMap.lTensor,
    ← schurMul_apply_apply, outDegree_apply_schurMul gns, inDegree_apply_schurMul gns,
    LinearMap.real_real,
    symmMap_apply, schurMul_adjoint]
  rw [sub_sub_sub_comm, sub_add]
  rfl

open scoped Bimodule
theorem Bimodule.lsmul_sub {R H₁ H₂ : Type*} [CommSemiring R] [Ring H₁]
  [Ring H₂] [Algebra R H₁] [Algebra R H₂] (x : H₁) (a b : H₁ ⊗[R] H₂) :
  x •ₗ (a - b) = x •ₗ a - x •ₗ b :=
map_sub _ _ _
theorem Bimodule.sub_rsmul {R H₁ H₂ : Type*} [CommSemiring R] [Ring H₁]
  [Ring H₂] [Algebra R H₁] [Algebra R H₂] (x : H₂) (a b : H₁ ⊗[R] H₂) :
  (a - b) •ᵣ x = a •ᵣ x - b •ᵣ x :=
map_sub _ _ _

theorem QuantumGraph.apply_mul_of_isReal
  (gns : k B = 0) {A : B →ₗ[ℂ] B} (hA : LinearMap.IsReal A) (x y : B) :
    Grad A (x * y) = Grad A x •ᵣ y + x •ₗ Grad A y :=
by
  simp only [Grad_apply' gns, Bimodule.lsmul_sub,
    PhiMap_apply, TensorProduct.toIsBimoduleMap_apply_coe, rmulMapLmul_apply_apply,
    Bimodule.one_lsmul, Bimodule.rsmul_one, Bimodule.sub_rsmul,
    Bimodule.rsmul_rsmul, Bimodule.lsmul_lsmul,
    Bimodule.lsmul_rsmul_assoc, LinearMap.real_of_isReal hA,
    sub_add_sub_cancel]
