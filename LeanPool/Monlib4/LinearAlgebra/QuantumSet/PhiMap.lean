/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Basic
import LeanPool.Monlib4.LinearAlgebra.MyBimodule

/-!
# The Phi Map

This file packages the upstream `Upsilon` equivalence as a bimodule-map
equivalence and records the one-vector inner-product identities used by
downstream quantum graph files.
-/

/-- The `Upsilon` equivalence viewed through the tensor-product bimodule map API. -/
noncomputable abbrev PhiMap {A B : Type*} [starAlgebra B] [starAlgebra A] [QuantumSet A]
  [QuantumSet B] :=
    (Upsilon (A := A) (B := B)).trans TensorProduct.toIsBimoduleMap

/-- Applying `PhiMap` is applying `Upsilon` and then coercing to a bimodule map. -/
lemma PhiMap_apply {A B : Type*} [starAlgebra B] [starAlgebra A] [QuantumSet A]
  [QuantumSet B] (f : A →ₗ[ℂ] B) :
  PhiMap f = TensorProduct.toIsBimoduleMap (Upsilon f) :=
rfl

open scoped InnerProductSpace

/-- Mapping the unit and then pairing with the unit agrees with applying `Psi` first. -/
theorem oneInner_map_one_eq_oneInner_Psi_map
  {A B : Type*} [starAlgebra B] [starAlgebra A] [hA : QuantumSet A] [hB : QuantumSet B]
  (f : A →ₗ[ℂ] B) (r t : ℝ) :
    ⟪1, f 1⟫_ℂ = ⟪1, QuantumSet.Psi r t f⟫_ℂ := by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne f
  simp_rw [map_sum, LinearMap.sum_apply, inner_sum]
  congr
  ext1 i
  simp_rw [QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, inner_smul_right, Algebra.TensorProduct.one_def, TensorProduct.inner_tmul,
    ← MulOpposite.op_one, MulOpposite.inner_eq', starAlgebra.modAut_star,
    ← AlgEquiv.toLinearMap_apply, ← LinearMap.adjoint_inner_left,
    QuantumSet.modAut_adjoint, AlgEquiv.toLinearMap_apply, map_one,
    QuantumSet.inner_eq_counit', QuantumSet.inner_eq_counit, map_one, mul_one, mul_comm]

/-- Mapping the unit and pairing with the unit agrees after applying `PhiMap`. -/
lemma oneInner_map_one_eq_oneInner_PhiMap_map_one
  {A B : Type*} [starAlgebra B] [starAlgebra A] [hA : QuantumSet A] [hB : QuantumSet B]
  (f : A →ₗ[ℂ] B) :
  ⟪1, f 1⟫_ℂ = ⟪1, ((PhiMap f : (TensorProduct ℂ A B →ₗ[ℂ] TensorProduct ℂ A B)) 1)⟫_ℂ := by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne f
  simp_rw [map_sum, LinearMap.IsBimoduleMap.sum_coe,
    LinearMap.sum_apply, inner_sum]
  congr
  ext1 i
  simp_rw [PhiMap_apply, Upsilon_rankOne, TensorProduct.toIsBimoduleMap_apply_coe,
    rmulMapLmul_apply_one, ContinuousLinearMap.coe_coe, rankOne_apply,
    Algebra.TensorProduct.one_def, TensorProduct.inner_tmul, inner_smul_right]
  rw [← one_mul (modAut _ _), ← QuantumSet.inner_conj_left, one_mul]
