/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.LinearAlgebra.Ips.TensorHilbert
import LeanPool.Monlib4.LinearAlgebra.Ips.Nontracial
import LeanPool.Monlib4.LinearAlgebra.DirectSumFromTo
import LeanPool.Monlib4.LinearAlgebra.PiDirectSum
import LeanPool.Monlib4.LinearAlgebra.Coalgebra.FiniteDimensional

/-!
 # Frobenius equations

 This file contains the proof of the Frobenius equations.
-/


variable {n p : Type _} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} (hφ : φ.IsFaithfulPosMap) {ψ : Module.Dual ℂ (Matrix p p ℂ)}
  (hψ : ψ.IsFaithfulPosMap) {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {θ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [hθ : ∀ i, (θ i).IsFaithfulPosMap]

open scoped Matrix Kronecker TensorProduct BigOperators Functional InnerProductSpace

open Matrix

-- def linear_map.is_faithful_pos_map.tensor_pow (x : ℕ) :
--   ⨂[ℂ]^x (matrix n n ℂ) →ₗ[ℂ] ℂ :=
-- { to_fun := fun a, by { simp only [tensor_algebra] } }
/-- Tensor product of two matrix-valued module dual functionals. -/
noncomputable def Module.Dual.tensorMul {n p : Type _} (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) : Module.Dual ℂ (Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ) :=
  (TensorProduct.lid ℂ ℂ : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ) ∘ₗ TensorProduct.map φ₁ φ₂

omit [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p] in
theorem Module.Dual.tensorMul_apply (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) (x : Matrix n n ℂ) (y : Matrix p p ℂ) :
    (φ₁.tensorMul φ₂) (x ⊗ₜ[ℂ] y) = φ₁ x * φ₂ y :=
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j k l) -/
theorem Module.Dual.tensorMul_apply' (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) (x : Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ) :
    φ₁.tensorMul φ₂ x =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (TensorProduct.toKronecker x) (i, k) (j, l) *
          (φ₁ (stdBasisMatrix i j (1 : ℂ)) * φ₂ (stdBasisMatrix k l (1 : ℂ))) :=
  by
  simp_rw [← Module.Dual.tensorMul_apply, ← smul_eq_mul, ← _root_.map_smul, ← map_sum]
  rw [← x.matrix_eq_sum_std_basis]

theorem Module.Dual.tensorMul_apply'' (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) (a : Matrix (n × p) (n × p) ℂ) :
    ((φ₁.tensorMul φ₂).comp kroneckerToTensorProduct) a = (φ₁.matrix ⊗ₖ φ₂.matrix * a).trace :=
  by
  have :
    (φ₁.matrix ⊗ₖ φ₂.matrix * a).trace =
      ((traceLinearMap _ ℂ ℂ).comp (LinearMap.mulLeft ℂ (φ₁.matrix ⊗ₖ φ₂.matrix))) a :=
    rfl
  simp_rw [this]
  clear this
  revert a
  rw [← LinearMap.ext_iff, KroneckerProduct.ext_iff]
  intro x y
  simp_rw [LinearMap.comp_apply, kroneckerToTensorProduct_apply, Module.Dual.tensorMul_apply,
    LinearMap.mulLeft_apply, traceLinearMap_apply, ← mul_kronecker_mul,
    trace_kronecker, Module.Dual.apply]

theorem Module.Dual.tensorMul_matrix (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) :
    Module.Dual.matrix ((φ₁.tensorMul φ₂).comp kroneckerToTensorProduct) = φ₁.matrix ⊗ₖ φ₂.matrix :=
  by
  symm
  apply Module.Dual.apply_eq_of
  simp_rw [← Module.Dual.tensorMul_apply'' φ₁ φ₂]
  intros
  trivial

/-- Tensor products of faithful positive matrix functionals are faithful and positive. -/
theorem Module.Dual.IsFaithfulPosMap.tensorMul {φ₁ : Module.Dual ℂ (Matrix n n ℂ)}
    {φ₂ : Module.Dual ℂ (Matrix p p ℂ)} [hφ₁ : φ₁.IsFaithfulPosMap]
    [hφ₂ : φ₂.IsFaithfulPosMap] :
    (Module.Dual.IsFaithfulPosMap ((φ₁.tensorMul φ₂).comp kroneckerToTensorProduct)) :=
  by
  rw [Module.Dual.isFaithfulPosMap_iff_of_matrix, Module.Dual.tensorMul_matrix]
  exact PosDef.kronecker hφ₁.matrixIsPosDef hφ₂.matrixIsPosDef

attribute [instance] Module.Dual.IsFaithfulPosMap.tensorMul

theorem Matrix.kroneckerToTensorProduct_adjoint [hφ : φ.IsFaithfulPosMap]
    [hψ : ψ.IsFaithfulPosMap] :-- =
      -- @linear_map.adjoint ℂ (matrix (n × p) (n × p) ℂ) (matrix n n ℂ ⊗[ℂ] matrix p p ℂ) _
      --   (nacg_th hφ hψ) (nacg_tt hφ hψ) (ips_th hφ hψ) (ips_tt hφ hψ) _ _
      letI : _root_.NormedAddCommGroup (Matrix n n ℂ) := Module.Dual.NormedAddCommGroup φ
      letI : _root_.SeminormedAddCommGroup (Matrix n n ℂ) :=
        (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
      letI : _root_.InnerProductSpace ℂ (Matrix n n ℂ) := Module.Dual.InnerProductSpace φ
      letI : _root_.NormedAddCommGroup (Matrix p p ℂ) := Module.Dual.NormedAddCommGroup ψ
      letI : _root_.SeminormedAddCommGroup (Matrix p p ℂ) :=
        (Module.Dual.NormedAddCommGroup ψ).toSeminormedAddCommGroup
      letI : _root_.InnerProductSpace ℂ (Matrix p p ℂ) := Module.Dual.InnerProductSpace ψ
      letI : _root_.NormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
        Module.Dual.NormedAddCommGroup ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
      letI : _root_.SeminormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
        (Module.Dual.NormedAddCommGroup
          ((φ.tensorMul ψ).comp kroneckerToTensorProduct)).toSeminormedAddCommGroup
      letI : _root_.InnerProductSpace ℂ (Matrix (n × p) (n × p) ℂ) :=
        Module.Dual.InnerProductSpace ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
      (@TensorProduct.toKronecker ℂ n p _ _ _ _ _ :
        Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ →ₗ[ℂ] Matrix (n × p) (n × p) ℂ) =
      LinearMap.adjoint (kroneckerToTensorProduct :
          Matrix (n × p) (n × p) ℂ →ₗ[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ) :=
    by
  letI : _root_.NormedAddCommGroup (Matrix n n ℂ) := Module.Dual.NormedAddCommGroup φ
  letI : _root_.SeminormedAddCommGroup (Matrix n n ℂ) :=
    (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI : _root_.InnerProductSpace ℂ (Matrix n n ℂ) := Module.Dual.InnerProductSpace φ
  letI : _root_.NormedAddCommGroup (Matrix p p ℂ) := Module.Dual.NormedAddCommGroup ψ
  letI : _root_.SeminormedAddCommGroup (Matrix p p ℂ) :=
    (Module.Dual.NormedAddCommGroup ψ).toSeminormedAddCommGroup
  letI : _root_.InnerProductSpace ℂ (Matrix p p ℂ) := Module.Dual.InnerProductSpace ψ
  letI : _root_.NormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
    Module.Dual.NormedAddCommGroup ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
  letI : _root_.SeminormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
    (Module.Dual.NormedAddCommGroup
      ((φ.tensorMul ψ).comp kroneckerToTensorProduct)).toSeminormedAddCommGroup
  letI : _root_.InnerProductSpace ℂ (Matrix (n × p) (n × p) ℂ) :=
    Module.Dual.InnerProductSpace ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
  rw [TensorProduct.ext_iff']
  intro x y
  apply @ext_inner_left ℂ _ _
  intro a
  rw [TensorProduct.toKronecker_apply, LinearMap.adjoint_inner_right, Matrix.kmul_representation a]
  simp_rw [map_sum, _root_.map_smul, sum_inner, inner_smul_left]
  apply Finset.sum_congr rfl
  intros x_1 _
  apply Finset.sum_congr rfl
  intros x_2 _
  apply Finset.sum_congr rfl
  intros x_3 _
  apply Finset.sum_congr rfl
  intros x_4 _
  symm
  calc
    (starRingEnd ℂ) (a (x_1, x_3) (x_2, x_4)) *
          (⟪(kroneckerToTensorProduct
              (stdBasisMatrix x_1 x_2 (1 : ℂ) ⊗ₖ stdBasisMatrix x_3 x_4 (1 : ℂ))),
            x ⊗ₜ[ℂ] y⟫_ℂ) =
        (starRingEnd ℂ) (a (x_1, x_3) (x_2, x_4)) *
          (⟪(stdBasisMatrix x_1 x_2 (1 : ℂ) ⊗ₜ[ℂ] stdBasisMatrix x_3 x_4 (1 : ℂ)),
            x ⊗ₜ[ℂ] y⟫_ℂ) :=
      by rw [kroneckerToTensorProduct_apply]
    _ =
        (starRingEnd ℂ) (a (x_1, x_3) (x_2, x_4)) *
          (⟪stdBasisMatrix x_1 x_2 (1 : ℂ), x⟫_ℂ *
            ⟪stdBasisMatrix x_3 x_4 (1 : ℂ), y⟫_ℂ) :=
      by rw [TensorProduct.inner_tmul]
    _ =
        (starRingEnd ℂ) (a (x_1, x_3) (x_2, x_4)) *
          (⟪(stdBasisMatrix x_1 x_2 (1 : ℂ) ⊗ₖ stdBasisMatrix x_3 x_4 (1 : ℂ)),
            x ⊗ₖ y⟫_ℂ) :=
      by
        rw [Module.Dual.IsFaithfulPosMap.inner_eq' _
          ((stdBasisMatrix x_1 x_2 (1 : ℂ)) ⊗ₖ (stdBasisMatrix x_3 x_4 (1 : ℂ))) (x ⊗ₖ y),
          Module.Dual.tensorMul_matrix, kronecker_conjTranspose, ← mul_kronecker_mul,
            ← mul_kronecker_mul, trace_kronecker,
          Module.Dual.IsFaithfulPosMap.inner_eq', Module.Dual.IsFaithfulPosMap.inner_eq']

theorem TensorProduct.toKronecker_adjoint [hφ : φ.IsFaithfulPosMap]
    [hψ : ψ.IsFaithfulPosMap] :
    letI : _root_.NormedAddCommGroup (Matrix n n ℂ) := Module.Dual.NormedAddCommGroup φ
    letI : _root_.SeminormedAddCommGroup (Matrix n n ℂ) :=
      (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI : _root_.InnerProductSpace ℂ (Matrix n n ℂ) := Module.Dual.InnerProductSpace φ
    letI : _root_.NormedAddCommGroup (Matrix p p ℂ) := Module.Dual.NormedAddCommGroup ψ
    letI : _root_.SeminormedAddCommGroup (Matrix p p ℂ) :=
      (Module.Dual.NormedAddCommGroup ψ).toSeminormedAddCommGroup
    letI : _root_.InnerProductSpace ℂ (Matrix p p ℂ) := Module.Dual.InnerProductSpace ψ
    letI : _root_.NormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
      Module.Dual.NormedAddCommGroup ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
    letI : _root_.SeminormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
      (Module.Dual.NormedAddCommGroup
        ((φ.tensorMul ψ).comp kroneckerToTensorProduct)).toSeminormedAddCommGroup
    letI : _root_.InnerProductSpace ℂ (Matrix (n × p) (n × p) ℂ) :=
      Module.Dual.InnerProductSpace ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
    (kroneckerToTensorProduct : Matrix (n × p) (n × p) ℂ →ₗ[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ) =
      LinearMap.adjoint (@TensorProduct.toKronecker ℂ n p _ _ _ _ _ :
          Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ →ₗ[ℂ] Matrix (n × p) (n × p) ℂ) :=
  by
  letI : _root_.NormedAddCommGroup (Matrix n n ℂ) := Module.Dual.NormedAddCommGroup φ
  letI : _root_.SeminormedAddCommGroup (Matrix n n ℂ) :=
    (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI : _root_.InnerProductSpace ℂ (Matrix n n ℂ) := Module.Dual.InnerProductSpace φ
  letI : _root_.NormedAddCommGroup (Matrix p p ℂ) := Module.Dual.NormedAddCommGroup ψ
  letI : _root_.SeminormedAddCommGroup (Matrix p p ℂ) :=
    (Module.Dual.NormedAddCommGroup ψ).toSeminormedAddCommGroup
  letI : _root_.InnerProductSpace ℂ (Matrix p p ℂ) := Module.Dual.InnerProductSpace ψ
  letI : _root_.NormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
    Module.Dual.NormedAddCommGroup ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
  letI : _root_.SeminormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
    (Module.Dual.NormedAddCommGroup
      ((φ.tensorMul ψ).comp kroneckerToTensorProduct)).toSeminormedAddCommGroup
  letI : _root_.InnerProductSpace ℂ (Matrix (n × p) (n × p) ℂ) :=
    Module.Dual.InnerProductSpace ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
  rw [@Matrix.kroneckerToTensorProduct_adjoint n p _ _ _ _ φ ψ hφ hψ, LinearMap.adjoint_adjoint]

theorem Matrix.kroneckerToTensorProduct_comp_toKronecker :
    (kroneckerToTensorProduct : Matrix (n × p) (n × p) ℂ →ₗ[ℂ] _).comp
        (TensorProduct.toKronecker : Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ →ₗ[ℂ] _) =
      1 :=
  by
  rw [TensorProduct.ext_iff']
  intro x y
  simp_rw [LinearMap.comp_apply, TensorProduct.toKronecker_to_tensorProduct, Module.End.one_apply]

local notation "ℍ" => Matrix n n ℂ

local notation "ℍ_" i => Matrix (s i) (s i) ℂ

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "id" => (1 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)

-- @[default_instance]
/-- The normed additive group of matrices induced by a faithful positive functional. -/
@[reducible]
noncomputable def Module.Dual.isNormedAddCommGroupOfRing {n : Type _} [Fintype n]
    [DecidableEq n] (ψ : Module.Dual ℂ (Matrix n n ℂ)) [ψ.IsFaithfulPosMap] :
    NormedAddCommGroupOfRing (Matrix n n ℂ)
    where
  toNorm := (Module.Dual.NormedAddCommGroup ψ).toNorm
  toMetricSpace := (Module.Dual.NormedAddCommGroup ψ).toMetricSpace
  dist_eq := (Module.Dual.NormedAddCommGroup ψ).dist_eq

-- @[default_instance]
/-- The normed additive commutative group structure induced by faithful block functionals. -/
@[reducible]
noncomputable def Pi.module.Dual.isNormedAddCommGroupOfRing
    (ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)) [∀ i, (ψ i).IsFaithfulPosMap] :
    NormedAddCommGroupOfRing (PiMat ℂ k s)
    where
  toNorm := (Module.Dual.PiNormedAddCommGroup (φ := ψ)).toNorm
  toMetricSpace := (Module.Dual.PiNormedAddCommGroup (φ := ψ)).toMetricSpace
  dist_eq := (Module.Dual.PiNormedAddCommGroup (φ := ψ)).dist_eq

-- @[default_instance]
-- noncomputable
-- def Pi.module.Dual.isNormedAddCommGroupOfStarRing
--   {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)} [∀ i, (ψ i).IsFaithfulPosMap] :
--     NormedAddCommGroupOfStarRing (PiMat ℂ k s) where
--     toNormedAddCommGroupOfRing := Pi.module.Dual.isNormedAddCommGroupOfRing ψ
-- set_option synthInstance.checkSynthOrder false in
-- scoped[Functional] attribute [instance] Module.Dual.isNormedAddCommGroupOfStarRing

-- theorem Module.Dual.inner_eq_counit (φ : Module.Dual ℂ (Matrix n n ℂ)) [hφ : φ.IsFaithfulPosMap]
-- (x y : ℍ) :
--   ⟪x, y⟫_ℂ = Coalgebra.counit (star x * y) :=
-- by
--   simp_rw [Coalgebra.counit, Module.Dual.IsFaithfulPosMap.inner_eq,
--     ← Nontracial.unit_adjoint_eq, star_eq_conjTranspose]
--   congr 2
--   rw [LinearMap.ext_iff]
--   intro
--   simp_rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
-- theorem Module.Dual.pi.inner_eq_counit (ψ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ))
--   [hψ : ∀ i, (ψ i).IsFaithfulPosMap] (x y : PiMat ℂ k s) :
--   ⟪x, y⟫_ℂ = Coalgebra.counit (star x * y) :=
-- by
--   simp_rw [Coalgebra.counit, Module.Dual.pi.IsFaithfulPosMap.inner_eq,
--     ← Nontracial.Pi.unit_adjoint_eq]
--   congr 2
--   rw [LinearMap.ext_iff]
--   intro
--   simp_rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]

-- set_option maxHeartbeats 400000 in
-- -- set_option synthInstance.maxHeartbeats 0 in
-- theorem frobenius_equation [hφ : φ.IsFaithfulPosMap] :
--     (LinearMap.mul' ℂ ℍ ⊗ₘ id) ∘ₗ (υ⁻¹) ∘ₗ (id ⊗ₘ (LinearMap.adjoint (LinearMap.mul' ℂ ℍ))) =
--       (LinearMap.adjoint (LinearMap.mul' ℂ ℍ)) ∘ₗ LinearMap.mul' ℂ ℍ :=
-- by
--   apply Coalgebra.rTensor_mul_comp_lTensor_mul_adjoint
--     (Module.Dual.inner_eq_counit φ)

local notation "l(" x ")" => x →ₗ[ℂ] x

open scoped BigOperators

/-- Linear map from one matrix summand to another in a direct product of matrix blocks. -/
noncomputable def matrixDirectSumFromTo
    (i j : k) :-- {k : Type*} [decidable_eq k] {s : k → Type*}
        -- [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
        -- (i j : k) :
        Matrix
        (s i) (s i) ℂ →ₗ[ℂ]
      Matrix (s j) (s j) ℂ :=
  @directSumFromTo ℂ _ k _ (fun a => Matrix (s a) (s a) ℂ) _ (fun _ => Matrix.module) i j

omit [Fintype k] [(i : k) → Fintype (s i)] [(i : k) → DecidableEq (s i)] in
theorem matrixDirectSumFromTo_same (i : k) :
    (matrixDirectSumFromTo i i : Matrix (s i) (s i) ℂ →ₗ[ℂ] _) = 1 :=
  directSumFromTo_apply_same _

-- set_option maxHeartbeats 0 in
-- set_option synthInstance.maxHeartbeats 0 in
open scoped Classical in
omit [Fintype k] [(i : k) → DecidableEq (s i)] in
theorem LinearMap.pi_mul'_apply_includeBlock' {i j : k} :
    letI : ∀ i, DecidableEq (s i) := fun i => Classical.decEq (s i)
    (LinearMap.mul' ℂ (PiMat ℂ k s)) ∘ₗ
        (TensorProduct.map (includeBlock : (ℍ_ i) →ₗ[ℂ] (PiMat ℂ k s)) (includeBlock :
          (ℍ_ j) →ₗ[ℂ] (PiMat ℂ k s))) =
      if i = j then
        (includeBlock : (ℍ_ j) →ₗ[ℂ] (PiMat ℂ k s)) ∘ₗ
          (LinearMap.mul' ℂ (ℍ_ j)) ∘ₗ
            (TensorProduct.map (matrixDirectSumFromTo i j) (1 : (ℍ_ j) →ₗ[ℂ] ℍ_ j))
      else 0 :=
  by
  classical
  rw [TensorProduct.ext_iff']
  intro x y
  rw [funext_iff]
  intro a
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    includeBlock_apply, Pi.mul_apply, dite_hMul, hMul_dite, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, ite_apply_lm, LinearMap.zero_apply, ite_apply, Pi.zero_apply,
    Module.End.one_apply]
  by_cases h : j = a
  · simp_rw [matrixDirectSumFromTo, directSumFromTo, LinearMap.comp_apply]
    simp [Pi.single, Function.update, h]
    split_ifs <;> aesop
  · simp [h]

/-- Linear equivalence splitting the tensor product of matrix-block products into block tensor
  products. -/
noncomputable def directSumTensorMatrix :
    ((PiMat ℂ k s) ⊗[ℂ] PiMat ℂ k s) ≃ₗ[ℂ]
      Π i : k × k, (ℍ_ i.1) ⊗[ℂ] ℍ_ i.2 :=
  @directSumTensor ℂ _ k k _ _ _ _ (fun i => Matrix (s i) (s i) ℂ) (fun i => Matrix (s i) (s i) ℂ) _
    _ (fun _ => Matrix.module) fun _ => Matrix.module

@[simp]
theorem Module.Dual.IsFaithfulPosMap.sig_apply' [hφ : φ.IsFaithfulPosMap] {r : ℝ}
  {x : ℍ} : hφ.sig r x = hφ.matrixIsPosDef.rpow (-r) * x * hφ.matrixIsPosDef.rpow r :=
rfl

-- theorem frobenius_equation' [hφ : φ.IsFaithfulPosMap] :
--     ((id ⊗ₘ LinearMap.mul' ℂ ℍ) ∘ₗ υ ∘ₗ LinearMap.adjoint (LinearMap.mul' ℂ ℍ) ⊗ₘ id) =
--       LinearMap.adjoint (LinearMap.mul' ℂ ℍ) ∘ₗ LinearMap.mul' ℂ ℍ :=
-- by
--   apply Coalgebra.lTensor_mul_comp_rTensor_mul_adjoint_of
--   let σ : ℍ ≃ₐ[ℂ] ℍ := (hφ.sig (-1 : ℝ))
--   refine ⟨σ, fun _ _ _ => ?_⟩
--   simp only [σ, hφ.sig_apply', neg_neg, Matrix.PosDef.rpow_one_eq_self,
--     Matrix.PosDef.rpow_neg_one_eq_inv_self, star_eq_conjTranspose, hφ.inner_right_conj]

-- theorem LinearMap.mul'_assoc :
--     (LinearMap.mul' ℂ (Matrix n n ℂ) ∘ₗ LinearMap.mul' ℂ (Matrix n n ℂ) ⊗ₘ id) =
--       LinearMap.mul' ℂ (Matrix n n ℂ) ∘ₗ
--         (id ⊗ₘ LinearMap.mul' ℂ (Matrix n n ℂ)) ∘ₗ
--           (↑(TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ) : _ ≃ₗ[ℂ] _) :
--             _ →ₗ[ℂ] _) :=
-- Algebra.assoc

-- noncomputable
-- def Matrix.Coalgebra [hφ : φ.IsFaithfulPosMap] :
--   Coalgebra ℂ (Matrix n n ℂ) :=
-- by infer_instance

-- section

-- set_option synthInstance.checkSynthOrder false in
-- attribute [local instance] Matrix.Coalgebra
-- theorem LinearMap.mul'_coassoc [hφ : φ.IsFaithfulPosMap] :
--     rTensor ℍ (LinearMap.adjoint (LinearMap.mul' ℂ ℍ)) ∘ₗ LinearMap.adjoint (LinearMap.mul' ℂ ℍ)
-- =
--       υ⁻¹ ∘ₗ lTensor ℍ (LinearMap.adjoint (LinearMap.mul' ℂ ℍ)) ∘ₗ LinearMap.adjoint
-- (LinearMap.mul' ℂ ℍ) :=
-- by simp_rw [← Coalgebra.comul_eq_mul_adjoint, Coalgebra.coassoc_symm.symm]

-- end

--  m(η ⊗ id) = τ
-- theorem LinearMap.mul'_comp_unit_map_id_eq_lid : LinearMap.mul' ℂ ℍ ∘ₗ (η ⊗ₘ id) = τ :=
-- Algebra.mul_comp_rTensor_unit

-- m(id ⊗ η)κ⁻¹ = τ
-- theorem LinearMap.mul'_comp_idMap_unit_assoc_eq_lid :
--   LinearMap.mul' ℂ ℍ ∘ₗ (id ⊗ₘ η) = TensorProduct.rid ℂ ℍ :=
-- Algebra.mul_comp_lTensor_unit

-- set_option synthInstance.maxHeartbeats 0 in
-- private theorem linear_map.idMapMul'_comp_unit_eq [hφ : φ.IsFaithfulPosMap] :
--     ((1 : ℍ →ₗ[ℂ] ℍ) ⊗ₘ ((LinearMap.adjoint (LinearMap.mul' ℂ ℍ)) ∘ₗ η))
--       = ((1 : ℍ →ₗ[ℂ] ℍ) ⊗ₘ (LinearMap.adjoint (LinearMap.mul' ℂ ℍ))) ∘ₗ ((1 : ℍ →ₗ[ℂ] ℍ) ⊗ₘ η)
-- :=
--   by rw [← TensorProduct.map_comp, LinearMap.comp_one]

-- (m ⊗ id)υ⁻¹(id ⊗ m⋆η)κ⁻¹τ⁻¹ = m⋆
-- theorem LinearMap.mul'_adjoint_eq' [hφ : φ.IsFaithfulPosMap] :
--     (LinearMap.mul' ℂ ℍ ⊗ₘ id) ∘ₗ υ⁻¹ ∘ₗ (id ⊗ₘ (LinearMap.adjoint (LinearMap.mul' ℂ ℍ) ∘ₗ η))
-- ∘ₗ (TensorProduct.rid ℂ ℍ).symm =
--       (LinearMap.adjoint (LinearMap.mul' ℂ ℍ)) :=
--   by
--   rw [linear_map.idMapMul'_comp_unit_eq]
--   have := @frobenius_equation n _ _ φ _
--   simp_rw [← LinearMap.comp_assoc] at this ⊢
--   rw [this]
--   simp_rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc (TensorProduct.rid ℂ ℍ).symm.toLinearMap,
--     LinearMap.mul'_comp_idMap_unit_assoc_eq_lid, LinearMap.comp_assoc,
--     LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
--     LinearEquiv.refl_toLinearMap, LinearMap.comp_id]

-- private theorem linear_map.mul'_comp_unit_map_id_eq [hφ : φ.IsFaithfulPosMap] :
--     ((LinearMap.adjoint (LinearMap.mul' ℂ ℍ) ∘ₗ η) ⊗ₘ id) = (LinearMap.adjoint (LinearMap.mul' ℂ
-- ℍ) ⊗ₘ id) ∘ₗ η ⊗ₘ id :=
--   by rw [← TensorProduct.map_comp, LinearMap.comp_one]

-- (id ⊗ m)υ(m∗η ⊗ id) τ⁻¹ = m⋆
-- theorem LinearMap.mul'_adjoint_eq'' [hφ : φ.IsFaithfulPosMap] :
--     (id ⊗ₘ LinearMap.mul' ℂ ℍ) ∘ₗ υ ∘ₗ ((LinearMap.adjoint (LinearMap.mul' ℂ ℍ) ∘ₗ η) ⊗ₘ id) ∘ₗ
-- τ⁻¹ =
--       LinearMap.adjoint (LinearMap.mul' ℂ ℍ) :=
--   by
--   rw [linear_map.mul'_comp_unit_map_id_eq]
--   have := @frobenius_equation' n _ _ φ _
--   simp_rw [← LinearMap.comp_assoc] at this ⊢
--   rw [this]
--   simp_rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ (_ ⊗ₘ _),
--     LinearMap.mul'_comp_unit_map_id_eq_lid, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
--     LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
