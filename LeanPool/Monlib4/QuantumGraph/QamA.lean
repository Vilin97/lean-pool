/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.QuantumGraph.ToProjections

/-!

# Single-edged quantum graphs

This file defines the single-edged quantum graph, and proves that it is a `QAM`.

-/


variable {n : Type _} [Fintype n] [DecidableEq n]

open scoped TensorProduct BigOperators Kronecker Functional
@[reducible]
local notation "ℍ" => Matrix n n ℂ
@[reducible]
local notation "ℍ_" i => Matrix (n i) (n i) ℂ

@[reducible]
local notation "l(" x ")" => x →ₗ[ℂ] x
@[reducible]
local notation "L(" x ")" => x →L[ℂ] x
@[reducible]
local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)

variable {φ : Module.Dual ℂ (Matrix n n ℂ)}

open scoped Matrix

open Matrix

local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y

local notation "m" => LinearMap.mul' ℂ ℍ

local notation "η" => Algebra.linearMap ℂ ℍ

local notation x " ⊗ₘ " y => TensorProduct.map x y

local notation "υ" => (TensorProduct.assoc ℂ ℍ ℍ ℍ : (ℍ ⊗[ℂ] ℍ) ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℍ ⊗[ℂ] ℍ)

local notation "υ⁻¹" =>
  (LinearEquiv.symm (TensorProduct.assoc ℂ ℍ ℍ ℍ) : ℍ ⊗[ℂ] ℍ ⊗[ℂ] ℍ →ₗ[ℂ] (ℍ ⊗[ℂ] ℍ) ⊗[ℂ] ℍ)

local notation "ϰ" => ((TensorProduct.comm ℂ ℍ ℂ) : ℍ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ ⊗[ℂ] ℍ)

local notation "ϰ⁻¹" => (LinearEquiv.symm (TensorProduct.comm ℂ ℍ ℂ) : ℂ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ ⊗[ℂ] ℂ)

local notation "τ" => (TensorProduct.lid ℂ ℍ : ℂ ⊗[ℂ] ℍ →ₗ[ℂ] ℍ)

local notation "τ⁻¹" => (LinearEquiv.symm (TensorProduct.lid ℂ ℍ) : ℍ →ₗ[ℂ] ℂ ⊗[ℂ] ℍ)

local notation "id" => (1 : ℍ →ₗ[ℂ] ℍ)

/-- The rank-one quantum adjacency map associated to a nonzero matrix. -/
noncomputable def qamA (hφ : φ.IsFaithfulPosMap)
    (x : { x : ℍ // x ≠ 0 }) :--(hx : x ≠ 0) :
      ℍ →ₗ[ℂ]
      ℍ := by
  letI : φ.IsFaithfulPosMap := hφ
  withMatrixQuantumCtx[φ]
  exact
    (1 / (‖x.1‖ ^ 2 : ℂ)) •
      (LinearMap.mulLeft ℂ (x.1 * φ.matrix) *
        LinearMap.adjoint (LinearMap.mulRight ℂ (φ.matrix * x.1)))

theorem qamA_eq [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) :
    qamA hφ x =
      withMatrixQuantum[φ]
        ((1 / (‖x.1‖ ^ 2 : ℂ)) •
          (LinearMap.mulLeft ℂ (x.1 * φ.matrix) *
            LinearMap.adjoint (LinearMap.mulRight ℂ (φ.matrix * x.1)))) := by
  withMatrixQuantumCtx[φ]
  rfl

theorem qamA.toMatrix [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) :
    withMatrixQuantum[φ]
      (hφ.toMatrix (qamA hφ x) =
        (1 / ‖x.1‖ ^ 2 : ℂ) •
          (x.1 * φ.matrix) ⊗ₖ
            (hφ.matrixIsPosDef.rpow (1 / 2) * x.1 * hφ.matrixIsPosDef.rpow (1 / 2))ᴴᵀ) := by
  withMatrixQuantumCtx[φ]
  simp only [qamA_eq, _root_.map_smul, _root_.map_mul, LinearMap.mulLeft_toMatrix,
    LinearMap.matrix.mulRight_adjoint, LinearMap.mulRight_toMatrix,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig, Matrix.conjTranspose_mul,
    hφ.matrixIsPosDef.1.eq, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one]
  have :
    (hφ.sig (1 / 2 + -1)) (x.1ᴴ * φ.matrix) =
      (hφ.matrixIsPosDef.rpow (1 / 2) * x.1 *
          hφ.matrixIsPosDef.rpow (1 / 2))ᴴ :=
    calc
      (hφ.sig (1 / 2 + -1)) (x.1ᴴ * φ.matrix) =
          hφ.matrixIsPosDef.rpow (1 / 2) * x.1ᴴ * φ.matrix *
            hφ.matrixIsPosDef.rpow (-(1 / 2)) :=
        by simp only [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc]; norm_num
      _ =
          hφ.matrixIsPosDef.rpow (1 / 2) * x.1ᴴ * hφ.matrixIsPosDef.rpow 1 *
            hφ.matrixIsPosDef.rpow (-(1 / 2)) :=
        by simp only [Matrix.PosDef.rpow_one_eq_self]
      _ =
          (hφ.matrixIsPosDef.rpow (1 / 2) * x.1 *
              hφ.matrixIsPosDef.rpow (1 / 2))ᴴ := by
          simp only [Matrix.PosDef.rpow_mul_rpow, Matrix.conjTranspose_mul,
            (Matrix.PosDef.rpow.isPosDef _ _).1.eq, Matrix.mul_assoc]
          norm_num
  rw [Matrix.conj, ← this, ← _root_.map_mul]

@[reducible, instance]
private noncomputable def has_smul.units_matrix_ne_zero : SMul ℂˣ { x : Matrix n n ℂ // x ≠ 0 }
    where smul α x :=
    (⟨((α : ℂ) • x.1 : Matrix n n ℂ),
        smul_ne_zero (Units.ne_zero α) (Set.mem_setOf.mp (Subtype.mem x))⟩ :
      { x : Matrix n n ℂ // x ≠ 0 })

omit [Fintype n] [DecidableEq n] in
private theorem has_smul.units_matrix_ne_zero_coe (x : { x : Matrix n n ℂ // x ≠ 0 }) (α : ℂˣ) :
    (α • x : { x : Matrix n n ℂ // x ≠ 0 }).1 = (α : ℂ) • x.1 :=
  rfl

open Matrix

/-- given a non-zero matrix $x$, we always get $A(x)$ is non-zero -/
theorem qamA.ne_zero [hφ : φ.IsFaithfulPosMap] (x : { x : Matrix n n ℂ // x ≠ 0 }) :
    qamA hφ x ≠ 0 := by
  withMatrixQuantumCtx[φ]
  have hx := x.property
  simp_rw [ne_eq, qamA, smul_eq_zero, div_eq_zero_iff, one_ne_zero, false_or, sq_eq_zero_iff,
    Complex.ofReal_eq_zero, norm_eq_zero, hx, false_or, ← rankOne_toMatrix_transpose_psi_symm,
    ← oneMapTranspose_symm_eq, LinearEquiv.map_eq_zero_iff, StarAlgEquiv.map_eq_zero_iff,
    AlgEquiv.map_eq_zero_iff, ContinuousLinearMap.coe_eq_zero, rankOne.eq_zero_iff, or_self_iff, hx,
    not_false_iff]

/-- Given any non-zero matrix $x$ and non-zero $\alpha\in\mathbb{C}$ we have
  $$A(\alpha x)=A(x),$$
  in other words, it is not injective. However, it `is_almost_injective` (see
    `qam_A.is_almost_injective`). -/
theorem qamA.smul [hφ : φ.IsFaithfulPosMap] (x : { x : Matrix n n ℂ // x ≠ 0 }) (α : ℂˣ) :
    qamA hφ (α • x) = qamA hφ x := by
  withMatrixQuantumCtx[φ]
  simp_rw [qamA_eq, has_smul.units_matrix_ne_zero_coe, norm_smul, smul_mul, Matrix.mul_smul,
    LinearMap.mulRight_smul, LinearMap.adjoint_smul, LinearMap.mulLeft_smul, smul_mul_smul,
    smul_smul, Complex.mul_conj, Complex.ofReal_mul, mul_pow, ← one_div_mul_one_div_rev, mul_assoc,
    ← Complex.ofReal_pow, Complex.normSq_eq_norm_sq]
  rw [one_div_mul_cancel, mul_one]
  · simp_rw [ne_eq, Complex.ofReal_eq_zero, sq_eq_zero_iff, norm_eq_zero]
    exact Units.ne_zero _

theorem qamA.is_idempotent [hφ : φ.IsFaithfulPosMap] (x : { x : Matrix n n ℂ // x ≠ 0 }) :
    withMatrixQuantum[φ]
      letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
      (Qam.reflIdempotent hφ (qamA hφ x) (qamA hφ x) = qamA hφ x) := by
  withMatrixQuantumCtx[φ]
  letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  rw [← Function.Injective.eq_iff (hφ.psi (ψ := φ) 0 (1 / 2)).injective,
    Module.Dual.IsFaithfulPosMap.psi, Qam.reflIdempotent, Psi.schurMul, qamA_eq]
  simp only [← rankOne_toMatrix_transpose_psi_symm]
  simp_rw [Module.Dual.IsFaithfulPosMap.psi, _root_.map_smul, LinearEquiv.apply_symm_apply,
    smul_mul_smul, ← oneMapTranspose_symm_eq, ← _root_.map_mul]
  have hrank :
      (((rankOne ℂ x.1 x.1 : L(ℍ)) : l(ℍ)) *
          ((rankOne ℂ x.1 x.1 : L(ℍ)) : l(ℍ)) : l(ℍ)) =
        (‖x.1‖ ^ 2 : ℂ) • ((rankOne ℂ x.1 x.1 : L(ℍ)) : l(ℍ)) := by
    ext y i j
    simp [Module.End.mul_apply, inner_self_eq_norm_sq_to_K]
    ring
  rw [hrank]
  simp_rw [_root_.map_smul, smul_smul, mul_assoc]
  have : (‖x.1‖ ^ 2 : ℂ) ≠ 0 :=
  by simp_rw [ne_eq, sq_eq_zero_iff, Complex.ofReal_eq_zero, norm_eq_zero]; exact x.property
  have this' := one_div_mul_cancel this
  simp_rw [Complex.ofReal'_eq_isROrC_ofReal] at this' ⊢
  simp_rw [this', mul_one]

theorem Psi.one [hφ : φ.IsFaithfulPosMap] :
    withMatrixQuantum[φ]
      (hφ.psi (ψ := φ) 0 (1 / 2) 1 =
        (TensorProduct.map (1 : l(ℍ)) (transposeAlgEquiv n ℂ ℂ).toLinearMap)
          (Matrix.kroneckerToTensorProduct (hφ.toMatrix |φ.matrix⁻¹⟩⟨φ.matrix⁻¹|))) := by
  withMatrixQuantumCtx[φ]
  nth_rw 1 [←
    rankOne.sum_orthonormalBasis_eq_id_lm
      (@Module.Dual.IsFaithfulPosMap.orthonormalBasis n _ _ φ _)]
  apply_fun (oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _) using StarAlgEquiv.injective _
  ext i j
  simp only [← oneMapTranspose_symm_eq, StarAlgEquiv.apply_symm_apply, map_sum,
    Module.Dual.IsFaithfulPosMap.psi, QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply,
    oneMapTranspose_apply]
  have hbasis : hφ.basis = hφ.orthonormalBasis.toBasis := by
    ext ij i j
    simp [Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply,
      Module.Dual.IsFaithfulPosMap.basis_apply]
  rw [show hφ.toMatrix = hφ.orthonormalBasis.toMatrix.toAlgEquiv by
    simp [Module.Dual.IsFaithfulPosMap.toMatrix, hbasis,
      orthonormalBasis_toMatrix_eq_basis_toMatrix]]
  simp only [StarAlgEquiv.coe_toAlgEquiv, OrthonormalBasis.toMatrix_apply,
    ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_right]
  have hmod : ∀ x, modAut (1 / 2) (hφ.orthonormalBasis x) =
      (hφ.orthonormalBasis x.swap)ᴴ := by
    intro x
    rw [show (modAut (1 / 2) : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) =
      hφ.sig (1 / 2) from rfl]
    simp only [Module.Dual.IsFaithfulPosMap.sig_apply, hφ.orthonormalBasis_apply, conjTranspose_mul,
      mul_assoc, PosDef.rpow_mul_rpow, neg_add_cancel, PosDef.rpow_zero,
      mul_one, (PosDef.rpow.isPosDef _ _).1.eq, single_conjTranspose, star_one]
    rfl
  simp only [hmod, star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [show inner ℂ φ.matrix⁻¹ (hφ.orthonormalBasis j) =
      star ((φ.matrix⁻¹ * hφ.matrixIsPosDef.rpow (1 / 2)) j.1 j.2) by
    rw [← inner_conj_symm]
    simp [hφ.inner_coord]]
  rw [hφ.inner_coord, ← PosDef.rpow_neg_one_eq_inv_self hφ.matrixIsPosDef]
  simp only [Matrix.sum_apply, kroneckerMap_apply, transpose_apply, starAlgebra.modAut_zero,
    AlgEquiv.one_apply, Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, mul_apply,
    single_eq, boole_mul]
  simp_rw [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, ite_mul, zero_mul, Prod.swap, mul_ite, mul_zero,
    Finset.sum_product_univ, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [← mul_apply]
  rw [PosDef.rpow_mul_rpow]
  ring_nf
  rw [← conjTranspose_apply, (PosDef.rpow.isPosDef _ _).1.eq, mul_comm]

theorem one_map_transpose_psi_eq [hφ : φ.IsFaithfulPosMap] (A : l(ℍ)) :
    withMatrixQuantum[φ]
      ((TensorProduct.map (1 : l(ℍ)) (transposeAlgEquiv n ℂ ℂ).symm.toLinearMap)
          (hφ.psi (ψ := φ) 0 (1 / 2) A) =
        (TensorProduct.map A (1 : l(ℍ)))
          (kroneckerToTensorProduct (hφ.toMatrix |φ.matrix⁻¹⟩⟨φ.matrix⁻¹|))) := by
  withMatrixQuantumCtx[φ]
  have :=
    calc
      ∑ k, ∑ l,
            ((rankOne ℂ
              (A (e_{k,l} * hφ.matrixIsPosDef.rpow (-(1 / 2))))
              (e_{k,l} * hφ.matrixIsPosDef.rpow (-(1 / 2))) : L(ℍ)).toLinearMap) =
          A ∘ₗ
            ∑ k, ∑ l,
              ((rankOne ℂ
                (e_{k,l} * hφ.matrixIsPosDef.rpow (-(1 / 2)))
                (e_{k,l} * hφ.matrixIsPosDef.rpow (-(1 / 2))) : L(ℍ)).toLinearMap) :=
        by simp_rw [← LinearMap.comp_rankOne, ← LinearMap.comp_sum]
      _ = A ∘ₗ 1 := by
        simp_rw [← Finset.sum_product', ← Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply,
          Finset.univ_product_univ, rankOne.sum_orthonormalBasis_eq_id_lm]
      _ = A := by rw [LinearMap.comp_one]
  nth_rw 1 [← this]
  simp_rw [map_sum, Module.Dual.IsFaithfulPosMap.psi, QuantumSet.Psi_apply,
    QuantumSet.PsiToFun_apply]
  have hzero :
    ∀ x x_1,
      (modAut 0) (A (stdBasisMatrix x x_1 1 * hφ.matrixIsPosDef.rpow (-(1 / 2)))) =
        A
          ((modAut 0)
            (stdBasisMatrix x x_1 1 * hφ.matrixIsPosDef.rpow (-(1 / 2)))) := by
    intro x x_1
    simp [starAlgebra.modAut_zero]
  simp_rw [hzero, TensorProduct.map_tmul, Module.End.one_apply, ← TensorProduct.map_tmul A,
    ← QuantumSet.PsiToFun_apply, ← QuantumSet.Psi_apply, ← map_sum, ← Finset.sum_product',
    ← Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, Finset.univ_product_univ,
    rankOne.sum_orthonormalBasis_eq_id_lm]
  have hPsi := @Psi.one n _ _ φ hφ
  rw [Module.Dual.IsFaithfulPosMap.psi] at hPsi
  simp_rw [hPsi, ← oneMapTranspose_symm_eq]
  have :
    ∀ x,
      (TensorProduct.map A (transposeAlgEquiv n ℂ ℂ).symm.toLinearMap)
          (StarAlgEquiv.symm (oneMapTranspose : (ℍ ⊗[ℂ] ℍᵐᵒᵖ) ≃⋆ₐ[ℂ] _) x) =
        (TensorProduct.map A (1 : l(ℍ))) (kroneckerToTensorProduct x) := by
    intro x
    rw [Matrix.kmul_representation x]
    simp_rw [map_sum, _root_.map_smul, oneMapTranspose_symm_eq,
      kroneckerToTensorProduct_apply, TensorProduct.map_tmul, Module.End.one_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]
  simp_rw [this]

theorem Psi.schurMul_faithful [hφ : φ.IsFaithfulPosMap] (r₁ r₂ : ℝ) (f g : l(ℍ)) :
    withMatrixQuantum[φ]
      letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
      (hφ.psi (ψ := φ) r₁ r₂ (f •ₛ g) =
        hφ.psi (ψ := φ) r₁ r₂ f * hφ.psi (ψ := φ) r₁ r₂ g) := by
  withMatrixQuantumCtx[φ]
  letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  rw [Module.Dual.IsFaithfulPosMap.psi, Psi.schurMul]

theorem qamA.isReal [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) :
    withMatrixQuantum[φ] (LinearMap.IsReal (qamA hφ x)) := by
  withMatrixQuantumCtx[φ]
  simp_rw [LinearMap.isReal_iff, qamA_eq, LinearMap.real_smul, Module.End.mul_eq_comp,
    LinearMap.real_comp, LinearMap.matrix.mulRight_adjoint, LinearMap.mulRight_real,
    LinearMap.mulLeft_real, ← Module.End.mul_eq_comp, ← (LinearMap.commute_mulLeft_right _ _).eq,
    conjTranspose_mul, hφ.matrixIsPosDef.1.eq, sig_apply_matrix_hMul_posDef',
    star_eq_conjTranspose, conjTranspose_mul, hφ.matrixIsPosDef.1.eq,
    conjTranspose_conjTranspose, starRingEnd_apply, star_div₀, star_one, Complex.star_def, ←
    Complex.ofReal_pow, Complex.conj_ofReal]

private theorem qam_A_is_sa_iff_aux [hφ : φ.IsFaithfulPosMap] (x : ℍ) :
    withMatrixQuantum[φ]
      ((|φ.matrix * x⟩⟨φ.matrix * x| : l(ℍ)) =
        LinearMap.mulLeft ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ)) ∘ₗ LinearMap.mulLeft ℂ φ.matrix) := by
  withMatrixQuantumCtx[φ]
  calc
    (|φ.matrix * x⟩⟨φ.matrix * x| : l(ℍ)) =
        LinearMap.mulLeft ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ)) ∘ₗ
          LinearMap.adjoint (LinearMap.mulLeft ℂ φ.matrix) := by
      simp only [LinearMap.comp_rankOne, LinearMap.rankOne_comp', LinearMap.mulLeft_apply]
    _ = LinearMap.mulLeft ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ)) ∘ₗ LinearMap.mulLeft ℂ φ.matrix := by
      simp_rw [LinearMap.matrix.mulLeft_adjoint, hφ.matrixIsPosDef.1.eq]

private theorem qam_A_is_sa_iff_aux2 [hφ : φ.IsFaithfulPosMap] (x : ℍ) :
    withMatrixQuantum[φ]
      ((|x * φ.matrix⟩⟨φ.matrix * x| : l(ℍ)) =
        LinearMap.mulRight ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ)) ∘ₗ LinearMap.mulLeft ℂ φ.matrix) := by
  withMatrixQuantumCtx[φ]
  calc
    (|x * φ.matrix⟩⟨φ.matrix * x| : l(ℍ)) =
        LinearMap.mulRight ℂ φ.matrix ∘ₗ
          (|x⟩⟨x| : l(ℍ)) ∘ₗ LinearMap.adjoint (LinearMap.mulLeft ℂ φ.matrix) := by
      simp only [LinearMap.comp_rankOne, LinearMap.rankOne_comp', LinearMap.mulLeft_apply,
        LinearMap.mulRight_apply]
    _ = LinearMap.mulRight ℂ φ.matrix ∘ₗ (|x⟩⟨x| : l(ℍ)) ∘ₗ LinearMap.mulLeft ℂ φ.matrix := by
      simp_rw [LinearMap.matrix.mulLeft_adjoint, hφ.matrixIsPosDef.1.eq]

theorem sig_eq_lmul_rmul [hφ : φ.IsFaithfulPosMap] (t : ℝ) :
    (hφ.sig t).toLinearMap =
      LinearMap.mulLeft ℂ (hφ.matrixIsPosDef.rpow (-t)) ∘ₗ
        LinearMap.mulRight ℂ (hφ.matrixIsPosDef.rpow t) := by
  rw [LinearMap.ext_iff]
  intro a
  simp_rw [AlgEquiv.toLinearMap_apply, hφ.sig_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← mul_assoc]

namespace Qam
namespace RankOne

theorem symmetric_eq [hφ : φ.IsFaithfulPosMap] (x : ℍ) :
    withMatrixQuantum[φ]
      (symmMap ℂ ℍ ℍ |x⟩⟨x| = |hφ.sig (-1) xᴴ⟩⟨xᴴ|) := by
  withMatrixQuantumCtx[φ]
  rw [symmMap_rankOne_apply, show k ℍ = 0 by rfl]
  simp_rw [star_eq_conjTranspose]
  rw [show modAut (-(2 * (0 : ℝ)) - 1) xᴴ =
      hφ.sig (-(2 * (0 : ℝ)) - 1) xᴴ by rfl]
  ring_nf

theorem symmetric'_eq [hφ : φ.IsFaithfulPosMap] (x : ℍ) :
    withMatrixQuantum[φ]
      ((symmMap ℂ ℍ ℍ).symm |x⟩⟨x| = |xᴴ⟩⟨hφ.sig (-1) xᴴ|) := by
  withMatrixQuantumCtx[φ]
  rw [symmMap_symm_rankOne_apply, show k ℍ = 0 by rfl]
  simp_rw [star_eq_conjTranspose]
  rw [show modAut (-(2 * (0 : ℝ)) - 1) xᴴ =
      hφ.sig (-(2 * (0 : ℝ)) - 1) xᴴ by rfl]
  ring_nf

end RankOne
end Qam

private theorem qam_A_is_sa_iff_aux5 [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) :
    withMatrixQuantum[φ]
      ((h :
        (LinearMap.mulLeft ℂ φ.matrix).comp (|x.1ᴴ⟩⟨x.1ᴴ| : l(ℍ)) =
          (LinearMap.mulRight ℂ φ.matrix).comp (|x.1⟩⟨x.1| : l(ℍ))) →
      symmMap ℂ ℍ ℍ |x.1⟩⟨x.1| = |x.1⟩⟨x.1|) := by
  withMatrixQuantumCtx[φ]
  intro h
  haveI := hφ.matrixIsPosDef.invertible
  calc
    symmMap ℂ ℍ ℍ |x.1⟩⟨x.1| =
        (hφ.sig (-1)).toLinearMap ∘ₗ (|x.1ᴴ⟩⟨x.1ᴴ| : l(ℍ)) :=
      ?_
    _ =
        LinearMap.mulLeft ℂ φ.matrix ∘ₗ
          LinearMap.mulRight ℂ φ.matrix⁻¹ ∘ₗ (|x.1ᴴ⟩⟨x.1ᴴ| : l(ℍ)) :=
      ?_
    _ =
        LinearMap.mulRight ℂ (φ.matrix⁻¹ : ℍ) ∘ₗ
          LinearMap.mulRight ℂ φ.matrix ∘ₗ (|x.1⟩⟨x.1| : l(ℍ)) :=
      ?_
    _ = (|x.1⟩⟨x.1| : l(ℍ)) := ?_
  · rw [symmMap_rankOne_apply, LinearMap.comp_rankOne, AlgEquiv.toLinearMap_apply]
    rw [show k ℍ = 0 by rfl]
    simp_rw [star_eq_conjTranspose]
    rw [show (modAut (-(2 * (0 : ℝ)) - 1) x.1ᴴ) =
        hφ.sig (-(2 * (0 : ℝ)) - 1) x.1ᴴ by rfl]
    ring_nf
  · simp_rw [sig_eq_lmul_rmul, neg_neg, PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self,
      LinearMap.comp_assoc]
  · simp_rw [← Module.End.mul_eq_comp, ← mul_assoc, (LinearMap.commute_mulLeft_right _ _).eq,
      mul_assoc, Module.End.mul_eq_comp, h]
  · rw [← LinearMap.comp_assoc, ← LinearMap.mulRight_mul, mul_inv_of_invertible,
      LinearMap.mulRight_one, LinearMap.id_comp]

theorem sig_comp_eq_iff_eq_sig_inv_comp [hφ : φ.IsFaithfulPosMap] (r : ℝ) (a b : l(ℍ)) :
    (hφ.sig r).toLinearMap.comp a = b ↔ a = (hφ.sig (-r)).toLinearMap.comp b := by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply]
  constructor <;> intro h x
  · simp_rw [← h, AlgEquiv.toLinearMap_apply, hφ.sig_apply_sig, neg_add_cancel,
      hφ.sig_zero, AlgEquiv.one_apply]
  · simp_rw [h, AlgEquiv.toLinearMap_apply, hφ.sig_apply_sig, add_neg_cancel,
      hφ.sig_zero, AlgEquiv.one_apply]

theorem sig_eq_iff_eq_sig_inv [hφ : φ.IsFaithfulPosMap] (r : ℝ) (a b : ℍ) : hφ.sig r a = b ↔ a =
  hφ.sig (-r) b := by
  constructor <;> rintro rfl <;>
    simp only [hφ.sig_apply_sig, neg_add_cancel, add_neg_cancel, hφ.sig_zero,
      AlgEquiv.one_apply]

theorem comp_sig_eq_iff_eq_comp_sig_inv [hφ : φ.IsFaithfulPosMap] (r : ℝ) (a b : l(ℍ)) :
    a.comp (hφ.sig r).toLinearMap = b ↔ a = b.comp (hφ.sig (-r)).toLinearMap := by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply]
  constructor <;> intro h x
  · simp only [← h, AlgEquiv.toLinearMap_apply, hφ.sig_apply_sig, add_neg_cancel,
      hφ.sig_zero, AlgEquiv.one_apply]
  · simp only [h, hφ.sig_apply_sig, neg_add_cancel, hφ.sig_zero, AlgEquiv.toLinearMap_apply,
      AlgEquiv.one_apply]

private theorem qam_A_is_sa_iff_aux_aux6 [hφ : φ.IsFaithfulPosMap] (r : ℝ) (a b : ℍ) :
    inner ℂ (hφ.sig r a) b = inner ℂ (hφ.sig (r / 2) a) (hφ.sig (r / 2) b) := by
  simp_rw [← AlgEquiv.toLinearMap_apply]
  symm
  nth_rw 2 [← Module.Dual.IsFaithfulPosMap.sig_adjoint]
  simp_rw [LinearMap.adjoint_inner_right, AlgEquiv.toLinearMap_apply,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig hφ, add_halves]

private theorem qam_A_is_sa_iff_aux3_aux6 [hφ : φ.IsFaithfulPosMap] (x : ℍ) (α : NNRealˣ)
    : withMatrixQuantum[φ]
      ((H : (|xᴴ⟩⟨xᴴ|) = (|hφ.sig 1 x⟩⟨x|)) →
      (h : hφ.sig 1 x = (((α : NNReal) : ℝ) : ℂ) • x) →
      |(Real.sqrt ((α : NNReal) : ℝ) : ℂ) • x⟩⟨(Real.sqrt ((α : NNReal) : ℝ) : ℂ) • x| =
        |xᴴ⟩⟨xᴴ|) := by
  withMatrixQuantumCtx[φ]
  intro H h
  have : 0 ≤ ((α : NNReal) : ℝ) := NNReal.coe_nonneg _
  rw [H, h]
  have hsqrt_star :
      ((Real.sqrt ((α : NNReal) : ℝ) : ℂ) • x) =
        (star (Real.sqrt ((α : NNReal) : ℝ) : ℂ)) • x := by
    simp [Complex.conj_ofReal]
  calc
    rankOne ℂ ((Real.sqrt ((α : NNReal) : ℝ) : ℂ) • x)
        ((Real.sqrt ((α : NNReal) : ℝ) : ℂ) • x) =
          ((Real.sqrt ((α : NNReal) : ℝ) : ℂ) *
              (Real.sqrt ((α : NNReal) : ℝ) : ℂ)) • rankOne ℂ x x := by
      rw [hsqrt_star, rankOne_smul_smul]
      simp [Complex.conj_ofReal]
    _ = ((((α : NNReal) : ℝ) : ℂ) * 1) • rankOne ℂ x x := by
      rw [show (Real.sqrt ((α : NNReal) : ℝ) : ℂ) *
          (Real.sqrt ((α : NNReal) : ℝ) : ℂ) =
            ((((α : NNReal) : ℝ) : ℂ) * 1) by
        rw [← Complex.ofReal_mul, ← Real.sqrt_mul this, Real.sqrt_mul_self this]
        simp]
    _ = rankOne ℂ (((((α : NNReal) : ℝ) : ℂ) • x)) x := by
      symm
      rw [show x = star (1 : ℂ) • x by simp, rankOne_smul_smul]
      simp

private theorem qam_A_is_sa_iff_aux4_aux6 [hφ : φ.IsFaithfulPosMap] (x' : { x : ℍ // x ≠ 0 })
    : withMatrixQuantum[φ]
      ((this :
        inner ℂ x'.1 x'.1 • hφ.sig 1 x'.1 =
          inner ℂ (hφ.sig 1 x'.1) x'.1 • x'.1) →
      ∃ α : NNRealˣ, hφ.sig 1 x'.1 = (((α : NNReal) : ℝ) : ℂ) • x'.1) := by
  withMatrixQuantumCtx[φ]
  intro this
  let x : ℍ := x'.1
  have hx : x ≠ 0 := x'.property
  let α : ℝ := ‖hφ.sig (1 / 2) x‖ ^ 2 / ‖x‖ ^ 2
  have hα' : 0 ≤ α := by
    simp_rw [α]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  let α' : NNReal := ⟨α, hα'⟩
  have hα : α' ≠ 0 := by
    have hsig : hφ.sig (1 / 2) x ≠ 0 := by
      intro hzero
      rw [sig_eq_iff_eq_sig_inv] at hzero
      have hzero' : x = 0 := by simpa using hzero
      exact hx hzero'
    have hnum : ‖hφ.sig (1 / 2) x‖ ^ 2 ≠ 0 := by
      simpa [norm_eq_zero] using hsig
    have hden : ‖x‖ ^ 2 ≠ 0 := by
      simpa [norm_eq_zero] using hx
    intro hzero
    have hαzero : α = 0 := by
      change (α' : ℝ) = 0
      exact congrArg (fun z : NNReal => (z : ℝ)) hzero
    exact hnum ((div_eq_zero_iff.mp hαzero).resolve_right hden)
  exists Units.mk0 α' hα
  change hφ.sig 1 x = ((α : ℝ) : ℂ) • x
  rw [show α = ‖hφ.sig (1 / 2) x‖ ^ 2 / ‖x‖ ^ 2 by rfl, Complex.ofReal_div]
  symm
  calc
    (((‖(hφ.sig (1 / 2)) x‖ ^ 2 : ℝ) : ℂ) / ((‖x‖ ^ 2 : ℝ) : ℂ)) • x =
        (1 / (‖x‖ ^ 2 : ℂ)) • (‖hφ.sig (1 / 2) x‖ ^ 2 : ℂ) • x :=
      by simp_rw [smul_smul, mul_comm (1 / _ : ℂ), mul_one_div, Complex.ofReal_pow]
    _ = (1 / inner ℂ x x) • inner ℂ (hφ.sig (1 / 2) x) (hφ.sig (1 / 2) x) • x := by
      simp_rw [inner_self_eq_norm_sq_to_K]; rfl
    _ = (1 / inner ℂ x x) • inner ℂ (hφ.sig 1 x) x • x := by rw [← qam_A_is_sa_iff_aux_aux6]
    _ = (1 / inner ℂ x x) • inner ℂ x x • hφ.sig 1 x := by rw [← this]
    _ = hφ.sig 1 x := ?_
  rw [smul_smul, one_div, inv_mul_cancel₀ (inner_self_ne_zero.mpr hx), one_smul]

theorem sig_eq_self_iff_commute [hφ : φ.IsFaithfulPosMap] (x : ℍ) : hφ.sig 1 x = x ↔
  Commute φ.matrix x := by
  simp_rw [hφ.sig_apply, Commute, SemiconjBy, PosDef.rpow_one_eq_self,
    PosDef.rpow_neg_one_eq_inv_self]
  haveI := hφ.matrixIsPosDef.invertible
  constructor <;> intro h
  · nth_rw 1 [← h]
    rw [Matrix.mul_assoc, mul_inv_cancel_left_of_invertible]
  · rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, inv_mul_of_invertible, Matrix.one_mul]

omit [Fintype n] [DecidableEq n] in
private theorem qam_A_is_sa_iff_aux7 (x : { x : ℍ // x ≠ 0 }) (α : NNRealˣ) (β : ℂˣ)
    (hx : x.1 = (star (β : ℂ) * (Real.sqrt ((α : NNReal) : ℝ) : ℂ)) • x.1ᴴ)
    (hx2 : x.1 = ((β⁻¹ : ℂ) * (((Real.sqrt ((α : NNReal) : ℝ))⁻¹ : ℝ) : ℂ)) • x.1ᴴ) :
    ‖(β : ℂ)‖ ^ 2 * ((α : NNReal) : ℝ) = 1 := by
  have : x.1 - x.1 = 0 := sub_self _
  nth_rw 1 [hx] at this
  nth_rw 2 [hx2] at this
  simp_rw [← sub_smul, smul_eq_zero, ← star_eq_conjTranspose, star_eq_zero,
    x.property, or_false, sub_eq_zero, Complex.ofReal_inv, ← mul_inv] at this
  have hi : 0 ≤ ((α : NNReal) : ℝ) := NNReal.coe_nonneg _
  rw [← mul_inv_eq_one₀, inv_inv, mul_mul_mul_comm, Complex.star_def, ←
    Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ←
    Complex.ofReal_mul, ← Real.sqrt_mul hi, Real.sqrt_mul_self hi, ← Complex.ofReal_mul,
    Complex.ofReal_eq_one] at this
  · exact this
  · simp_rw [ne_eq, inv_eq_zero, mul_eq_zero, Complex.ofReal_eq_zero, Real.sqrt_eq_zero hi,
      NNReal.coe_eq_zero, Units.ne_zero, or_false, not_false_iff]

private theorem qam_A_is_sa_iff_aux8 (α : NNRealˣ) (β : ℂˣ)
    (h : ‖(β : ℂ)‖ ^ 2 * ((α : NNReal) : ℝ) = 1) :
    ∃ γ : ℂˣ,
      (γ : ℂ) ^ 2 = (β : ℂ) * (((α : NNReal) : ℝ).sqrt : ℂ) ∧
        ‖(γ : ℂ)‖ ^ 2 = 1 ∧ star (γ : ℂ) = (γ : ℂ)⁻¹ := by
  let γ : ℂ := ((β : ℂ) * (((α : NNReal) : ℝ).sqrt : ℂ)) ^ ((2 : ℕ) : ℂ)⁻¹
  have hγ : γ ≠ 0 := by
    simp only [ne_eq, γ, Complex.cpow_eq_zero_iff, ne_eq, inv_eq_zero, Units.mul_right_eq_zero,
      Complex.ofReal_eq_zero, Real.sqrt_eq_zero, NNReal.zero_le_coe, NNReal.coe_eq_zero,
      Units.ne_zero, not_false_iff, false_and]
  have : γ ^ 2 = (β : ℂ) * (((α : NNReal) : ℝ).sqrt : ℂ) := by
    simp_rw [γ, Complex.cpow_nat_inv_pow _ two_ne_zero]
  have this1 : ‖γ‖ ^ 2 = 1 := by
    rw [show ‖γ‖ ^ 2 = ‖γ ^ 2‖ by rw [norm_pow], this, norm_mul]
    have hsquare :
        (‖(β : ℂ)‖ * ‖(((α : NNReal) : ℝ).sqrt : ℂ)‖) ^ 2 = (1 : ℝ) ^ 2 := by
      rw [mul_pow, Complex.ofReal'_eq_isROrC_ofReal,
        RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (NNReal.coe_nonneg _), h, one_pow]
    have hnonneg : 0 ≤ ‖(β : ℂ)‖ * ‖(((α : NNReal) : ℝ).sqrt : ℂ)‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith
  use Units.mk0 γ hγ
  constructor
  · exact this
  constructor
  · exact this1
  rw [← Complex.ofReal_inj, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
    Complex.ofReal_one, starRingEnd_apply, mul_comm, mul_eq_one_iff_eq_inv₀ hγ] at this1
  exact this1

omit [Fintype n] [DecidableEq n] in
private theorem qam_A_is_sa_iff_aux9 (x : ℍ) (α : NNRealˣ) (β γ : ℂˣ)
    (h : (γ : ℂ) ^ 2 = (β : ℂ) * (((α : NNReal) : ℝ).sqrt : ℂ)) (h2 : star (γ : ℂ) = (γ : ℂ)⁻¹)
    (hx : xᴴ = ((β : ℂ) * (Real.sqrt ((α : NNReal) : ℝ) : ℂ)) • x) : x.IsAlmostHermitian := by
  use Units.mk0 (star (γ : ℂ)) (star_ne_zero.mpr (Units.ne_zero _))
  use (γ : ℂ) • x
  simp_rw [IsHermitian, conjTranspose_smul, h2, Units.val_mk0, smul_smul,
    inv_mul_cancel₀ (Units.ne_zero γ), one_smul, true_and]
  rw [eq_comm, eq_inv_smul_iff₀ (Units.ne_zero γ), smul_smul, ← sq, h]
  exact hx.symm

private theorem qam_A_is_sa_iff_aux5_aux6 [hφ : φ.IsFaithfulPosMap] (x' : { x : ℍ // x ≠ 0 })
    : withMatrixQuantum[φ]
      ((this :
        inner ℂ x'.1 x'.1 • hφ.sig 1 x'.1 =
          inner ℂ (hφ.sig 1 x'.1) x'.1 • x'.1) →
      (h : symmMap ℂ ℍ ℍ |x'.1⟩⟨x'.1| = |x'.1⟩⟨x'.1|) →
      (hh : x'.1.IsAlmostHermitian) → Commute φ.matrix x'.1) := by
  withMatrixQuantumCtx[φ]
  intro this h hh
  obtain ⟨α, hα⟩ := qam_A_is_sa_iff_aux4_aux6 x' this
  have : hφ.sig (-1) x'.1ᴴ = (((α : NNReal) : ℝ) : ℂ) • x'.1ᴴ := by
    rw [← Module.Dual.IsFaithfulPosMap.sig_conjTranspose, hα, conjTranspose_smul, Complex.star_def,
      Complex.conj_ofReal]
  rw [Qam.RankOne.symmetric_eq, this] at h
  obtain ⟨β, y, hβy, hy⟩ := hh
  have this1 : y ≠ 0 := by
    intro H
    rw [H, smul_zero, eq_comm] at hβy
    exact x'.property hβy
  have Hβ : β ≠ 0 := by
    intro hβ
    rw [hβ, zero_smul, eq_comm] at hβy
    exact x'.property hβy
  simp_rw [← hβy, conjTranspose_smul, hy.eq, rankOne_eq_rankOneLm, smul_smul, rankOneLm_smul,
    smul_rankOneLm, smul_rankOneLm', smul_smul] at h
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, rankOneLm_eq_rankOne,
    ContinuousLinearMap.coe_eq_zero, rankOne.eq_zero_iff, or_self_iff] at h
  have hscalar : (((α : NNReal) : ℝ) : ℂ) * star β * β - β * star β = 0 :=
    h.resolve_right this1
  have hβnorm : star β * β ≠ 0 := mul_ne_zero (star_ne_zero.mpr Hβ) Hβ
  have hαone : (((α : NNReal) : ℝ) : ℂ) = 1 := by
    have hfactor : ((((α : NNReal) : ℝ) : ℂ) - 1) * (star β * β) = 0 := by
      ring_nf at hscalar ⊢
      exact hscalar
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hβnorm)
  rw [hαone, one_smul, sig_eq_self_iff_commute] at hα
  exact hα

private theorem qam_A_is_sa_iff_aux6 [hφ : φ.IsFaithfulPosMap] (x' : { x : ℍ // x ≠ 0 })
    : withMatrixQuantum[φ]
      ((h : symmMap ℂ ℍ ℍ |x'.1⟩⟨x'.1| = |x'.1⟩⟨x'.1|) →
      x'.1.IsAlmostHermitian ∧ Commute φ.matrix x'.1) := by
  withMatrixQuantumCtx[φ]
  intro h
  let x : ℍ := x'.1
  have hx : x ≠ 0 := x'.property
  have h' := h
  rw [← LinearEquiv.eq_symm_apply] at h'
  have H : (|xᴴ⟩⟨xᴴ| : l(ℍ)) = (|hφ.sig 1 x⟩⟨x| : l(ℍ)) := by
    rw [← AlgEquiv.toLinearMap_apply, ← LinearMap.comp_rankOne, ← neg_neg (1 : ℝ), ←
      sig_comp_eq_iff_eq_sig_inv_comp, LinearMap.comp_rankOne]
    rw [Qam.RankOne.symmetric_eq] at h
    exact h
  have H' : (|xᴴ⟩⟨xᴴ| : l(ℍ)) = (|x⟩⟨hφ.sig 1 x| : l(ℍ)) := by
    simp_rw [← AlgEquiv.toLinearMap_apply]
    rw [← Module.Dual.IsFaithfulPosMap.sig_adjoint, ← LinearMap.rankOne_comp, ← neg_neg (1 : ℝ), ←
      comp_sig_eq_iff_eq_comp_sig_inv]
    have :
      (|xᴴ⟩⟨xᴴ| : l(ℍ)) ∘ₗ (hφ.sig (-1)).toLinearMap =
        |xᴴ⟩⟨LinearMap.adjoint (hφ.sig (-1)).toLinearMap xᴴ| :=
      LinearMap.rankOne_comp _ _ _
    rw [this, Module.Dual.IsFaithfulPosMap.sig_adjoint]
    rw [Qam.RankOne.symmetric'_eq] at h'
    exact h'.symm
  have : (|hφ.sig 1 x⟩⟨x| : l(ℍ)) = |x⟩⟨hφ.sig 1 x| := by rw [← H, ← H']
  simp_rw [ContinuousLinearMap.coe_inj] at H this
  simp_rw [ContinuousLinearMap.ext_iff, rankOne_apply] at this
  specialize this x
  obtain ⟨α, hα⟩ := qam_A_is_sa_iff_aux4_aux6 x' this
  have hα' := (qam_A_is_sa_iff_aux3_aux6 _ α H hα).symm
  have hxstar : xᴴ ≠ 0 := by
    simpa [star_eq_conjTranspose] using star_ne_zero.mpr hx
  have hsqrtx : ((Real.sqrt ((α : NNReal) : ℝ) : ℂ) • x) ≠ 0 := by
    apply smul_ne_zero
    · simp [Units.ne_zero α]
    · exact hx
  obtain ⟨β, hβ⟩ := rankOne.ext_iff hxstar hsqrtx hα'
  rw [smul_smul] at hβ
  have hβ' : (x : ℍ) = (star (β : ℂ) * (Real.sqrt ((α : NNReal) : ℝ) : ℂ)) • (x : ℍ)ᴴ := by
    rw [← Function.Injective.eq_iff (conjTransposeAddEquiv n n ℂ).injective]
    simp_rw [conjTransposeAddEquiv_apply, conjTranspose_smul, star_mul', star_star,
      Complex.star_def, Complex.conj_ofReal, conjTranspose_conjTranspose]
    exact hβ
  have hβ'' : (x : ℍ) = ((β⁻¹ : ℂ) * (((Real.sqrt ((α : NNReal) : ℝ))⁻¹ : ℝ) : ℂ)) • (x : ℍ)ᴴ := by
    rw [hβ, smul_smul, mul_mul_mul_comm, inv_mul_cancel₀ (Units.ne_zero β), one_mul, ←
      Complex.ofReal_mul, inv_mul_cancel₀ (by
        rw [Real.sqrt_ne_zero (NNReal.coe_nonneg _), NNReal.coe_ne_zero]
        exact Units.ne_zero _), Complex.ofReal_one, one_smul]
  have Hβ := qam_A_is_sa_iff_aux7 x' α β hβ' hβ''
  obtain ⟨γ, hγ, _, Hγ'⟩ := qam_A_is_sa_iff_aux8 α β Hβ
  have Hβ' := qam_A_is_sa_iff_aux9 x α β γ hγ Hγ' hβ
  exact ⟨Hβ', qam_A_is_sa_iff_aux5_aux6 x' this h Hβ'⟩

theorem qamA.of_is_self_adjoint [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 })
    : withMatrixQuantum[φ]
      ((h : LinearMap.adjoint (qamA hφ x) = qamA hφ x) →
      x.1.IsAlmostHermitian ∧ Commute φ.matrix x.1) := by
  withMatrixQuantumCtx[φ]
  intro h
  simp_rw [qamA_eq, LinearMap.adjoint_smul, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint, LinearMap.matrix.mulLeft_adjoint, ← Module.End.mul_eq_comp, ←
    (LinearMap.commute_mulLeft_right _ _).eq, conjTranspose_mul, hφ.matrixIsPosDef.1.eq] at h
  have :
    LinearMap.mulRight ℂ (φ.matrix * x.1) =
      LinearMap.adjoint (LinearMap.mulRight ℂ (φ.matrix * x.1ᴴ)) := by
    simp_rw [LinearMap.matrix.mulRight_adjoint, conjTranspose_mul, conjTranspose_conjTranspose,
      hφ.matrixIsPosDef.1.eq, sig_apply_matrix_hMul_posDef']
  nth_rw 1 [this] at h
  simp_rw [← rankOne_psi_transpose_to_lin, ← oneMapTranspose_eq, ← _root_.map_smul] at h
  simp only [(AlgEquiv.injective _).eq_iff, (LinearEquiv.injective _).eq_iff,
    (StarAlgEquiv.injective _).eq_iff] at h
  have thisss : 1 / (‖x.1‖ : ℂ) ^ 2 ≠ 0 := by
    simp_rw [ne_eq, div_eq_zero_iff, one_ne_zero, false_or, sq_eq_zero_iff,
      Complex.ofReal_eq_zero, norm_eq_zero]
    exact x.property
  simp_rw [starRingEnd_apply, star_div₀, star_one, Complex.star_def, ← Complex.ofReal_pow,
    Complex.conj_ofReal, Complex.ofReal_pow] at h
  simp_rw [← ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.coe_inj] at h
  letI gg : NoZeroSMulDivisors ℂ (ℍ →ₗ[ℂ] ℍ) := by infer_instance
  rw [smul_right_inj thisss] at h
  simp_rw [← ContinuousLinearMap.coe_inj] at h
  rw [qam_A_is_sa_iff_aux, qam_A_is_sa_iff_aux2] at h
  haveI := hφ.matrixIsPosDef.invertible
  simp_rw [← LinearMap.comp_assoc, LinearMap.mulLeft_comp_inj] at h
  have h' := qam_A_is_sa_iff_aux5 x h
  exact qam_A_is_sa_iff_aux6 x h'

theorem qamA.is_self_adjoint_of [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) (hx₁ :
    x.1.IsAlmostHermitian)
    (hx₂ : Commute φ.matrix x.1) : withMatrixQuantum[φ] (LinearMap.adjoint (qamA hφ x) =
      qamA hφ x) := by
  withMatrixQuantumCtx[φ]
  simp_rw [qamA_eq, LinearMap.adjoint_smul, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint, LinearMap.matrix.mulLeft_adjoint, ← Module.End.mul_eq_comp, ←
    (LinearMap.commute_mulLeft_right _ _).eq, conjTranspose_mul, hφ.matrixIsPosDef.1.eq]
  obtain ⟨α, y, ⟨hxy, hy⟩⟩ := hx₁
  have : 1 / (‖x.1‖ : ℂ) ^ 2 ≠ 0 := by
    simp_rw [ne_eq, div_eq_zero_iff, one_ne_zero, false_or, sq_eq_zero_iff,
      Complex.ofReal_eq_zero, norm_eq_zero]
    exact x.property
  simp_rw [starRingEnd_apply, star_div₀, star_one, Complex.star_def, ← Complex.ofReal_pow,
    Complex.conj_ofReal, Complex.ofReal_pow, smul_right_inj this]
  simp_rw [← hx₂.eq, ← hxy, conjTranspose_smul, mul_smul_comm,
    LinearMap.mulLeft_smul, LinearMap.mulRight_smul, LinearMap.adjoint_smul, smul_mul_smul,
    starRingEnd_apply, mul_comm, LinearMap.matrix.mulRight_adjoint, conjTranspose_mul,
    hφ.matrixIsPosDef.1.eq, hy.eq, sig_apply_matrix_hMul_posDef']

theorem qamA.is_self_adjoint_iff [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) :
  withMatrixQuantum[φ]
    (LinearMap.adjoint (qamA hφ x) = qamA hφ x ↔
      x.1.IsAlmostHermitian ∧ Commute φ.matrix x.1) := by
  withMatrixQuantumCtx[φ]
  exact ⟨fun h => qamA.of_is_self_adjoint x h, fun h => qamA.is_self_adjoint_of x h.1 h.2⟩

theorem qamA.isRealQam [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) :
    withMatrixQuantum[φ]
      letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
      RealQam hφ (qamA hφ x) := by
  withMatrixQuantumCtx[φ]
  letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  exact ⟨qamA.is_idempotent _, qamA.isReal _⟩

open scoped ComplexOrder
omit [Fintype n] [DecidableEq n] in
theorem Matrix.PosDef.ne_zero [Finite n] [Nontrivial n] {Q : ℍ} (hQ : Q.PosDef) : Q ≠ 0 := by
  classical
  letI := Fintype.ofFinite n
  have := PosDef.trace_ne_zero hQ
  intro h
  rw [h, trace_zero] at this
  contradiction

theorem qamA.edges [hφ : φ.IsFaithfulPosMap] (x : { x : ℍ // x ≠ 0 }) :
    withMatrixQuantum[φ]
      letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
      (@qamA.isRealQam n _ _ φ hφ x).edges = 1 := by
  withMatrixQuantumCtx[φ]
  letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  rw [RealQam.edges_eq_one_iff]
  exact ⟨x, rfl⟩

theorem qamA.is_irreflexive_iff [hφ : φ.IsFaithfulPosMap] [Nontrivial n] (x : { x : ℍ // x ≠ 0 }) :
    withMatrixQuantum[φ]
      letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
      (Qam.reflIdempotent hφ (qamA hφ x) 1 = 0 ↔ x.1.trace = 0) := by
  withMatrixQuantumCtx[φ]
  letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  simp_rw [qamA_eq, ← rankOne_toMatrix_transpose_psi_symm]
  rw [← Function.Injective.eq_iff (hφ.psi (ψ := φ) 0 (1 / 2)).injective]
  simp_rw [Qam.reflIdempotent, Psi.schurMul_faithful, Psi.one, _root_.map_smul,
    LinearEquiv.apply_symm_apply, smul_mul_assoc, ←
    oneMapTranspose_symm_eq, ← _root_.map_mul, LinearEquiv.map_zero, smul_eq_zero,
      StarAlgEquiv.map_eq_zero_iff,
    AlgEquiv.map_eq_zero_iff, rankOne_eq_rankOneLm, one_div, inv_eq_zero, sq_eq_zero_iff,
    Complex.ofReal_eq_zero, norm_eq_zero, x.property, false_or,
    Module.End.mul_eq_comp, rankOneLm_comp_rankOneLm, smul_eq_zero, rankOneLm_eq_rankOne,
    ContinuousLinearMap.coe_eq_zero, rankOne.eq_zero_iff,
    Matrix.PosDef.ne_zero hφ.matrixIsPosDef.inv, or_false,
    x.property, or_false, Module.Dual.IsFaithfulPosMap.inner_eq']
  haveI := hφ.matrixIsPosDef.invertible
  rw [trace_mul_cycle, Matrix.mul_assoc, inv_mul_cancel_left_of_invertible, ← trace_star,
    star_eq_zero]

theorem qamA.is_almost_injective [hφ : φ.IsFaithfulPosMap] (x y : { x : ℍ // x ≠ 0 }) :
    withMatrixQuantum[φ]
      (qamA hφ x = qamA hφ y ↔ ∃ α : ℂˣ, x.1 = (α : ℂ) • y.1) := by
  withMatrixQuantumCtx[φ]
  simp_rw [qamA_eq, ← rankOne_toMatrix_transpose_psi_symm, ← _root_.map_smul, ←
    oneMapTranspose_symm_eq]
  rw [Function.Injective.eq_iff (hφ.psi _ _).symm.injective,
    Function.Injective.eq_iff (oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _).symm.injective,
    Function.Injective.eq_iff hφ.toMatrix.injective]
  have :
    ∀ x : { x : ℍ // x ≠ 0 },
      (1 / (‖x.1‖ : ℂ) ^ 2) • (|x.1⟩⟨x.1| : l(ℍ)) =
        |(1 / (‖x.1‖ : ℂ)) • x.1⟩⟨(1 / (‖x.1‖ : ℂ)) • x.1| := by
    intro y
    symm
    rw [show (1 / (‖y.1‖ : ℂ)) • y.1 =
        star (1 / (‖y.1‖ : ℂ)) • y.1 by
      simp [Complex.conj_ofReal]]
    rw [rankOne_lm_smul_smul]
    simp [Complex.conj_ofReal, sq]
  simp_rw [this, ContinuousLinearMap.coe_inj]
  constructor
  · intro h
    have hxnorm : ((1 / (‖x.1‖ : ℂ)) • x.1) ≠ 0 := by
      apply smul_ne_zero
      · simp [norm_ne_zero_iff.mpr x.property]
      · exact x.property
    have hynorm : ((1 / (‖y.1‖ : ℂ)) • y.1) ≠ 0 := by
      apply smul_ne_zero
      · simp [norm_ne_zero_iff.mpr y.property]
      · exact y.property
    obtain ⟨α, hα⟩ := rankOne.ext_iff hxnorm hynorm h
    let β := (‖x.1‖ : ℂ) * (α : ℂ) * (1 / (‖y.1‖ : ℂ))
    have : β ≠ 0 := by
      simp_rw [β, one_div]
      apply mul_ne_zero
      · apply mul_ne_zero
        · simp only [Complex.ofReal_ne_zero, norm_ne_zero_iff]
          exact x.property
        · exact Units.ne_zero _
      · apply inv_ne_zero
        simpa only [Complex.ofReal_ne_zero, norm_ne_zero_iff] using y.property
    use Units.mk0 β this
    simp_rw [Units.val_mk0, β, mul_assoc]
    rw [← smul_smul]
    rw [smul_smul] at hα
    rw [← hα, smul_smul, one_div, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr (x.property)), Complex.ofReal_one,
      one_smul]
  · rintro ⟨α, hα⟩
    simp_rw [← ContinuousLinearMap.coe_inj, ← this, hα, rankOne_eq_rankOneLm, rankOneLm_smul,
      smul_rankOneLm', smul_smul, norm_smul]
    simp [Complex.normSq_eq_norm_sq, Complex.mul_conj, Complex.ofReal_mul, one_div, mul_pow]

theorem qamA.is_reflexive_iff [hφ : φ.IsFaithfulPosMap] [Nontrivial n] (x : { x : ℍ // x ≠ 0 }) :
    withMatrixQuantum[φ]
      letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
      (Qam.reflIdempotent hφ (qamA hφ x) 1 = 1 ↔ ∃ α : ℂˣ, x.1 = (α : ℂ) • φ.matrix⁻¹) := by
  withMatrixQuantumCtx[φ]
  letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  simp_rw [qamA_eq, ← rankOne_toMatrix_transpose_psi_symm]
  rw [← Function.Injective.eq_iff (hφ.psi (ψ := φ) 0 (1 / 2)).injective]
  simp_rw [Qam.reflIdempotent, Psi.schurMul_faithful, Psi.one, _root_.map_smul,
    LinearEquiv.apply_symm_apply, smul_mul_assoc, ←
    oneMapTranspose_symm_eq, ← _root_.map_mul, ← _root_.map_smul]
  rw [Function.Injective.eq_iff (oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _).symm.injective,
    Function.Injective.eq_iff hφ.toMatrix.injective]
  simp_rw [rankOne_eq_rankOneLm, Module.End.mul_eq_comp, rankOneLm_comp_rankOneLm, ←
    smul_rankOneLm, rankOneLm_eq_rankOne, ContinuousLinearMap.coe_inj]
  rw [← sub_eq_zero]
  simp only [smul_smul]
  rw [rankOne.smul_right_to_left]
  have hstar :
      star (star ((1 : ℂ) / (↑‖x.1‖ : ℂ) ^ 2) *
          star (inner ℂ x.1 φ.matrix⁻¹)) =
        ((1 : ℂ) / (↑‖x.1‖ : ℂ) ^ 2) * inner ℂ x.1 φ.matrix⁻¹ := by
    simp
  rw [hstar, ← rankOne.left_sub, rankOne.eq_zero_iff]
  haveI := hφ.matrixIsPosDef.invertible
  simp only [sub_eq_zero, Module.Dual.IsFaithfulPosMap.inner_eq']
  rw [trace_mul_cycle, inv_mul_of_invertible, Matrix.one_mul, ← trace_star]
  simp only [hφ.matrixIsPosDef.inv.ne_zero, or_false]
  constructor
  · intro h
    simp_rw [← h, smul_smul]
    have : x.1.trace ≠ 0 := by
      intro h'
      rw [h', star_zero, MulZeroClass.mul_zero, zero_smul] at h
      exact hφ.matrixIsPosDef.inv.ne_zero h.symm
    have : 1 / ↑‖x.1‖ ^ 2 * star x.1.trace ≠ 0 := by
      apply mul_ne_zero
      · simp only [one_div, inv_eq_zero, ne_eq, sq_eq_zero_iff, Complex.ofReal_eq_zero,
          norm_eq_zero]
        exact x.property
      · simp only [ne_eq, star_eq_zero]
        exact this
    use Units.mk0 _ (inv_ne_zero this)
    rw [Units.val_mk0, inv_mul_cancel₀ this, one_smul]
  · rintro ⟨α, hx⟩
    simp_rw [hx, trace_smul, star_smul, norm_smul, trace_star]
    have : (‖φ.matrix⁻¹‖ : ℂ) ^ 2 = φ.matrix⁻¹.trace := by
      simp_rw [Complex.ofReal'_eq_isROrC_ofReal, ← inner_self_eq_norm_sq_to_K,
        Module.Dual.IsFaithfulPosMap.inner_eq',
        hφ.matrixIsPosDef.inv.1.eq, Matrix.mul_assoc, mul_inv_cancel_left_of_invertible]
    simp only [Complex.ofReal_mul, mul_pow, one_div, _root_.mul_inv_rev, this, smul_smul,
      smul_eq_mul]
    rw [mul_rotate, mul_rotate _ _ (α : ℂ), mul_assoc _ _ (star (α : ℂ)), Complex.star_def,
      Complex.mul_conj, mul_mul_mul_comm, Complex.normSq_eq_norm_sq, ←
      Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      hφ.matrixIsPosDef.inv.1.eq, mul_inv_cancel₀ (PosDef.trace_ne_zero hφ.matrixIsPosDef.inv),
      mul_inv_cancel₀, one_mul, Complex.ofReal_one, one_smul]
    simp only [ne_eq, sq_eq_zero_iff, norm_eq_zero, Units.ne_zero, not_false_iff]

theorem qamA.of_trivialGraph [hφ : φ.IsFaithfulPosMap] [Nontrivial n] [Nonempty n] :
    withMatrixQuantum[φ]
      letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
      letI : QuantumSetDeltaForm ℍ := Matrix.quantumSetDeltaForm (φ := φ)
      qamA hφ ⟨φ.matrix⁻¹, hφ.matrixIsPosDef.inv.ne_zero⟩ = Qam.trivialGraph ℍ := by
  withMatrixQuantumCtx[φ]
  letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  letI : QuantumSetDeltaForm ℍ := Matrix.quantumSetDeltaForm (φ := φ)
  rw [qamA_eq]
  haveI := hφ.matrixIsPosDef.invertible
  simp only [inv_mul_of_invertible, mul_inv_of_invertible, LinearMap.mulLeft_one,
    LinearMap.mulRight_one, ← Module.End.one_eq_id, LinearMap.adjoint_one, one_mul]
  have : ((‖φ.matrix⁻¹‖ : ℝ) : ℂ) ^ 2 = φ.matrix⁻¹.trace := by
    simp_rw [Complex.ofReal'_eq_isROrC_ofReal, ← inner_self_eq_norm_sq_to_K,
      Module.Dual.IsFaithfulPosMap.inner_eq',
      hφ.matrixIsPosDef.inv.1.eq, Matrix.mul_assoc, mul_inv_cancel_left_of_invertible]
  rw [this, one_div, Qam.trivialGraph_eq]
  change φ.matrix⁻¹.trace⁻¹ • (1 : l(ℍ)) = φ.matrix⁻¹.trace⁻¹ • (1 : l(ℍ))
  rfl

theorem Qam.unique_one_edge_and_refl [hφ : φ.IsFaithfulPosMap] [Nontrivial n] [Nonempty n]
    {A : l(ℍ)} :
    withMatrixQuantum[φ]
      letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
      letI : QuantumSetDeltaForm ℍ := Matrix.quantumSetDeltaForm (φ := φ)
      (hA : RealQam hφ A) →
      hA.edges = 1 ∧ Qam.reflIdempotent hφ A 1 = 1 ↔ A = Qam.trivialGraph ℍ := by
  withMatrixQuantumCtx[φ]
  letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  letI : QuantumSetDeltaForm ℍ := Matrix.quantumSetDeltaForm (φ := φ)
  intro hA
  constructor
  · rintro ⟨h1, h2⟩
    rw [RealQam.edges_eq_one_iff] at h1
    rcases h1 with ⟨x, rfl⟩
    rw [← qamA_eq] at h2
    rw [← qamA_eq, ← qamA.of_trivialGraph, qamA.is_almost_injective]
    exact (qamA.is_reflexive_iff x).mp h2
  · rintro rfl
    exact ⟨Qam.trivialGraph_edges, Qam.Nontracial.trivialGraph⟩

private theorem star_alg_equiv.is_isometry_iff [hφ : φ.IsFaithfulPosMap] [Nontrivial n] (f :
    ℍ ≃⋆ₐ[ℂ] ℍ) :
    withMatrixQuantum[φ] (StarAlgEquiv.IsIsometry f ↔ f φ.matrix = φ.matrix) := by
  withMatrixQuantumCtx[φ]
  rw [StarAlgEquiv.IsIsometry, isometry_iff_norm]
  exact List.TFAE.out
    (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ _ f) 4 0

-- The conjugation normal form produces large matrix expressions before simplification.
theorem qamA.isometric_starAlgEquiv_conj [hφ : φ.IsFaithfulPosMap] [Nontrivial n]
    (x : { x : ℍ // x ≠ 0 }) :
    withMatrixQuantum[φ]
      (∀ {f : ℍ ≃⋆ₐ[ℂ] ℍ}, StarAlgEquiv.IsIsometry f →
        f.toAlgEquiv.toLinearMap ∘ₗ qamA hφ x ∘ₗ f.symm.toAlgEquiv.toLinearMap =
          qamA hφ
            ⟨f x.1,
              (LinearEquiv.map_ne_zero_iff f.toAlgEquiv.toLinearEquiv).mpr x.property⟩) := by
  withMatrixQuantumCtx[φ]
  intro f hf
  apply_fun hφ.toMatrix using (AlgEquiv.injective _)
  have hf' := hf
  rw [star_alg_equiv.is_isometry_iff] at hf
  haveI := hφ.matrixIsPosDef.invertible
  have this2 : f φ.matrix⁻¹ = φ.matrix⁻¹ := by
    symm
    apply inv_eq_left_inv
    nth_rw 2 [← hf]
    rw [← _root_.map_mul, inv_mul_of_invertible, _root_.map_one]
  obtain ⟨U, rfl⟩ := f.of_matrix_is_inner
  have hU : Commute φ.matrix (U⁻¹ : unitaryGroup n ℂ) := by
    have hU' : Commute φ.matrix U :=
      (unitary_commutes_with_hφ_matrix_iff_isIsometry hφ U).mpr hf'
    have hU'' : Commute (star φ.matrix) U := by
      rw [star_eq_conjTranspose, hφ.matrixIsPosDef.1.eq]
      exact hU'
    exact hU''.star_right
  simp only [← Module.End.mul_eq_comp, _root_.map_mul, innerAutStarAlg_equiv_toLinearMap,
    innerAutStarAlg_equiv_symm_toLinearMap, InnerAut.toMatrix, qamA.toMatrix,
    Matrix.smul_mul, Matrix.mul_smul, ← mul_kronecker_mul, ← Matrix.conj_mul]
  let rpow := hφ.matrixIsPosDef.rpow
  have :=
    calc
      ((modAut (-(1 / 2)) : ℍ ≃ₐ[ℂ] ℍ) U) *
            (rpow (1 / 2) * x.1 * rpow (1 / 2) *
              ((modAut (-(1 / 2)) : ℍ ≃ₐ[ℂ] ℍ) (U⁻¹ : unitaryGroup n ℂ))) =
          rpow (1 / 2) * U * (rpow (-(1 / 2)) * rpow (1 / 2)) * x.1 *
                (rpow (1 / 2) * rpow (1 / 2)) *
              (U⁻¹ : unitaryGroup n ℂ) *
            rpow (-(1 / 2)) := by
          rw [show (modAut (-(1 / 2)) : ℍ ≃ₐ[ℂ] ℍ) = hφ.sig (-(1 / 2)) from rfl]
          simp only [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc, rpow, neg_neg]
      _ = rpow (1 / 2) * U * x.1 * (φ.matrix * (U⁻¹ : unitaryGroup n ℂ)) * rpow (-(1 / 2)) := by
        rw [PosDef.rpow_mul_rpow, PosDef.rpow_mul_rpow,
          neg_add_cancel, PosDef.rpow_zero, Matrix.mul_one,
          add_halves, PosDef.rpow_one_eq_self, Matrix.mul_assoc]
        simp_rw [mul_assoc]
      _ = rpow (1 / 2) * U * x.1 * (U⁻¹ : unitaryGroup n ℂ) * (rpow 1 * rpow (-(1 / 2))) := by
        simp_rw [hU.eq, rpow, PosDef.rpow_one_eq_self, mul_assoc]
      _ = rpow (1 / 2) * U * x.1 * (U⁻¹ : unitaryGroup n ℂ) * rpow (1 / 2) := by
        simp only [rpow, PosDef.rpow_mul_rpow]
        have : (1 : ℝ) + -(1 / 2 : ℝ) = 1 / 2 := by norm_num
        rw [this]
  have hnorm : ‖(innerAutStarAlg U) x.1‖ = ‖x.1‖ := by
    rw [StarAlgEquiv.IsIsometry, isometry_iff_norm] at hf'
    exact hf' x.1
  rw [this, hnorm]
  simp_rw [innerAutStarAlg_apply, Matrix.mul_assoc, hU.eq, UnitaryGroup.inv_apply,
    unitaryGroup.star_coe_eq_coe_star]
  simp only [rpow]

theorem qamA.iso_iff [hφ : φ.IsFaithfulPosMap] [Nontrivial n]
    {x y : { x : ℍ // x ≠ 0 }} :-- (hx : _root_.is_self_adjoint (qam_A hφ x))
        -- (hy : _root_.is_self_adjoint (qam_A hφ y))
        -- qam.iso (@qam_A.is_idempotent n _ _ φ hφ x) (qam_A.is_idempotent y)
        withMatrixQuantum[φ]
          (@Qam.Iso
            n _ _ φ (qamA hφ x) (qamA hφ y) ↔
          ∃ U : unitaryGroup n ℂ,
            (∃ β : ℂˣ, x.1 = innerAut U ((β : ℂ) • y.1)) ∧ Commute φ.matrix U) := by
  withMatrixQuantumCtx[φ]
  rw [Qam.iso_iff]
  simp_rw [← innerAutStarAlg_equiv_toLinearMap]
  constructor
  · rintro ⟨U, ⟨hU, hUU⟩⟩
    have hUUiso : StarAlgEquiv.IsIsometry (innerAutStarAlg U) :=
      (unitary_commutes_with_hφ_matrix_iff_isIsometry hφ U).mp hUU
    have hU' :
        qamA hφ x =
          (innerAutStarAlg U).toAlgEquiv.toLinearMap ∘ₗ qamA hφ y ∘ₗ
            (innerAutStarAlg U).symm.toAlgEquiv.toLinearMap := by
      refine LinearMap.ext fun z => ?_
      simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
        StarAlgEquiv.coe_toAlgEquiv, StarAlgEquiv.apply_symm_apply] using
        LinearMap.congr_fun hU ((innerAutStarAlg U).symm z)
    rw [qamA.isometric_starAlgEquiv_conj _ hUUiso, qamA.is_almost_injective,
      Subtype.coe_mk] at hU'
    use U
    constructor
    · simpa [_root_.map_smul, AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv] using hU'
    · exact hUU
  · rintro ⟨U, ⟨hU, hUU⟩⟩
    have hUUiso : StarAlgEquiv.IsIsometry (innerAutStarAlg U) :=
      (unitary_commutes_with_hφ_matrix_iff_isIsometry hφ U).mp hUU
    have hU' :
        qamA hφ x =
          (innerAutStarAlg U).toAlgEquiv.toLinearMap ∘ₗ qamA hφ y ∘ₗ
            (innerAutStarAlg U).symm.toAlgEquiv.toLinearMap := by
      rw [qamA.isometric_starAlgEquiv_conj _ hUUiso, qamA.is_almost_injective,
        Subtype.coe_mk]
      simpa [_root_.map_smul, AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv] using hU
    use U
    constructor
    · rw [hU']
      ext z
      simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
        StarAlgEquiv.coe_toAlgEquiv, StarAlgEquiv.symm_apply_apply]
    · exact hUU
