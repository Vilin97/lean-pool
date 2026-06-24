/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.QuantumGraph.Nontracial
import LeanPool.Monlib4.LinearAlgebra.Ips.MinimalProj
import LeanPool.Monlib4.QuantumGraph.Iso
import LeanPool.Monlib4.QuantumGraph.PiMatFinTwo

/-!

# Quantum graphs as projections

This file contains the definition of a quantum graph as a projection, and the proof that the

-/


variable {p : Type _} [Fintype p] [DecidableEq p] {n : p → Type _} [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (n i)]

open scoped TensorProduct BigOperators Kronecker Functional ComplexOrder

@[reducible]
local notation "ℍ" => Matrix p p ℂ
@[reducible]
local notation "ℍ_" i => Matrix (n i) (n i) ℂ

@[reducible]
local notation "l(" x ")" => x →ₗ[ℂ] x
@[reducible]
local notation "L(" x ")" => x →L[ℂ] x
@[reducible]
local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)

variable {φ : Module.Dual ℂ (Matrix p p ℂ)}

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

/-- Elaborate projection/QAM statements with the matrix coalgebra induced by `φ`. -/
syntax "withProjectionMatrixCoalgebraQuantum[" term "] " term : term
macro_rules
  | `(withProjectionMatrixCoalgebraQuantum[$φ] $p) =>
      `(withMatrixQuantum[$φ]
        letI : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
        $p)

/-- Introduce the projection matrix coalgebra context induced by `φ` in a proof. -/
syntax "withProjectionMatrixCoalgebraQuantumCtx" "[" term "]" : tactic
macro_rules
  | `(tactic| withProjectionMatrixCoalgebraQuantumCtx[$φ]) =>
      `(tactic|
        withMatrixQuantumCtx[$φ];
        letI : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra)

namespace FiniteDimensional

/-- Compatibility spelling for the old `FiniteDimensional.finrank` namespace. -/
noncomputable abbrev finrank (𝕜 E : Type*) [DivisionRing 𝕜] [AddCommGroup E]
    [Module 𝕜 E] : ℕ :=
  Module.finrank 𝕜 E

end FiniteDimensional

namespace Qam

/-- The reflexive idempotent product used in older Monlib quantum-graph files. -/
noncomputable abbrev reflIdempotent (hφ : φ.IsFaithfulPosMap) (A : l(ℍ)) :
    l(ℍ) →ₗ[ℂ] l(ℍ) := by
  letI : φ.IsFaithfulPosMap := hφ
  withProjectionMatrixCoalgebraQuantumCtx[φ]
  exact schurMul A

theorem isReal_and_idempotent_iff_psi_orthogonal_projection
    (hφ : φ.IsFaithfulPosMap) (A : l(ℍ)) :
    Qam.reflIdempotent hφ A A = A ∧ LinearMap.IsReal A ↔
      IsIdempotentElem ((hφ.psi (ψ := φ) 0 (1 / 2)) A) ∧
        IsSelfAdjoint ((hφ.psi (ψ := φ) 0 (1 / 2)) A) := by
  letI : φ.IsFaithfulPosMap := hφ
  withProjectionMatrixCoalgebraQuantumCtx[φ]
  change A •ₛ A = A ∧ LinearMap.IsReal A ↔
    IsIdempotentElem ((QuantumSet.Psi (A := ℍ) (B := ℍ) 0 (1 / 2)) A) ∧
      IsSelfAdjoint ((QuantumSet.Psi (A := ℍ) (B := ℍ) 0 (1 / 2)) A)
  rw [← schurIdempotent_iff_Psi_isIdempotentElem A 0 (1 / 2)]
  convert (and_congr_right ?_) using 1
  intro _
  rw [isReal_iff_Psi_isSelfAdjoint A, show QuantumSet.k ℍ = 0 by rfl]
  norm_num

end Qam

/-- Linear equivalence from block-diagonal matrix coordinates to the tensor product of
  block-diagonal matrices. -/
noncomputable def blockDiag'KroneckerEquiv {φ : ∀ i, Module.Dual ℂ (ℍ_ i)}
    (hφ : ∀ i, (φ i).IsFaithfulPosMap) :
    Matrix (Σ i, n i × n i) (Σ i, n i × n i) ℂ ≃ₗ[ℂ]
      { x : Matrix (Σ i, n i) (Σ i, n i) ℂ // x.IsBlockDiagonal } ⊗[ℂ]
        { x : Matrix (Σ i, n i) (Σ i, n i) ℂ // x.IsBlockDiagonal } :=
  ((Module.Dual.pi.IsFaithfulPosMap.toMatrix fun i => (hφ i)).symm.toLinearEquiv.trans
        ((Module.Dual.pi.IsFaithfulPosMap.psi hφ hφ 0 0).trans
          (LinearEquiv.TensorProduct.map (1 : (∀ i, Matrix (n i) (n i) ℂ) ≃ₗ[ℂ] _)
            (Pi.transposeAlgEquiv p n : _ ≃ₐ[ℂ] _ᵐᵒᵖ).symm.toLinearEquiv))).trans
    (LinearEquiv.TensorProduct.map isBlockDiagonalPiAlgEquiv.symm.toLinearEquiv
      isBlockDiagonalPiAlgEquiv.symm.toLinearEquiv)

theorem Matrix.conj_conjTranspose' {R n₁ n₂ : Type _} [InvolutiveStar R] (A : Matrix n₁ n₂ R) :
    (Aᴴᵀ)ᴴ = Aᵀ := by rw [← conj_conjTranspose A]

-- Porting the inherited block-diagonal matrix calculation needs more heartbeats after Mathlib
-- changes.
theorem toMatrix_mulLeft_mulRight_adjoint {φ : ∀ i, Module.Dual ℂ (Matrix (n i) (n i) ℂ)}
    (hφ : ∀ i, (φ i).IsFaithfulPosMap) (x y : ∀ i, ℍ_ i) :
    letI : ∀ i, (φ i).IsFaithfulPosMap := hφ
    withPiBlockQuantum[φ]
    ((Module.Dual.pi.IsFaithfulPosMap.toMatrix fun i => (hφ i))
        (LinearMap.mulLeft ℂ x * (LinearMap.adjoint (LinearMap.mulRight ℂ y) : l(∀ i, ℍ_ i))) =
      blockDiagonal' fun i => x i ⊗ₖ ((hφ i).sig (1 / 2) (y i))ᴴᵀ) := by
  letI : ∀ i, (φ i).IsFaithfulPosMap := hφ
  withPiBlockQuantumCtx[φ]
  simp_rw [_root_.map_mul, ← lmul_eq_mul, ← rmul_eq_mul, rmul_adjoint, pi_lmul_toMatrix,
    pi_rmul_toMatrix, ← blockDiagonal'_mul, ← mul_kronecker_mul]
  simp only [Matrix.mul_one, Matrix.one_mul]
  apply Matrix.blockDiagonal'_inj.mpr
  funext i
  rw [show (modAut (-QuantumSet.k ((i : p) → Matrix (n i) (n i) ℂ) - 1) (star y)) i =
      (hφ i).sig (-1) ((y i)ᴴ) by
    change (Module.Dual.pi.IsFaithfulPosMap.sig hφ
        (-QuantumSet.k ((i : p) → Matrix (n i) (n i) ℂ) - 1) (star y)) i =
      (hφ i).sig (-1) (y i)ᴴ
    rw [show QuantumSet.k ((i : p) → Matrix (n i) (n i) ℂ) = 0 by rfl]
    simp [Module.Dual.pi.IsFaithfulPosMap.sig_eq_pi_blocks, Pi.star_apply,
      star_eq_conjTranspose]]
  rw [show (hφ i).sig (1 / 2) ((hφ i).sig (-1) ((y i)ᴴ)) =
      ((hφ i).sig (1 / 2) (y i))ᴴ by
    rw [Module.Dual.IsFaithfulPosMap.sig_apply_sig]
    have : (1 / 2 : ℝ) + -1 = -(1 / 2) := by norm_num
    rw [this]
    exact (Module.Dual.IsFaithfulPosMap.sig_conjTranspose (hφ i) (1 / 2) (y i)).symm]
  rfl

/-- Apply a linear map between dependent products to a selected input and output component. -/
@[simps]
def Pi.LinearMap.apply {ι₁ ι₂ : Type _} {E₁ : ι₁ → Type _} [DecidableEq ι₁]
    [∀ i, AddCommMonoid (E₁ i)] [∀ i, Module ℂ (E₁ i)] {E₂ : ι₂ → Type _}
    [∀ i, AddCommMonoid (E₂ i)] [∀ i, Module ℂ (E₂ i)] (i : ι₁) (j : ι₂) :
    ((∀ a, E₁ a) →ₗ[ℂ] ∀ a, E₂ a) →ₗ[ℂ] E₁ i →ₗ[ℂ] E₂ j
    where
  toFun x :=
    { toFun := fun a => (x ((LinearMap.single ℂ E₁ i : E₁ i →ₗ[ℂ] ∀ b, E₁ b) a)) j
      map_add' := fun a b => by simp only [map_add, Pi.add_apply]
      map_smul' := fun c a => by
        simp only [LinearMap.map_smul, Pi.smul_apply, RingHom.id_apply] }
  map_add' x y := by
    ext a
    simp only [LinearMap.add_apply, Pi.add_apply, LinearMap.coe_mk]
    rfl
  map_smul' c x := by
    ext a
    simp only [LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply,
      LinearMap.coe_mk]
    rfl

-- The matrix/tensor rank-one calculation unfolds several equivalences after the Mathlib port.
theorem rankOne_psi_transpose_to_lin {n : Type _} [DecidableEq n] [Fintype n]
    {φ : Module.Dual ℂ (Matrix n n ℂ)} [hφ : φ.IsFaithfulPosMap] (x y : Matrix n n ℂ) :
    withMatrixQuantum[φ]
    (hφ.toMatrix.symm
        (TensorProduct.toKronecker
          ((TensorProduct.map (1 :
            l(Matrix n n ℂ)) (AlgEquiv.toLinearMap (transposeAlgEquiv n ℂ ℂ).symm))
            ((hφ.psi (ψ := φ) 0 (1 / 2)) |x⟩⟨y|))) =
      LinearMap.mulLeft ℂ x * (LinearMap.adjoint (LinearMap.mulRight ℂ y) : l(Matrix n n ℂ))) := by
  withMatrixQuantumCtx[φ]
  rw [← Function.Injective.eq_iff hφ.toMatrix.injective]
  simp_rw [_root_.map_mul, LinearMap.matrix.mulRight_adjoint, LinearMap.mulRight_toMatrix,
    LinearMap.mulLeft_toMatrix, ← mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Module.Dual.IsFaithfulPosMap.sig_apply_sig]
  have : (1 / 2 : ℝ) + -1 = -(1 / 2) := by norm_num
  rw [AlgEquiv.apply_symm_apply, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk]
  simp only [QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply, TensorProduct.map_tmul,
    TensorProduct.toKronecker_apply, Module.End.one_apply, AlgEquiv.toLinearMap_apply,
    LinearEquiv.coe_coe, transposeAlgEquiv_symm_op_apply]
  rw [starAlgebra.modAut_zero, this]
  simp only [AlgEquiv.one_apply]
  rw [show modAut (1 / 2) y = hφ.sig (1 / 2) y by rfl, Matrix.star_eq_conjTranspose,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose hφ (1 / 2) y]

private theorem matrix.stdBasisMatrix.transpose' {R n p : Type _} [DecidableEq n] [DecidableEq p]
    [Semiring R] {i : n} {j : p} {α : R} :
    (stdBasisMatrix i j α)ᵀ = stdBasisMatrix j i α := by
  ext
  simp [transpose_apply, stdBasisMatrix, single, and_comm]

theorem rankOne_toMatrix_transpose_psi_symm [hφ : φ.IsFaithfulPosMap]
  (x y : ℍ) :
    withMatrixQuantum[φ]
    ((hφ.psi (ψ := φ) 0 (1 / 2)).symm
        ((TensorProduct.map id (transposeAlgEquiv p ℂ ℂ).toLinearMap)
          (kroneckerToTensorProduct (hφ.toMatrix |x⟩⟨y|))) =
      LinearMap.mulLeft ℂ (x * φ.matrix) *
        (LinearMap.adjoint (LinearMap.mulRight ℂ (φ.matrix * y)) : l(ℍ))) := by
  withMatrixQuantumCtx[φ]
  have hbasis : hφ.basis = hφ.orthonormalBasis.toBasis := by
    ext ij i j
    simp [Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply,
      Module.Dual.IsFaithfulPosMap.basis_apply]
  rw [show hφ.toMatrix |x⟩⟨y| =
      LinearMap.toMatrix hφ.orthonormalBasis.toBasis hφ.orthonormalBasis.toBasis
        (|x⟩⟨y| : l(ℍ)) by
    ext i j
    simp [Module.Dual.IsFaithfulPosMap.toMatrix, hbasis, LinearMap.toMatrixAlgEquiv_apply,
      LinearMap.toMatrix_apply]]
  rw [rankOne_toMatrix_of_onb hφ.orthonormalBasis hφ.orthonormalBasis x y]
  simp only [Module.Dual.IsFaithfulPosMap.psi, Matrix.conjTranspose_replicateCol]
  rw [show
      replicateCol (Fin 1) (hφ.orthonormalBasis.repr x).ofLp *
          replicateRow (Fin 1) (star (hφ.orthonormalBasis.repr y).ofLp) =
        vecMulVec (hφ.orthonormalBasis.repr x).ofLp
          (star (hφ.orthonormalBasis.repr y).ofLp) from
    (Matrix.vecMulVec_eq (Fin 1) (hφ.orthonormalBasis.repr x).ofLp
      (star (hφ.orthonormalBasis.repr y).ofLp)).symm]
  rw [Matrix.kmul_representation
    (vecMulVec (hφ.orthonormalBasis.repr x).ofLp (star (hφ.orthonormalBasis.repr y).ofLp))]
  simp only [map_sum, _root_.map_smul, kroneckerToTensorProduct_apply,
    TensorProduct.map_tmul, QuantumSet.Psi_symm_apply, QuantumSet.PsiInvFun_apply,
    vecMulVec_apply, neg_zero, starAlgebra.modAut_zero, AlgEquiv.one_apply]
  simp_rw [AlgEquiv.toLinearMap_apply, transposeAlgEquiv_apply, MulOpposite.unop_op,
    Module.End.one_apply, ← rankOne_lm_smul_smul, Pi.star_apply, star_star,
    matrix.stdBasisMatrix.transpose', star_eq_conjTranspose, Matrix.single_conjTranspose,
    star_one]
  ext a i j
  simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_left,
    QuantumSet.modAut_isSymmetric, Module.End.mul_apply, LinearMap.matrix.mulRight_adjoint,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply, OrthonormalBasis.repr_apply_apply,
    inner_single_left, Module.Dual.IsFaithfulPosMap.inner_coord hφ]
  simp_rw [starRingEnd_apply, smul_smul, mul_assoc,
    ← mul_comm _ ((modAut (-(1 / 2)) (_ : ℍ) * φ.matrix) _ _)]
  rw [Finset.sum_sum_comm_sum]
  simp only [← Finset.sum_smul, ← Finset.mul_sum, ← mul_apply]
  simp_rw [mul_comm (star _), ← conjTranspose_apply, ← mul_apply, ← Matrix.smul_single']
  rw [show
      (∑ x_1, ∑ x_2, Matrix.single x_1 x_2
          ((x * hφ.matrixIsPosDef.rpow (1 / 2) *
              ((modAut (-(1 / 2)) : ℍ ≃ₐ[ℂ] ℍ) a * φ.matrix) *
                (y * hφ.matrixIsPosDef.rpow (1 / 2))ᴴ) x_1 x_2)) =
        x * hφ.matrixIsPosDef.rpow (1 / 2) *
          ((modAut (-(1 / 2)) : ℍ ≃ₐ[ℂ] ℍ) a * φ.matrix) *
            (y * hφ.matrixIsPosDef.rpow (1 / 2))ᴴ by
    exact (Matrix.matrix_eq_sum_single
      (x * hφ.matrixIsPosDef.rpow (1 / 2) *
        ((modAut (-(1 / 2)) : ℍ ≃ₐ[ℂ] ℍ) a * φ.matrix) *
          (y * hφ.matrixIsPosDef.rpow (1 / 2))ᴴ)).symm]
  rw [show (modAut (-(1 / 2)) : ℍ ≃ₐ[ℂ] ℍ) = hφ.sig (-(1 / 2)) from rfl]
  simp only [Module.Dual.IsFaithfulPosMap.sig_apply, conjTranspose_mul,
    (PosDef.rpow.isPosDef _ _).1.eq, hφ.matrixIsPosDef.1.eq]
  simp only [neg_neg]
  simp_rw [← mul_assoc]
  nth_rw 1 [mul_assoc x (hφ.matrixIsPosDef.rpow (1 / 2)) (hφ.matrixIsPosDef.rpow (1 / 2))]
  rw [show hφ.matrixIsPosDef.rpow (1 / 2) * hφ.matrixIsPosDef.rpow (1 / 2) =
      φ.matrix by
    rw [PosDef.rpow_mul_rpow, add_halves, PosDef.rpow_one_eq_self]]
  simp_rw [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  nth_rw 1 [mul_assoc (x * hφ.matrixIsPosDef.rpow 1 * a)
    (hφ.matrixIsPosDef.rpow (-(1 / 2))) (hφ.matrixIsPosDef.rpow 1)]
  rw [PosDef.rpow_mul_rpow]
  ring_nf
  nth_rw 1 [mul_assoc (x * hφ.matrixIsPosDef.rpow 1 * a *
    hφ.matrixIsPosDef.rpow 1 * yᴴ) (hφ.matrixIsPosDef.rpow 1)
      (hφ.matrixIsPosDef.rpow (-1))]
  rw [PosDef.rpow_mul_rpow]
  ring_nf
  simp only [PosDef.rpow_zero, mul_one]
  nth_rw 1 [mul_assoc (x * hφ.matrixIsPosDef.rpow 1 * a)
    (hφ.matrixIsPosDef.rpow (1 / 2)) (hφ.matrixIsPosDef.rpow (1 / 2))]
  rw [PosDef.rpow_mul_rpow]
  ring_nf

open LinearMap in
private theorem lm_to_clm_comp {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {p q : E →ₗ[𝕜] E} :
    toContinuousLinearMap p * toContinuousLinearMap q = toContinuousLinearMap (p * q) :=
  rfl

open LinearMap in
private theorem is_idempotent_elem_to_clm {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {p : E →ₗ[𝕜] E} :
    IsIdempotentElem p ↔ IsIdempotentElem (toContinuousLinearMap p) := by
  simp_rw [IsIdempotentElem, lm_to_clm_comp, Function.Injective.eq_iff (LinearEquiv.injective _)]

open scoped FiniteDimensional
open LinearMap in
private theorem is_self_adjoint_to_clm {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
    {p : E →ₗ[𝕜] E} :
    IsSelfAdjoint p ↔ IsSelfAdjoint (toContinuousLinearMap p) :=
  (LinearMap.isSelfAdjoint_toContinuousLinearMap p).symm

-- Orthogonal projection existence goes through finite-dimensional completeness and CLM coercions.
open LinearMap in
theorem orthogonal_projection_iff_lm {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {p : E →ₗ[𝕜] E} :
    (∃ U : Submodule 𝕜 E, (orthogonalProjection' U : E →ₗ[𝕜] E) = p) ↔
      IsSelfAdjoint p ∧ IsIdempotentElem p := by
  letI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have := @orthogonal_projection_iff 𝕜 E _ _ _ _ _ (toContinuousLinearMap p)
  simp_rw [is_idempotent_elem_to_clm, is_self_adjoint_to_clm] at this ⊢
  rw [← this]
  constructor
  all_goals
    rintro ⟨U, hU⟩
    use U
  · rw [← hU]
    rfl
  · rw [hU]
    rfl

theorem Matrix.conj_eq_transpose_conjTranspose {R n₁ n₂ : Type _} [Star R] (A : Matrix n₁ n₂ R) :
    Aᴴᵀ = (Aᵀ)ᴴ :=
  rfl

theorem Matrix.conj_eq_conjTranspose_transpose {R n₁ n₂ : Type _} [Star R] (A : Matrix n₁ n₂ R) :
    Aᴴᵀ = (Aᴴ)ᵀ :=
  rfl

theorem Matrix.star_transpose_eq_star_transpose {R n : Type _} [Star R] (A : Matrix n n R) :
    (star A)ᵀ = star Aᵀ :=
  rfl

-- Star preservation for this tensor-product algebra equivalence requires deep instance search.
/-- Star algebra equivalence between a matrix tensor product and matrices on product indices. -/
noncomputable def oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] Matrix (p × p) (p × p) ℂ :=
  StarAlgEquiv.ofAlgEquiv
    ((AlgEquiv.TensorProduct.map (1 : ℍ ≃ₐ[ℂ] ℍ) (transposeAlgEquiv p ℂ ℂ).symm).trans
      tensorToKronecker)
    (by
      let F : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃ₐ[ℂ] Matrix (p × p) (p × p) ℂ :=
        (AlgEquiv.TensorProduct.map (1 : ℍ ≃ₐ[ℂ] ℍ) (transposeAlgEquiv p ℂ ℂ).symm).trans
          tensorToKronecker
      change ∀ x, F (star x) = star (F x)
      intro x
      refine x.induction_on ?zero ?tmul ?add
      · simp only [star_zero, map_zero]
      · intro x₁ x₂
        simp [F, TensorProduct.star_tmul, AlgEquiv.TensorProduct.map_tmul,
          tensorToKronecker_apply, TensorProduct.toKronecker_star]
        rfl
      · intro a b ha hb
        calc
          F (star (a + b)) = F (star a + star b) := by rw [star_add]
          _ = F (star a) + F (star b) := F.map_add (star a) (star b)
          _ = star (F a) + star (F b) := by rw [ha, hb]
          _ = star (F a + F b) := by rw [star_add]
          _ = star (F (a + b)) := by
            rw [show F (a + b) = F a + F b from F.map_add a b])

theorem oneMapTranspose_eq (x : ℍ ⊗[ℂ] ℍᵐᵒᵖ) :
    (oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _) x =
      TensorProduct.toKronecker
        ((TensorProduct.map (1 : l(ℍ)) (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap) x) :=
  rfl

theorem oneMapTranspose_symm_eq (x : Matrix (p × p) (p × p) ℂ) :
    (oneMapTranspose : ℍ ⊗[ℂ] ℍᵐᵒᵖ ≃⋆ₐ[ℂ] _).symm x =
      (TensorProduct.map (1 : l(ℍ)) (transposeAlgEquiv p ℂ ℂ).toLinearMap)
        (Matrix.kroneckerToTensorProduct x) :=
  rfl

theorem oneMapTranspose_apply (x y : ℍ) :
    (oneMapTranspose : _ ≃⋆ₐ[ℂ] Matrix (p × p) (p × p) ℂ) (x ⊗ₜ MulOpposite.op y) = x ⊗ₖ yᵀ := by
  rw [oneMapTranspose_eq, TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply,
    TensorProduct.toKronecker_apply, transposeAlgEquiv_symm_op_apply]
  rfl

theorem toMatrix''_map_star [hφ : φ.IsFaithfulPosMap] (x : l(ℍ)) :
    withMatrixQuantum[φ]
    (hφ.toMatrix (LinearMap.adjoint (x : l(ℍ))) = star (hφ.toMatrix x)) := by
  withMatrixQuantumCtx[φ]
  ext
  simp only [Module.Dual.IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv_apply,
    star_apply,
    LinearMap.adjoint_inner_right, RCLike.star_def, inner_conj_symm,
    Module.Dual.IsFaithfulPosMap.basis_repr_apply]

private theorem ffsugh [hφ : φ.IsFaithfulPosMap] {x : Matrix (p × p) (p × p) ℂ} {y : l(ℍ)} :
    hφ.toMatrix.symm x = y ↔ x = hφ.toMatrix y :=
  Equiv.symm_apply_eq _

theorem toMatrix''_symm_map_star [hφ : φ.IsFaithfulPosMap] (x : Matrix (p × p) (p × p) ℂ) :
    withMatrixQuantum[φ]
    (hφ.toMatrix.symm (star x) = LinearMap.adjoint (hφ.toMatrix.symm x)) := by
  withMatrixQuantumCtx[φ]
  rw [ffsugh, toMatrix''_map_star, AlgEquiv.apply_symm_apply]

/-- The orthogonal projection onto a submodule, using the finite-dimensional matrix context. -/
noncomputable def Qam.fdOrthogonalProjection [hφ : φ.IsFaithfulPosMap]
    (U : Submodule ℂ ℍ) : l(ℍ) := by
  withMatrixQuantumCtx[φ]
  letI : AddCommGroup U := Submodule.addCommGroup U
  letI : NormedAddCommGroup U := Submodule.normedAddCommGroup U
  letI : NormedSpace ℂ U := Submodule.normedSpace U
  letI : FiniteDimensional ℂ U :=
    Submodule.finiteDimensional_of_le (show U ≤ (⊤ : Submodule ℂ ℍ) from le_top)
  letI : ProperSpace U := FiniteDimensional.proper ℂ U
  let completeU : @CompleteSpace U PseudoMetricSpace.toUniformSpace := complete_of_proper
  letI : U.HasOrthogonalProjection :=
    @Submodule.HasOrthogonalProjection.ofCompleteSpace ℂ ℍ _ _ _ U completeU
  exact (orthogonalProjection' U : l(ℍ))

theorem Qam.fd_orthogonal_projection_iff_lm [hφ : φ.IsFaithfulPosMap] {q : l(ℍ)} :
    withMatrixQuantum[φ]
      ((∃ U : Submodule ℂ ℍ, Qam.fdOrthogonalProjection (φ := φ) U = q) ↔
        IsSelfAdjoint q ∧ IsIdempotentElem q) := by
  withMatrixQuantumCtx[φ]
  change (∃ U : Submodule ℂ ℍ, (orthogonalProjection' U : l(ℍ)) = q) ↔
    IsSelfAdjoint q ∧ IsIdempotentElem q
  exact orthogonal_projection_iff_lm

theorem Qam.fdOrthogonalProjection_eq_sum_rankOne [hφ : φ.IsFaithfulPosMap]
    {ι : Type _} [Fintype ι] {U : Submodule ℂ ℍ} :
    withMatrixQuantum[φ]
      (∀ b : OrthonormalBasis ι ℂ U,
        Qam.fdOrthogonalProjection (φ := φ) U =
          ∑ i : ι, ((rankOne ℂ (b i).1 (b i).1 : L(ℍ)) : l(ℍ))) := by
  withMatrixQuantumCtx[φ]
  intro b
  letI : AddCommGroup U := Submodule.addCommGroup U
  letI : NormedAddCommGroup U := Submodule.normedAddCommGroup U
  letI : NormedSpace ℂ U := Submodule.normedSpace U
  letI : FiniteDimensional ℂ U :=
    Submodule.finiteDimensional_of_le (show U ≤ (⊤ : Submodule ℂ ℍ) from le_top)
  letI : ProperSpace U := FiniteDimensional.proper ℂ U
  let completeU : @CompleteSpace U PseudoMetricSpace.toUniformSpace := complete_of_proper
  letI : U.HasOrthogonalProjection :=
    @Submodule.HasOrthogonalProjection.ofCompleteSpace ℂ ℍ _ _ _ U completeU
  unfold Qam.fdOrthogonalProjection
  change ((orthogonalProjection' U : L(ℍ)) : l(ℍ)) =
    ∑ i : ι, ((rankOne ℂ (b i).1 (b i).1 : L(ℍ)) : l(ℍ))
  rw [← ContinuousLinearMap.toLinearMap_sum,
    @OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne ι ℂ _ ℍ _ _ _ U completeU b]

theorem Qam.idempotent_and_real_iff_exists_ortho_proj [hφ : φ.IsFaithfulPosMap] (A : l(ℍ)) :
      withMatrixQuantum[φ]
      (Qam.reflIdempotent hφ A A = A ∧ LinearMap.IsReal A ↔
        ∃ U : Submodule ℂ ℍ,
          Qam.fdOrthogonalProjection (φ := φ) U =
            hφ.toMatrix.symm
              (TensorProduct.toKronecker
                ((TensorProduct.map id (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap)
                ((hφ.psi (ψ := φ) 0 (1 / 2)) A)))) := by
  withMatrixQuantumCtx[φ]
  rw [Qam.isReal_and_idempotent_iff_psi_orthogonal_projection,
    Qam.fd_orthogonal_projection_iff_lm, ← oneMapTranspose_eq, IsIdempotentElem.algEquiv,
    IsIdempotentElem.starAlgEquiv, and_comm]
  simp_rw [_root_.IsSelfAdjoint, LinearMap.star_eq_adjoint, ← toMatrix''_symm_map_star, ←
    map_star, Function.Injective.eq_iff (AlgEquiv.injective _),
    Function.Injective.eq_iff (StarAlgEquiv.injective _)]

/-- The submodule associated to an idempotent real quantum adjacency map. -/
noncomputable def Qam.submoduleOfIdempotentAndReal [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)}
    (hA1 : Qam.reflIdempotent hφ A A = A) (hA2 : LinearMap.IsReal A) : Submodule ℂ ℍ := by
  withMatrixQuantumCtx[φ]
  choose U _ using (Qam.idempotent_and_real_iff_exists_ortho_proj A).mp ⟨hA1, hA2⟩
  exact U

theorem Qam.orthogonalProjection'_eq [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)}
  (hA1 : Qam.reflIdempotent hφ A A = A) (hA2 : LinearMap.IsReal A) :
  withMatrixQuantum[φ]
  (Qam.fdOrthogonalProjection (φ := φ) (Qam.submoduleOfIdempotentAndReal hA1 hA2) =
    hφ.toMatrix.symm
      (TensorProduct.toKronecker
        ((TensorProduct.map id (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap)
          ((hφ.psi (ψ := φ) 0 (1 / 2)) A)))) := by
  withMatrixQuantumCtx[φ]
  exact (Qam.idempotent_and_real_iff_exists_ortho_proj A).mp ⟨hA1, hA2⟩ |>.choose_spec

/-- A canonical orthonormal basis for the submodule associated to an idempotent real QAM. -/
noncomputable def Qam.onbOfIdempotentAndReal [hφ : φ.IsFaithfulPosMap]
  {A : l(ℍ)} (hA1 : Qam.reflIdempotent hφ A A = A) (hA2 : LinearMap.IsReal A) :
  withMatrixQuantum[φ]
  (OrthonormalBasis (Fin (FiniteDimensional.finrank ℂ (Qam.submoduleOfIdempotentAndReal hA1 hA2)))
    ℂ (Qam.submoduleOfIdempotentAndReal hA1 hA2)) := by
  withMatrixQuantumCtx[φ]
  exact stdOrthonormalBasis ℂ _

-- The orthonormal-basis finrank index requires synthesizing the restored submodule structure.
theorem Qam.IdempotentAndReal.eq [hφ : φ.IsFaithfulPosMap]
  {A : l(ℍ)} (hA1 : Qam.reflIdempotent hφ A A = A)
  (hA2 : LinearMap.IsReal A) :
    withMatrixQuantum[φ]
    (A =
      ∑ i,
        LinearMap.mulLeft ℂ
          (((Qam.onbOfIdempotentAndReal hA1 hA2 i).1 * φ.matrix)) *
          (LinearMap.adjoint
            (LinearMap.mulRight ℂ
              (φ.matrix *
                (Qam.onbOfIdempotentAndReal hA1 hA2 i).1)))) := by
  withMatrixQuantumCtx[φ]
  let U := Qam.submoduleOfIdempotentAndReal hA1 hA2
  letI : AddCommGroup U := Submodule.addCommGroup U
  letI : NormedAddCommGroup U := Submodule.normedAddCommGroup U
  letI : NormedSpace ℂ U := Submodule.normedSpace U
  letI : FiniteDimensional ℂ U :=
    Submodule.finiteDimensional_of_le
      (show U ≤ (⊤ : Submodule ℂ ℍ) from le_top)
  simp_rw [← rankOne_toMatrix_transpose_psi_symm, ← map_sum, ←
    Qam.fdOrthogonalProjection_eq_sum_rankOne (Qam.onbOfIdempotentAndReal hA1 hA2),
    Qam.orthogonalProjection'_eq, AlgEquiv.apply_symm_apply]
  simp_rw [← oneMapTranspose_symm_eq, ← oneMapTranspose_eq, StarAlgEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

/-- Quantum adjacency maps that are both Schur-idempotent and real. -/
@[class]
structure RealQam (hφ : φ.IsFaithfulPosMap) (A : l(ℍ)) : Prop where
/-- The Schur idempotence condition. -/
toIdempotent : Qam.reflIdempotent hφ A A = A
/-- The realness condition. -/
toIsReal : LinearMap.IsReal A

lemma RealQam_iff [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)} :
  RealQam hφ A ↔ Qam.reflIdempotent hφ A A = A ∧ LinearMap.IsReal A :=
⟨fun h => ⟨h.toIdempotent, h.toIsReal⟩, fun h => ⟨h.1, h.2⟩⟩

theorem RealQam.add_iff [hφ : φ.IsFaithfulPosMap] {A B : ℍ →ₗ[ℂ] ℍ} (hA : RealQam hφ A) (hB :
    RealQam hφ B) :
    RealQam hφ (A + B) ↔ Qam.reflIdempotent hφ A B + Qam.reflIdempotent hφ B A = 0 := by
  simp only [RealQam_iff] at hA hB ⊢
  simp [map_add, LinearMap.add_apply, hA, hB, add_assoc, add_left_comm, add_comm,
    LinearMap.isReal_iff, LinearMap.real_add,
    (LinearMap.isReal_iff _).mp hA.2, (LinearMap.isReal_iff _).mp hB.2]

/-- The zero map as a real QAM. -/
theorem RealQam.zero [hφ : φ.IsFaithfulPosMap] : RealQam hφ (0 : l(ℍ)) := by
  simp_rw [RealQam_iff, LinearMap.map_zero, true_and]
  intro
  simp only [LinearMap.zero_apply, star_zero]

@[reducible, instance]
noncomputable def RealQam.hasZero [hφ : φ.IsFaithfulPosMap] :
    Zero { x // RealQam hφ x } where zero := ⟨0, RealQam.zero⟩

theorem Qam.reflIdempotent_zero [hφ : φ.IsFaithfulPosMap] (a : l(ℍ)) : Qam.reflIdempotent hφ a 0 =
  0 :=
  map_zero _

theorem Qam.zero_reflIdempotent [hφ : φ.IsFaithfulPosMap] (a : l(ℍ)) : Qam.reflIdempotent hφ 0 a =
  0 := by
  simp_rw [LinearMap.map_zero, LinearMap.zero_apply]

/-- Number of edges of a real QAM, computed as the rank of its associated submodule. -/
@[reducible]
noncomputable def RealQam.edges [hφ : φ.IsFaithfulPosMap] {x : l(ℍ)} (hx : RealQam hφ x) : ℕ :=
  FiniteDimensional.finrank ℂ (Qam.submoduleOfIdempotentAndReal hx.1 hx.2)

/-- Edge-count function on the subtype of real QAMs. -/
@[reducible]
noncomputable def RealQam.edges' [hφ : φ.IsFaithfulPosMap] : { x :
    ℍ →ₗ[ℂ] ℍ // RealQam hφ x } → ℕ := fun x =>
  FiniteDimensional.finrank ℂ
    (Qam.submoduleOfIdempotentAndReal (Set.mem_setOf.mp (Subtype.mem x)).1
      (Set.mem_setOf.mp (Subtype.mem x)).2)

theorem RealQam.edges_eq [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)} (hA : RealQam hφ A) :
    withMatrixQuantum[φ]
    ((hA.edges : ℂ) = (A φ.matrix⁻¹).trace) := by
  withMatrixQuantumCtx[φ]
  obtain ⟨hA1, hA2⟩ := hA
  symm
  nth_rw 1 [Qam.IdempotentAndReal.eq hA1 hA2]
  let U := Qam.submoduleOfIdempotentAndReal hA1 hA2
  simp_rw [LinearMap.sum_apply, LinearMap.matrix.mulRight_adjoint, Module.End.mul_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply, conjTranspose_mul,
    hφ.matrixIsPosDef.1.eq, ← Matrix.mul_assoc, sig_apply_matrix_hMul_posDef']
  have :
    ∀ x : Fin (FiniteDimensional.finrank ℂ ↥U),
      ((Qam.onbOfIdempotentAndReal hA1 hA2 x).1 * φ.matrix * φ.matrix⁻¹ * φ.matrix *
            (Qam.onbOfIdempotentAndReal hA1 hA2 x).1ᴴ).trace =
        1 := by
    intro x
    calc
      ((Qam.onbOfIdempotentAndReal hA1 hA2 x).1 * φ.matrix * φ.matrix⁻¹ * φ.matrix *
              (Qam.onbOfIdempotentAndReal hA1 hA2 x).1ᴴ).trace =
          ((Qam.onbOfIdempotentAndReal hA1 hA2 x).1 * hφ.matrixIsPosDef.rpow 1 *
                  hφ.matrixIsPosDef.rpow (-1) *
                φ.matrix *
              (Qam.onbOfIdempotentAndReal hA1 hA2 x).1ᴴ).trace :=
        by simp_rw [PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self]
      _ =
          ((Qam.onbOfIdempotentAndReal hA1 hA2 x).1 *
                  (hφ.matrixIsPosDef.rpow 1 * hφ.matrixIsPosDef.rpow (-1)) *
                φ.matrix *
              (Qam.onbOfIdempotentAndReal hA1 hA2 x).1ᴴ).trace :=
        by simp_rw [Matrix.mul_assoc]
      _ =
          ((Qam.onbOfIdempotentAndReal hA1 hA2 x).1 * φ.matrix *
              (Qam.onbOfIdempotentAndReal hA1 hA2 x).1ᴴ).trace :=
        by simp_rw [PosDef.rpow_mul_rpow, add_neg_cancel, PosDef.rpow_zero, Matrix.mul_one]
      _ = inner ℂ (Qam.onbOfIdempotentAndReal hA1 hA2 x).1
          (Qam.onbOfIdempotentAndReal hA1 hA2 x).1 := by
          rw [Module.Dual.IsFaithfulPosMap.inner_eq' hφ, ← trace_mul_cycle]
      _ = inner ℂ (Qam.onbOfIdempotentAndReal hA1 hA2 x)
          (Qam.onbOfIdempotentAndReal hA1 hA2 x) := rfl
      _ = 1 := by
        rw [← OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_self,
          PiLp.single_apply]
        simp_rw [if_true]
  simp_rw [trace_sum, ← Matrix.mul_assoc, this, Finset.sum_const, Finset.card_fin,
    Nat.smul_one_eq_cast]

theorem completeGraphRealQam [hφ : φ.IsFaithfulPosMap] :
    withProjectionMatrixCoalgebraQuantum[φ]
    (RealQam hφ (Qam.completeGraph ℍ ℍ)) := by
  withProjectionMatrixCoalgebraQuantumCtx[φ]
  exact ⟨Qam.Nontracial.CompleteGraph.qam, Qam.Nontracial.CompleteGraph.isReal⟩

theorem Qam.completeGraph_edges [hφ : φ.IsFaithfulPosMap] :
  withProjectionMatrixCoalgebraQuantum[φ]
  ((@completeGraphRealQam p _ _ φ hφ).edges =
    FiniteDimensional.finrank ℂ (⊤ : Submodule ℂ ℍ)) := by
  withProjectionMatrixCoalgebraQuantumCtx[φ]
  have this : (RealQam.edges completeGraphRealQam : ℂ) =
    (Qam.completeGraph ℍ ℍ φ.matrix⁻¹).trace := RealQam.edges_eq _
  haveI ig := hφ.matrixIsPosDef.invertible
  simp_rw [Qam.completeGraph, ContinuousLinearMap.coe_coe, rankOne_apply,
    Module.Dual.IsFaithfulPosMap.inner_eq', conjTranspose_one, Matrix.mul_one,
    mul_inv_of_invertible, trace_smul, smul_eq_mul, trace_one,
    ← Nat.cast_mul, Nat.cast_inj] at this
  simp_rw [Qam.completeGraph, finrank_top, Module.finrank_matrix, Module.finrank_self, mul_one]
  exact this

-- Matrix delta-form inference for the restored nontracial trivial graph is expensive here.
-- The theorem statement itself requires synthesizing the Matrix quantum-set delta-form instance.
theorem Qam.trivialGraphRealQam [hφ : φ.IsFaithfulPosMap] [Nonempty p] :
    withProjectionMatrixCoalgebraQuantum[φ]
    (letI : QuantumSetDeltaForm ℍ := Matrix.quantumSetDeltaForm (φ := φ)
     RealQam hφ (Qam.trivialGraph ℍ)) := by
  withProjectionMatrixCoalgebraQuantumCtx[φ]
  letI : QuantumSetDeltaForm ℍ := Matrix.quantumSetDeltaForm (φ := φ)
  exact ⟨Qam.Nontracial.TrivialGraph.qam, Qam.Nontracial.trivialGraph.isReal⟩

theorem Qam.trivialGraph_edges [hφ : φ.IsFaithfulPosMap] [Nonempty p] :
    withProjectionMatrixCoalgebraQuantum[φ]
    (letI : QuantumSetDeltaForm ℍ := Matrix.quantumSetDeltaForm (φ := φ)
     (@Qam.trivialGraphRealQam p _ _ φ hφ _).edges = 1) := by
  withProjectionMatrixCoalgebraQuantumCtx[φ]
  letI : QuantumSetDeltaForm ℍ := Matrix.quantumSetDeltaForm (φ := φ)
  have := RealQam.edges_eq (@Qam.trivialGraphRealQam p _ _ φ hφ _)
  nth_rw 2 [Qam.trivialGraph_eq] at this
  simp_rw [LinearMap.smul_apply, Module.End.one_apply, trace_smul, smul_eq_mul] at this
  rw [show QuantumSetDeltaForm.delta ℍ = φ.matrix⁻¹.trace by rfl] at this
  have hδ : φ.matrix⁻¹.trace ≠ 0 := ne_of_gt (Qam.Nontracial.delta_pos (φ := φ))
  rw [inv_mul_cancel₀ hδ] at this
  exact_mod_cast this

theorem RealQam.edges_eq_zero_iff [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)} (hA : RealQam hφ A) :
    hA.edges = 0 ↔ A = 0 := by
  constructor
  · intro h
    rw [RealQam.edges] at h
    have h' := h
    simp only [Submodule.finrank_eq_zero] at h
    rw [Qam.IdempotentAndReal.eq hA.1 hA.2]
    let u := Qam.onbOfIdempotentAndReal hA.1 hA.2
    apply Finset.sum_eq_zero
    intro i _
    rw [finrank_zero_iff_forall_zero.mp h' (u i)]
    norm_cast
    simp_rw [Matrix.zero_mul, LinearMap.mulLeft_zero_eq_zero, MulZeroClass.zero_mul]
  · intro h
    rw [← Nat.cast_inj (R := ℂ), RealQam.edges_eq, h, LinearMap.zero_apply, trace_zero]
    norm_cast

theorem psi_apply_complete_graph [hφ : φ.IsFaithfulPosMap] {t s : ℝ} :
    withMatrixQuantum[φ]
    (hφ.psi (ψ := φ) t s |(1 : ℍ)⟩⟨(1 : ℍ)| = 1) := by
  withMatrixQuantumCtx[φ]
  simp only [Module.Dual.IsFaithfulPosMap.psi,
    QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply, _root_.map_one]
  simp [star_one, MulOpposite.op_one, Algebra.TensorProduct.one_def]

lemma AlgEquiv.TensorProduct.map_toLinearMap' {R S T U V : Type _} [CommSemiring R]
  [Semiring S] [Semiring T] [Semiring U] [Semiring V]
  [Algebra R S] [Algebra R T] [Algebra R U] [Algebra R V]
  (f : S ≃ₐ[R] T) (g : U ≃ₐ[R] V) :
  (AlgEquiv.TensorProduct.map f g).toLinearMap =
    _root_.TensorProduct.map f.toLinearMap g.toLinearMap :=
rfl

lemma AlgEquiv.toLinearMap_one {R S : Type _} [CommSemiring R] [Semiring S] [Algebra R S] :
  (AlgEquiv.toLinearMap (1 : S ≃ₐ[R] S)) = 1 :=
rfl

theorem RealQam.edges_eq_dim_iff [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)} (hA : RealQam hφ A) :
    withMatrixQuantum[φ]
    (hA.edges = FiniteDimensional.finrank ℂ (⊤ : Submodule ℂ ℍ) ↔
      A = |(1 : ℍ)⟩⟨(1 : ℍ)|) := by
  withMatrixQuantumCtx[φ]
  constructor
  · intro h
    rw [RealQam.edges] at h
    simp only [finrank_top] at h
    let U := Qam.submoduleOfIdempotentAndReal hA.1 hA.2
    have hU : U = (⊤ : Submodule ℂ ℍ) := Submodule.eq_top_of_finrank_eq h
    rw [← Function.Injective.eq_iff (LinearEquiv.injective (hφ.psi (ψ := φ) 0 (1 / 2))),
      psi_apply_complete_graph]
    have t1 := Qam.orthogonalProjection'_eq hA.1 hA.2
    have : Qam.fdOrthogonalProjection (φ := φ) U = 1 := by
      rw [hU]
      unfold Qam.fdOrthogonalProjection
      change ((orthogonalProjection' (⊤ : Submodule ℂ ℍ) : L(ℍ)) : l(ℍ)) = 1
      rw [orthogonalProjection_of_top]
      rfl
    change Qam.fdOrthogonalProjection (φ := φ) U =
      hφ.toMatrix.symm
        (TensorProduct.toKronecker
          ((TensorProduct.map id (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap)
            ((hφ.psi (ψ := φ) 0 (1 / 2)) A))) at t1
    rw [this] at t1
    have this' := (AlgEquiv.eq_apply_iff_symm_eq _).mpr t1.symm
    simp_rw [_root_.map_one, ← tensorToKronecker_apply, MulEquivClass.map_eq_one_iff] at this'
    have this'' := AlgEquiv.TensorProduct.map_toLinearMap (1 :
      ℍ ≃ₐ[ℂ] ℍ) (transposeAlgEquiv p ℂ ℂ).symm
    rw [AlgEquiv.toLinearMap_one] at this''
    rw [← this'', AlgEquiv.toLinearMap_apply, MulEquivClass.map_eq_one_iff] at this'
    exact this'
  · intro h
    rw [← @Qam.completeGraph_edges p _ _ φ]
    simp_rw [← @Nat.cast_inj ℂ, RealQam.edges_eq, h]
    rfl

-- The dimension-one projection extraction uses finite-dimensional basis instance synthesis.
private theorem orthogonal_projection_of_dim_one {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {U : Submodule 𝕜 E}
    (hU : FiniteDimensional.finrank 𝕜 U = 1) :
    ∃ v : { x : E // (x : E) ≠ 0 },
      orthogonalProjection' U = (1 / (‖(v : E)‖ ^ 2 : 𝕜)) • rankOne 𝕜 (v : E) (v : E) := by
  let u : OrthonormalBasis (Fin 1) 𝕜 U := by
    rw [← hU]
    exact stdOrthonormalBasis 𝕜 U
  rw [OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne u, Fin.sum_univ_one]
  have hcc : (u 0 : E) ≠ 0 := by
    intro h
    exact (u.orthonormal.ne_zero 0) (Subtype.ext h)
  have : ‖(u 0 : E)‖ = 1 := by
    rw [@norm_eq_sqrt_re_inner 𝕜, Real.sqrt_eq_one]
    simp_rw [← Submodule.coe_inner, orthonormal_iff_ite.mp u.orthonormal, if_true,
      RCLike.one_re]
  use ⟨u 0, hcc⟩
  simp only [this, RCLike.ofReal_one, one_div_one, one_smul, one_pow]

lemma Complex.ofReal'_eq_isROrC_ofReal (a : ℝ) :
  (a : ℂ) = RCLike.ofReal a :=
rfl

-- set_option pp.explicit true in
theorem RealQam.edges_eq_one_iff [hφ : φ.IsFaithfulPosMap] {A : l(ℍ)} (hA : RealQam hφ A) :
    withMatrixQuantum[φ]
    (hA.edges = 1 ↔
      ∃ x : { x : ℍ // x ≠ 0 },
        A =
          (1 / (‖x.1‖ ^ 2 : ℂ)) •
            (LinearMap.mulLeft ℂ (x.1 * φ.matrix) *
              LinearMap.adjoint (LinearMap.mulRight ℂ (φ.matrix * x.1)))) := by
  withMatrixQuantumCtx[φ]
  constructor
  · intro h
    let h' := h
    rw [← @Nat.cast_inj ℂ, RealQam.edges_eq hA] at h'
    rw [RealQam.edges] at h
    let this : (hA.toIdempotent : ((Qam.reflIdempotent hφ) A) A = A) = hA.toIdempotent := rfl
    rw [this] at h
    obtain ⟨u, hu⟩ := orthogonal_projection_of_dim_one h
    let hu' : (u : ℍ) ≠ 0 := u.property
    use⟨u, hu'⟩
    let t1 := Qam.orthogonalProjection'_eq hA.toIdempotent hA.toIsReal
    simp_rw [← rankOne_toMatrix_transpose_psi_symm, ← LinearEquiv.map_smul,
      ← LinearMap.map_smul, ← _root_.map_smul,
      ← ContinuousLinearMap.toLinearMap_smul,
      Complex.ofReal'_eq_isROrC_ofReal, ← hu]
    simp_rw [LinearEquiv.eq_symm_apply, ← oneMapTranspose_symm_eq,
      StarAlgEquiv.eq_apply_iff_symm_eq,
      StarAlgEquiv.symm_symm, AlgEquiv.eq_apply_iff_symm_eq, oneMapTranspose_eq]
    rw [← t1]
    unfold Qam.fdOrthogonalProjection
    rfl
  · rintro ⟨x, rfl⟩
    letI := hφ.matrixIsPosDef.invertible
    have ugh : ((x : ℍ) * φ.matrix * (x : ℍ)ᴴ).trace = ‖(x : ℍ)‖ ^ 2 := by
      rw [← trace_mul_cycle, ← Module.Dual.IsFaithfulPosMap.inner_eq' hφ,
        inner_self_eq_norm_sq_to_K]
      rfl
    have := RealQam.edges_eq hA
    rw [← @Nat.cast_inj ℂ, this]
    simp only [LinearMap.smul_apply, trace_smul, Module.End.mul_apply,
      LinearMap.matrix.mulRight_adjoint, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      conjTranspose_mul, hφ.matrixIsPosDef.1.eq, sig_apply_matrix_hMul_posDef',
      inv_mul_cancel_left_of_invertible, ugh, smul_eq_mul, one_div] at this ⊢
    have this' : ((‖(x : ℍ)‖ : ℝ) ^ 2 : ℂ) ≠ (0 : ℂ) := by
      simp_rw [ne_eq, sq_eq_zero_iff, Complex.ofReal_eq_zero, norm_eq_zero]
      exact x.property
    --},
    rw [inv_mul_cancel₀ this', Nat.cast_one]

-- },
