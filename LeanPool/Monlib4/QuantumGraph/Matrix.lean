/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.QuantumGraph.PiMatFinTwo

/-!
# LeanPool.Monlib4.QuantumGraph.Matrix

Imported Lean Pool material for `LeanPool.Monlib4.QuantumGraph.Matrix`.
-/

open scoped Functional MatrixOrder ComplexOrder TensorProduct Matrix

open scoped Kronecker

variable {n : Type*} [Fintype n] [DecidableEq n]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} [hφ : φ.IsFaithfulPosMap]

/-- Elaborate a matrix quantum-graph statement with its finite-dimensional coalgebra. -/
syntax "withMatrixCoalgebraQuantum[" term "] " term : term
macro_rules
  | `(withMatrixCoalgebraQuantum[$φ] $p) =>
      `(withMatrixQuantum[$φ]
        letI : Coalgebra ℂ (Matrix n n ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
        $p)

/-- Introduce the matrix quantum-set and finite-dimensional coalgebra instances in a proof. -/
syntax "withMatrixCoalgebraQuantumCtx" "[" term "]" : tactic
macro_rules
  | `(tactic| withMatrixCoalgebraQuantumCtx[$φ]) =>
      `(tactic|
        withMatrixQuantumCtx[$φ];
        letI : Coalgebra ℂ (Matrix n n ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra)

theorem lmul_toMatrix (x : Matrix n n ℂ) :
  withMatrixQuantum[φ]
    (onb.toMatrix (lmul x) = x ⊗ₖ (1 : Matrix n n ℂ)) :=
by
  withMatrixQuantumCtx[φ]
  simp only [← Matrix.ext_iff, QuantumSet.n]
  intro i j
  simp_rw [OrthonormalBasis.toMatrix_apply, lmul_apply, Matrix.kroneckerMap_apply,
    onb, Module.Dual.IsFaithfulPosMap.inner_coord hφ,
    hφ.orthonormalBasis_apply, mul_assoc, Matrix.PosDef.rpow_mul_rpow,
    neg_add_cancel, Matrix.PosDef.rpow_zero, mul_one, Matrix.mul_apply,
    Matrix.single_eq, Matrix.one_apply, mul_boole, ite_and, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, eq_comm]

theorem rmul_toMatrix (x : Matrix n n ℂ) :
  withMatrixQuantum[φ]
    (onb.toMatrix (rmul x) = (1 : Matrix n n ℂ) ⊗ₖ (modAut (1 / 2) x)ᵀ) :=
by
  withMatrixQuantumCtx[φ]
  simp only [← Matrix.ext_iff, QuantumSet.n]
  intro i j
  simp_rw [OrthonormalBasis.toMatrix_apply, rmul_apply, Matrix.kroneckerMap_apply,
    onb, Module.Dual.IsFaithfulPosMap.inner_coord hφ,
    hφ.orthonormalBasis_apply, mul_assoc,
    modAut, ← mul_assoc (Matrix.PosDef.rpow _ _), ← sig_apply, Matrix.mul_apply,
    Matrix.single_eq, Matrix.one_apply, boole_mul, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, eq_comm]
  rfl

open Matrix

theorem Matrix.single_transpose {R n p : Type*} [DecidableEq n] [DecidableEq p]
    [Zero R] {i : n} {j : p} {α : R} :
    (single i j α)ᵀ = single j i α :=
by ext; simp_rw [transpose_apply, single, of_apply,  and_comm]

lemma Module.Dual.IsFaithfulPosMap.inner_coord_onb
  (y : Matrix n n ℂ) (i j : n) :
  withMatrixQuantum[φ]
    (inner ℂ (onb (i, j)) y = (y * hφ.matrixIsPosDef.rpow (1 / 2)) i j) :=
by
  withMatrixQuantumCtx[φ]
  exact hφ.inner_coord _ _

/-- Matrix transpose as a star-algebra equivalence to the opposite algebra. -/
noncomputable abbrev Matrix.transposeStarAlgEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
  Matrix ι ι ℂ ≃⋆ₐ[ℂ] (Matrix ι ι ℂ)ᵐᵒᵖ :=
StarAlgEquiv.ofAlgEquiv (transposeAlgEquiv ι ℂ ℂ) (fun _ => rfl)
theorem Matrix.transposeStarAlgEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
  (x : Matrix ι ι ℂ) :
  Matrix.transposeStarAlgEquiv ι x = MulOpposite.op (xᵀ) :=
rfl
theorem Matrix.transposeStarAlgEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
  (x : (Matrix ι ι ℂ)ᵐᵒᵖ) :
  (Matrix.transposeStarAlgEquiv ι).symm x = x.unopᵀ :=
rfl

theorem QuantumSet.Psi_symm_transpose_kroneckerToTensor_toMatrix_rankOne
  (x y : Matrix n n ℂ) :
  withMatrixQuantum[φ]
    ((QuantumSet.Psi 0 (1 / 2)).symm
      ((StarAlgEquiv.lTensor _ (transposeStarAlgEquiv n))
        (kroneckerToTensor
          (onb.toMatrix ((rankOne ℂ x y) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)))) =
    lmul (x * φ.matrix) * (LinearMap.adjoint (rmul (φ.matrix * y)))) :=
by
  withMatrixQuantumCtx[φ]
  simp only [← StarAlgEquiv.coe_toAlgEquiv,
    ← orthonormalBasis_toMatrix_eq_basis_toMatrix,
    LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply,
    rankOne_toMatrix_of_onb, conjTranspose_replicateCol]
  rw [show replicateCol (Fin 1) (onb.repr x).ofLp *
      replicateRow (Fin 1) (star (onb.repr y).ofLp) =
        vecMulVec (onb.repr x).ofLp (star (onb.repr y).ofLp) from
    (Matrix.vecMulVec_eq (Fin 1) (onb.repr x).ofLp
      (star (onb.repr y).ofLp)).symm]
  rw [Matrix.kmul_representation (vecMulVec _ _)]
  simp only [map_sum, _root_.map_smul, kroneckerToTensor, tensorToKronecker_symm_apply,
    kroneckerToTensorProduct_apply, StarAlgEquiv.coe_toAlgEquiv,
    StarAlgEquiv.lTensor_tmul, QuantumSet.Psi_symm_apply,
    QuantumSet.PsiInvFun_apply, vecMulVec_apply, neg_zero, starAlgebra.modAut_zero,
    transposeStarAlgEquiv_apply, MulOpposite.unop_op, AlgEquiv.one_apply]
  simp_rw [← rankOne_lm_smul_smul, Pi.star_apply, star_star,
    single_transpose, star_eq_conjTranspose, single_conjTranspose,
    star_one]
  ext1
  simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
    rankOne_apply, inner_smul_left, QuantumSet.modAut_isSymmetric,
    Module.End.mul_apply, rmul_adjoint, rmul_apply, lmul_apply,
    OrthonormalBasis.repr_apply_apply, inner_single_left,
    Module.Dual.IsFaithfulPosMap.inner_coord_onb (hφ := hφ)]
  simp_rw [starRingEnd_apply, smul_smul, mul_assoc,
    ← mul_comm _ ((modAut (-(1/2)) (_ : Matrix n n ℂ) * φ.matrix) _ _),
    ]
  rw [Finset.sum_sum_comm_sum]
  simp only [← Finset.sum_smul, ← Finset.mul_sum, ← mul_apply]
  rw [Matrix.k (φ := φ)]
  simp_rw [mul_comm (star _), ← conjTranspose_apply, ← mul_apply, ← smul_single',
    conjTranspose_apply, modAut, sig_apply, star_eq_conjTranspose, conjTranspose_mul,
    (PosDef.rpow.isPosDef _ _).1.eq, hφ.matrixIsPosDef.1.eq]
  rw [← matrix_eq_sum_single]
  rw [show (modAut (-(1 / 2)) : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) =
    hφ.sig (-(1 / 2)) from rfl]
  simp only [Module.Dual.IsFaithfulPosMap.sig_apply, neg_neg]
  simp_rw [← mul_assoc]
  nth_rw 1 [mul_assoc _ (PosDef.rpow _ _) (PosDef.rpow _ _)]
  rw [PosDef.rpow_mul_rpow]
  simp only [mul_assoc]
  nth_rw 5 [← mul_assoc]
  nth_rw 3 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  nth_rw 5 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  nth_rw 7 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  simp_rw [PosDef.rpow_mul_rpow]
  nth_rw 4 [← mul_assoc]
  rw [PosDef.rpow_mul_rpow]
  ring_nf
  simp only [PosDef.rpow_zero, mul_one]

theorem QuantumGraph.Real.matrix_isOrthogonalProjection
  : withMatrixCoalgebraQuantum[φ]
    ∀ {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}, (hA : QuantumGraph.Real _ A) →
    (ContinuousLinearMap.toLinearMapAlgEquiv.symm
    ((onb.toMatrix.symm (tensorToKronecker
    ((StarAlgEquiv.lTensor _ (transposeStarAlgEquiv n).symm)
      ((QuantumSet.Psi 0 (1 / 2)) A))))
        : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)).IsOrthogonalProjection :=
by
  withMatrixCoalgebraQuantumCtx[φ]
  intro A hA
  rw [ContinuousLinearMap.toLinearMapAlgEquiv_symm_apply,
    LinearMap.isOrthogonalProjection_iff]
  rw [IsIdempotentElem, ← _root_.map_mul, ← map_mul tensorToKronecker,
    ← map_mul (StarAlgEquiv.lTensor _ _), ← Psi.schurMul, hA.1]
  refine ⟨rfl, ?_⟩
  rw [isSelfAdjoint_iff, ← map_star]
  simp_rw [tensorToKronecker, AlgEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [TensorProduct.toKronecker_star, ← map_star]
  congr
  simpa [QuantumSet.k] using
    (quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp hA).2.star_eq

/-- The submodule corresponding to a real matrix quantum graph. -/
noncomputable def QuantumGraph.Real.matrixSubmodule
  : withMatrixCoalgebraQuantum[φ]
    ∀ {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}, (hA : QuantumGraph.Real _ A) →
      Submodule ℂ (Matrix n n ℂ) :=
by
  withMatrixCoalgebraQuantumCtx[φ]
  intro A hA
  choose U hU using orthogonal_projection_iff.mpr ((And.comm.mp
    (ContinuousLinearMap.isOrthogonalProjection_iff'.mp
    hA.matrix_isOrthogonalProjection)))
  exact U

lemma QuantumGraph.Real.matrix_orthogonalProjection_eq
  : withMatrixCoalgebraQuantum[φ]
    ∀ {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}, (hA : QuantumGraph.Real _ A) →
  orthogonalProjection' (hA.matrixSubmodule (φ := φ)) =
    ContinuousLinearMap.toLinearMapAlgEquiv.symm ((onb.toMatrix.symm
    (tensorToKronecker
      ((StarAlgEquiv.lTensor (Matrix n n ℂ)
        (transposeStarAlgEquiv n).symm)
        ((QuantumSet.Psi 0 (1 / 2)) A))))) :=
by
  withMatrixCoalgebraQuantumCtx[φ]
  intro A hA
  rw [matrixSubmodule]
  generalize_proofs
  (expose_names; exact pf_24)
-- QuantumGraph.Real.matrixSubmodule.proof_19 hA

theorem StarAlgEquiv.lTensor_symm {R A B C : Type*}
  [RCLike R] [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
  [StarAddMonoid A] [StarAddMonoid B] [StarAddMonoid C] [StarModule R A]
  [StarModule R B] [StarModule R C] [Module.Finite R A] [Module.Finite R B] [Module.Finite R C]
  (f : A ≃⋆ₐ[R] B) :
  (StarAlgEquiv.lTensor C f).symm = StarAlgEquiv.lTensor C f.symm :=
rfl

theorem QuantumGraph.Real.matrix_eq_of_orthonormalBasis
  : withMatrixCoalgebraQuantum[φ]
    ∀ {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}, (hA : QuantumGraph.Real _ A) →
    ∀ {ι : Type*} [Fintype ι],
    (u : OrthonormalBasis ι ℂ (hA.matrixSubmodule (φ := φ))) →
    A = ∑ i,
      lmul (R := ℂ) ((((u i : hA.matrixSubmodule (φ := φ)) : Matrix n n ℂ) * φ.matrix)) *
        (LinearMap.adjoint
          (rmul (R := ℂ)
            (φ.matrix * ((u i : hA.matrixSubmodule (φ := φ)) : Matrix n n ℂ)))) :=
by
  withMatrixCoalgebraQuantumCtx[φ]
  intro A hA ι _ u
  simp_rw [← QuantumSet.Psi_symm_transpose_kroneckerToTensor_toMatrix_rankOne]
  rw [← map_sum]
  rw [← map_sum (StarAlgEquiv.lTensor (Matrix n n ℂ) (transposeStarAlgEquiv n))]
  rw [← map_sum kroneckerToTensor]
  rw [← map_sum onb.toMatrix]
  rw [← ContinuousLinearMap.toLinearMap_sum]
  rw [← OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne u]
  rw [hA.matrix_orthogonalProjection_eq]
  simp only [ContinuousLinearMap.toLinearMapAlgEquiv_symm_apply]
  simp only [LinearMap.coe_toContinuousLinearMap,
    StarAlgEquiv.apply_symm_apply, kroneckerToTensor, tensorToKronecker]
  simp only [AlgEquiv.symm_apply_apply, ← StarAlgEquiv.lTensor_symm,
    StarAlgEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

theorem QuantumGraph.Real.matrixSubmodule_exists_orthonormalBasis
  : withMatrixCoalgebraQuantum[φ]
    ∀ {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}, (hA : QuantumGraph.Real _ A) →
  ∃ u : OrthonormalBasis
      (Fin (Module.finrank ℂ (hA.matrixSubmodule (φ := φ)))) ℂ
      (hA.matrixSubmodule (φ := φ)),
    A = ∑ i,
      lmul (R := ℂ) ((((u i : hA.matrixSubmodule (φ := φ)) : Matrix n n ℂ) * φ.matrix)) *
        (LinearMap.adjoint
          (rmul (R := ℂ)
            (φ.matrix * ((u i : hA.matrixSubmodule (φ := φ)) : Matrix n n ℂ)))) :=
by
  withMatrixCoalgebraQuantumCtx[φ]
  intro A hA
  exact ⟨stdOrthonormalBasis ℂ _, (hA.matrix_eq_of_orthonormalBasis _)⟩

/-- Rank-one real quantum graph generated by a norm-one matrix. -/
noncomputable abbrev QuantumGraph.Real.ofNormOneMatrix
  : withMatrixQuantum[φ]
    ({ x : Matrix n n ℂ // ‖x‖ = 1 } →
      Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :=
by
  withMatrixQuantumCtx[φ]
  exact fun u =>
    lmul (R := ℂ) (u * φ.matrix) *
      (LinearMap.adjoint (rmul (R := ℂ) (φ.matrix * u)))

-- theorem OrthonormalBasis.norm_eq_one
--   {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
--   [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι]
--   (u : OrthonormalBasis ι 𝕜 E) (i : ι) :
--     ‖u i‖ = 1 :=
-- by
--   rw [@norm_eq_sqrt_inner 𝕜, Real.sqrt_eq_one]
--   simp_rw [orthonormal_iff_ite.mp u.orthonormal, if_true, RCLike.one_re]

theorem orthogonalProjection'_of_finrank_eq_one
  {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] {U : Submodule 𝕜 E} (hU : Module.finrank 𝕜 U = 1) :
  letI : Module.Finite 𝕜 U := Module.finite_of_finrank_eq_succ hU;
  ∃ v : { x : E // ‖x‖ = 1 },
    orthogonalProjection' U = rankOne 𝕜 (v : E) (v : E) :=
by
  letI : Module.Finite 𝕜 U := Module.finite_of_finrank_eq_succ hU
  let u : OrthonormalBasis (Fin 1) 𝕜 U := by
    rw [← hU]; exact stdOrthonormalBasis 𝕜 U
  rw [u.orthogonalProjection'_eq_sum_rankOne, Fin.sum_univ_one]
  refine ⟨⟨u 0, u.norm_eq_one _⟩, rfl⟩

theorem QuantumSet.Psi_apply_matrix_one {n : Type*} [DecidableEq n] [Fintype n]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} [hφ : φ.IsFaithfulPosMap] :
    withMatrixQuantum[φ]
    (QuantumSet.Psi 0 (1 / 2) (1 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      (StarAlgEquiv.lTensor _ (transposeStarAlgEquiv n))
        (kroneckerToTensor
           (onb.toMatrix
            ((rankOne ℂ (φ.matrix⁻¹) (φ.matrix⁻¹) : Matrix n n ℂ →ₗ[ℂ] _))))) :=
by
  withMatrixQuantumCtx[φ]
  nth_rw 1 [←
    rankOne.sum_orthonormalBasis_eq_id_lm
      (@Module.Dual.IsFaithfulPosMap.orthonormalBasis n _ _ φ _)]
  simp only [map_sum, QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply,
    ← StarAlgEquiv.coe_toAlgEquiv,
    ← orthonormalBasis_toMatrix_eq_basis_toMatrix,
    LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply,
    rankOne_toMatrix_of_onb,
    ]
  simp_rw [StarAlgEquiv.coe_toAlgEquiv, StarAlgEquiv.eq_apply_iff_symm_eq,
    AlgEquiv.eq_apply_iff_symm_eq, map_sum, StarAlgEquiv.lTensor_symm_tmul,
      kroneckerToTensor_symm_apply,
    TensorProduct.toKronecker_apply, transposeStarAlgEquiv_symm_apply,
    MulOpposite.unop_op, starAlgebra.modAut_zero, AlgEquiv.one_apply,
    conjTranspose_replicateCol]
  rw [show replicateCol (Fin 1) (onb.repr φ.matrix⁻¹).ofLp *
      replicateRow (Fin 1) (star (onb.repr φ.matrix⁻¹).ofLp) =
        vecMulVec (onb.repr φ.matrix⁻¹).ofLp
          (star (onb.repr φ.matrix⁻¹).ofLp) from
    (Matrix.vecMulVec_eq (Fin 1) (onb.repr φ.matrix⁻¹).ofLp
      (star (onb.repr φ.matrix⁻¹).ofLp)).symm]
  have : ∀ x, modAut (1 / 2) (hφ.orthonormalBasis x)
    = (hφ.orthonormalBasis x.swap)ᴴ :=
  by
    intro x
    rw [show (modAut (1 / 2) : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) =
      hφ.sig (1 / 2) from rfl]
    simp only [Module.Dual.IsFaithfulPosMap.sig_apply, hφ.orthonormalBasis_apply,
      conjTranspose_mul,
      mul_assoc, PosDef.rpow_mul_rpow, neg_add_cancel, PosDef.rpow_zero,
      mul_one, (PosDef.rpow.isPosDef _ _).1.eq, single_conjTranspose,
      star_one]
    rfl
  simp only [this, star_eq_conjTranspose, conjTranspose_conjTranspose]
  ext
  simp only [Matrix.sum_apply, kroneckerMap_apply, vecMulVec_apply,
    Pi.star_apply, OrthonormalBasis.repr_apply_apply, transpose_apply,
    Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply, mul_apply,
    single_eq, boole_mul]
  simp_rw [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ite_mul, zero_mul,
    Prod.swap, mul_ite, mul_zero, Finset.sum_product_univ, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Module.Dual.IsFaithfulPosMap.inner_coord_onb,
    Module.Dual.IsFaithfulPosMap.inner_coord_onb (hφ := hφ),
    ← PosDef.rpow_neg_one_eq_inv_self hφ.matrixIsPosDef]
  simp only [PosDef.rpow_mul_rpow, mul_comm]
  ring_nf
  rw [← conjTranspose_apply, (PosDef.rpow.isPosDef _ _).1.eq]

theorem
  Module.Dual.IsFaithfulPosMap.inner_dualMatrix_right
  (x : Matrix n n ℂ) :
    withMatrixQuantum[φ]
      (inner ℂ x φ.matrix⁻¹ = star (x : Matrix n n ℂ).trace) :=
by
  withMatrixQuantumCtx[φ]
  simp only [hφ.inner_eq']
  letI := hφ.matrixIsPosDef.invertible
  rw [trace_mul_cycle, inv_mul_of_invertible, one_mul, trace_conjTranspose]

theorem QuantumGraph.Real.ofNormOneMatrix_is_irreflexive_iff
  [Nontrivial n] (x : { x : Matrix n n ℂ // ‖x‖ = 1 }) :
    withMatrixCoalgebraQuantum[φ]
      (ofNormOneMatrix (φ := φ) x •ₛ 1 = 0 ↔ (x : Matrix n n ℂ).trace = 0) :=
by
  withMatrixCoalgebraQuantumCtx[φ]
  simp_rw [ofNormOneMatrix,
    ← QuantumSet.Psi_symm_transpose_kroneckerToTensor_toMatrix_rankOne,
    ←
    Function.Injective.eq_iff (QuantumSet.Psi 0 (1 / 2)).injective,
    Psi.schurMul, LinearEquiv.apply_symm_apply, QuantumSet.Psi_apply_matrix_one]
  rw [← _root_.map_mul]
  rw [← _root_.map_mul]
  rw [← _root_.map_mul onb.toMatrix]
  rw [LinearEquiv.map_zero]
  simp only [map_eq_zero_iff _ (StarAlgEquiv.injective _),
    map_eq_zero_iff _ (AlgEquiv.injective _)]
  simp only [Module.End.mul_eq_comp, LinearMap.comp_rankOne,
    ContinuousLinearMap.coe_coe, rankOne_apply,
    ContinuousLinearMap.coe_eq_zero, rankOne.eq_zero_iff, smul_eq_zero,
    hφ.inner_dualMatrix_right, star_eq_zero]
  letI := hφ.matrixIsPosDef.invertible
  simp only [Invertible.ne_zero, or_false, ne_zero_of_norm_ne_zero
      (a := (x : Matrix n n ℂ))
      (by simp only [x.property, ne_eq, one_ne_zero, not_false_eq_true])]

/-- Normalize a nonzero vector to a unit vector. -/
noncomputable def normalizeOfNeZero {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {a : E} (ha : a ≠ 0) :
  { x : E // ‖x‖ = 1 } :=
by
  use ((1 / ‖a‖) : ℂ) • a
  rw [norm_smul, norm_div]
  simp only [norm_one, Complex.norm_real, norm_norm, one_div]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)

theorem Module.Dual.IsFaithfulPosMap.norm_sq_dualMatrix_inv :
  withMatrixQuantum[φ]
    ((‖φ.matrix⁻¹‖ : ℂ) ^ 2 = (φ.matrix⁻¹).trace) :=
by
  withMatrixQuantumCtx[φ]
  rw [← Complex.ofReal_pow, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  simp only [RCLike.re_to_complex]
  rw [hφ.inner_dualMatrix_right, ← trace_conjTranspose,
    hφ.matrixIsPosDef.inv.1.eq]
  refine Complex.conj_eq_iff_re.mp ?_
  simp only [starRingEnd_apply, ← trace_conjTranspose, hφ.matrixIsPosDef.inv.1.eq]

theorem QuantumGraph.Real.ofNormOneMatrix_eq_trivialGraph
  [Nontrivial n] :
    withMatrixCoalgebraQuantum[φ]
      letI : QuantumSetDeltaForm (Matrix n n ℂ) := Matrix.quantumSetDeltaForm (φ := φ)
      (ofNormOneMatrix (φ := φ) (hφ := hφ)
      (normalizeOfNeZero
        (hφ.matrixIsPosDef.inv.invertible.ne_zero))
    = Qam.trivialGraph (Matrix n n ℂ)) :=
by
  withMatrixCoalgebraQuantumCtx[φ]
  letI : QuantumSetDeltaForm (Matrix n n ℂ) := Matrix.quantumSetDeltaForm (φ := φ)
  letI := hφ.matrixIsPosDef.invertible
  simp only [ofNormOneMatrix, normalizeOfNeZero,
    Qam.trivialGraph_eq, smul_mul_assoc,
    inv_mul_of_invertible, rmul_adjoint, StarMul.star_mul, star_smul,
    _root_.map_smul]
  simp only [← StarMul.star_mul, mul_inv_of_invertible, star_one, _root_.map_one,
    rmul_one, lmul_one, one_mul, smul_smul, star_div₀]
  simp only [one_div, RCLike.star_def, Complex.conj_ofReal, ← pow_two]
  simp only [inv_pow]
  simp only [QuantumSetDeltaForm.delta, ← hφ.norm_sq_dualMatrix_inv]

theorem QuantumGraph.Real.ofNormOneMatrix_is_reflexive_iff
  [Nontrivial n] (x : { x : Matrix n n ℂ // ‖x‖ = 1 }) :
    withMatrixCoalgebraQuantum[φ]
      (ofNormOneMatrix (φ := φ) x •ₛ 1 = 1 ↔
      ∃ α : ℂˣ,
      (x : Matrix n n ℂ) = (α : ℂ) • φ.matrix⁻¹) :=
by
  withMatrixCoalgebraQuantumCtx[φ]
  simp_rw [ofNormOneMatrix,
    ← QuantumSet.Psi_symm_transpose_kroneckerToTensor_toMatrix_rankOne,
    ← Function.Injective.eq_iff (QuantumSet.Psi 0 (1 / 2)).injective,
    Psi.schurMul, LinearEquiv.apply_symm_apply, QuantumSet.Psi_apply_matrix_one]
  rw [← _root_.map_mul]
  rw [← _root_.map_mul]
  rw [← _root_.map_mul onb.toMatrix]
  simp only [(StarAlgEquiv.injective _).eq_iff, (AlgEquiv.injective _).eq_iff]
  simp only [Module.End.mul_eq_comp, LinearMap.comp_rankOne, ContinuousLinearMap.coe_coe,
    rankOne_apply, ContinuousLinearMap.coe_inj, hφ.inner_dualMatrix_right]
  rw [← sub_eq_zero]
  simp_rw [← LinearMap.sub_apply, ← map_sub]
  letI : Invertible (φ.matrix) := hφ.matrixIsPosDef.invertible
  rw [rankOne.eq_zero_iff, sub_eq_zero]
  simp only [Invertible.ne_zero, or_false, ← trace_conjTranspose]
  constructor
  · intro h
    rw [← h]
    have htrace : ((x : Matrix n n ℂ)ᴴ).trace ≠ 0 := by
      intro hx
      rw [hx, zero_smul, eq_comm] at h
      simp only [Invertible.ne_zero] at h
    let α := Units.mk0 (((x : Matrix n n ℂ)ᴴ).trace) htrace
    have hα : α = ((x : Matrix n n ℂ)ᴴ).trace := rfl
    use α⁻¹
    simp only [← hα, smul_smul, Units.inv_mul, one_smul]
  · intro ⟨α, hα⟩
    simp_rw [hα, conjTranspose_smul, trace_smul, hφ.matrixIsPosDef.inv.1.eq,
      smul_smul, smul_eq_mul]
    rw [mul_rotate _ _ (α : ℂ), mul_assoc _ _ (star (α : ℂ)), Complex.star_def,
      Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← hφ.norm_sq_dualMatrix_inv, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, ← mul_pow, mul_comm,
      ← norm_smul, ← hα, x.property, one_pow, Complex.ofReal_one, one_smul]

theorem Matrix.traceLinearMap_comp_tensorToKronecker {n : Type*} [DecidableEq n] [Fintype n] :
  Matrix.traceLinearMap (n × n) ℂ ℂ ∘ₗ TensorProduct.toKronecker
    = LinearMap.mul' ℂ _
       ∘ₗ (TensorProduct.map
         (Matrix.traceLinearMap n ℂ ℂ) (Matrix.traceLinearMap n ℂ ℂ)) :=
by ext; simp [TensorProduct.toKronecker_apply, trace_kronecker]

theorem traceLinearMap_comp_transposeStarAlgEquiv_symm
  {n : Type*} [DecidableEq n] [Fintype n] :
  traceLinearMap n ℂ ℂ ∘ₗ (transposeStarAlgEquiv n).symm.toLinearMap
    = traceLinearMap n ℂ ℂ ∘ₗ (unop ℂ).toLinearMap :=
by rfl

open scoped InnerProductSpace
theorem QuantumGraph.NumOfEdges_eq {A : Type*} [starAlgebra A] [QuantumSet A]
  (B : A →ₗ[ℂ] A) :
  QuantumGraph.NumOfEdges B = ⟪1, B 1⟫_ℂ :=
rfl

-- set_option maxHeartbeats 0 in
theorem QuantumGraph.Real.matrixSubmodule_finrank_eq_numOfEdges_of_counit_eq_trace
  : withMatrixCoalgebraQuantum[φ]
    (Coalgebra.counit (R := ℂ) (A := Matrix n n ℂ) = Matrix.traceLinearMap n ℂ ℂ) →
    ∀ {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ},
    (hA : QuantumGraph.Real _ A) →
  (Module.finrank ℂ (hA.matrixSubmodule (φ := φ)) : ℂ) = QuantumGraph.NumOfEdges A :=
by
  withMatrixCoalgebraQuantumCtx[φ]
  intro hc A hA
  simp only [← _root_.orthogonalProjection_trace, hA.matrix_orthogonalProjection_eq]
  simp only [ContinuousLinearMap.toLinearMapAlgEquiv_symm_apply]
  simp only [LinearMap.coe_toContinuousLinearMap]
  rw [LinearMap.trace_eq_matrix_trace ℂ onb.toBasis]
  have htoMatrix :
      (LinearMap.toMatrix onb.toBasis onb.toBasis) =
        (onb.toMatrix :
          (Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) ≃⋆ₐ[ℂ]
            Matrix (n × n) (n × n) ℂ).toAlgEquiv.toLinearEquiv := by
    rw [← orthonormalBasis_toMatrix_eq_basis_toMatrix onb]
    rfl
  rw [htoMatrix]
  change (((onb.toMatrix :
      (Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) ≃⋆ₐ[ℂ]
        Matrix (n × n) (n × n) ℂ)
    ((onb.toMatrix :
      (Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) ≃⋆ₐ[ℂ]
        Matrix (n × n) (n × n) ℂ).symm
      (tensorToKronecker
        ((StarAlgEquiv.lTensor (Matrix n n ℂ) (transposeStarAlgEquiv n).symm)
          ((QuantumSet.Psi 0 (1 / 2)) A))))).trace) =
    (QuantumGraph.NumOfEdges A : ℂ)
  rw [StarAlgEquiv.apply_symm_apply]
  simp only [tensorToKronecker_apply]
  rw [← Matrix.traceLinearMap_apply _ ℂ, ← LinearMap.comp_apply]
  change (Matrix.traceLinearMap (n × n) ℂ ℂ ∘ₗ TensorProduct.toKronecker)
      ((StarAlgEquiv.lTensor (Matrix n n ℂ) (transposeStarAlgEquiv n).symm)
        ((QuantumSet.Psi 0 (1 / 2)) A)) =
    QuantumGraph.NumOfEdges A
  rw [Matrix.traceLinearMap_comp_tensorToKronecker]
  rw [← StarAlgEquiv.toLinearMap_apply,
    StarAlgEquiv.lTensor_toLinearMap, ← LinearMap.comp_apply,
    LinearMap.comp_assoc, LinearMap.map_comp_lTensor,
    traceLinearMap_comp_transposeStarAlgEquiv_symm]
  simp only [QuantumGraph.NumOfEdges_eq]
  rw [oneInner_map_one_eq_oneInner_Psi_map _ 0 (1 / 2)]
  rw [← bra_apply_apply ℂ (1 : Matrix n n ℂ ⊗[ℂ] (Matrix n n ℂ)ᵐᵒᵖ),
    ← ContinuousLinearMap.coe_coe,
    ← Coalgebra.counit_self_tensor_mulOpposite_eq_bra_one]
  simp only [TensorProduct.instCoalgebraStruct'_counit, hc, LinearMap.comp_apply]
  congr 1
  · apply TensorProduct.ext'
    simp [mul_comm]
  · rw [TensorProduct.AlgebraTensorModule.map_eq]
    change (TensorProduct.map (traceLinearMap n ℂ ℂ)
        (traceLinearMap n ℂ ℂ ∘ₗ (unop ℂ).toLinearMap)) ((QuantumSet.Psi 0 (1 / 2)) A) =
      (TensorProduct.map (traceLinearMap n ℂ ℂ)
        (Coalgebra.counit (R := ℂ) (A := (Matrix n n ℂ)ᵐᵒᵖ))) ((QuantumSet.Psi 0 (1 / 2)) A)
    rw [Coalgebra.counit_mulOpposite, hc]

theorem Matrix.traceLinearMap_dualMatrix_eq
  {n : Type*} [DecidableEq n] [Fintype n] :
  -- {φ : Module.Dual ℂ (Matrix n n ℂ)} [hφ : φ.IsFaithfulPosMap]
  -- (hc : Coalgebra.counit (R := ℂ) (A := Matrix n n ℂ) = Matrix.traceLinearMap n ℂ ℂ) :
  -- φ.matrix = 1 :=
  Module.Dual.matrix (Matrix.traceLinearMap n ℂ ℂ) = 1 :=
by
  refine Eq.symm (Module.Dual.apply_eq_of _ 1 (fun _ => ?_))
  simp only [one_mul]
  rfl

theorem QuantumGraph.Real.ofNormOneMatrix_eq_ofNormOneMatrix_iff
  {x y : { x : Matrix n n ℂ // ‖x‖ = 1 }} :
  withMatrixQuantum[φ]
    (ofNormOneMatrix (φ := φ) x = ofNormOneMatrix (φ := φ) y
      ↔ ∃ α : ℂˣ, (x : Matrix n n ℂ) = (α : ℂ) • (y : Matrix n n ℂ)) :=
by
  withMatrixQuantumCtx[φ]
  simp only [ofNormOneMatrix]
  simp only [← @QuantumSet.Psi_symm_transpose_kroneckerToTensor_toMatrix_rankOne,
    (LinearEquiv.injective _).eq_iff,
    (StarAlgEquiv.injective _).eq_iff, (AlgEquiv.injective _).eq_iff]
  constructor
  · simp_rw [ContinuousLinearMap.coe_inj];
    exact colinear_of_rankOne_self_eq_rankOne_self _ _
  · rintro ⟨α, hα⟩
    have := x.property
    simp only [hα, norm_smul, y.property, mul_one] at this
    simp only [hα, _root_.map_smul, map_smulₛₗ,
      LinearMap.smul_apply, ContinuousLinearMap.toLinearMap_smul]
    rw [smul_smul, RCLike.conj_mul, this, RCLike.ofReal_one, one_pow, one_smul]

theorem QuantumGraph.Real.reflexive_matrix_numOfEdges_eq_one_iff_eq_trivialGraph_of_counit_eq_trace
  [Nontrivial n]
  : withMatrixCoalgebraQuantum[φ]
    letI : QuantumSetDeltaForm (Matrix n n ℂ) := Matrix.quantumSetDeltaForm (φ := φ)
    (Coalgebra.counit (R := ℂ) (A := Matrix n n ℂ) = Matrix.traceLinearMap n ℂ ℂ) →
    ∀ {A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ}, (hA : QuantumGraph.Real _ A) →
      A •ₛ 1 = 1 →
      (QuantumGraph.NumOfEdges A = 1 ↔ A = Qam.trivialGraph _) :=
by
  withMatrixCoalgebraQuantumCtx[φ]
  letI : QuantumSetDeltaForm (Matrix n n ℂ) := Matrix.quantumSetDeltaForm (φ := φ)
  intro hc A hA hA₂
  constructor
  · rw [← matrixSubmodule_finrank_eq_numOfEdges_of_counit_eq_trace hc hA]
    simp only [Nat.cast_eq_one]
    letI := hφ.matrixIsPosDef.invertible
    intro h
    -- obtain ⟨u, hu⟩ := orthogonalProjection'_of_finrank_eq_one h
    let u : OrthonormalBasis (Fin 1) ℂ _ :=
      by rw [← h]; exact stdOrthonormalBasis ℂ (hA.matrixSubmodule (φ := φ))
    let u' : { x : Matrix n n ℂ // ‖x‖ = 1 } := ⟨u 0, u.norm_eq_one _⟩
    have : A = ofNormOneMatrix u' :=
      by
        rw [hA.matrix_eq_of_orthonormalBasis u]
        simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
        rfl
    rw [this, ← ofNormOneMatrix_eq_trivialGraph, ofNormOneMatrix_eq_ofNormOneMatrix_iff,
      normalizeOfNeZero]
    simp only [this] at *
    rw [ofNormOneMatrix_is_reflexive_iff (φ := φ) u'] at hA₂
    obtain ⟨α, hα⟩ := hA₂
    simp only [u'] at *
    let α' : ℂˣ := Units.mk0 ‖φ.matrix⁻¹‖ (by simp only [ne_eq, Complex.ofReal_eq_zero,
      norm_eq_zero, Invertible.ne_zero, not_false_eq_true])
    have hα' : α' = (‖φ.matrix⁻¹‖ : ℂ) := rfl
    use α * α'
    rw [hα]
    simp only [Units.val_mul, α', Units.val_mk0, smul_smul, one_div]
    simp only [← hα']
    simp only [isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true,
      IsUnit.mul_inv_cancel_right]
  · rintro rfl
    rw [QuantumGraph.NumOfEdges_eq, Qam.trivialGraph_eq,
      LinearMap.smul_apply, inner_smul_right, Module.End.one_apply]
    have : φ = Matrix.traceLinearMap n ℂ ℂ := by
      rw [← hc]; exact Eq.symm counit_eq_dual
    simp only [QuantumSetDeltaForm.delta, this,
      Matrix.traceLinearMap_dualMatrix_eq, inv_one,
      hφ.inner_eq', one_mul, conjTranspose_one]
    rw [inv_mul_cancel₀]
    simp only [trace_one, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]

theorem counit_eq_traceLinearMap_of_counit_eq_piMat_traceLinearMap
  {ι : Type*} [DecidableEq ι] [Fintype ι] {p : ι → Type*} [Π i, Fintype (p i)]
  [Π i, DecidableEq (p i)]
  {φ : Π i, Module.Dual ℂ (Matrix (p i) (p i) ℂ)}
  [hφ : Π i, (φ i).IsFaithfulPosMap]
  : withPiBlockCoalgebraQuantum[φ]
    letI := fun i => (Coalgebra.ofFiniteDimensionalHilbertAlgebra
      (R := ℂ) (A := Mat ℂ (p i)) : Coalgebra ℂ (Mat ℂ (p i)))
    (Coalgebra.counit (R := ℂ) (A := PiMat ℂ ι p) = PiMat.traceLinearMap) →
    ∀ i : ι,
      Coalgebra.counit (R := ℂ) (A := Mat ℂ (p i)) = traceLinearMap (p i) ℂ ℂ :=
by
  withPiBlockCoalgebraQuantumCtx[φ]
  letI := fun i => (Coalgebra.ofFiniteDimensionalHilbertAlgebra
    (R := ℂ) (A := Mat ℂ (p i)) : Coalgebra ℂ (Mat ℂ (p i)))
  intro hc i
  simp only [PiMat.counit_eq_dual, counit_eq_dual, LinearMap.ext_iff] at hc ⊢
  intro x
  specialize hc (includeBlock ((includeBlock x) i))
  rw [Module.Dual.pi.apply_single_block, includeBlock_apply_same] at hc
  rw [hc]
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    traceLinearMap_apply, blockDiagonal'AlgHom_apply, blockDiagonal'_includeBlock_trace']

theorem QuantumGraph.Real.PiMatFinTwo_same_isSelfAdjoint_reflexive_and_numOfEdges_eq_one
  {φ : Π i, Module.Dual ℂ (Matrix (PiFinTwoSame n i) (PiFinTwoSame n i) ℂ)}
  [hφ : Π i, (φ i).IsFaithfulPosMap]
  [Nontrivial n]
  : withPiBlockCoalgebraQuantum[φ]
    letI := fun i => (Coalgebra.ofFiniteDimensionalHilbertAlgebra
      (R := ℂ) (A := Mat ℂ (PiFinTwoSame n i)) :
        Coalgebra ℂ (Mat ℂ (PiFinTwoSame n i)))
    letI := fun i => (Matrix.quantumSetDeltaForm (φ := φ i) :
      QuantumSetDeltaForm (Mat ℂ (PiFinTwoSame n i)))
    (Coalgebra.counit (R := ℂ) (A := PiMat ℂ (Fin 2) (PiFinTwoSame n)) =
      PiMat.traceLinearMap) →
    ∀ {A : PiMat ℂ (Fin 2) (PiFinTwoSame n) →ₗ[ℂ]
        PiMat ℂ (Fin 2) (PiFinTwoSame n)},
    (hA : QuantumGraph.Real _ A) →
    LinearMap.adjoint A = A →
    A •ₛ 1 = 1 →
    QuantumGraph.NumOfEdges A = 1 →
  A = LinearMap.adjoint (LinearMap.proj 0)
    ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwoSame n 0))
    ∘ₗ LinearMap.proj 0
  ∨
  A = LinearMap.adjoint (LinearMap.proj 1)
    ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwoSame n 1))
    ∘ₗ LinearMap.proj 1 :=
by
    withPiBlockCoalgebraQuantumCtx[φ]
    letI := fun i => (Coalgebra.ofFiniteDimensionalHilbertAlgebra
      (R := ℂ) (A := Mat ℂ (PiFinTwoSame n i)) :
        Coalgebra ℂ (Mat ℂ (PiFinTwoSame n i)))
    letI := fun i => (Matrix.quantumSetDeltaForm (φ := φ i) :
      QuantumSetDeltaForm (Mat ℂ (PiFinTwoSame n i)))
    intro hc A hA hA₂ hA₃ hA₄
    obtain (hf | hf) := hA.piFinTwo_same_exists_matrix_map_eq_map_of_adjoint_and_dim_eq_one hA₂
      (by rw [← Nat.cast_inj (R := ℂ),
        QuantumGraph.dimOfPiMatSubmodule_eq_numOfEdges_of_trace_counit (hφ := hφ) hc, hA₄,
        Nat.cast_one])
    on_goal 1 =>
      let i : Fin 2 := 0
      let f := LinearMap.proj i ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj i)
      left
    on_goal 2 =>
      let i : Fin 2 := 1
      let f := LinearMap.proj i ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj i)
      right
    all_goals
      have hf₁ : f = LinearMap.proj i ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj i) := rfl
      have hf₂ : QuantumGraph.Real _ f := QuantumGraph.Real.conj_proj_isReal hA _
      have hf₃ : f •ₛ 1 = 1 := by
        let proj : PiMat ℂ (Fin 2) (PiFinTwoSame n) →ₗ[ℂ] Mat ℂ (PiFinTwoSame n i) :=
          LinearMap.proj i
        let adj : Mat ℂ (PiFinTwoSame n i) →ₗ[ℂ] PiMat ℂ (Fin 2) (PiFinTwoSame n) :=
          LinearMap.adjoint proj
        have hcomp : (proj ∘ₗ A ∘ₗ adj) •ₛ (proj ∘ₗ adj) =
            (proj ∘ₗ (A •ₛ 1)) ∘ₗ adj := by
          calc
            (proj ∘ₗ A ∘ₗ adj) •ₛ (proj ∘ₗ adj)
                = ((proj ∘ₗ A) •ₛ proj) ∘ₗ adj := by
                  simpa only [proj, adj, LinearMap.comp_assoc] using
                    (schurMul_comp_proj_adjoint (hφ := hφ) (LinearMap.proj i ∘ₗ A)
                      (LinearMap.proj i) i)
            _ = (proj ∘ₗ (A •ₛ 1)) ∘ₗ adj := by
                  congr 1
                  simpa only [proj, LinearMap.comp_one] using
                    (schurMul_proj_comp (hφ := hφ) A 1 i)
        rw [hf₁]
        change (proj ∘ₗ A ∘ₗ adj) •ₛ LinearMap.id = LinearMap.id
        simpa only [proj, adj, hA₃, LinearMap.one_comp, LinearMap.comp_one, LinearMap.proj_adjoint,
          LinearMap.proj_comp_single_same] using hcomp
      have hf₄ : QuantumGraph.NumOfEdges f = 1 := by
        rw [QuantumGraph.NumOfEdges_eq, ← hf] at hA₄
        simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right] at hA₄
        simp only [← LinearMap.comp_apply, ← LinearMap.comp_assoc] at hA₄
        rw [LinearMap.comp_assoc _ A _, ← hf₁, LinearMap.comp_apply, LinearMap.proj_apply,
          Pi.one_apply] at hA₄
        exact hA₄
      rw [reflexive_matrix_numOfEdges_eq_one_iff_eq_trivialGraph_of_counit_eq_trace
        (counit_eq_traceLinearMap_of_counit_eq_piMat_traceLinearMap hc _) hf₂ (by rw [hf₃])] at hf₄
      rw [← hf₄, hf₁]
      simp only [i, LinearMap.comp_assoc, hf]

/-- Isomorphism data between two quantum graphs via a star-algebra equivalence. -/
class QuantumGraph.equiv
    {A B : Type*} [starAlgebra A] [QuantumSet A] [starAlgebra B] [QuantumSet B]
    (x : A →ₗ[ℂ] A) (y : B →ₗ[ℂ] B) (f : A ≃⋆ₐ[ℂ] B) : Prop where
  /-- The equivalence is isometric. -/
  isIsometry : Isometry f
  /-- The equivalence intertwines the adjacency maps. -/
  prop : f.toLinearMap ∘ₗ x = y ∘ₗ f.toLinearMap

lemma QuantumGraph.equiv_prop {A B : Type*} [starAlgebra A] [QuantumSet A]
  [starAlgebra B] [QuantumSet B]
  (x : A →ₗ[ℂ] A) (y : B →ₗ[ℂ] B) {f : A ≃⋆ₐ[ℂ] B} (hf : QuantumGraph.equiv x y f) :
    f.toLinearMap ∘ₗ x = y ∘ₗ f.toLinearMap :=
hf.prop

lemma QuantumGraph.equiv_prop' {A B : Type*} [starAlgebra A] [QuantumSet A]
  [starAlgebra B] [QuantumSet B]
  (x : A →ₗ[ℂ] A) (y : B →ₗ[ℂ] B) {f : A ≃⋆ₐ[ℂ] B} (hf : QuantumGraph.equiv x y f) :
    f.toLinearMap ∘ₗ x ∘ₗ LinearMap.adjoint f.toLinearMap = y :=
by
  rw [← LinearMap.comp_assoc, hf.prop,
    QuantumSet.starAlgEquiv_isometry_iff_adjoint_eq_symm.mp hf.isIsometry,
    eq_comm, ← StarAlgEquiv.comp_eq_iff]

lemma Pi.eq_sum_single_proj (R : Type*) {ι : Type*} [Semiring R]
  [Fintype ι] [DecidableEq ι]
  {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)]
  [(i : ι) → Module R (φ i)]
  (x : Π i, φ i) :
  x = ∑ i, Pi.single (i : ι) (x i) :=
by
  simp_rw [← LinearMap.proj_apply (R := R) (φ := φ), ← LinearMap.single_apply (R:=R),
    ← LinearMap.comp_apply, ← LinearMap.sum_apply, LinearMap.sum_single_comp_proj]
  rfl

/-- Swap the two equal blocks of a `Fin 2`-indexed `PiMat` as a star-algebra equivalence. -/
noncomputable def PiMatFinTwoSameSwapStarAlgEquiv {n : Type*} [Fintype n] [DecidableEq n] :
  PiMat ℂ (Fin 2) (PiFinTwoSame n) ≃⋆ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwoSame n) :=
  StarAlgEquiv.ofAlgEquiv (PiMatFinTwoSameSwapAlgEquiv (n := n))
    (fun x => by
      rw [Pi.eq_sum_single_proj ℂ x]
      simp only [Fin.sum_univ_two, Fin.isValue, star_add, map_add, ← Pi.single_star,
        PiMatFinTwoSameSwapAlgEquiv_apply_piSingle_one,
        PiMatFinTwoSameSwapAlgEquiv_apply_piSingle_zero])

lemma PiMatFinTwoSameSwapStarAlgEquiv_apply {n : Type*} [Fintype n] [DecidableEq n]
  (x : PiMat ℂ (Fin 2) (PiFinTwoSame n)) :
  PiMatFinTwoSameSwapStarAlgEquiv x =
    Pi.single (0 : Fin 2) (x 1) + Pi.single (1 : Fin 2) (x 0) :=
by
  nth_rw 1 [Pi.eq_sum_single_proj ℂ x]
  simp only [Fin.sum_univ_two, Fin.isValue, map_add,
    PiMatFinTwoSameSwapStarAlgEquiv, StarAlgEquiv.ofAlgEquiv_coe,
    PiMatFinTwoSameSwapAlgEquiv_apply_piSingle_one,
    PiMatFinTwoSameSwapAlgEquiv_apply_piSingle_zero, add_comm]

lemma PiMatFinTwoSameSwapStarAlgEquiv_toAlgEquiv {n : Type*} [Fintype n] [DecidableEq n] :
  (PiMatFinTwoSameSwapStarAlgEquiv (n := n)).toAlgEquiv = PiMatFinTwoSameSwapAlgEquiv :=
rfl

theorem PiMatFinTwoSameSwapStarAlgEquiv_symm {n : Type*} [Fintype n] [DecidableEq n] :
  (PiMatFinTwoSameSwapStarAlgEquiv (n := n)).symm
    = PiMatFinTwoSameSwapStarAlgEquiv :=
rfl

/-- The constant two-block functional used for two identical matrix summands. -/
abbrev PiFinTwoSameFunctional {n : Type*}
    (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    (i : Fin 2) → Module.Dual ℂ
      (Matrix (PiFinTwoSame n i) (PiFinTwoSame n i) ℂ) :=
  fun _ => φ

lemma PiMatFinTwoSameSwapStarAlgEquiv_isometry :
  letI : ∀ i, (PiFinTwoSameFunctional φ i).IsFaithfulPosMap := fun _ => hφ
  withPiBlockQuantum[PiFinTwoSameFunctional φ]
    (LinearMap.adjoint PiMatFinTwoSameSwapStarAlgEquiv.toLinearMap
      = (PiMatFinTwoSameSwapStarAlgEquiv (n := n)).symm.toLinearMap) :=
by
  let ψ := PiFinTwoSameFunctional φ
  letI : ∀ i, (ψ i).IsFaithfulPosMap := fun _ => hφ
  withPiBlockQuantumCtx[ψ]
  simp only [PiMatFinTwoSameSwapStarAlgEquiv_symm]
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [LinearMap.adjoint_inner_right, StarAlgEquiv.toLinearMap_apply,
    PiMatFinTwoSameSwapStarAlgEquiv_apply]
  nth_rw 1 [Pi.eq_sum_single_proj ℂ x]
  nth_rw 3 [Pi.eq_sum_single_proj ℂ y]
  simp only [Fin.isValue, Fin.sum_univ_two]
  simp only [inner, Fin.isValue, Pi.add_apply, Fin.sum_univ_two,
    Pi.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true,
    Pi.single_eq_of_ne, add_comm, zero_add, one_ne_zero]
  rw [inner_pi_eq_sum (ψ := ψ)]
  simp [PiFinTwoSameFunctional, Module.Dual.IsFaithfulPosMap.inner_eq, Fin.sum_univ_two]
  simp [ψ, PiFinTwoSameFunctional]

theorem PiMatFinTwoSameSwapStarAlgEquiv_comp_linearMapSingle_zero
  {n : Type*} [Fintype n] [DecidableEq n] :
  (PiMatFinTwoSameSwapStarAlgEquiv (n := n)).toLinearMap
    ∘ₗ (LinearMap.single ℂ (fun (j : Fin 2) => Mat ℂ (PiFinTwoSame n j)) 0)
    = LinearMap.single ℂ (fun (j : Fin 2) => Mat ℂ (PiFinTwoSame n j)) 1 :=
PiMatFinTwoSameSwapAlgEquiv_comp_linearMapSingle_zero
theorem PiMatFinTwoSameSwapStarAlgEquiv_comp_linearMapSingle_one
  {n : Type*} [Fintype n] [DecidableEq n] :
  (PiMatFinTwoSameSwapStarAlgEquiv (n := n)).toLinearMap
    ∘ₗ (LinearMap.single ℂ (fun (j : Fin 2) => Mat ℂ (PiFinTwoSame n j)) 1)
    = LinearMap.single ℂ (fun (j : Fin 2) => Mat ℂ (PiFinTwoSame n j)) 0 :=
PiMatFinTwoSameSwapAlgEquiv_comp_linearMapSingle_one
theorem PiMat_finTwo_same_proj_zero_comp_swapStarAlgEquiv
  {n : Type*} [Fintype n] [DecidableEq n] :
  LinearMap.proj 0 ∘ₗ (PiMatFinTwoSameSwapStarAlgEquiv (n := n)).toLinearMap
    = LinearMap.proj 1 :=
rfl
theorem PiMat_finTwo_same_proj_one_comp_swapStarAlgEquiv
  {n : Type*} [Fintype n] [DecidableEq n] :
  LinearMap.proj 1 ∘ₗ (PiMatFinTwoSameSwapStarAlgEquiv (n := n)).toLinearMap
    = LinearMap.proj 0 :=
rfl

theorem
  QuantumGraph.Real.piMatFinTwo_same_eq_zero_of_isSelfAdjoint_and_reflexive_and_numOfEdges_eq_one
  [Nontrivial n]
  : letI : ∀ i, (PiFinTwoSameFunctional φ i).IsFaithfulPosMap := fun _ => hφ
    withPiBlockCoalgebraQuantum[PiFinTwoSameFunctional φ]
      (Coalgebra.counit (R := ℂ) (A := PiMat ℂ (Fin 2) (PiFinTwoSame n)) =
        PiMat.traceLinearMap) →
      ∀ {A : PiMat ℂ (Fin 2) (PiFinTwoSame n) →ₗ[ℂ]
          PiMat ℂ (Fin 2) (PiFinTwoSame n)},
      (hA : QuantumGraph.Real _ A) →
      LinearMap.adjoint A = A →
      A •ₛ 1 = 1 →
      QuantumGraph.NumOfEdges A = 1 →
      A = 0 :=
by
  let ψ := PiFinTwoSameFunctional φ
  letI : ∀ i, (ψ i).IsFaithfulPosMap := fun _ => hφ
  withPiBlockCoalgebraQuantumCtx[ψ]
  letI := fun i => (Coalgebra.ofFiniteDimensionalHilbertAlgebra
    (R := ℂ) (A := Mat ℂ (PiFinTwoSame n i)) :
      Coalgebra ℂ (Mat ℂ (PiFinTwoSame n i)))
  intro hc A hA hA₂ hA₃ hA₄
  rw [← QuantumGraph.dimOfPiMatSubmodule_eq_numOfEdges_of_trace_counit hc hA.toQuantumGraph,
    Nat.cast_eq_one] at hA₄
  obtain ⟨i, hi, hf⟩ :=
    hA.exists_unique_includeMap_of_adjoint_and_dim_ofPiMatSubmodule_eq_one hA₂ hA₄
  let p : (j : Fin 2) → PiMat ℂ (Fin 2) (PiFinTwoSame n) →ₗ[ℂ]
      Mat ℂ (PiFinTwoSame n j) := fun j => LinearMap.proj j
  have hp : ∀ j, p j = LinearMap.proj j := fun j => rfl
  have : ∀ j, p j ∘ₗ LinearMap.adjoint (p j) = 1 :=
  fun j => by
    simp only [LinearMap.proj_adjoint, p, Module.End.one_eq_id, LinearMap.proj_comp_single_same]
  have this' : ∀ j, (p j ∘ₗ A ∘ₗ LinearMap.adjoint (p j)) •ₛ 1 = 1 :=
  fun j => by
    calc (p j ∘ₗ A ∘ₗ LinearMap.adjoint (p j)) •ₛ 1
          = (p j ∘ₗ A ∘ₗ LinearMap.adjoint (p j) ∘ₗ 1) •ₛ (p j ∘ₗ 1 ∘ₗ LinearMap.adjoint (p j)) :=
            by simp only [LinearMap.one_comp, LinearMap.comp_one, this]
          _ = p j ∘ₗ ((A ∘ₗ LinearMap.adjoint (p j)) •ₛ (1 ∘ₗ LinearMap.adjoint (p j))) :=
              by
                simp only [p]
                rw [schurMul_proj_comp (hφ := fun _ => hφ)]
                simp only [LinearMap.comp_one]
          _ = p j ∘ₗ (A •ₛ 1) ∘ₗ LinearMap.adjoint (p j) :=
              by
                simp only [p]
                rw [schurMul_comp_proj_adjoint (hφ := fun _ => hφ)]
            _ = 1 := by simp only [hA₃, LinearMap.one_comp, this]
  have :=
  calc
    LinearMap.adjoint (p i) ∘ₗ p i + ∑ j ∈ Finset.univ \ {i}, LinearMap.adjoint (p j) ∘ₗ p j
      = ∑ j, LinearMap.adjoint (p j) ∘ₗ p j :=
        by
          simp only [Finset.subset_univ, Finset.sum_sdiff_eq_sub, Fin.sum_univ_two, Fin.isValue,
            Finset.sum_singleton, add_sub_cancel, p]
    _ = 1 :=
        by
          rw [Module.End.one_eq_id, ← LinearMap.sum_single_comp_proj]
          simp only [p, LinearMap.proj_adjoint]
    _ = A •ₛ 1 := hA₃.symm
    _ = ∑ j, (LinearMap.adjoint (p i) ∘ₗ (p i) ∘ₗ A ∘ₗ LinearMap.adjoint (p i) ∘ₗ (p i))
        •ₛ (LinearMap.adjoint (p j) ∘ₗ 1 ∘ₗ p j) :=
        by
          simp only [p, hi]
          simp_rw [← map_sum,
            LinearMap.one_comp]
          congr
          rw [Module.End.one_eq_id, ← LinearMap.sum_single_comp_proj]
          simp only [LinearMap.proj_adjoint]
    _ = (LinearMap.adjoint (p i) ∘ₗ (p i) ∘ₗ A ∘ₗ LinearMap.adjoint (p i) ∘ₗ (p i))
        •ₛ (LinearMap.adjoint (p i) ∘ₗ 1 ∘ₗ p i)
        + ∑ j ∈ Finset.univ \ {i},
          (LinearMap.adjoint (p i) ∘ₗ (p i) ∘ₗ A ∘ₗ LinearMap.adjoint (p i) ∘ₗ (p i))
          •ₛ (LinearMap.adjoint (p j) ∘ₗ 1 ∘ₗ p j) :=
        by
          simp only [schurMul_apply_apply, Fin.sum_univ_two, Fin.isValue, Finset.subset_univ,
            Finset.sum_sdiff_eq_sub, Finset.sum_singleton, add_sub_cancel,]
    _ = LinearMap.adjoint (p i) ∘ₗ p i :=
        by
          simp only [p, schurMul_proj_adjoint_comp]
          simp only [← LinearMap.comp_assoc, schurMul_comp_proj]
          simp only [LinearMap.comp_assoc, ← hp, this']
          simp only [LinearMap.one_comp, add_eq_left]
          apply Finset.sum_eq_zero
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
          push Not
          intro j hj
          rw [schurMul_proj_adjoint_comp_of_ne_eq_zero (hφ := fun _ => hφ) hj.symm]
  simp only [Finset.subset_univ, Finset.sum_sdiff_eq_sub, Fin.sum_univ_two, Fin.isValue,
    Finset.sum_singleton, add_sub_cancel, LinearMap.ext_iff, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.proj_adjoint_apply, funext_iff,
    Pi.add_apply, p] at this
  have hii : i = 0 ∨ i = 1 := Fin.exists_fin_two.mp ⟨i, rfl⟩
  specialize this 1 (if i = 0 then 1 else 0)
  rcases hii with (hii | hii)
  <;> rw [hii] at this
  <;> simp only [add_eq_left, add_eq_right, includeBlock_apply, dite_eq_right_iff] at this
  <;> simp only [Fin.isValue, ↓reduceIte, ↓dreduceIte, Pi.one_apply, eq_mp_eq_cast, cast_eq,
    one_ne_zero, imp_false, not_true_eq_false] at this

-- theorem QuantumGraph.Real.piMatFinTwo_same_isSelfAdjoint_reflexive_and_numOfEdges_eq_one_equiv
--   [Nontrivial n]
--   (hc : Coalgebra.counit (R := ℂ) (A := PiMat ℂ (Fin 2) (PiFinTwoSame n)) =
-- PiMat.traceLinearMap)
--   {A B : PiMat ℂ (Fin 2) (PiFinTwoSame n) →ₗ[ℂ] PiMat ℂ (Fin 2) (PiFinTwoSame n)}
--   (hA : QuantumGraph.Real _ A) (hA₂ : LinearMap.adjoint A = A) (hA₃ : A •ₛ 1 = 1)
--   (hA₄ : QuantumGraph.NumOfEdges A = 1)
--   (hB : QuantumGraph.Real _ B) (hB₂ : LinearMap.adjoint B = B) (hB₃ : B •ₛ 1 = 1)
--   (hB₄ : QuantumGraph.NumOfEdges B = 1) :
--   ∃ f : PiMat ℂ (Fin 2) (PiFinTwoSame n) ≃⋆ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwoSame n),
--     QuantumGraph.equiv A B f :=
-- by
--   have hA₅ := hA.PiMatFinTwo_same_isSelfAdjoint_reflexive_and_numOfEdges_eq_one hc hA₂ hA₃ hA₄
--   have hB₅ := hB.PiMatFinTwo_same_isSelfAdjoint_reflexive_and_numOfEdges_eq_one hc hB₂ hB₃ hB₄
--   have H1 : ∀ i : Fin 2, (A = LinearMap.adjoint (LinearMap.proj i)
--     ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwoSame n i)) ∘ₗ LinearMap.proj i
--     ∧ B = LinearMap.adjoint (LinearMap.proj i)
--     ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwoSame n i)) ∘ₗ LinearMap.proj i)
--     →
--     QuantumGraph.equiv A B (StarAlgEquiv.refl) :=
--   by
--     intro i h
--     refine ⟨fun x1 ↦ congrFun rfl, ?_⟩
--     apply LinearMap.ext
--     simp only [h, Fin.isValue, LinearMap.coe_comp, LinearMap.coe_proj, Function.comp_apply,
--       Function.eval, StarAlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_refl, id_eq, implies_true]
--   have H2 :
--     ((A = LinearMap.adjoint (LinearMap.proj 0)
--       ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwoSame n 0)) ∘ₗ LinearMap.proj 0
--     ∧ B = LinearMap.adjoint (LinearMap.proj 1)
--       ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwoSame n 1)) ∘ₗ LinearMap.proj 1)
--     ∨
--     (A = LinearMap.adjoint (LinearMap.proj 1)
--       ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwoSame n 1)) ∘ₗ LinearMap.proj 1
--     ∧ B = LinearMap.adjoint (LinearMap.proj 0)
--       ∘ₗ Qam.trivialGraph (Mat ℂ (PiFinTwoSame n 0)) ∘ₗ LinearMap.proj 0))
--     → QuantumGraph.equiv A B (PiMatFinTwoSameSwapStarAlgEquiv) :=
--   by
--     rintro (h | h)
--     all_goals
--       constructor
--       . rw [QuantumSet.starAlgEquiv_isometry_iff_adjoint_eq_symm]
--         exact PiMatFinTwoSameSwapStarAlgEquiv_isometry
--       . simp_rw [h.1, h.2, LinearMap.comp_assoc]
--         simp only [PiMat_finTwo_same_proj_one_comp_swapStarAlgEquiv,
--           PiMat_finTwo_same_proj_zero_comp_swapStarAlgEquiv,
--           ← LinearMap.comp_assoc, LinearMap.proj_adjoint,
--           PiMatFinTwoSameSwapStarAlgEquiv_comp_linearMapSingle_zero,
--           PiMatFinTwoSameSwapStarAlgEquiv_comp_linearMapSingle_one]
--   obtain (hf | hf) := hA₅
--   . obtain (hg | hg) := hB₅
--     . exact ⟨_, H1 _ ⟨hf, hg⟩⟩
--     . exact ⟨_, H2 (Or.inl ⟨hf, hg⟩)⟩
--   . obtain (hg | hg) := hB₅
--     . exact ⟨_, H2 (Or.inr ⟨hf, hg⟩)⟩
--     . exact ⟨_, H1 _ ⟨hf, hg⟩⟩
