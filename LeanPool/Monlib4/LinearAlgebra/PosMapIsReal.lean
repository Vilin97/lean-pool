/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.InnerAut
import LeanPool.Monlib4.LinearAlgebra.Matrix.IncludeBlock
import LeanPool.Monlib4.LinearAlgebra.InvariantSubmodule
import LeanPool.Monlib4.LinearAlgebra.Ips.MinimalProj
import LeanPool.Monlib4.LinearAlgebra.Nacgor
import Mathlib.Analysis.InnerProductSpace.StarOrder
import LeanPool.Monlib4.LinearAlgebra.OfNorm
import LeanPool.Monlib4.LinearAlgebra.Matrix.StarOrderedRing
import LeanPool.Monlib4.LinearAlgebra.Matrix.PosDefRpow
import LeanPool.Monlib4.LinearAlgebra.ToMatrixOfEquiv
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# LeanPool.Monlib4.LinearAlgebra.PosMapIsReal

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.PosMapIsReal`.
-/

variable {A : Type _} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [PartialOrder A]
  [_root_.StarOrderedRing A]

/-- we say a map $f \colon M_1 \to M_2$ is a positive map
  if for all positive $x \in M_1$, we also get $f(x)$ is positive -/
def LinearMap.IsPosMap
  {M₁ M₂ : Type*} [Zero M₁] [Zero M₂] [PartialOrder M₁] [PartialOrder M₂]
  {F : Type*} [FunLike F M₁ M₂] (f : F) : Prop :=
∀ ⦃x : M₁⦄, 0 ≤ x → 0 ≤ f x

/-- The self-adjoint real part of an element. -/
noncomputable abbrev selfAdjointDecompositionLeft
  {B : Type*} [Star B] [Add B] [SMul ℂ B] (a : B) :=
(1 / 2 : ℂ) • (a + star a)
local notation "aL" => selfAdjointDecompositionLeft

lemma selfAdjointDecompositionLeft_one
  {B : Type*} [AddCommMonoid B] [MulOneClass B] [StarMul B] [Module ℂ B] :
  aL (1 : B) = 1 := by
  rw [selfAdjointDecompositionLeft, star_one, ← two_smul ℂ, smul_smul]
  norm_num

/-- The self-adjoint imaginary part of an element. -/
noncomputable abbrev selfAdjointDecompositionRight
  {B : Type*} [Star B] [Sub B] [SMul ℂ B] (a : B) :=
(RCLike.I : ℂ) • ((1 / 2 : ℂ) • (star a - a))
local notation "aR" => selfAdjointDecompositionRight

lemma selfAdjointDecompositionRight_one
  {B : Type*} [AddCommGroup B] [MulOneClass B] [StarMul B] [SMulZeroClass ℂ B] :
    aR (1 : B) = 0 := by
  simp_rw [selfAdjointDecompositionRight, star_one, sub_self, smul_zero]

lemma selfAdjointDecompositionRight_eq_zero_iff
  {B : Type*} [Star B] [AddGroup B]
  [SMulWithZero ℂ B] [NoZeroSMulDivisors ℂ B] (a : B) :
    aR a = 0 ↔ IsSelfAdjoint a := by
  rw [isSelfAdjoint_iff]
  constructor
  · intro h
    have h1 : (1 / 2 : ℂ) • (star a - a) = 0 :=
      (eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left Complex.I_ne_zero
    have h2 : star a - a = 0 :=
      (eq_zero_or_eq_zero_of_smul_eq_zero h1).resolve_left
        (by norm_num : (1 / 2 : ℂ) ≠ 0)
    exact sub_eq_zero.mp h2
  · intro h
    simp [selfAdjointDecompositionRight, h]

theorem selfAdjointDecompositionLeft_isSelfAdjoint
  {B : Type*} [AddCommMonoid B] [StarAddMonoid B] [SMul ℂ B] [StarModule ℂ B] (a : B) :
    IsSelfAdjoint (aL a) :=
by simp [selfAdjointDecompositionLeft, isSelfAdjoint_iff, star_smul, add_comm]

theorem selfAdjointDecompositionRight_isSelfAdjoint
  {B : Type*} [AddCommGroup B] [StarAddMonoid B]
  [Module ℂ B] [StarModule ℂ B]
  (a : B) :
    IsSelfAdjoint (aR a) := by
  simp only [selfAdjointDecompositionRight, RCLike.I_to_complex, one_div, smul_smul,
    isSelfAdjoint_iff, star_smul, star_mul', RCLike.star_def, Complex.conj_I,
    star_inv₀, star_ofNat, neg_mul, star_sub, star_star, neg_smul]
  rw [← neg_sub, ← neg_smul, neg_smul_neg]

theorem selfAdjointDecomposition
  {B : Type*} [AddCommGroup B] [StarAddMonoid B]
  [Module ℂ B] [StarModule ℂ B] (a : B) :
  a = aL a + (RCLike.I : ℂ) • (aR a) := by
  simp_rw [selfAdjointDecompositionLeft, selfAdjointDecompositionRight,
    smul_smul, ← mul_assoc, RCLike.I, Complex.I_mul_I, smul_add, smul_sub,
    neg_mul, one_mul, neg_smul, neg_sub_neg]
  simp only [one_div, add_add_sub_cancel]
  simp_rw [← two_smul ℂ, smul_smul]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀, one_smul]

/-- The algebra equivalence between continuous endomorphisms and linear endomorphisms
in finite-dimensional inner product spaces. -/
noncomputable
def ContinuousLinearMap.toLinearMapAlgEquiv
  {𝕜 B : Type*} [RCLike 𝕜] [NormedAddCommGroup B]
  [InnerProductSpace 𝕜 B] [FiniteDimensional 𝕜 B] :
  (B →L[𝕜] B) ≃ₐ[𝕜] (B →ₗ[𝕜] B) :=
AlgEquiv.ofLinearEquiv LinearMap.toContinuousLinearMap.symm rfl (fun _ _ => rfl)

lemma ContinuousLinearMap.toLinearMapAlgEquiv_apply
  {𝕜 B : Type*} [RCLike 𝕜] [NormedAddCommGroup B]
  [InnerProductSpace 𝕜 B] [FiniteDimensional 𝕜 B]
  (f : B →L[𝕜] B) :
  ContinuousLinearMap.toLinearMapAlgEquiv f = f.toLinearMap :=
rfl

lemma ContinuousLinearMap.toLinearMapAlgEquiv_symm_apply
  {𝕜 B : Type*} [RCLike 𝕜] [NormedAddCommGroup B]
  [InnerProductSpace 𝕜 B] [FiniteDimensional 𝕜 B]
  (f : B →ₗ[𝕜] B) :
  ContinuousLinearMap.toLinearMapAlgEquiv.symm f = LinearMap.toContinuousLinearMap f :=
rfl

theorem ContinuousLinearMap.spectrum_coe {𝕜 B : Type*} [RCLike 𝕜] [NormedAddCommGroup B]
  [InnerProductSpace 𝕜 B] [FiniteDimensional 𝕜 B] (T : B →L[𝕜] B) :
  spectrum 𝕜 T.toLinearMap = spectrum 𝕜 T :=
by rw [← ContinuousLinearMap.toLinearMapAlgEquiv_apply, AlgEquiv.spectrum_eq]

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [FiniteDimensional ℂ B]

open scoped MatrixOrder ComplexOrder FiniteDimensional
theorem ContinuousLinearMap.nonneg_iff_isSelfAdjoint_and_nonneg_spectrum
  (T : B →L[ℂ] B) :
  0 ≤ T ↔ IsSelfAdjoint T ∧ spectrum ℂ T ⊆ {a : ℂ | 0 ≤ a} := by
  rw [nonneg_iff_isPositive, ContinuousLinearMap.IsPositive.toLinearMap',
    LinearMap.isPositive'_iff_isSymmetric_and_nonneg_spectrum,
    isSelfAdjoint_iff_isSymmetric, spectrum_coe]

theorem ContinuousLinearMap.nonneg_iff_exists
  (T : B →L[ℂ] B) :
  0 ≤ T ↔ ∃ f, T = star f * f :=
by rw [nonneg_iff_isPositive]; exact isPositive_iff_exists_adjoint_hMul_self _


lemma orthogonalProjection_ker_comp_eq_of_comp_eq_zero {T S : B →L[ℂ] B} (h : T * S = 0) :
  orthogonalProjection' (LinearMap.ker T.toLinearMap) * S = S := by
  have : LinearMap.range S.toLinearMap ≤ LinearMap.ker T.toLinearMap := by
    intro x ⟨y, hy⟩
    rw [← hy, LinearMap.mem_ker]
    have hfun := congrArg (fun f : B →L[ℂ] B => f y) h
    simpa [mul_apply_eq_comp] using hfun
  rw [← orthogonalProjection.range (LinearMap.ker T.toLinearMap)] at this
  rw [← ContinuousLinearMap.coe_inj, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.toLinearMap_comp, IsIdempotentElem.comp_idempotent_iff]
  · exact this
  · exact ContinuousLinearMap.IsIdempotentElem.toLinearMap
      (orthogonalProjection.isIdempotentElem _)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- matrix of orthogonalProjection -/
noncomputable def Matrix.orthogonalProjection
  (U : Submodule ℂ (EuclideanSpace ℂ n)) :
  Matrix n n ℂ :=
(Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (orthogonalProjection' U)

/-- The blockwise matrix of orthogonal projections for a `PiMat`. -/
noncomputable def PiMat.orthogonalProjection
  {k : Type*} {n : k → Type*}
  [Π i, Fintype (n i)] [Π i, DecidableEq (n i)]
  (U : Π i, Submodule ℂ (EuclideanSpace ℂ (n i))) :
    PiMat ℂ k n :=
fun i => Matrix.orthogonalProjection (U i)

lemma Matrix.toEuclideanLin_symm {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  (x : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n) :
  (Matrix.toEuclideanLin.symm x) =
    LinearMap.toMatrix (EuclideanSpace.basisFun n 𝕜).toBasis
      (EuclideanSpace.basisFun n 𝕜).toBasis x := by
  rfl

lemma EuclideanSpace.trace_eq_matrix_trace' {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] (f : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n) :
  LinearMap.trace 𝕜 _ f = Matrix.trace (Matrix.toEuclideanLin.symm f) := by
  rw [LinearMap.trace_eq_matrix_trace 𝕜 (EuclideanSpace.basisFun n 𝕜).toBasis f]
  congr 1

theorem Matrix.coe_toEuclideanCLM_symm_eq_toEuclideanLin_symm {𝕜 n : Type*}
  [RCLike 𝕜] [Fintype n] [DecidableEq n]
  (A : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) :
  (toEuclideanCLM (𝕜 := 𝕜)).symm A = toEuclideanLin.symm A :=
rfl

theorem Matrix.orthogonalProjection_trace {U : Submodule ℂ (EuclideanSpace ℂ n)} :
  (Matrix.orthogonalProjection U).trace = Module.finrank ℂ U := by
  rw [orthogonalProjection, Matrix.coe_toEuclideanCLM_symm_eq_toEuclideanLin_symm,
    ← EuclideanSpace.trace_eq_matrix_trace']
  exact _root_.orthogonalProjection_trace _

theorem PiMat.orthogonalProjection_trace {k : Type*} {n : k → Type*} [Fintype k] [DecidableEq k]
  [Π i, Fintype (n i)] [Π i, DecidableEq (n i)]
  (U : Π i, Submodule ℂ (EuclideanSpace ℂ (n i))) :
  (Matrix.blockDiagonal' (PiMat.orthogonalProjection U)).trace
    = ∑ i, Module.finrank ℂ (U i) := by
  simp_rw [Matrix.trace_blockDiagonal', PiMat.orthogonalProjection,
    Matrix.orthogonalProjection_trace, Nat.cast_sum]

lemma Matrix.isIdempotentElem_toEuclideanCLM {n : Type*} [Fintype n] [DecidableEq n]
  (x : Matrix n n ℂ) :
  IsIdempotentElem x ↔ IsIdempotentElem (toEuclideanCLM (𝕜 := ℂ) x) := by
  simp_rw [IsIdempotentElem, ← _root_.map_mul]
  exact Iff.symm (EmbeddingLike.apply_eq_iff_eq toEuclideanCLM)

lemma Matrix.CLM_apply_orthogonalProjection {U : Submodule ℂ (EuclideanSpace ℂ n)} :
  Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.orthogonalProjection U)
    = orthogonalProjection' U := by
  ext1
  simp [orthogonalProjection', orthogonalProjection]

lemma Matrix.orthogonalProjection_ortho_eq {U : Submodule ℂ (EuclideanSpace ℂ n)} :
  Matrix.orthogonalProjection Uᗮ = 1 - Matrix.orthogonalProjection U := by
  apply_fun Matrix.toEuclideanCLM (𝕜 := ℂ)
  simp only [map_sub, _root_.map_one]
  simp only [Matrix.CLM_apply_orthogonalProjection]
  exact orthogonalProjection.orthogonal_complement_eq U

lemma Matrix.orthogonalProjection_isPosSemidef {U : Submodule ℂ (EuclideanSpace ℂ n)} :
  (Matrix.orthogonalProjection U).PosSemidef := by
  rw [posSemidef_eq_linearMap_positive', ← coe_toEuclideanCLM_eq_toEuclideanLin,
    Matrix.CLM_apply_orthogonalProjection,
    ← ContinuousLinearMap.IsPositive.toLinearMap',
    ← ContinuousLinearMap.nonneg_iff_isPositive]
  exact orthogonalProjection.is_positive

lemma Matrix.IsHermitian.orthogonalProjection_ker_apply_self {x : Matrix n n ℂ}
  (hx : x.IsHermitian) :
  Matrix.orthogonalProjection (LinearMap.ker (toEuclideanCLM (𝕜 := ℂ) x).toLinearMap) *
    x = 0 := by
  apply_fun Matrix.toEuclideanCLM (𝕜 := ℂ)
  simp only [_root_.map_mul, map_zero]
  simp only [Matrix.CLM_apply_orthogonalProjection]
  ext1
  simp only [mul_apply_eq_comp, _root_.zero_apply]
  simp only [orthogonalProjection'_eq, ContinuousLinearMap.coe_comp, Submodule.coe_subtypeL,
    Submodule.coe_subtype, Function.comp_apply, ZeroMemClass.coe_eq_zero,
    Submodule.orthogonalProjectionOnto_eq_zero_iff]
  rw [ContinuousLinearMap.ker_eq_ortho_adjoint_range, Submodule.orthogonal_orthogonal,
    ← ContinuousLinearMap.star_eq_adjoint]
  simp only [← map_star, star_eq_conjTranspose, hx.eq]
  exact LinearMap.mem_range_self _ _

private lemma auxaux_2 {T S : Matrix n n ℂ} (h : T * S = 0) :
  Matrix.orthogonalProjection (LinearMap.ker (Matrix.toEuclideanCLM (𝕜 := ℂ) T).toLinearMap) *
    S = S := by
  apply_fun Matrix.toEuclideanCLM (𝕜 := ℂ) at h ⊢
  simp only [_root_.map_mul, map_zero] at h ⊢
  simp only [Matrix.CLM_apply_orthogonalProjection]
  exact orthogonalProjection_ker_comp_eq_of_comp_eq_zero h

omit [Fintype n] [DecidableEq n] in
theorem Matrix.nonneg_def {x : Matrix n n ℂ} :
  0 ≤ x ↔ x.PosSemidef :=
by rw [le_iff, sub_zero]

/-- the positive square root of the square of a Hermitian matrix `x`,
  in other words, `√(x ^ 2)` -/
noncomputable def Matrix.IsHermitian.sqSqrt {x : Matrix n n ℂ}
  (hx : x.IsHermitian) :
  Matrix n n ℂ :=
innerAut (hx.eigenvectorUnitary)
  (Matrix.diagonal (RCLike.ofReal ∘ (fun i => √ ((hx.eigenvalues i) ^ 2 : ℝ))))

lemma Matrix.IsHermitian.sqSqrt_eq {x : Matrix n n ℂ} (hx : x.IsHermitian) :
  hx.sqSqrt = innerAut (hx.eigenvectorUnitary)
    (Matrix.diagonal (RCLike.ofReal ∘ (|hx.eigenvalues|))) :=
by simp only [sqSqrt, Real.sqrt_sq_eq_abs]; rfl

lemma Matrix.IsHermitian.sqSqrt_isPosSemidef {x : Matrix n n ℂ} (hx : x.IsHermitian) :
  hx.sqSqrt.PosSemidef := by
  rw [sqSqrt_eq]
  apply (innerAut_posSemidef_iff _).mpr
  apply (diagonal_posSemidef_iff _).mpr
  intro
  rw [Function.comp_apply, Pi.zero_apply, RCLike.ofReal_nonneg, Pi.abs_apply]
  exact abs_nonneg _

/-- the square of the positive square root of a Hermitian matrix is equal to the square of the
  matrix -/
lemma Matrix.IsHermitian.sqSqrt_sq {x : Matrix n n ℂ} (hx : x.IsHermitian) :
  hx.sqSqrt ^ 2 = x ^ 2 := by
  symm
  nth_rw 1 [hx.spectral_theorem'']
  simp_rw [sqSqrt, innerAut.map_pow, diagonal_pow]
  simp only [innerAut_coe, EmbeddingLike.apply_eq_iff_eq, diagonal_eq_diagonal_iff,
    Pi.pow_apply, Function.comp_apply, ← RCLike.ofReal_pow,
    Real.sq_sqrt (sq_nonneg _), implies_true]

/-- The positive part in the decomposition of a Hermitian matrix. -/
noncomputable def Matrix.IsHermitian.posSemidefDecompositionLeft
  (x : Matrix n n ℂ) [hx : Fact x.IsHermitian] :=
(1 / 2 : ℂ) • (hx.out.sqSqrt + x)
/-- Notation for the positive part in the decomposition of a Hermitian matrix. -/
notation3:80 (name := posL) x:81"₊" =>
  @Matrix.IsHermitian.posSemidefDecompositionLeft _ _ _ x _
lemma Matrix.IsHermitian.sqSqrt_isHermitian {x : Matrix n n ℂ} (hx : x.IsHermitian) :
  hx.sqSqrt.IsHermitian := by
  rw [sqSqrt]
  apply (innerAut_isHermitian_iff _ _).mp _
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  simp only [Function.comp_apply, _root_.IsSelfAdjoint, RCLike.star_def, RCLike.conj_ofReal]

lemma Matrix.IsHermitian.posSemidefDecompositionLeft_isHermitian
  {x : Matrix n n ℂ} [hx : Fact x.IsHermitian] : x₊.IsHermitian := by
  rw [IsHermitian, posSemidefDecompositionLeft, conjTranspose_smul,
    conjTranspose_add, hx.out.eq, RCLike.star_def]
  simp only [one_div, map_inv₀, map_ofNat]
  rw [hx.out.sqSqrt_isHermitian.eq]

/-- The negative part in the decomposition of a Hermitian matrix. -/
noncomputable def Matrix.IsHermitian.posSemidefDecompositionRight
  (x : Matrix n n ℂ) [hx : Fact x.IsHermitian] :=
(1 / 2 : ℂ) • (hx.out.sqSqrt - x)
/-- Notation for the negative part in the decomposition of a Hermitian matrix. -/
notation3:80 (name := posR) x:81"₋" =>
  Matrix.IsHermitian.posSemidefDecompositionRight x
lemma Matrix.IsHermitian.posSemidefDecompositionRight_isHermitian
  {x : Matrix n n ℂ} [hx : Fact x.IsHermitian] :
  x₋.IsHermitian := by
  rw [IsHermitian, posSemidefDecompositionRight, conjTranspose_smul,
    conjTranspose_sub, hx.out.eq, RCLike.star_def]
  simp only [one_div, map_inv₀, map_ofNat]
  rw [hx.out.sqSqrt_isHermitian.eq]

/-- a Hermitian matrix commutes with its positive squared-square-root,
  i.e., `x * √(x^2) = √(x^2) * x`. -/
lemma Matrix.IsHermitian.commute_sqSqrt {x : Matrix n n ℂ} (hx : x.IsHermitian) :
  Commute x hx.sqSqrt := by
  rw [Commute, SemiconjBy]
  nth_rw 1 [hx.spectral_theorem'']
  symm
  nth_rw 2 [hx.spectral_theorem'']
  simp only [sqSqrt, ← Matrix.innerAut.map_mul, diagonal_mul_diagonal, mul_comm]

lemma Matrix.IsHermitian.posSemidefDecompositionLeft_mul_right (x : Matrix n n ℂ)
  [hx : Fact x.IsHermitian] :
  x₊ * x₋ = 0 := by
  simp_rw [posSemidefDecompositionLeft, posSemidefDecompositionRight,
    smul_add, smul_sub, add_mul, mul_sub]
  simp only [one_div, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  simp_rw [← pow_two, hx.out.commute_sqSqrt.eq]
  simp only [sub_add_sub_cancel, sqSqrt_sq]
  simp only [sub_self]
lemma Matrix.IsHermitian.posSemidefDecompositionRight_mul_left (x : Matrix n n ℂ)
  [hx : Fact x.IsHermitian] :
  x₋ * x₊ = 0 := by
  simp_rw [posSemidefDecompositionLeft, posSemidefDecompositionRight,
    smul_add, smul_sub, sub_mul, mul_add]
  simp only [one_div, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  simp_rw [← pow_two, hx.out.commute_sqSqrt.eq]
  nth_rw 1 [sqSqrt_sq]
  simp only [sub_add_eq_sub_sub, add_sub_cancel_right, sub_self]

lemma Matrix.IsHermitian.posSemidefDecomposition_eq (x : Matrix n n ℂ) [hx : Fact x.IsHermitian] :
  x = x₊ - x₋ := by
  simp_rw [posSemidefDecompositionLeft, posSemidefDecompositionRight,
    ← smul_sub, add_sub_sub_cancel, ← two_smul ℂ, smul_smul]
  norm_num

theorem Matrix.IsHermitian.posSemidefDecomposition_posSemidef_left_right
  {x : Matrix n n ℂ} (hx : Fact x.IsHermitian) :
  x₊.PosSemidef ∧ x₋.PosSemidef  := by
  have h := fun (a b : Matrix n n ℂ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    => Matrix.posSemidef_iff_commute ha hb
  simp only [sub_zero, Matrix.nonneg_def] at h
  have h₂ := auxaux_2 (IsHermitian.posSemidefDecompositionLeft_mul_right x)
  have h₃ : hx.out.sqSqrt = x₊ + x₋ := by
    simp_rw [IsHermitian.posSemidefDecompositionLeft, IsHermitian.posSemidefDecompositionRight,
      ← smul_add, add_add_sub_cancel, ← two_smul ℂ, smul_smul]
    norm_num
  have h₄ :
      orthogonalProjection (LinearMap.ker (toEuclideanCLM (𝕜 := ℂ) (x₊)).toLinearMap) *
        hx.out.sqSqrt = x₋ := by
    rw [h₃, mul_add, h₂, Matrix.IsHermitian.orthogonalProjection_ker_apply_self
      IsHermitian.posSemidefDecompositionLeft_isHermitian, zero_add]
  have h₅ : x =
      (1 - (2 : ℂ) •
          (orthogonalProjection
            (LinearMap.ker (toEuclideanCLM (𝕜 := ℂ) (x₊)).toLinearMap)))
    * hx.out.sqSqrt := by
    rw [sub_mul, smul_mul_assoc, h₄, h₃, one_mul, two_smul, add_sub_add_right_eq_sub]
    exact IsHermitian.posSemidefDecomposition_eq _
  have h₆ : x₊ =
      (orthogonalProjection
        (LinearMap.ker (toEuclideanCLM (𝕜 := ℂ) (x₊)).toLinearMap)ᗮ)
    * hx.out.sqSqrt := by
    nth_rw 1 [IsHermitian.posSemidefDecompositionLeft]
    nth_rw 3 [h₅]
    rw [Matrix.orthogonalProjection_ortho_eq]
    simp_rw [sub_mul, one_mul, smul_add, smul_sub, smul_mul_assoc,
      h₄, smul_smul, add_sub, ← smul_add, ← two_smul ℂ, smul_smul]
    norm_num
  have h₄' : x₋ =
      hx.out.sqSqrt *
        (orthogonalProjection (LinearMap.ker (toEuclideanCLM (𝕜 := ℂ) (x₊)).toLinearMap)) :=
  by rw [← IsHermitian.posSemidefDecompositionRight_isHermitian, ← h₄,
    conjTranspose_mul, (IsHermitian.sqSqrt_isPosSemidef _).1.eq,
    Matrix.orthogonalProjection_isPosSemidef.1.eq]
  have h₆' : x₊ =
      hx.out.sqSqrt *
        (orthogonalProjection (LinearMap.ker (toEuclideanCLM (𝕜 := ℂ) (x₊)).toLinearMap)ᗮ) := by
    nth_rw 1 [← IsHermitian.posSemidefDecompositionLeft_isHermitian, h₆]
    rw [conjTranspose_mul, (IsHermitian.sqSqrt_isPosSemidef _).1.eq,
      Matrix.orthogonalProjection_isPosSemidef.1.eq]
  constructor
  · rw [h₆', ← h _ _ (IsHermitian.sqSqrt_isPosSemidef _)
      orthogonalProjection_isPosSemidef, Commute, SemiconjBy, ← h₆, ← h₆']
  · rw [h₄', ← h _ _ (IsHermitian.sqSqrt_isPosSemidef _)
      orthogonalProjection_isPosSemidef, Commute, SemiconjBy, h₄, ← h₄']

open scoped Matrix
omit [DecidableEq n] in
theorem Matrix.IsHermitian.posSemidefDecomposition'
  {x : Matrix n n ℂ} (hx : x.IsHermitian) :
  ∃ a b, x = aᴴ * a - bᴴ * b := by
  classical
  let hx := Fact.mk hx
  simp_rw [posSemidefDecomposition_eq]
  obtain ⟨α, hα⟩ := (Matrix.posSemidef_iff (x₊)).mp
    (posSemidefDecomposition_posSemidef_left_right hx).1
  obtain ⟨β, hβ⟩ := (Matrix.posSemidef_iff (x₋)).mp
    (posSemidefDecomposition_posSemidef_left_right hx).2
  use α, β
  rw [hα, hβ]

theorem PiMat.IsSelfAdjoint.posSemidefDecomposition {k : Type*} {n : k → Type*}
  [Π i, Fintype (n i)]
  {x : PiMat ℂ k n} (hx : IsSelfAdjoint x) :
  ∃ a b, x = star a * a - star b * b := by
  have : ∀ i, (x i).IsHermitian := fun i =>
  by
    rw [IsSelfAdjoint, funext_iff] at hx
    simp_rw [Pi.star_apply, Matrix.star_eq_conjTranspose] at hx
    exact hx i
  have := fun i => Matrix.IsHermitian.posSemidefDecomposition' (this i)
  let a : PiMat ℂ k n :=
  fun i => (this i).choose
  let b : PiMat ℂ k n :=
  fun i => (this i).choose_spec.choose
  have hab : ∀ i, x i = star (a i) * (a i) - star (b i) * (b i) :=
  fun i => (this i).choose_spec.choose_spec
  use a, b
  ext1
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.star_apply, hab]

open ContinuousLinearMap in
theorem IsSelfAdjoint.isPositiveDecomposition
  {x : B →L[ℂ] B} (hx : IsSelfAdjoint x) :
  ∃ a b, x = star a * a - star b * b := by
  let e := stdOrthonormalBasis ℂ B
  have hx' : Matrix.IsHermitian (e.toMatrix x.toLinearMap) := by
    rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose, ← map_star]
    congr
    rw [isSelfAdjoint_iff_isSymmetric, LinearMap.isSymmetric_iff_isSelfAdjoint] at hx
    exact hx
  obtain ⟨a, b, hab⟩ := hx'.posSemidefDecomposition'
  let a' : B →L[ℂ] B := LinearMap.toContinuousLinearMap (e.toMatrix.symm a)
  let b' : B →L[ℂ] B := LinearMap.toContinuousLinearMap (e.toMatrix.symm b)
  use a', b'
  apply_fun e.toMatrix.symm at hab
  simp_rw [StarAlgEquiv.symm_apply_apply, map_sub, map_mul, ← Matrix.star_eq_conjTranspose,
    map_star] at hab
  calc x = LinearMap.toContinuousLinearMap (x.toLinearMap) := rfl
    _ = LinearMap.toContinuousLinearMap (star (e.toMatrix.symm a)) * a' -
      LinearMap.toContinuousLinearMap (star (e.toMatrix.symm b)) * b' := ?_
    _ = star a' * a' - star b' * b' := rfl
  · rw [hab, ← toLinearMapAlgEquiv_symm_apply, map_sub, map_mul]
    rfl

universe u

/-- Data exhibiting a star algebra as equivalent to a finite product of matrix algebras. -/
structure isEquivToPiMat (A : Type u) [Add A] [Mul A] [Star A] [SMul ℂ A] where
  /-- The index type for the product of matrix algebras. -/
  k : Type u
  /-- The matrix index type in each summand. -/
  -- hn₁ : Fintype n
  -- hn₂ : DecidableEq n
  rk : k → Type u
  /-- Finiteness of each matrix index type. -/
  hrk₁ : Π i, Fintype (rk i)
  /-- Decidable equality for each matrix index type. -/
  hrk₂ : Π i, DecidableEq (rk i)
  /-- The star algebra equivalence to the product of matrix algebras. -/
  φ : A ≃⋆ₐ[ℂ] PiMat ℂ k rk
-- attribute [instance] isEquivToPiMat.hn₁
-- attribute [instance] isEquivToPiMat.hn₂
attribute [instance] isEquivToPiMat.hrk₁
attribute [instance] isEquivToPiMat.hrk₂

/-- Matrices are trivially equivalent to a one-summand product of matrix algebras. -/
noncomputable def Matrix.isEquivToPiMat :
  isEquivToPiMat (Matrix n n ℂ) :=
let f : Matrix n n ℂ ≃⋆ₐ[ℂ] PiMat ℂ PUnit (fun _ => n) :=
{ toFun := fun x _ => x
  invFun := fun x => x default
  left_inv := fun x => rfl
  right_inv := fun x => funext (fun i => by cases i; rfl)
  map_mul' := fun x y => rfl
  map_add' := fun x y => rfl
  map_smul' := fun x y => rfl
  map_star' := fun x => rfl }
{ k := PUnit
  rk := fun _ => n
  φ := f
  hrk₁ := fun i ↦ by infer_instance
  hrk₂ := fun i ↦ by infer_instance }

omit [StarModule ℂ A] [PartialOrder A] [StarOrderedRing A] in
theorem IsSelfAdjoint.isPositiveDecomposition_of_starAlgEquiv_piMat
  (hφ : isEquivToPiMat A)
  {x : A} (hx : _root_.IsSelfAdjoint x) :
  ∃ a b, x = star a * a - star b * b := by
  have : IsSelfAdjoint (hφ.φ x) := by
    rw [IsSelfAdjoint, ← map_star, hx]
  obtain ⟨α, β, h⟩ := PiMat.IsSelfAdjoint.posSemidefDecomposition this
  use hφ.φ.symm α, hφ.φ.symm β
  apply_fun hφ.φ
  simp_rw [h, map_sub, map_mul, map_star, StarAlgEquiv.apply_symm_apply]

/-- Core of `isReal_of_isPosMap`: a positivity-preserving map out of a `ℂ`-star-algebra
  whose self-adjoint elements decompose as `star a * a - star b * b` is star-preserving. -/
private theorem isReal_of_isPosMap_of_selfAdjointDecomposition
  {M K : Type*} [Ring M] [StarRing M] [PartialOrder M] [_root_.StarOrderedRing M]
  [Module ℂ M] [StarModule ℂ M]
  [Ring K] [StarRing K] [PartialOrder K] [Algebra ℂ K] [StarOrderedRing K] [StarModule ℂ K]
  {φ : M →ₗ[ℂ] K} (hφ : LinearMap.IsPosMap φ)
  (hdec : ∀ ⦃x : M⦄, _root_.IsSelfAdjoint x → ∃ a b, x = star a * a - star b * b) :
  LinearMap.IsReal φ := by
  intro x
  rw [selfAdjointDecomposition x]
  let L := aL x
  have hL : L = aL x := rfl
  let R := aR x
  have hR : R = aR x := rfl
  rw [← hL, ← hR]
  simp only [star_add, map_add, star_smul, _root_.map_smul]
  repeat rw [selfAdjointDecompositionLeft_isSelfAdjoint _]
  suffices h2 : ∀ a (_ : _root_.IsSelfAdjoint a), φ (star a) = star (φ a) by
    rw [← h2 _ (selfAdjointDecompositionLeft_isSelfAdjoint _),
      ← h2 _ (selfAdjointDecompositionRight_isSelfAdjoint _),
      selfAdjointDecompositionLeft_isSelfAdjoint,
      selfAdjointDecompositionRight_isSelfAdjoint]
  intro x hx
  obtain ⟨a, b, rfl⟩ := hdec hx
  simp only [star_sub, star_mul, star_star, map_sub]
  rw [IsSelfAdjoint.of_nonneg (hφ (star_mul_self_nonneg a)),
    IsSelfAdjoint.of_nonneg (hφ (star_mul_self_nonneg b))]

omit [Fintype n] [DecidableEq n] in
/-- if a map preserves positivity, then it is star-preserving -/
theorem Matrix.isReal_of_isPosMap
  [Finite n]
  {K : Type*}
  [Ring K] [StarRing K] [PartialOrder K] [Algebra ℂ K] [StarOrderedRing K] [StarModule ℂ K]
  {φ : Matrix n n ℂ →ₗ[ℂ] K} (hφ : LinearMap.IsPosMap φ) :
  LinearMap.IsReal φ := by
  classical
  letI := Fintype.ofFinite n
  refine isReal_of_isPosMap_of_selfAdjointDecomposition hφ (fun x hx => ?_)
  obtain ⟨a, b, hab⟩ := Matrix.IsHermitian.posSemidefDecomposition' hx
  exact ⟨a, b, by simpa only [star_eq_conjTranspose] using hab⟩

theorem StarNonUnitalAlgHom.toLinearMap_apply
  {R A B : Type*} [Semiring R] [NonUnitalNonAssocSemiring A]
  [Module R A] [NonUnitalNonAssocSemiring B] [Module R B]
  [Star A] [Star B]
  (f : A →⋆ₙₐ[R] B) (x : A) : (f : A →ₗ[R] B) x = f x := rfl

theorem LinearMap.isPosMap_iff_star_mul_self_nonneg {A K : Type*}
  [NonUnitalSemiring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [NonUnitalSemiring K] [PartialOrder K] [StarRing K] [StarOrderedRing K]
  (hA : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ b, a = star b * b)
  {F : Type*} [FunLike F A K] {f : F} :
  LinearMap.IsPosMap f ↔ ∀ a : A, 0 ≤ f (star a * a) := by
  refine ⟨fun h a => h (star_mul_self_nonneg _), fun h a => ?_⟩
  · rw [hA]
    rintro ⟨b, rfl⟩
    exact h _

theorem LinearMap.isPosMap_iff_comp_starAlgEquiv
  {K A B : Type*}
  [Mul K] [Mul A] [Mul B] [Star K] [Star A] [Star B]
  [Zero A] [Zero B] [Zero K]
  [PartialOrder A] [PartialOrder B] [PartialOrder K]
  (hA : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ b, a = star b * b)
  (hB : ∀ ⦃a : B⦄, 0 ≤ a ↔ ∃ b, a = star b * b)
  {F S : Type*} [FunLike F A K] {φ : F}
  [EquivLike S B A] [MulEquivClass S B A] [StarHomClass S B A]
  (ψ : S) :
  LinearMap.IsPosMap φ ↔ ∀ ⦃x⦄, 0 ≤ x → 0 ≤ φ (ψ x) := by
  simp_rw [IsPosMap, hA, hB]
  simp only [forall_exists_index, forall_eq_apply_imp_iff, map_mul,
    map_star]
  refine ⟨fun h _ => h _, fun h x => ?_⟩
  simpa using h (EquivLike.inv ψ x)

theorem LinearMap.isReal_iff_comp_starEquiv
  {K A B : Type*}
  [Star K] [Star A] [Star B]
  {F S : Type*} [FunLike F A K] [EquivLike S B A] [StarHomClass S B A]
  {φ : F} (ψ : S) :
  LinearMap.IsReal φ ↔ ∀ x, φ (ψ (star x)) = star (φ (ψ x)) := by
  simp_rw [map_star]
  constructor
  · intro h _
    exact h _
  · intro h x
    simpa using h (EquivLike.inv ψ x)

/-- if a map preserves positivity, then it is star-preserving -/
theorem isReal_of_isPosMap
  {K : Type*}
  [Ring K] [StarRing K] [PartialOrder K] [Algebra ℂ K] [StarOrderedRing K] [StarModule ℂ K]
  {φ : (B →L[ℂ] B) →ₗ[ℂ] K} (hφ : LinearMap.IsPosMap φ) :
  LinearMap.IsReal φ :=
isReal_of_isPosMap_of_selfAdjointDecomposition hφ (fun _ hx => hx.isPositiveDecomposition)

theorem isReal_of_isPosMap_of_starAlgEquiv_piMat
  (hφ : isEquivToPiMat A)
  {K : Type*}
  [Ring K] [StarRing K] [PartialOrder K] [Algebra ℂ K] [StarOrderedRing K] [StarModule ℂ K]
  {f : A →ₗ[ℂ] K} (hf : LinearMap.IsPosMap f) :
  LinearMap.IsReal f :=
isReal_of_isPosMap_of_selfAdjointDecomposition hf
  (fun _ hx => hx.isPositiveDecomposition_of_starAlgEquiv_piMat hφ)

/-- a $^*$-homomorphism from $A$ to $B$ is a positive map -/
theorem starMulHom_isPosMap
  {A K : Type*}
  [Semiring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [Semiring K] [PartialOrder K] [StarRing K] [StarOrderedRing K]
  (hA : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ b, a = star b * b)
  {F : Type*} [FunLike F A K] [StarHomClass F A K] [MulHomClass F A K]
  (f : F) :
  LinearMap.IsPosMap f := by
  intro a ha
  obtain ⟨b, rfl⟩ := hA.mp ha
  rw [map_mul, map_star]
  exact star_mul_self_nonneg _

theorem NonUnitalAlgHom.isPosMap_iff_isReal_of_nonUnitalStarAlgEquiv_piMat
  (hφ : isEquivToPiMat A)
  (hA : ∀ ⦃a : A⦄, 0 ≤ a ↔ ∃ b, a = star b * b)
  {K : Type*}
  [Ring K] [StarRing K] [PartialOrder K] [Algebra ℂ K] [StarOrderedRing K] [StarModule ℂ K]
  {f : A →ₙₐ[ℂ] K} :
  LinearMap.IsPosMap f ↔ LinearMap.IsReal f := by
  have : LinearMap.IsPosMap f ↔ LinearMap.IsPosMap (f : A →ₗ[ℂ] K) := by rfl
  refine ⟨fun h => isReal_of_isPosMap_of_starAlgEquiv_piMat hφ (this.mp h), fun h => ?_⟩
  let f' : A →⋆ₙₐ[ℂ] K := NonUnitalStarAlgHom.mk f h
  exact starMulHom_isPosMap hA f'

theorem Matrix.innerAut.map_zpow {n : Type*} [Fintype n] [DecidableEq n]
  {𝕜 : Type*} [RCLike 𝕜] (U : ↥(Matrix.unitaryGroup n 𝕜)) (x : Matrix n n 𝕜) (z : ℤ) :
  (Matrix.innerAut U) x ^ z = (Matrix.innerAut U) (x ^ z) := by
  induction z using Int.induction_on
  · exact map_pow U x 0
  · rename_i i _
    exact map_pow U x (↑i + 1)
  · rename_i i _
    calc (innerAut U x ^ (-(i:ℤ)-1))
      = (innerAut U x ^ (i + 1))⁻¹ :=
        by rw [← Matrix.zpow_neg_natCast, neg_sub_left, add_comm]; rfl
    _ = (innerAut U (x ^ (i + 1)))⁻¹ := by rw [innerAut.map_pow]
    _ = innerAut U ((x ^ (i + 1))⁻¹) := by rw [map_inv]
    _ = innerAut U (x ^ (-(i:ℤ)-1)) := by
      rw [← Matrix.zpow_neg_natCast, neg_sub_left, add_comm]; rfl

lemma Matrix.inv_diagonal' {R n : Type*} [Field R]
  [Fintype n] [DecidableEq n]
  (d : n → R) [Invertible d] :
  (Matrix.diagonal d)⁻¹ = Matrix.diagonal d⁻¹ := by
  haveI := Matrix.diagonalInvertible d
  rw [← invOf_eq_nonsing_inv, invOf_diagonal_eq]
  simp only [diagonal_eq_diagonal_iff, Pi.inv_apply]
  intro
  refine eq_inv_of_mul_eq_one_left ?h
  rw [← Pi.mul_apply, invOf_mul_self]
  rfl

theorem Matrix.diagonal_zpow
  {𝕜 : Type*} [Field 𝕜] (x : n → 𝕜) [Invertible x] (z : ℤ) :
  (Matrix.diagonal x) ^ z = Matrix.diagonal (x ^ z) := by
  induction z using Int.induction_on
  · simp only [zpow_zero]; rfl
  · norm_cast
    exact diagonal_pow x _
  · rename_i i _
    rw [neg_sub_left, add_comm]
    calc diagonal x ^ (-((i : ℤ)+1)) = (diagonal x ^ (-((i + 1 : ℕ) : ℤ))) := rfl
      _ = (diagonal x ^ (i + 1))⁻¹ := by rw [Matrix.zpow_neg_natCast]
      _ = (diagonal (x ^ (i + 1)))⁻¹ := by rw [diagonal_pow]
      _ = diagonal ((x ^ (i + 1))⁻¹) := by rw [inv_diagonal']
      _ = diagonal ((x ^ ((i : ℤ) + 1))⁻¹) := by norm_cast
      _ = diagonal (x ^ (-((i:ℤ)+1))) := by
        rw [← _root_.zpow_neg, neg_add]

theorem Matrix.PosDef.rpow_zpow {𝕜 : Type*} [RCLike 𝕜]
  {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ) (z : ℤ) :
  (hQ.rpow r) ^ z = hQ.rpow (r * (z : ℝ)) := by
  have := PosDef.rpow.isPosDef hQ r
  rw [hQ.rpow_eq, innerAut_posDef_iff, Matrix.PosDef.diagonal_iff] at this
  have : Invertible (RCLike.ofReal ∘ (hQ.1.eigenvalues ^ r) : n → 𝕜) := by
    simp only [Function.comp_apply, Pi.pow_apply, RCLike.ofReal_pos] at this
    use RCLike.ofReal ∘ (hQ.1.eigenvalues ^ (-r))
    <;>
    { ext i
      simp only [Pi.mul_apply, Function.comp_apply, Pi.pow_apply, Pi.one_apply,
        ← RCLike.ofReal_mul]
      rw [← Real.rpow_add (hQ.eigenvalues_pos _)]
      simp only [neg_add_cancel, add_neg_cancel, Real.rpow_zero, RCLike.ofReal_one] }
  simp_rw [rpow_eq, innerAut.map_zpow, diagonal_zpow]
  simp only [innerAut_coe, EmbeddingLike.apply_eq_iff_eq, diagonal_eq_diagonal_iff,
    Pi.pow_apply, Function.comp_apply, ← RCLike.ofReal_zpow]
  intro i
  rw [Real.rpow_mul (le_of_lt (hQ.eigenvalues_pos i))]
  norm_cast

theorem Matrix.PosDef.rpow_eq_pow {𝕜 : Type*} [RCLike 𝕜]
  {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℕ) :
  hQ.rpow r = Q ^ r := by
  nth_rw 2 [hQ.1.spectral_theorem'']
  simp only [innerAut.map_pow, diagonal_pow]
  rw [rpow_eq]
  simp only [innerAut_coe, EmbeddingLike.apply_eq_iff_eq, diagonal_eq_diagonal_iff,
    Function.comp_apply, Pi.pow_apply, Real.rpow_natCast,
    RCLike.ofReal_pow, implies_true]

theorem Matrix.PosDef.rpow_eq_zpow {𝕜 : Type*} [RCLike 𝕜]
  {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℤ) :
  hQ.rpow r = Q ^ r := by
  letI := PosDef.eigenvaluesInvertible' hQ
  nth_rw 2 [hQ.1.spectral_theorem'']
  simp only [innerAut.map_zpow, diagonal_zpow]
  rw [rpow_eq]
  simp only [innerAut_coe, EmbeddingLike.apply_eq_iff_eq, diagonal_eq_diagonal_iff,
    Function.comp_apply, Pi.pow_apply, Real.rpow_intCast,
    RCLike.ofReal_zpow, implies_true]

theorem Matrix.PosDef.rpow_rzpow {𝕜 : Type*} [RCLike 𝕜]
  {Q : Matrix n n 𝕜} (hQ : Q.PosDef) (r : ℝ) (z : ℤ) :
  (PosDef.rpow.isPosDef hQ r).rpow z = hQ.rpow (r * (z : ℝ)) :=
by rw [rpow_eq_zpow, rpow_zpow]

theorem Matrix.PosDef.eq_zpow_of_zpow_inv_eq {𝕜 : Type*} [RCLike 𝕜]
  {Q R : Matrix n n 𝕜} (hQ : Q.PosDef)
  {z : ℤ} (hz : z ≠ 0)
  (h : hQ.rpow (z⁻¹) = R) : Q = R ^ z := by
  have : (hQ.rpow z⁻¹) ^ (z : ℤ) = R ^ (z : ℤ) := by rw [h]
  rw [rpow_zpow, inv_mul_cancel₀ (Int.cast_ne_zero.mpr hz), rpow_one_eq_self] at this
  exact this

theorem Matrix.PosDef.eq_of_zpow_inv_eq_zpow_inv {𝕜 : Type*} [RCLike 𝕜]
  {Q R : Matrix n n 𝕜} (hQ : Q.PosDef) (hR : R.PosDef)
  {r : ℤ} (hr : r ≠ 0) (hQR : hQ.rpow r⁻¹ = hR.rpow r⁻¹) : Q = R := by
  have := eq_zpow_of_zpow_inv_eq hQ hr hQR
  rw [rpow_zpow, inv_mul_cancel₀ (Int.cast_ne_zero.mpr hr),
    rpow_one_eq_self] at this
  exact this

theorem selfAdjointDecomposition_ext_iff
  {B : Type*} [AddCommGroup B] [StarAddMonoid B]
  [Module ℂ B] [StarModule ℂ B] (a b : B) :
    a = b ↔ aL a = aL b ∧ aR a = aR b := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  rw [selfAdjointDecomposition a, h.1, h.2]
  exact Eq.symm (selfAdjointDecomposition b)

theorem selfAdjointDecompositionLeft_of
  {B : Type*} [AddCommGroup B] [StarAddMonoid B]
  [Module ℂ B] [StarModule ℂ B] (a b : B)
  (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    aL (a + Complex.I • b) = a := by
  rw [selfAdjointDecompositionLeft, star_add, star_smul, ha, hb,
    Complex.star_def, Complex.conj_I, neg_smul, add_add_add_comm, add_neg_cancel, add_zero,
    ← two_smul ℂ, smul_smul]
  norm_num

theorem selfAdjointDecompositionRight_of
  {B : Type*} [AddCommGroup B] [StarAddMonoid B]
  [Module ℂ B] [StarModule ℂ B] (a b : B)
  (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    aR (a + Complex.I • b) = b := by
  rw [selfAdjointDecompositionRight, star_add, star_smul, ha, hb,
    Complex.star_def, Complex.conj_I, neg_smul, sub_eq_add_neg,
    neg_add, add_add_add_comm, add_neg_cancel, zero_add, ← two_smul ℂ]
  simp only [smul_smul, smul_neg]
  simp only [RCLike.I_to_complex, one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, IsUnit.inv_mul_cancel_left, Complex.I_mul_I, neg_smul, one_smul, neg_neg]

theorem complex_decomposition_mul_decomposition
  {B : Type*} [Ring B] [StarRing B]
  [Module ℂ B] [StarModule ℂ B] [IsScalarTower ℂ B B]
  [SMulCommClass ℂ B B] (a b c d : B) :
    (a + Complex.I • b) * (c + Complex.I • d)
      = (a * c - b * d) + Complex.I • (b * c + a * d) := by
  simp only [mul_add, add_mul, sub_eq_add_neg, smul_add]
  simp only [add_assoc]
  congr 1
  simp only [smul_mul_assoc, mul_smul_comm]
  nth_rw 1 [← add_assoc, add_comm]
  congr 1
  simp only [smul_smul, Complex.I_mul_I, neg_smul, one_smul]

theorem selfAdjointDecompositionLeft_mul_self
  {B : Type*} [Ring B] [StarRing B]
  [Module ℂ B] [StarModule ℂ B] [IsScalarTower ℂ B B]
  [SMulCommClass ℂ B B] (a : B) :
    aL (a * a) = aL a * aL a - aR a * aR a := by
  nth_rw 2 [selfAdjointDecomposition a]
  nth_rw 1 [selfAdjointDecomposition a]
  have : (aL a + RCLike.I • aR a) * (aL a + RCLike.I • aR a)
   = _ :=
    complex_decomposition_mul_decomposition _ _ _ _
  rw [this, selfAdjointDecompositionLeft_of]
  all_goals { simp only [isSelfAdjoint_iff, star_sub, star_mul,
    isSelfAdjoint_iff.mp (selfAdjointDecompositionLeft_isSelfAdjoint _),
    isSelfAdjoint_iff.mp (selfAdjointDecompositionRight_isSelfAdjoint _),
    star_add, add_comm] }
theorem selfAdjointDecompositionRight_mul_self
  {B : Type*} [Ring B] [StarRing B]
  [Module ℂ B] [StarModule ℂ B] [IsScalarTower ℂ B B]
  [SMulCommClass ℂ B B] (a : B) :
    aR (a * a) = aR a * aL a + aL a * aR a := by
  nth_rw 2 [selfAdjointDecomposition a]
  nth_rw 1 [selfAdjointDecomposition a]
  have : (aL a + RCLike.I • aR a) * (aL a + RCLike.I • aR a)
   = _ :=
    complex_decomposition_mul_decomposition _ _ _ _
  rw [this, selfAdjointDecompositionRight_of]
  all_goals { simp only [isSelfAdjoint_iff, star_sub, star_mul,
    isSelfAdjoint_iff.mp (selfAdjointDecompositionLeft_isSelfAdjoint _),
    isSelfAdjoint_iff.mp (selfAdjointDecompositionRight_isSelfAdjoint _),
    star_add, add_comm] }

theorem isStarNormal_iff_selfAdjointDecomposition_commute
  {B : Type*} [Ring B] [StarRing B]
  [Module ℂ B] [StarModule ℂ B] [IsScalarTower ℂ B B]
  [SMulCommClass ℂ B B] (p : B) :
    IsStarNormal p ↔ Commute (aL p) (aR p) := by
  let a := aL p
  let b := aR p
  have h : p = a + Complex.I • b := selfAdjointDecomposition _
  have h₁ : p * star p = (a ^ 2 + b ^ 2) + Complex.I • (b * a - a * b) := by
    rw [h, star_add]
    nth_rw 2 [star_smul]
    rw [Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg,
      complex_decomposition_mul_decomposition,
      selfAdjointDecompositionLeft_isSelfAdjoint, selfAdjointDecompositionRight_isSelfAdjoint,
      mul_neg, sub_neg_eq_add, mul_neg, sub_eq_add_neg]
    simp only [pow_two]
    rfl
  have h₂ : star p * p = (a ^ 2 + b ^ 2) + Complex.I • (a * b - b * a) := by
    rw [h, star_add]
    nth_rw 2 [star_smul]
    rw [Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg,
      complex_decomposition_mul_decomposition,
      selfAdjointDecompositionLeft_isSelfAdjoint, selfAdjointDecompositionRight_isSelfAdjoint,
      neg_mul, sub_neg_eq_add, neg_mul]
    simp_rw [sub_eq_add_neg, pow_two]
    nth_rw 3 [add_comm]
  have h₃ :=
    calc IsStarNormal p ↔ p * star p = star p * p :=
        by rw [isStarNormal_iff, commute_iff_eq, eq_comm]
    _ ↔ Complex.I • (b * a - a * b) = Complex.I • (a * b - b * a) :=
        by rw [h₁, h₂, add_left_cancel_iff]
    _ ↔ b * a - a * b = a * b - b * a := smul_right_inj Complex.I_ne_zero
    _ ↔ (2 : ℂ) • (b * a) = (2 : ℂ) • (a * b) :=
        by simp only [two_smul, sub_eq_iff_eq_add, sub_add_eq_add_sub, eq_sub_iff_add_eq]
    _ ↔ b * a = a * b := smul_right_inj two_ne_zero
    _ ↔ a * b = b * a := eq_comm
  exact h₃

theorem isSelfAdjoint_iff_selfAdjointDecompositionRight_eq_zero
  {B : Type*} [Ring B] [StarRing B]
  [Module ℂ B] [StarModule ℂ B] [IsScalarTower ℂ B B]
  [SMulCommClass ℂ B B] (p : B) :
    IsSelfAdjoint p ↔ aR p = 0 := by
  simp only [isSelfAdjoint_iff, RCLike.I_to_complex, isUnit_iff_ne_zero, ne_eq, Complex.I_ne_zero,
    not_false_eq_true, IsUnit.smul_eq_zero, one_div, inv_eq_zero, OfNat.ofNat_ne_zero, sub_eq_zero]

theorem IsIdempotentElem.isSelfAdjoint_iff_isStarNormal
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (p : V →L[ℂ] V) (hp : IsIdempotentElem p) [CompleteSpace V] :
    IsSelfAdjoint p ↔ IsStarNormal p := by
  constructor
  · intro h
    rw [isStarNormal_iff, h]
  · intro h
    have h : IsStarNormal (1 - p) := by
    { simp only [isStarNormal_iff, commute_iff_eq, star_sub, star_one,
        mul_sub, sub_mul, mul_one, one_mul]
      simp only [sub_eq_add_neg, add_assoc, neg_add, neg_neg]
      rw [(isStarNormal_iff _).mp h]
      rw [← add_assoc, add_add_add_comm, add_assoc] }
    have := (ContinuousLinearMap.IsStarNormal.norm_eq_adjoint _).mp h
    have :=
      calc
        p = Star.star p * p ↔ ∀ x, ‖(p - (Star.star p * p)) x‖ = 0 := by
          simp only [norm_eq_zero, sub_apply, sub_eq_zero]
          rw [@ContinuousLinearMap.ext_iff]
        _ ↔ ∀ x, ‖(ContinuousLinearMap.adjoint (1 - p)) (p x)‖ = 0 := by
          simp only [← ContinuousLinearMap.star_eq_adjoint, star_sub, star_one,
            sub_apply, mul_apply_eq_comp]
          rfl
        _ ↔ ∀ x, ‖(1 - p) (p x)‖ = 0 := by simp only [this]
        _ ↔ ∀ x, ‖(p - p * p) x‖ = 0 := by simp
        _ ↔ p - p * p = 0 := by
          simp only [norm_eq_zero, ContinuousLinearMap.ext_iff, zero_apply]
        _ ↔ IsIdempotentElem p := by simp only [sub_eq_zero, IsIdempotentElem, eq_comm]
    rw [this.mpr hp]
    exact IsSelfAdjoint.star_mul_self _

open scoped InnerProductSpace
theorem LinearMap.IsPositive'.add_ker_eq_inf_ker
  {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] {S T : V →ₗ[𝕜] V} (hS : S.IsPositive') (hT : T.IsPositive') :
    LinearMap.ker (S + T) = LinearMap.ker S ⊓ LinearMap.ker T := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.add_apply, Submodule.mem_inf]
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2, add_zero]⟩
  rw [eq_comm, ← sub_eq_iff_eq_add, eq_comm, zero_sub] at h
  rw [h, neg_eq_zero, and_self]
  have : ⟪x, S x⟫_𝕜 = 0 := le_antisymm
    (by rw [h, inner_neg_right, neg_le, neg_zero]; exact hT.2 x)
    (hS.2 x)
  obtain ⟨f, rfl⟩ := (LinearMap.isPositive'_iff_exists_adjoint_hMul_self _).mp hS
  simp only [Module.End.mul_apply, LinearMap.adjoint_inner_right, inner_self_eq_zero] at this
  simp only [Module.End.mul_apply, this, map_zero, zero_eq_neg] at h
  exact h

theorem mem_unitary_iff_isStarNormal_and_decomposition_left_sq_add_right_sq_eq_one
  {B : Type*} [Ring B] [StarRing B]
  [Module ℂ B] [StarModule ℂ B] [IsScalarTower ℂ B B]
  [SMulCommClass ℂ B B] (a : B) :
    a ∈ unitary B ↔ IsStarNormal a ∧ (aL a) ^ 2 + (aR a) ^ 2 = 1 := by
  have this1 :=
    calc a * star a = (aL a + Complex.I • aR a) * star (aL a + Complex.I • aR a) :=
        by simp_rw [← RCLike.I_to_complex, ← selfAdjointDecomposition]
      _ = (aL a * aL a + aR a * aR a) + Complex.I • ((aR a * aL a) - (aL a * aR a)) := by
          rw [star_add]
          nth_rw 2 [star_smul]
          rw [Complex.star_def, Complex.conj_I, neg_smul,
            isSelfAdjoint_iff.mp (selfAdjointDecompositionLeft_isSelfAdjoint _),
            isSelfAdjoint_iff.mp (selfAdjointDecompositionRight_isSelfAdjoint _),
            ← smul_neg]
          simp_rw [complex_decomposition_mul_decomposition, mul_neg, sub_neg_eq_add,
            sub_eq_add_neg]
      _ = ((aL a) ^ 2 + (aR a) ^ 2) + Complex.I • (aR a * aL a - aL a * aR a) :=
        by simp only [pow_two, smul_sub]
  rw [Unitary.mem_iff]
  constructor
  · intro h
    have : Commute (aL a) (aR a) :=
    by rw [← isStarNormal_iff_selfAdjointDecomposition_commute, isStarNormal_iff, commute_iff_eq,
      h.1, h.2]
    simp_rw [isStarNormal_iff_selfAdjointDecomposition_commute, this, true_and]
    rw [this1, this, sub_self, smul_zero, add_zero] at h
    exact h.2
  · rintro ⟨h1, h2⟩
    rw [(isStarNormal_iff _).mp h1, and_self, this1, h2, add_comm]
    apply add_eq_of_eq_sub
    rw [sub_self, smul_eq_zero, sub_eq_zero]
    right
    exact ((isStarNormal_iff_selfAdjointDecomposition_commute _).mp h1).symm

theorem LinearMap.exists_scalar_isometry_iff_preserves_ortho_of_ne_zero
  {𝕜 V W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
  (hV : 0 < Module.finrank 𝕜 V)
  {T : V →ₗ[𝕜] W} (hT : T ≠ 0) :
  (∃ (α : 𝕜ˣ), Isometry ((α : 𝕜) • T))
  ↔
  ∀ x y, ⟪x, y⟫_𝕜 = 0 → ⟪T x, T y⟫_𝕜 = 0 := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hV
  constructor
  · rintro ⟨α, h⟩ x y hxy
    have : ⟪T x, T y⟫_𝕜 = 0 ↔ ⟪((α : 𝕜) • T) x, ((α : 𝕜) • T) y⟫_𝕜 = 0 := by
        simp_rw [LinearMap.smul_apply, inner_smul_right, inner_smul_left,
          ← mul_assoc, RCLike.mul_conj, mul_eq_zero, sq_eq_zero_iff,
          RCLike.ofReal_eq_zero, norm_eq_zero]
        simp only [Units.ne_zero, false_or]
    rw [this, (isometry_iff_inner _).mp h, hxy]
  · intro h
    haveI : FiniteDimensional 𝕜 V := Module.finite_of_finrank_pos hV
    let e := stdOrthonormalBasis 𝕜 V
    have : ∀ i j, ⟪e i + e j, e i - e j⟫_𝕜 = 0 :=
    fun i j => by
      simp only [inner_add_left, inner_sub_right,
        orthonormal_iff_ite.mp (e.orthonormal)]
      simp only [↓reduceIte, eq_comm]
      ring
    have h' : ∀ i j, ⟪T (e i), T (e j)⟫_𝕜 =
        if i = j then ((‖T (e i)‖ ^ 2) : 𝕜) else 0 :=
    fun i j => by
      split_ifs with h'
      · simp only [h', inner_self_eq_norm_sq_to_K]
      · apply h
        simp only [orthonormal_iff_ite.mp (e.orthonormal), h', reduceIte]
    have this' := fun i j => h _ _ (this i j)
    simp only [map_add, map_sub, inner_add_left, inner_sub_right, h',
      reduceIte, add_ite, ite_add, eq_comm, ite_sub_ite] at this'
    simp only [sub_self, add_zero, zero_add] at this'
    simp_rw [@eq_comm _ (0 : 𝕜), ite_eq_iff, and_true, sub_eq_zero] at this'
    let α : ℝ := ‖T (e ⟨0, hV⟩)‖
    simp only [← RCLike.ofReal_pow, RCLike.ofReal_inj,
      sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] at this'
    have hα : ∀ i, α = ‖T (e i)‖ := fun i => by
      by_cases hi : i = ⟨0, hV⟩
      · rw [hi]
      · specialize this' ⟨0, hV⟩ i
        simp only [hi, eq_comm, false_or, not_false_iff, true_and] at this'
        simp only [α, this']
    have : ∀ x, ‖T x‖ = α * ‖x‖ :=
    fun x => by
      simp_rw [hα ⟨0, hV⟩]
      rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
        ← RCLike.ofReal_inj (K := 𝕜), RCLike.ofReal_pow,
        mul_pow, RCLike.ofReal_mul, RCLike.ofReal_pow, ← hα, RCLike.ofReal_pow]
      rw [← OrthonormalBasis.sum_repr e x]
      simp_rw [← inner_self_eq_norm_sq_to_K]
      simp only [map_sum, map_smul, sum_inner, inner_smul_left,
        inner_sum, inner_smul_right, h', mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, ← hα]
      simp only [← mul_assoc, RCLike.mul_conj, orthonormal_iff_ite.mp (e.orthonormal),
        mul_boole, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp_rw [← Finset.sum_mul, mul_comm]
    have hα' : α = 0 ↔ T = 0 := by
      constructor
      · intro h
        simp_rw [h, zero_mul, norm_eq_zero] at this
        ext x
        simp only [LinearMap.zero_apply, this]
      · intro h
        simp only [h, LinearMap.zero_apply, norm_zero, @eq_comm _ (0 : ℝ),
          mul_eq_zero, norm_eq_zero] at this
        obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := by exact exists_ne 0
        specialize this x
        simp only [hx, or_false] at this
        exact this
    simp only [hT, iff_false, ← ne_eq] at hα'
    have hα'' : (α : 𝕜) ≠ 0 := by simp only [ne_eq, algebraMap.coe_eq_zero_iff, hα',
      not_false_iff]
    use ((Units.mk0 α hα'')⁻¹ : 𝕜ˣ)
    rw [isometry_iff_norm]
    intro x
    simp only [LinearMap.smul_apply, norm_smul, this]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv, RCLike.norm_ofReal]
    simp only [abs_of_nonneg (norm_nonneg _),
      ← hα, α, ← mul_assoc, inv_mul_cancel₀ hα', one_mul]

theorem LinearMap.exists_scalar_isometry_iff_preserves_ortho
  {𝕜 V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [Module.Finite 𝕜 V]
  {T : V →ₗ[𝕜] V} :
  (∃ (α : 𝕜) (S : V →ₗᵢ[𝕜] V), T = α • S.toLinearMap)
  ↔
  ∀ x y, ⟪x, y⟫_𝕜 = 0 → ⟪T x, T y⟫_𝕜 = 0 := by
  constructor
  · rintro ⟨α, S, h⟩ x y hxy
    simp only [h, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
      LinearIsometry.coe_toLinearMap, LinearIsometry.inner_map_map, hxy, mul_zero]
  · intro h
    by_cases hT : T = 0
    · rw [hT]
      use 0, 1
      simp only [zero_smul]
    · by_cases hV : Module.rank 𝕜 V = 0
      · rw [rank_zero_iff_forall_zero] at hV
        simp only [LinearMap.ext_iff,
          hV, implies_true, exists_true_iff_nonempty]
        use 0, 0
        simp only [norm_zero, hV, implies_true]
      · simp only [← pos_iff_ne_zero] at hV
        rw [rank_pos_iff_nontrivial] at hV
        have : 0 < Module.finrank 𝕜 V := Module.finrank_pos
        obtain ⟨α, hα⟩ :=
          (LinearMap.exists_scalar_isometry_iff_preserves_ortho_of_ne_zero this hT).mpr h
        use (α⁻¹ : 𝕜ˣ), ⟨((α : 𝕜) • T), (isometry_iff_norm _).mp hα⟩
        simp only [Units.val_inv_eq_inv_val, ne_eq, Units.ne_zero, not_false_eq_true,
          inv_smul_smul₀]

theorem LinearMap.isSymmetric_adjoint_mul_self'
  {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
  [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
  (T : V →ₗ[𝕜] W) :
    IsSymmetric (LinearMap.adjoint T ∘ₗ T) := by
  intro x y
  simp only [coe_comp, Function.comp_apply, adjoint_inner_left, adjoint_inner_right]
