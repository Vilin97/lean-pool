/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Basic
import LeanPool.Monlib4.LinearAlgebra.InnerAut
import LeanPool.Monlib4.LinearAlgebra.Matrix.Reshape
import LeanPool.Monlib4.Preq.StarAlgEquiv

/-!
# Linear equivalence conjugation compatibility

Mathlib's `LinearEquiv.conjAlgEquiv` is the current version of the upstream
`LinearEquiv.innerConj` construction used by the Monlib4 `IncludeBlock` slice.
-/

open scoped BigOperators
open Matrix Module.End InnerProductSpace

variable {𝕜 : Type _} [RCLike 𝕜]

/-- Star-algebra equivalence from endomorphisms of a finite-dimensional inner-product
space to matrices in an orthonormal basis. -/
noncomputable def OrthonormalBasis.toMatrix {n E : Type _} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (b : OrthonormalBasis n 𝕜 E) :
    (E →ₗ[𝕜] E) ≃⋆ₐ[𝕜] Matrix n n 𝕜 where
  toFun x k p := inner 𝕜 (b k) (x (b p))
  invFun x := ∑ i, ∑ j,
    x i j • (InnerProductSpace.rankOne 𝕜 (b i) (b j)).toLinearMap
  map_add' x y := by
    simp only [LinearMap.add_apply, inner_add_right]
    rfl
  map_smul' r x := by
    simp only [LinearMap.smul_apply, inner_smul_right]
    rfl
  map_mul' x y := by
    ext
    simp only [Module.End.mul_apply, Matrix.mul_apply, ← LinearMap.adjoint_inner_left x,
      OrthonormalBasis.sum_inner_mul_inner]
  map_star' x := by
    ext
    simp only [star_eq_conjTranspose, conjTranspose_apply, LinearMap.star_eq_adjoint,
      LinearMap.adjoint_inner_right, RCLike.star_def, inner_conj_symm]
  right_inv x := by
    ext
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply, inner_sum, smul_smul, inner_smul_right]
    simp only [orthonormal_iff_ite.mp b.orthonormal, mul_boole, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  left_inv x := by
    ext
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply, ← LinearMap.adjoint_inner_left x, smul_smul,
      ← Finset.sum_smul, OrthonormalBasis.sum_inner_mul_inner]
    simp_rw [LinearMap.adjoint_inner_left, ← OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.sum_repr]

theorem OrthonormalBasis.toMatrix_apply {n E : Type _} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (b : OrthonormalBasis n 𝕜 E) (x : E →ₗ[𝕜] E) (i j : n) :
    b.toMatrix x i j = inner 𝕜 (b i) (x (b j)) :=
  rfl

theorem OrthonormalBasis.toMatrix_symm_apply {n E : Type _} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (b : OrthonormalBasis n 𝕜 E) (x : Matrix n n 𝕜) :
    b.toMatrix.symm x =
      ∑ i, ∑ j, x i j • (InnerProductSpace.rankOne 𝕜 (b i) (b j)).toLinearMap :=
  rfl

theorem OrthonormalBasis.toMatrix_symm_apply' {n E : Type _} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (b : OrthonormalBasis n 𝕜 E) (x : Matrix n n 𝕜) :
    b.toMatrix.symm x =
      ∑ i, ∑ j, x i j • (InnerProductSpace.rankOne 𝕜 (b i) (b j)).toLinearMap :=
  OrthonormalBasis.toMatrix_symm_apply b x

theorem orthonormalBasis_toMatrix_eq_basis_toMatrix {n E : Type _} [Fintype n]
    [DecidableEq n] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] (b : OrthonormalBasis n 𝕜 E) :
    LinearMap.toMatrixAlgEquiv b.toBasis = b.toMatrix.toAlgEquiv := by
  ext
  simp_rw [StarAlgEquiv.coe_toAlgEquiv, OrthonormalBasis.toMatrix_apply,
    LinearMap.toMatrixAlgEquiv_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]

alias EuclideanSpace.orthonormalBasis := EuclideanSpace.basisFun

theorem EuclideanSpace.orthonormalBasis.repr_eq_one {n : Type _} [Fintype n] :
    (EuclideanSpace.orthonormalBasis n 𝕜 :
      OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)).repr = 1 :=
  rfl

theorem LinearIsometryEquiv.toLinearEquiv_one {R E : Type _} [Semiring R]
    [SeminormedAddCommGroup E] [Module R E] :
    (1 : E ≃ₗᵢ[R] E).toLinearEquiv = 1 :=
  rfl

theorem LinearEquiv.one_symm {R E : Type _} [Semiring R] [AddCommMonoid E]
    [Module R E] :
    (1 : E ≃ₗ[R] E).symm = 1 :=
  rfl

theorem LinearEquiv.toLinearMap_one {R E : Type _} [Semiring R]
    [AddCommMonoid E] [Module R E] :
    (1 : E ≃ₗ[R] E).toLinearMap = 1 :=
  rfl

theorem LinearEquiv.refl_conj {R E : Type _} [CommSemiring R] [AddCommMonoid E]
    [Module R E] :
    (LinearEquiv.refl R E).conj = 1 := by
  ext
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.refl_apply, LinearEquiv.refl_symm]
  rfl

theorem LinearEquiv.conj_hMul {R E F : Type _} [CommSemiring R] [AddCommMonoid E]
    [AddCommMonoid F] [Module R E] [Module R F] (f : E ≃ₗ[R] F)
    (x y : Module.End R E) :
    f.conj (x * y) = f.conj x * f.conj y := by
  simp only [mul_eq_comp, LinearEquiv.conj_comp]

theorem LinearEquiv.conj_apply_one {R E F : Type _} [CommSemiring R]
    [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]
    (f : E ≃ₗ[R] F) : f.conj 1 = 1 :=
  LinearEquiv.conj_id _

theorem LinearEquiv.conj_one {R E : Type _} [CommSemiring R] [AddCommMonoid E]
    [Module R E] :
    (1 : E ≃ₗ[R] E).conj = 1 := by
  ext
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rfl

theorem LinearEquiv.one_apply {R E : Type _} [CommSemiring R] [AddCommMonoid E]
    [Module R E] (x : E) :
    (1 : E ≃ₗ[R] E) x = x :=
  rfl

theorem OrthonormalBasis.std_toMatrix {n : Type _} [Fintype n] [DecidableEq n] :
    (((EuclideanSpace.orthonormalBasis n 𝕜).toMatrix).symm).toLinearEquiv
      = Matrix.toEuclideanLin :=
  by
  change ((EuclideanSpace.orthonormalBasis n 𝕜).toMatrix.toAlgEquiv.symm).toLinearEquiv
    = Matrix.toEuclideanLin
  rw [← orthonormalBasis_toMatrix_eq_basis_toMatrix]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rfl

namespace LinearEquiv

/-- Conjugate endomorphism algebras along a linear equivalence. -/
def innerConj {R E F : Type*} [CommSemiring R] [AddCommMonoid E] [AddCommMonoid F]
    [Module R E] [Module R F] (e : E ≃ₗ[R] F) :
    Module.End R E ≃ₐ[R] Module.End R F :=
  e.conjAlgEquiv R

theorem innerConj_apply {R E F : Type*} [CommSemiring R] [AddCommMonoid E]
    [AddCommMonoid F] [Module R E] [Module R F] (e : E ≃ₗ[R] F)
    (f : Module.End R E) :
    e.innerConj f = e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap :=
  rfl

end LinearEquiv

variable {R I J : Type _} [Fintype I] [Fintype J] [CommSemiring R]
  [DecidableEq I] [DecidableEq J]

open scoped BigOperators
open Matrix Module.End

theorem Matrix.stdBasis_repr_eq_reshape {R I J : Type _} [Fintype I] [Finite J]
    [CommSemiring R] :
    (Matrix.stdBasis R I J).equivFun = Matrix.reshape :=
  by
  classical
  ext x ij
  rw [Module.Basis.equivFun_apply]
  exact (Matrix.stdBasis R I J).repr_apply_eq Matrix.reshape
    (by intro x y; ext ij; simp [Matrix.reshape_apply])
    (by intro c x; ext ij; simp [Matrix.reshape_apply])
    (by
      intro i
      ext j
      simp only [Finsupp.single_apply]
      calc Matrix.reshape (Matrix.stdBasis R I J i) j =
          Matrix.reshape (Matrix.single i.1 i.2 (1 : R)) j := by
            rw [Matrix.stdBasis_eq_single]
        _ = Matrix.single i.1 i.2 (1 : R) j.1 j.2 := rfl
        _ = if i = j then 1 else 0 := by
          simp_rw [Matrix.single, Matrix.of_apply, ← Prod.eq_iff_fst_eq_snd_eq])
    x ij

namespace LinearMap

open scoped Matrix BigOperators

theorem toMatrix_stdBasis_stdBasis {K L : Type _} [Fintype K] [Finite L]
    (x : Matrix I J R →ₗ[R] Matrix K L R) :
    toMatrix (Matrix.stdBasis R I J) (Matrix.stdBasis R K L) x =
      LinearMap.toMatrix' (Matrix.reshape.toLinearMap ∘ₗ
        x ∘ₗ Matrix.reshape.symm.toLinearMap) :=
  rfl

theorem toLin_stdBasis_stdBasis {K L : Type _} [Fintype K] [Finite L]
    (x : Matrix (K × L) (I × J) R) :
    (toLin (Matrix.stdBasis R I J) (Matrix.stdBasis R K L)) x =
      (Matrix.reshape : Matrix K L R ≃ₗ[R] _).symm.toLinearMap ∘ₗ
        toLin' x ∘ₗ (Matrix.reshape : Matrix I J R ≃ₗ[R] _).toLinearMap :=
  rfl

/-- Identify endomorphisms of a matrix space with matrices on the reshaped index type. -/
def toMatrixOfAlgEquiv : (Matrix I J R →ₗ[R] Matrix I J R) ≃ₐ[R]
    Matrix (I × J) (I × J) R :=
  (Matrix.reshape : Matrix I J R ≃ₗ[R] _).innerConj.trans toMatrixAlgEquiv'

theorem toMatrixOfAlgEquiv_apply (x : Matrix I J R →ₗ[R] Matrix I J R) :
    toMatrixOfAlgEquiv x =
      toMatrixAlgEquiv' ((Matrix.reshape : Matrix I J R ≃ₗ[R] _).toLinearMap ∘ₗ
        x ∘ₗ (Matrix.reshape : Matrix I J R ≃ₗ[R] _).symm.toLinearMap) :=
  rfl

theorem toMatrixOfAlgEquiv_symm_apply (x : Matrix (I × J) (I × J) R) :
    toMatrixOfAlgEquiv.symm x =
      (Matrix.reshape : Matrix I J R ≃ₗ[R] _).symm.toLinearMap ∘ₗ
        toMatrixAlgEquiv'.symm x ∘ₗ (Matrix.reshape : Matrix I J R ≃ₗ[R] _).toLinearMap :=
  rfl

theorem toMatrixOfAlgEquiv_apply' (x : Matrix I J R →ₗ[R] Matrix I J R)
    (ij kl : I × J) :
    toMatrixOfAlgEquiv x ij kl = x (Matrix.single kl.1 kl.2 (1 : R)) ij.1 ij.2 := by
  simp_rw [toMatrixOfAlgEquiv_apply, toMatrixAlgEquiv'_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Matrix.reshape_apply]
  have hsingle :
      (Matrix.reshape : Matrix I J R ≃ₗ[R] I × J → R).symm (Pi.single kl 1) =
        Matrix.single kl.1 kl.2 (1 : R) := by
    ext i j
    rw [Matrix.reshape_symm_apply, Matrix.single_apply]
    simp [Pi.single_apply, Prod.ext_iff, eq_comm]
  rw [hsingle]

end LinearMap

namespace Matrix

/-- The inverse algebra equivalence turning a matrix on `I × J` into an endomorphism
of `Matrix I J R`. -/
def toLinOfAlgEquiv : Matrix (I × J) (I × J) R ≃ₐ[R]
    Matrix I J R →ₗ[R] Matrix I J R :=
  LinearMap.toMatrixOfAlgEquiv.symm

theorem toLinOfAlgEquiv_apply (x : Matrix (I × J) (I × J) R)
    (y : Matrix I J R) :
    toLinOfAlgEquiv x y =
      (reshape : Matrix I J R ≃ₗ[R] I × J → R).symm (toLinAlgEquiv' x (reshape y)) :=
  rfl

/-- Rank-one endomorphism on the standard basis of a matrix space. -/
def rankOneStdBasis {I J : Type _} [DecidableEq I] [DecidableEq J]
    (ij kl : I × J) (r : R) : Matrix I J R →ₗ[R] Matrix I J R where
  toFun x := single ij.1 ij.2 (r • r • x kl.1 kl.2)
  map_add' x y := by
    simp_rw [Matrix.add_apply, smul_add, single_add]
  map_smul' r x := by
    simp_rw [RingHom.id_apply, Matrix.smul_apply, smul_single, smul_smul, mul_rotate']

theorem rankOneStdBasis_apply {I J : Type _} [DecidableEq I] [DecidableEq J]
    (ij kl : I × J) (r : R) (x : Matrix I J R) :
    rankOneStdBasis ij kl r x = single ij.1 ij.2 (r • r • x kl.1 kl.2) :=
  rfl

open scoped BigOperators

theorem toLinOfAlgEquiv_eq (x : Matrix (I × J) (I × J) R) :
    toLinOfAlgEquiv x =
      ∑ ij : I × J, ∑ kl : I × J, x ij kl • rankOneStdBasis ij kl (1 : R) := by
  simp_rw [LinearMap.ext_iff, ← ext_iff, toLinOfAlgEquiv_apply, reshape_symm_apply,
    LinearMap.sum_apply, Matrix.sum_apply, toLinAlgEquiv'_apply, mulVec, dotProduct,
    reshape_apply, LinearMap.smul_apply, Matrix.smul_apply, rankOneStdBasis_apply, single,
    of_apply, smul_ite, ← Prod.mk_inj, Prod.mk.eta, one_smul, smul_zero, smul_eq_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    forall₃_true_iff]

theorem toLinOfAlgEquiv_toMatrixOfAlgEquiv (x : Matrix (I × J) (I × J) R) :
    LinearMap.toMatrixOfAlgEquiv (toLinOfAlgEquiv x) = x := by
  rw [toLinOfAlgEquiv, AlgEquiv.apply_symm_apply]

end Matrix

open Matrix

theorem LinearMap.toMatrixOfAlgEquiv_toLinOfAlgEquiv
    (x : Matrix I J R →ₗ[R] Matrix I J R) :
    toLinOfAlgEquiv (toMatrixOfAlgEquiv x) = x := by
  rw [toLinOfAlgEquiv, AlgEquiv.symm_apply_apply]

open scoped Kronecker Matrix

variable {n 𝕜 : Type _} [Fintype n] [DecidableEq n] [RCLike 𝕜]

theorem innerAut_toMatrix (U : unitaryGroup n 𝕜) :
    LinearMap.toMatrixOfAlgEquiv (innerAut U) = U ⊗ₖ Uᴴᵀ := by
  ext
  simp_rw [LinearMap.toMatrixOfAlgEquiv_apply', innerAut_apply', Matrix.mul_apply,
    Matrix.single, Matrix.of_apply, mul_ite, mul_one, MulZeroClass.mul_zero,
    Finset.sum_mul, ite_mul, MulZeroClass.zero_mul, ite_and,
    ← unitaryGroup.star_coe_eq_coe_star, star_apply, kroneckerMap_apply, conj_apply]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem innerAut_coord (U : unitaryGroup n 𝕜) (ij kl : n × n) :
    (LinearMap.toMatrixOfAlgEquiv (innerAut U)) ij kl =
      U ij.1 kl.1 * star (U ij.2 kl.2) := by
  rw [innerAut_toMatrix]
  rfl

theorem innerAut_inv_coord (U : unitaryGroup n ℂ) (ij kl : n × n) :
    LinearMap.toMatrixOfAlgEquiv (innerAut U⁻¹) ij kl =
      U kl.2 ij.2 * star (U kl.1 ij.1) := by
  simp_rw [innerAut_toMatrix, UnitaryGroup.inv_apply, star_eq_conjTranspose,
    kroneckerMap_apply, conj_apply, conjTranspose_apply, star_star, mul_comm]
