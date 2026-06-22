/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.RCLike.Basic
import LeanPool.Monlib4.LinearAlgebra.Matrix.Conj
import LeanPool.Monlib4.LinearAlgebra.Ips.RankOne

/-!
# Matrix basics

Basic matrix lemmas used by the monlib4 automorphism-of-matrix-algebras
formalization.
-/

namespace Matrix

open scoped BigOperators Matrix Kronecker

/-- Compatibility name for the old Monlib/mathlib3 matrix unit API. -/
abbrev stdBasisMatrix {R n m : Type _} [Zero R] [DecidableEq n] [DecidableEq m]
    (i : n) (j : m) (a : R) : Matrix n m R :=
  single i j a

theorem eq_zero {R n₁ n₂ : Type _} [Zero R] (x : Matrix n₁ n₂ R) :
    (∀ (i : n₁) (j : n₂), x i j = 0) ↔ x = 0 := by
  simp_rw [← Matrix.ext_iff, Matrix.zero_apply]

theorem mulVec_stdBasis {R m n : Type _} [Semiring R] [Fintype n]
    (a : Matrix m n R) (i : m) (j : n) :
    (a.mulVec (Pi.basisFun R n j)) i = a i j := by
  classical
  simp_rw [mulVec, dotProduct, Pi.basisFun_apply, Pi.single_apply,
    mul_boole, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mulVec_eq {R m n : Type _} [CommSemiring R] [Fintype n]
    (a b : Matrix m n R) :
    a = b ↔ ∀ c : n → R, a.mulVec c = b.mulVec c := by
  refine ⟨fun h c => by rw [h], fun h => ?_⟩
  ext i j
  rw [← mulVec_stdBasis a i j, ← mulVec_stdBasis b i j, h _]

/-- A vector is nonzero iff at least one entry is nonzero. -/
theorem vec_ne_zero {R n : Type _} [Semiring R] (a : n → R) :
    (∃ i, a i ≠ 0) ↔ a ≠ 0 := by
  simp_rw [ne_eq, ← Classical.not_forall]
  constructor
  · intro h hzero
    simp_rw [hzero, Pi.zero_apply, imp_true_iff, not_true] at h
  · intro h hentries
    apply h
    ext x
    rw [Pi.zero_apply]
    exact hentries x

/-- Two vectors are equal iff their entries are equal. -/
theorem ext_vec {𝕜 n : Type _} (α β : n → 𝕜) :
    α = β ↔ ∀ i : n, α i = β i := by
  refine ⟨fun h i => by rw [h], fun h => ?_⟩
  ext i
  exact h i

/-- The transpose of `vecMulVec x y` is `vecMulVec y x`. -/
theorem vecMulVec_transpose {R n : Type _} [CommSemiring R] (x y : n → R) :
    (vecMulVec x y).transpose = vecMulVec y x := by
  simp_rw [← Matrix.ext_iff, transpose_apply, vecMulVec, mul_comm, of_apply,
    forall₂_true_iff]

theorem smul_mulVec_assoc {R m n : Type _} [Semiring R] [Fintype n]
    (r : R) (x : Matrix m n R) (y : n → R) :
    (r • x) *ᵥ y = r • (x *ᵥ y) := by
  ext i
  simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- The identity matrix as a sum of standard matrix units. -/
theorem one_eq_sum_std_matrix {n R : Type _} [CommSemiring R] [Fintype n] [DecidableEq n] :
    (1 : Matrix n n R) = ∑ r : n, Matrix.single r r (1 : R) := by
  simp_rw [← Matrix.ext_iff, Matrix.sum_apply, Matrix.one_apply, Matrix.single, ite_and,
    of_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true, forall₂_true_iff]

/-- The trace of a Kronecker product is the product of traces. -/
theorem kronecker_trace {R n : Type _} [CommSemiring R] [Fintype n]
    (A B : Matrix n n R) :
    (A ⊗ₖ B).trace = A.trace * B.trace := by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.kroneckerMap, Finset.sum_mul_sum,
    Matrix.of_apply, Fintype.sum_prod_type]

theorem _root_.Matrix.kronecker.trace {R n : Type _} [CommSemiring R] [Fintype n]
    (A B : Matrix n n R) :
    (A ⊗ₖ B).trace = A.trace * B.trace :=
  kronecker_trace A B

/-- The unitary eigenvector matrix associated to a Hermitian matrix. -/
noncomputable abbrev _root_.Matrix.IsHermitian.eigenvectorMatrix {n 𝕜 : Type*} [RCLike 𝕜]
    [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Matrix n n 𝕜 :=
  hA.eigenvectorUnitary

lemma _root_.Matrix.IsHermitian.eigenvectorUnitary_coe_eq_eigenvectorMatrix {n 𝕜 : Type*} [RCLike 𝕜]
    [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hA.eigenvectorMatrix = hA.eigenvectorUnitary :=
  rfl

lemma _root_.Matrix.IsHermitian.eigenvalues_eq' {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) (i : n) :
    hA.eigenvalues i =
      RCLike.re (star (hA.eigenvectorMatrixᵀ i) ⬝ᵥ A *ᵥ hA.eigenvectorMatrixᵀ i) := by
  simpa [IsHermitian.eigenvectorMatrix, Matrix.IsHermitian.eigenvectorUnitary_transpose_apply] using
    hA.eigenvalues_eq i

lemma _root_.Matrix.IsHermitian.eigenvectorMatrix_conjTranspose {n 𝕜 : Type*} [RCLike 𝕜]
    [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hA.eigenvectorMatrixᴴ = (hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ :=
  rfl

theorem _root_.Matrix.IsHermitian.eigenvectorMatrix_mul_conjTranspose {n 𝕜 : Type*} [RCLike 𝕜]
    [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hA.eigenvectorMatrix * hA.eigenvectorMatrixᴴ = 1 := by
  rw [IsHermitian.eigenvectorMatrix, ← star_eq_conjTranspose]
  exact (SetLike.coe_mem hA.eigenvectorUnitary).2

theorem _root_.Matrix.IsHermitian.trace_eq {𝕜 n : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A.trace = ∑ i : n, hA.eigenvalues i := by
  simpa using hA.trace_eq_sum_eigenvalues

theorem _root_.LinearMap.IsSymmetric.eigenvalue_mem_spectrum {𝕜 n : Type _} [RCLike 𝕜]
    [Fintype n] {E : Type _} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E}
    (hn : Module.finrank 𝕜 E = Fintype.card n) (hA : A.IsSymmetric)
    (i : Fin (Fintype.card n)) :
    (hA.eigenvalues hn i : 𝕜) ∈ spectrum 𝕜 A := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  exact hA.hasEigenvalue_eigenvalues hn i

theorem _root_.Matrix.IsHermitian.eigenvalues_hasEigenvalue {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.IsHermitian) (i : n) :
    Module.End.HasEigenvalue (toEuclideanLin M) (hM.eigenvalues i) := by
  simp_rw [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀]
  exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ _

theorem _root_.Matrix.IsHermitian.hasEigenvector_eigenvectorBasis
    {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.IsHermitian) (i : n) :
    Module.End.HasEigenvector (toEuclideanLin M) (hM.eigenvalues i) (hM.eigenvectorBasis i) := by
  simp_rw [Matrix.IsHermitian.eigenvectorBasis, Matrix.IsHermitian.eigenvalues,
    Matrix.IsHermitian.eigenvalues₀, OrthonormalBasis.reindex_apply]
  exact LinearMap.IsSymmetric.hasEigenvector_eigenvectorBasis _ _ _

theorem _root_.Matrix.IsHermitian.apply_eigenvectorBasis {𝕜 n : Type _} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.IsHermitian) (i : n) :
    M.mulVec (hM.eigenvectorBasis i) = hM.eigenvalues i • hM.eigenvectorBasis i := by
  simpa using hM.mulVec_eigenvectorBasis i

/-- Expand a square matrix indexed by a product as a sum of Kronecker products of matrix units. -/
theorem kmul_representation {R n₁ n₂ : Type _} [Fintype n₁] [Fintype n₂]
    [DecidableEq n₁] [DecidableEq n₂] [Semiring R]
    (x : Matrix (n₁ × n₂) (n₁ × n₂) R) :
    x =
      ∑ i : n₁, ∑ j : n₁, ∑ k : n₂, ∑ l : n₂,
        x (i, k) (j, l) • Matrix.single i j (1 : R) ⊗ₖ Matrix.single k l (1 : R) := by
  simp_rw [← Matrix.ext_iff, Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap,
    Matrix.single, Matrix.of_apply, ite_mul, MulZeroClass.zero_mul, one_mul, smul_ite,
    smul_zero, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Prod.mk.eta, smul_eq_mul, mul_one, forall₂_true_iff]

theorem kronecker_conjTranspose {R m n : Type _} [CommSemiring R] [StarRing R]
    (x : Matrix n n R) (y : Matrix m m R) :
    (x ⊗ₖ y)ᴴ = xᴴ ⊗ₖ yᴴ := by
  simp_rw [← Matrix.ext_iff, conjTranspose_apply, kroneckerMap, of_apply, star_mul',
    conjTranspose_apply, forall₂_true_iff]

theorem kronecker_star {R n : Type _} [CommSemiring R] [StarRing R] (x y : Matrix n n R) :
    star (x ⊗ₖ y) = star x ⊗ₖ star y :=
  Matrix.kronecker_conjTranspose _ _

theorem _root_.Matrix.kronecker.star {R n : Type _} [CommSemiring R] [StarRing R]
    (x y : Matrix n n R) :
    star (x ⊗ₖ y) = star x ⊗ₖ star y :=
  kronecker_star x y

theorem kronecker_transpose {R n : Type _} [CommSemiring R] (x y : Matrix n n R) :
    (x ⊗ₖ y)ᵀ = xᵀ ⊗ₖ yᵀ := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.kroneckerMap, of_apply]

theorem _root_.Matrix.kronecker.transpose {R n : Type _} [CommSemiring R] (x y : Matrix n n R) :
    (x ⊗ₖ y)ᵀ = xᵀ ⊗ₖ yᵀ :=
  kronecker_transpose x y

theorem kronecker_conj {R n : Type _} [CommSemiring R] [StarRing R] (x y : Matrix n n R) :
    (x ⊗ₖ y)ᴴᵀ = xᴴᵀ ⊗ₖ yᴴᵀ := by
  rw [Matrix.conj, Matrix.kronecker_conjTranspose, Matrix.kronecker_transpose]
  rfl

theorem _root_.Matrix.kronecker.conj {R n : Type _} [CommSemiring R] [StarRing R]
    (x y : Matrix n n R) :
    (x ⊗ₖ y)ᴴᵀ = xᴴᵀ ⊗ₖ yᴴᵀ :=
  kronecker_conj x y

theorem _root_.Matrix.unitaryGroup.coe_mk {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (x : Matrix n n 𝕜) (hx : x ∈ Matrix.unitaryGroup n 𝕜) :
    ⇑(⟨x, hx⟩ : Matrix.unitaryGroup n 𝕜) = x :=
  rfl

end Matrix

open scoped BigOperators InnerProductSpace Kronecker

theorem kmul_representation {R n₁ n₂ : Type _} [Fintype n₁] [Fintype n₂] [DecidableEq n₁]
    [DecidableEq n₂] [Semiring R] (x : Matrix (n₁ × n₂) (n₁ × n₂) R) :
    x =
      ∑ i : n₁, ∑ j : n₁, ∑ k : n₂, ∑ l : n₂,
        x (i, k) (j, l) • Matrix.single i j (1 : R) ⊗ₖ Matrix.single k l (1 : R) :=
  Matrix.kmul_representation x

noncomputable instance EuclideanSpace.instInnerPi {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] :
    Inner 𝕜 (n → 𝕜) :=
  { inner := fun x y =>
      ⟪(EuclideanSpace.equiv n 𝕜).symm x, (EuclideanSpace.equiv n 𝕜).symm y⟫_𝕜 }

theorem EuclideanSpace.inner_eq {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] {x y : n → 𝕜} :
    inner 𝕜 x y = star (x : n → 𝕜) ⬝ᵥ (y : n → 𝕜) := by
  change (∑ i, y i * star (x i)) = ∑ i, star (x i) * y i
  exact Finset.sum_congr rfl fun i _ => mul_comm (y i) (star (x i))

theorem EuclideanSpace.rankOne_of_orthonormalBasis_eq_one {n 𝕜 : Type _} [RCLike 𝕜]
    [Fintype n] (h : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) :
    ∑ i : n, rankOne 𝕜 (h i) (h i) = 1 := by
  simpa using rankOne.sum_orthonormalBasis_eq_id h

open scoped Matrix

variable {R n m : Type _} [Semiring R] [StarAddMonoid R] [DecidableEq n] [DecidableEq m]

theorem Matrix.single_conjTranspose (i : n) (j : m) (a : R) :
    (Matrix.single i j a)ᴴ = Matrix.single j i (star a) := by
  ext x y
  simp_rw [conjTranspose_apply, Matrix.single, ite_and]
  by_cases h : j = x ∧ i = y
  · simp_rw [h.1, h.2, of_apply, if_true]
  by_cases h' : a = 0
  · simp only [of_apply, h', star_zero, ite_self]
  · simp_rw [← ite_and, of_apply, @and_comm _ (j = x),
      (Ne.ite_eq_right_iff (star_ne_zero.mpr h')).mpr h, star_eq_iff_star_eq, star_zero]
    symm
    rw [ite_eq_right_iff]
    exact fun H => (h H).elim

theorem Matrix.single.star_apply (i k : n) (j l : m) (a : R) :
    star (Matrix.single i j a k l) = Matrix.single j i (star a) l k := by
  rw [← Matrix.single_conjTranspose, ← Matrix.conjTranspose_apply]

theorem Matrix.single.star_apply' (i : n) (j : m) (x : n × m) (a : R) :
    star (Matrix.single i j a x.fst x.snd) =
      Matrix.single j i (star a) x.snd x.fst := by
  rw [Matrix.single.star_apply]

/-- The conjugate transpose of a standard matrix unit. -/
theorem Matrix.single.star_one {R : Type _} [Semiring R] [StarRing R] (i : n) (j : m) :
    (Matrix.single i j (1 : R))ᴴ = Matrix.single j i (1 : R) := by
  nth_rw 2 [← _root_.star_one]
  exact Matrix.single_conjTranspose _ _ _

open scoped BigOperators

theorem Matrix.trace_iff {R n : Type _} [AddCommMonoid R] [Fintype n] (x : Matrix n n R) :
    x.trace = ∑ k : n, x k k :=
  rfl

theorem Matrix.single.hMul_apply_basis {R p q : Type _} [Semiring R] [DecidableEq p]
    [DecidableEq q] (i x : n) (j y : m) (k z : p) (l w : q) :
    Matrix.single k l (Matrix.single i j (1 : R) x y) z w =
      Matrix.single i j (1 : R) x y * Matrix.single k l (1 : R) z w := by
  simp_rw [Matrix.single, ite_and, of_apply, ite_mul, MulZeroClass.zero_mul, one_mul,
    ← ite_and, and_rotate, ← @and_assoc (k = z), @and_comm _ (i = x),
    ← and_assoc, @and_assoc _ (k = z), and_comm, and_assoc]

theorem Matrix.single.mul_apply_basis' {R p q : Type _} [Semiring R] [DecidableEq p]
    [DecidableEq q] (i x : n) (j y : m) (k z : p) (l w : q) :
    Matrix.single k l (Matrix.single i j (1 : R) x y) z w =
      ite (i = x ∧ j = y ∧ k = z ∧ l = w) 1 0 := by
  simp_rw [Matrix.single.hMul_apply_basis, Matrix.single, ite_and, of_apply, ite_mul,
    MulZeroClass.zero_mul, one_mul]

theorem Matrix.single.hMul_apply {R : Type _} [Fintype n] [Semiring R]
    (i j k l m p : n) :
    ∑ x : n × n, ∑ x_1 : n × n, ∑ x_2 : n, ∑ x_3 : n,
        Matrix.single l k (Matrix.single p m (1 : R) x_1.snd x_1.fst) x.snd x.fst *
          Matrix.single i x_2 (Matrix.single x_3 j (1 : R) x_1.fst x_1.snd) x.fst x.snd =
      ∑ x : n × n, ∑ x_1 : n × n, ∑ x_2 : n, ∑ x_3 : n,
        ite
          (p = x_1.snd ∧
            m = x_1.fst ∧
              l = x.snd ∧ k = x.fst ∧ x_3 = x_1.fst ∧ j = x_1.snd ∧ i = x.fst ∧
                x_2 = x.snd)
          1 0 := by
  simp_rw [Matrix.single.mul_apply_basis', ite_mul, one_mul, MulZeroClass.zero_mul, ← ite_and,
    and_assoc]

theorem Matrix.single.sum_star_hMul_self [Fintype n] (i j : n) (a b : R) :
    ∑ k : n, ∑ l : n, ∑ m : n, ∑ p : n,
        Matrix.single i j a k l * star (Matrix.single i j b) m p =
      a * star b := by
  simp_rw [Matrix.star_apply, Matrix.single.star_apply, Matrix.single, Matrix.of_apply, ite_mul,
    MulZeroClass.zero_mul, mul_ite, MulZeroClass.mul_zero, ite_and, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem Matrix.single.sum_star_hMul_self' {R : Type _} [Fintype n] [Semiring R] [StarRing R]
    (i j : n) :
    ∑ kl : n × n, ∑ mp : n × n,
        Matrix.single i j (1 : R) kl.1 kl.2 * star (Matrix.single i j (1 : R)) mp.1 mp.2 =
      1 := by
  classical
  rw [Finset.sum_eq_single (i, j)]
  · rw [Finset.sum_eq_single (j, i)]
    · simp [Matrix.star_apply, Matrix.single, Matrix.of_apply]
    · intro b _ hne
      have hcond : ¬(i = b.2 ∧ j = b.1) := by
        intro h
        apply hne
        ext <;> simp [h.1, h.2]
      simp [Matrix.star_apply, Matrix.single, Matrix.of_apply, hcond]
    · intro hnot
      simp at hnot
  · intro b _ hne
    have hcond : ¬(i = b.1 ∧ j = b.2) := by
      intro h
      apply hne
      ext <;> simp [h.1, h.2]
    simp [Matrix.single, Matrix.of_apply, hcond]
  · intro hnot
    simp at hnot

theorem Matrix.single.hMul_stdBasisMatrix {R p : Type _} [Semiring R] [DecidableEq p]
    [Fintype m] (i x : n) (j k : m) (l y : p) (a b : R) :
    (Matrix.single i j a * Matrix.single k l b) x y =
      ite (i = x ∧ j = k ∧ l = y) (a * b) 0 := by
  simp_rw [Matrix.mul_apply, Matrix.single, ite_and, of_apply, ite_mul,
    MulZeroClass.zero_mul, mul_ite, MulZeroClass.mul_zero, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero, eq_comm]

theorem Matrix.single.hMul_stdBasis_matrix' {R p : Type _} [Fintype n] [DecidableEq p]
    [Semiring R] (i : m) (j k : n) (l : p) :
    Matrix.single i j (1 : R) * Matrix.single k l (1 : R) =
      ite (j = k) (1 : R) 0 • Matrix.single i l (1 : R) := by
  ext x y
  simp_rw [Matrix.smul_apply, Matrix.mul_apply, Matrix.single, ite_and, of_apply, ite_mul,
    MulZeroClass.zero_mul, one_mul, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_const_zero, smul_ite, smul_zero, smul_eq_mul, mul_one, ← ite_and,
    eq_comm, and_comm]

theorem Matrix.transposeAlgEquiv_symm_op_apply {n R α : Type _} [CommSemiring R]
    [CommSemiring α] [Fintype n] [DecidableEq n] [Algebra R α] (x : Matrix n n α) :
    (Matrix.transposeAlgEquiv n R α).symm (MulOpposite.op x) = xᵀ := by
  rw [Matrix.transposeAlgEquiv_symm_apply]
  rfl

open Matrix

theorem Matrix.dotProduct_eq_trace {R n : Type _} [CommSemiring R] [StarRing R] [Fintype n]
    (x : n → R) (y : Matrix n n R) :
    star x ⬝ᵥ y.mulVec x =
      ((Matrix.replicateCol (Fin 1) x * Matrix.replicateRow (Fin 1) (star x))ᴴ * y).trace := by
  simp_rw [Matrix.trace_iff, dotProduct, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_replicateRow, Matrix.conjTranspose_replicateCol, star_star,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.replicateCol_apply,
    Matrix.replicateRow_apply, Pi.star_apply, Finset.sum_const]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.card_singleton, one_smul]
  simp_rw [Finset.mul_sum, mul_comm (x _), mul_comm _ (x _), ← mul_assoc, mul_comm]
  rw [Finset.sum_comm]

theorem forall_left_hMul {n R : Type _} [Fintype n] [Semiring R]
    (x y : Matrix n n R) : x = y ↔ ∀ a : Matrix n n R, a * x = a * y := by
  classical
  refine ⟨fun h a => by rw [h], fun h => ?_⟩
  simpa only [one_mul] using h 1

lemma _root_.Matrix.smul_one_eq_one_iff {𝕜 n : Type*} [DecidableEq n] [Field 𝕜] (c : 𝕜) :
    c • (1 : Matrix n n 𝕜) = (1 : Matrix n n 𝕜) ↔ c = 1 ∨ IsEmpty n := by
  simp_rw [← Matrix.ext_iff, Matrix.smul_apply, Matrix.one_apply, smul_ite, smul_zero,
    smul_eq_mul, mul_one]
  by_cases h : IsEmpty n
  · simp only [h, or_true, iff_true]
    intro i
    exact h.elim i
  · simp only [h, or_false]
    constructor
    · rintro h1
      rw [not_isEmpty_iff] at h
      let i : n := h.some
      specialize h1 i i
      simp only [↓reduceIte] at h1
      exact h1
    · rintro rfl i j
      rfl

/-- A linear equivalence of `R^n` gives an invertible matrix. -/
@[reducible]
def LinearEquiv.toInvertibleMatrix {n R : Type _} [CommSemiring R]
    [Fintype n] [DecidableEq n] (x : (n → R) ≃ₗ[R] n → R) :
    Invertible (LinearMap.toMatrix' (x : (n → R) →ₗ[R] n → R)) := by
  refine Invertible.mk
    (LinearMap.toMatrix' (x.symm : (n → R) →ₗ[R] n → R)) ?_ ?_
  · simp only [← LinearMap.toMatrix'_mul, Module.End.mul_eq_comp,
      LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  · simp only [← LinearMap.toMatrix'_mul, Module.End.mul_eq_comp,
      LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
