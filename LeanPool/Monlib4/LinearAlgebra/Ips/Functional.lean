/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.LinearAlgebra.Matrix.PosEqLinearMapIsPositive
import LeanPool.Monlib4.Preq.RCLikeLe
import LeanPool.Monlib4.LinearAlgebra.IsReal
import LeanPool.Monlib4.LinearAlgebra.Matrix.IncludeBlock
import LeanPool.Monlib4.LinearAlgebra.PosMapIsReal
import LeanPool.Monlib4.LinearAlgebra.Matrix.Cast

/-!

# Linear functionals

This file contains results for linear functionals on the set of $n \times n$ matrices $M_n$
  over $\mathbb{C}$.

## Main results
- `module.dual.apply`
- `module.dual.is_pos_map_iff`
- `module.dual.is_faithful_pos_map_iff`
- `module.dual.is_tracial_faithful_pos_map_iff`
- `module.dual.is_faithful_pos_map_iff_is_inner`

-/


open scoped Matrix BigOperators

section

variable {R k : Type _} {s : k → Type _}

open Matrix in
lemma includeBlock_apply_mul [CommSemiring R] [DecidableEq k] [Π i,
  Fintype (s i)] {i j : k} (x : Matrix (s i) (s i) R)
  (y : Matrix (s j) (s j) R) (p q : s j) :
  (includeBlock x j * y) p q
    = if i = j then (includeBlock x j * y) p q else 0 :=
by simp_rw [includeBlock_apply, dite_hMul, zero_mul]; aesop
open Matrix in
lemma includeBlock_mul_apply [CommSemiring R] [DecidableEq k]
  [Π i, Fintype (s i)] {i j : k} (x : Matrix (s j) (s j) R)
  (y : Matrix (s i) (s i) R) (p q : s j) :
  (x * includeBlock y j) p q
    = if i = j then (x * includeBlock y j) p q else 0 :=
by simp_rw [includeBlock_apply, hMul_dite, mul_zero]; aesop

end

section
variable {n : Type _} [Fintype n] [DecidableEq n]
variable {𝕜 R : Type _} [RCLike 𝕜] [CommSemiring R]

open Matrix

/-- the matrix of a linear map `φ : M_n →ₗ[R] R` is given by
  `∑ i j, single j i (φ (single i j 1))`. -/
def Module.Dual.matrix (φ : Module.Dual R (Matrix n n R)) :=
∑ i : n, ∑ j : n, Matrix.single j i (φ (Matrix.single i j 1))

/-- given any linear functional `φ : M_n →ₗ[R] R`, we get `φ a = (φ.matrix ⬝ a).trace`. -/
theorem Module.Dual.apply (φ : Module.Dual R (Matrix n n R)) (a : Matrix n n R) :
    φ a = (φ.matrix * a).trace := by
  simp_rw [Module.Dual.matrix, smul_single' _ _ (φ _)]
  simp_rw [Matrix.sum_mul, Matrix.smul_mul, trace_sum, trace_smul, Matrix.trace, Matrix.diag,
    mul_apply, single_eq, boole_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, ← ite_and, smul_eq_mul, mul_comm (φ _) _, ←
    smul_eq_mul, ← _root_.map_smul, ← map_sum]
  have :
    ∀ ⦃i : n⦄ ⦃j : n⦄ ⦃a : R⦄,
      single i j (a : R) = fun k l => ite (i = k ∧ j = l) (a : R) (0 : R) :=
    fun i j a => rfl
  simp_rw [← this, smul_single, smul_eq_mul, mul_one]
  rw [← matrix_eq_sum_single a]

/--
we linear maps `φ_i : M_[n_i] →ₗ[R] R`, we define its direct sum as the linear map `(Π i, M_[n_i])
  →ₗ[R] R`. -/
@[simps]
def Module.Dual.pi {k : Type _} [Fintype k] {s : k → Type _}
    (φ : ∀ i, Module.Dual R (Matrix (s i) (s i) R)) : Module.Dual R (PiMat R k s)
    where
  toFun a := ∑ i : k, φ i (a i)
  map_add' x y := by simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [_root_.map_smul, Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]

/-- Restrict a linear functional on a product of matrix algebras to each block. -/
@[simps!]
def Module.Dual.piOf {k : Type _} [DecidableEq k] {s : k → Type _}
    (φ : Module.Dual R (PiMat R k s)) :
    Π i, Module.Dual R (Matrix (s i) (s i) R) :=
fun _ => φ ∘ₗ includeBlock

/-- for direct sums, we get `φ x = ∑ i, ((φ i).matrix ⬝ x i).trace` -/
theorem Module.Dual.pi.apply {k : Type _} [Fintype k] {s : k → Type _} [∀ i, Fintype (s i)]
    [∀ i, DecidableEq (s i)] (φ : ∀ i, Module.Dual R (Matrix (s i) (s i) R))
    (x : PiMat R k s) : Module.Dual.pi φ x = ∑ i, ((φ i).matrix * x i).trace := by
  simp_rw [Module.Dual.pi_apply, Module.Dual.apply]

lemma Module.Dual.eq_piOf_pi {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Finite (s i)]
  (φ : Π i, Module.Dual R (Matrix (s i) (s i) R)) :
  φ = piOf (pi φ) := by
  classical
  letI : ∀ i, Fintype (s i) := fun i => Fintype.ofFinite (s i)
  ext i y
  simp_rw [Module.Dual.piOf_apply, pi_apply,
    Module.Dual.apply]
  symm
  calc ∑ j : k, trace (matrix (φ j) * includeBlock y j)
    = ∑ j : k, trace (if i = j then (matrix (φ j) * includeBlock y j) else 0) :=
      by congr; ext; congr; simp only [includeBlock_apply, hMul_dite, mul_zero]; aesop
    _ = ∑ j : k, if i = j then trace (matrix (φ j) * includeBlock y j) else 0 :=
      by congr; ext; aesop
    _ = trace (matrix (φ i) * includeBlock y i) :=
      by simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = trace (matrix (φ i) * y) := by simp only [includeBlock_apply_same]

lemma Module.Dual.eq_pi_piOf {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Finite (s i)]
  (φ : Module.Dual R (PiMat R k s)) :
  φ = pi (piOf φ) := by
  classical
  letI : ∀ i, Fintype (s i) := fun i => Fintype.ofFinite (s i)
  rw [LinearMap.ext_iff]
  intro x
  simp_rw [Module.Dual.pi_apply, Module.Dual.piOf_apply, ← map_sum,
    sum_includeBlock]

theorem Module.Dual.pi.apply' {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] (φ : ∀ i, Module.Dual R (Matrix (s i) (s i) R))
    (x : PiMat R k s) :
    Module.Dual.pi φ x
      = ∑ i, (blockDiagonal' (includeBlock (φ i).matrix) * blockDiagonal' x).trace := by
  symm
  simp_rw [← blockDiagonal'_mul]
  calc
    ∑ x_1 : k, (blockDiagonal' fun k_1 : k => includeBlock (φ x_1).matrix k_1 * x k_1).trace =
        ∑ x_1 : k, (blockDiagonal' fun k_1 => (includeBlock (φ x_1).matrix * x) k_1).trace :=
      rfl
    _ = ∑ x_1 : k, (blockDiagonal' fun k_1 =>
      ((includeBlock ((φ x_1).matrix * x x_1)) k_1)).trace := by
        congr
        ext
        congr
        ext
        simp only [includeBlock_hMul]
    _ = ∑ x_1 : k, (blockDiagonal' (includeBlock
      ((φ x_1).matrix * x x_1))).trace := rfl
    _ = ∑ x_1 : k, (blockDiagonal' (includeBlock
      ((fun i => (φ i).matrix * x i) x_1))).trace := rfl
    _ = ∑ x_1, ((φ x_1).matrix * x x_1).trace := by
      congr
      ext i
      rw [blockDiagonal'_includeBlock_trace (fun i => (φ i).matrix * x i) i]
    _ = pi φ x := (Module.Dual.pi.apply _ _).symm

theorem Module.Dual.pi_apply'' {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
    [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    (φ : Module.Dual R (PiMat R k s))
    (x : PiMat R k s) :
    φ x = ∑ i, ((piOf φ i).matrix * x i).trace :=
by simp_rw [← Module.Dual.apply, ← pi_apply, ← eq_pi_piOf]

theorem Module.Dual.apply_eq_of (φ : Module.Dual R (Matrix n n R)) (x : Matrix n n R)
    (h : ∀ a, φ a = (x * a).trace) : x = φ.matrix := by
  simp_rw [Module.Dual.apply, ← Matrix.ext_iff_trace] at h
  exact h.symm

omit [DecidableEq n] in
/--
Any linear functional $f$ on $M_n$ is given by a unique matrix $Q \in M_n$ such that
  $f(x)=\operatorname{Tr}(Qx)$ for any $x \in M_n$. -/
theorem Module.Dual.eq_trace_unique (φ : Module.Dual R (Matrix n n R)) :
    ∃! Q : Matrix n n R, ∀ a : Matrix n n R, φ a = (Q * a).trace := by
  classical
  use φ.matrix
  simp_rw [Module.Dual.apply, forall_true_iff, true_and, ←
    Matrix.ext_iff_trace, eq_comm, imp_self, forall_true_iff]

/-- Direct sum of matrix functionals as a functional on the block-diagonal subalgebra. -/
def Module.Dual.pi' {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
  (φ : ∀ i, Module.Dual R (Matrix (s i) (s i) R)) :
    Module.Dual R (BlockDiagonals R k s) :=
Module.Dual.pi φ ∘ₗ isBlockDiagonalPiAlgEquiv.toLinearMap

/-- `⨁_i φ_i ι_i (x_i) = φ_i (x_i)` -/
theorem Module.Dual.pi.apply_single_block {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Finite (s i)] (φ : Π i, Matrix (s i) (s i) R →ₗ[R] R)
  (x : Π i, Matrix (s i) (s i) R) (i : k) :
  (Module.Dual.pi φ) (includeBlock (x i)) = φ i (x i) := by
  classical
  letI : ∀ i, Fintype (s i) := fun i => Fintype.ofFinite (s i)
  simp_rw [Module.Dual.pi_apply, Module.Dual.apply]
  calc ∑ x_1 : k, trace (matrix (φ x_1) * includeBlock (x i) x_1)
      = ∑ x_1 : k, trace (if i = x_1 then matrix (φ x_1) * x x_1 else 0) := by
        congr; ext; congr
        simp_rw [includeBlock_apply, hMul_dite, mul_zero]
        aesop
    _ = ∑ x_1 : k, ∑ x_2 : s x_1, (if i = x_1 then matrix (φ x_1) * x x_1 else 0) x_2 x_2 := rfl
    _ = ∑ x_1 : k, ∑ x_2 : s x_1, (if i = x_1 then (matrix (φ x_1) * x x_1) x_2 x_2 else 0) := by
      congr 1 with x_1
      congr 1 with x_2
      split_ifs <;> rfl
    _ = trace (matrix (φ i) * x i) := ?_
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rfl

theorem Module.Dual.pi.apply_single_block' {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Finite (s i)] (φ : Π i, Matrix (s i) (s i) R →ₗ[R] R)
  {i : k} (x : Matrix (s i) (s i) R) :
  (Module.Dual.pi φ) (includeBlock x) = φ i x := by
  classical
  letI : ∀ i, Fintype (s i) := fun i => Fintype.ofFinite (s i)
  let x' := includeBlock x
  have hx : includeBlock x = includeBlock (x' i) := by simp_rw [x', includeBlock_apply_same]
  rw [hx, apply_single_block]
  simp_rw [x', includeBlock_apply_same]

open scoped ComplexOrder

open scoped DirectSum

/-- A linear functional $φ$ on $M_n$ is positive if $0 ≤ φ (x^*x)$ for all $x \in M_n$. -/
def Module.Dual.IsPosMap {A : Type _} [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
    (φ : Module.Dual 𝕜 A) : Prop :=
  ∀ a : A, 0 ≤ φ (star a * a)

open scoped MatrixOrder
lemma Matrix.nonneg_iff {k : Type*} [Fintype k] {x : Matrix k k ℂ} :
  0 ≤ x ↔ ∃ y : Matrix k k ℂ, x = star y * y := by
  classical
  rw [Matrix.nonneg_def]
  simpa [Matrix.star_eq_conjTranspose] using (Matrix.posSemidef_iff x)
lemma PiMat.nonneg_iff {k : Type _} [Finite k]
  {s : k → Type _} [Π i, Fintype (s i)]
  {x : PiMat ℂ k s} :
  0 ≤ x ↔ ∃ y : PiMat ℂ k s, x = star y * y := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  simp_rw [Pi.le_def, Pi.zero_apply, Pi.mul_def, Pi.star_apply, Matrix.nonneg_iff,
    funext_iff]
  exact ⟨fun h => ⟨(fun i => (h i).choose), fun _ => (h _).choose_spec⟩,
    fun h a => ⟨h.choose a, h.choose_spec _⟩⟩

lemma dual_isPosMap_of_linearMap_isPosMap {A :
    Type _} [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
  [PartialOrder A] [StarOrderedRing A] {φ : Module.Dual 𝕜 A} (h : LinearMap.IsPosMap φ) :
  φ.IsPosMap :=
fun _ => h (star_mul_self_nonneg _)

lemma Module.Dual.piIsPosMap_iff {k : Type _} [Finite k]
  [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)]
  (φ : Module.Dual 𝕜 (PiMat 𝕜 k s)) :
  φ.IsPosMap ↔ ∀ i, (piOf φ i).IsPosMap := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  constructor
  · intro h i x
    specialize h (includeBlock x)
    simp_rw [includeBlock_conjTranspose, includeBlock_hMul_same] at h
    exact h
  · intro h x
    simp_rw [IsPosMap, piOf_apply] at h
    nth_rw 1 [← sum_includeBlock x]
    simp_rw [star_sum, Finset.sum_mul, includeBlock_conjTranspose,
      includeBlock_hMul, map_sum]
    exact Finset.sum_nonneg (fun _ _ => h _ _)

lemma Module.Dual.pi_isPosMap_iff {k : Type _} [Fintype k]
  {s : k → Type _} [∀ i, Fintype (s i)]
  (φ : Π i, Module.Dual 𝕜 (Matrix (s i) (s i) 𝕜)) :
  (pi φ).IsPosMap ↔ ∀ i, (φ i).IsPosMap := by
  classical
  rw [Module.Dual.piIsPosMap_iff]
  simp_rw [← eq_piOf_pi]

/-- A linear functional $φ$ on $M_n$ is unital if $φ(1) = 1$. -/
def Module.Dual.IsUnital {A : Type _} [AddCommMonoid A] [Module R A] [One A] (φ : Module.Dual R A) :
    Prop :=
  φ (1 : A) = 1

/-- A linear functional is called a state if it is positive and unital -/
class Module.Dual.IsState {A : Type _} [Semiring A] [StarRing A] [Module 𝕜 A] (φ :
    Module.Dual 𝕜 A) :
    Prop where
toIsPosMap : φ.IsPosMap
toIsUnital : φ.IsUnital

lemma Module.Dual.IsState_iff {A : Type _} [Semiring A] [StarRing A] [Module 𝕜 A]
  (φ : Module.Dual 𝕜 A) : φ.IsState ↔ φ.IsPosMap ∧ φ.IsUnital :=
⟨fun h => ⟨h.toIsPosMap, h.toIsUnital⟩, fun h => ⟨h.1, h.2⟩⟩

omit [DecidableEq n] in
theorem Module.Dual.isPosMap_of_matrix (φ : Module.Dual 𝕜 (Matrix n n 𝕜)) :
    φ.IsPosMap ↔ ∀ a : Matrix n n 𝕜, a.PosSemidef → 0 ≤ φ a := by
  simp_rw [posSemidef_iff, exists_imp, Module.Dual.IsPosMap, forall_eq_apply_imp_iff,
    star_eq_conjTranspose]

/--
A linear functional $f$ on $M_n$ is said to be faithful if $f(x^*x)=0$ if and only if $x=0$ for any
  $x \in M_n$. -/
def Module.Dual.IsFaithful {A : Type _} [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
    (φ : Module.Dual 𝕜 A) : Prop :=
  ∀ a : A, φ (star a * a) = 0 ↔ a = 0

lemma Matrix.includeBlock_eq_zero {k : Type _} [Finite k] [DecidableEq k] {s : k → Type _}
  [∀ i, Finite (s i)] {i : k}
  {x : Matrix (s i) (s i) R} :
  includeBlock x = 0 ↔ x = 0 := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  letI : ∀ i, Fintype (s i) := fun i => Fintype.ofFinite (s i)
  simp_rw [funext_iff, Pi.zero_apply, includeBlock_apply,
    dite_eq_right_iff, eq_mp_eq_cast]
  exact ⟨fun h => (h i rfl), by rintro rfl a rfl; rfl⟩

lemma Module.Dual.piIsFaithful_iff {k : Type _} [Finite k]
  [DecidableEq k] {s : k → Type _} [∀ i, Fintype (s i)]
  {φ : Module.Dual 𝕜 (PiMat 𝕜 k s)} (hφ : φ.IsPosMap) :
  φ.IsFaithful ↔ ∀ i, (piOf φ i).IsFaithful := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  constructor
  · intro h i x
    specialize h (includeBlock x)
    simp_rw [includeBlock_conjTranspose, includeBlock_hMul_same,
      includeBlock_eq_zero] at h
    exact h
  · intro h x
    simp_rw [IsFaithful, piOf_apply] at h
    nth_rw 1 [← sum_includeBlock x]
    simp_rw [star_sum, Finset.sum_mul, includeBlock_conjTranspose,
      includeBlock_hMul, map_sum]
    refine ⟨fun h1 => ?_, fun h => by simp_rw [h, Pi.zero_apply, mul_zero, map_zero,
      Finset.sum_const_zero]⟩
    ext1 i
    rw [Pi.zero_apply]
    rw [Finset.sum_eq_zero_iff_of_nonneg] at h1
    · simp only [Finset.mem_univ, forall_true_left, ← star_eq_conjTranspose, h] at h1
      exact h1 i
    · intro i hi
      rw [piIsPosMap_iff] at hφ
      exact hφ _ _

omit [DecidableEq n] in
theorem Module.Dual.isFaithful_of_matrix (φ : Module.Dual 𝕜 (Matrix n n 𝕜)) :
    φ.IsFaithful ↔ ∀ a : Matrix n n 𝕜, a.PosSemidef → (φ a = 0 ↔ a = 0) := by
  simp_rw [posSemidef_iff, exists_imp, Module.Dual.IsFaithful, forall_eq_apply_imp_iff,
    conjTranspose_mul_self_eq_zero, star_eq_conjTranspose]

omit [DecidableEq n] in
/-- The quadratic form `star y ⬝ᵥ Q *ᵥ y` equals `(Q * vecMulVec y (star y)).trace`. -/
private lemma Matrix.dotProduct_mulVec_eq_trace_vecMulVec (Q : Matrix n n ℂ) (y : n → ℂ) :
    star y ⬝ᵥ Q *ᵥ y = (Q * vecMulVec y (star y)).trace := by
  rw [vecMulVec_eq Unit, trace_mul_cycle', ← replicateCol_mulVec]
  simp_rw [Matrix.trace_iff', replicateRow_mul_replicateCol_apply, Fintype.univ_punit,
    Finset.sum_const, Finset.card_singleton, nsmul_eq_mul, Nat.cast_one, one_mul]

/--
A linear functional $f$ is positive if and only if there exists a unique positive semi-definite
matrix $Q\in M_n$ such that $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$.
-/
theorem Module.Dual.isPosMap_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsPosMap ↔ φ.matrix.PosSemidef := by
  constructor
  · intro hs
    rw [Module.Dual.isPosMap_of_matrix] at hs
    simp only [Module.Dual.apply] at hs
    simp_rw [PosSemidef.complex, Matrix.dotProduct_mulVec_eq_trace_vecMulVec]
    intro y
    exact hs (vecMulVec y (star y)) (vecMulVec_posSemidef _)
  · intro hy y
    rw [φ.apply, ← Matrix.mul_assoc]
    exact hy.trace_conjTranspose_hMul_self_nonneg _

/--
A linear functional $f$ is a state if and only if there exists a unique positive semi-definite
  matrix $Q\in M_n$ such that its trace equals $1$ and $f(x)=\operatorname{Tr}(Qx)$ for all $x\in
  M_n$. -/
theorem Module.Dual.isState_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsState ↔ φ.matrix.PosSemidef ∧ φ.matrix.trace = 1 := by
  simp_rw [Module.Dual.IsState_iff, Module.Dual.isPosMap_iff_of_matrix, Module.Dual.IsUnital,
    Module.Dual.apply, Matrix.mul_one]

/--
A positive linear functional $f$ is faithful if and only if there exists a positive definite matrix
  such that $f(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
theorem Module.Dual.IsPosMap.isFaithful_iff_of_matrix {φ : Module.Dual ℂ (Matrix n n ℂ)}
    (hs : φ.IsPosMap) : φ.IsFaithful ↔ φ.matrix.PosDef := by
  have hs' := hs
  rw [Module.Dual.isPosMap_of_matrix] at hs'
  rw [Module.Dual.isFaithful_of_matrix]
  constructor
  · rw [Module.Dual.isPosMap_iff_of_matrix] at hs
    intro HHH
    · refine Matrix.PosDef.of_dotProduct_mulVec_pos hs.1 ?_
      intro x hx
      rw [Matrix.dotProduct_mulVec_eq_trace_vecMulVec]
      have this2 := HHH (vecMulVec x (star x)) (vecMulVec_posSemidef _)
      have this3 := hs' (vecMulVec x (star x)) (vecMulVec_posSemidef _)
      rw [le_iff_eq_or_lt] at this3
      rcases this3 with (this3 | this32)
      · rw [eq_comm, this2, vecMulVec_eq_zero_iff] at this3
        contradiction
      · rw [← Module.Dual.apply]
        exact this32
  · intro hQ a ha
    exact ⟨fun h => by
      obtain ⟨b, rfl⟩ := (posSemidef_iff _).mp ha
      rw [Module.Dual.apply, ← Matrix.mul_assoc,
        Nontracial.trace_conjTranspose_hMul_self_eq_zero hQ] at h
      rw [h, Matrix.mul_zero], fun h => by rw [h, map_zero]⟩

/-- A linear functional that is both positive and faithful on positive elements. -/
@[class]
structure Module.Dual.IsFaithfulPosMap {A : Type _} [NonUnitalSemiring A] [StarRing A]
    [Module 𝕜 A] (φ : Module.Dual 𝕜 A) : Prop where
  /-- The functional is positive on all `star a * a`. -/
  toIsPosMap : φ.IsPosMap
  /-- The functional detects zero positive elements. -/
  toIsFaithful : φ.IsFaithful

lemma Module.Dual.IsFaithfulPosMap_iff {A : Type _} [NonUnitalSemiring A] [StarRing A] [Module 𝕜 A]
  (φ : Module.Dual 𝕜 A) : φ.IsFaithfulPosMap ↔ φ.IsPosMap ∧ φ.IsFaithful :=
⟨fun h => ⟨h.toIsPosMap, h.toIsFaithful⟩, fun h => ⟨h.1, h.2⟩⟩

/--
A linear functional $φ$ is a faithful and positive if and only if there exists a unique positive
  definite matrix $Q$ such that $φ(x)=\operatorname{Tr}(Qx)$ for all $x\in M_n$. -/
theorem Module.Dual.isFaithfulPosMap_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsFaithfulPosMap ↔ φ.matrix.PosDef := by
  constructor
  · intro h
    exact h.1.isFaithful_iff_of_matrix.mp h.2
  intro hQ
  simp_rw [Module.Dual.IsFaithfulPosMap_iff, Module.Dual.IsFaithful,
    Module.Dual.isPosMap_iff_of_matrix,
    hQ.posSemidef, true_and, Module.Dual.apply, star_eq_conjTranspose,
    ← Matrix.mul_assoc, Nontracial.trace_conjTranspose_hMul_self_eq_zero hQ,
    forall_const]

/--
A state is faithful $f$ if and only if there exists a unique positive definite matrix $Q\in M_n$
  with trace equal to $1$ and $f(x)=\operatorname{Tr}(Qx)$ for all $x \in M_n$. -/
theorem Module.Dual.IsState.isFaithful_iff_of_matrix {φ : Module.Dual ℂ (Matrix n n ℂ)}
    (hs : φ.IsState) : φ.IsFaithful ↔ φ.matrix.PosDef ∧ φ.matrix.trace = 1 := by
  rw [hs.1.isFaithful_iff_of_matrix]
  constructor
  · intro hQ
    constructor
    · exact hQ
    rw [Module.Dual.isState_iff_of_matrix] at hs
    exact hs.2
  · intro hQ
    exact hQ.1

theorem Module.Dual.isFaithful_state_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsState ∧ φ.IsFaithful ↔ φ.matrix.PosDef ∧ φ.matrix.trace = 1 := by
  constructor
  · intro h
    exact h.1.isFaithful_iff_of_matrix.mp h.2
  intro hQ
  simp_rw [Module.Dual.IsFaithful, Module.Dual.isState_iff_of_matrix, hQ.2, hQ.1.posSemidef,
    true_and]
  rw [← Module.Dual.isFaithfulPosMap_iff_of_matrix] at hQ
  exact hQ.1.2

/-- A linear functional $f$ is tracial if and only if $f(xy)=f(yx)$ for all $x,y$. -/
def Module.Dual.IsTracial {A : Type _} [NonUnitalSemiring A] [Module 𝕜 A] (φ : Module.Dual 𝕜 A) :
    Prop :=
  ∀ x y : A, φ (x * y) = φ (y * x)

/-- Shared core of the tracial-positivity characterisations: a positive semidefinite tracial
matrix is the scalar `RCLike.re (φ.matrix i i)` times the identity, and that scalar is
nonnegative. -/
private lemma Module.Dual.tracial_posSemidef_matrix_eq_re_smul_one
    {φ : Module.Dual ℂ (Matrix n n ℂ)} (hQ : φ.matrix.PosSemidef) (h2 : φ.IsTracial) (i : n) :
    0 ≤ RCLike.re (φ.matrix i i) ∧
      φ.matrix = ((RCLike.re (φ.matrix i i) : ℝ) : ℂ) • 1 := by
  simp_rw [Module.Dual.IsTracial, Module.Dual.apply, Matrix.trace, Matrix.diag,
    mul_apply] at h2
  set Q := φ.matrix with hQdef
  have hdiag : ∀ p q r : n, Q p q = ite (p = q) (Q r r) 0 := fun p q r =>
    calc
      Q p q = ∑ i, ∑ j, Q i j * ∑ k, (single q r 1) j k * (single r p 1) k i := by
        simp only [single, of_apply, ite_and, Finset.sum_ite_irrel,
          Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
          mul_ite, MulZeroClass.mul_zero, mul_one]
      _ = ∑ i, ∑ j, Q i j * ∑ k, (single r p 1) j k * (single q r 1) k i := by rw [h2]
      _ = ite (p = q) (Q r r) 0 := by
        simp only [single, of_apply, ite_and, Finset.sum_ite_irrel,
          Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite,
          MulZeroClass.mul_zero, mul_one]
  have HH : Q = diagonal fun _ : n => Q i i := by ext; exact hdiag _ _ i
  have hre : ∀ p, Q p p = RCLike.re (Q p p) := fun p => by
    rw [eq_comm]
    simp_rw [RCLike.re_eq_complex_re, ← Complex.conj_eq_iff_re, ← RCLike.star_def,
      ← Matrix.star_apply, star_eq_conjTranspose]
    rw [hQ.1.eq]
  have hnn : 0 ≤ Q i i := by
    rw [PosSemidef.complex] at hQ
    specialize hQ fun j => ite (i = j) 1 0
    simpa only [dotProduct, mulVec, dotProduct, Pi.star_apply, star_ite, star_zero, star_one,
      boole_mul, mul_boole, Finset.sum_ite_eq, Finset.mem_univ, if_true] using hQ
  refine ⟨(RCLike.nonneg_def'.mp hnn).2, ?_⟩
  simp only [smul_eq_diagonal_mul, Matrix.mul_one]
  rwa [← hre]

/--
A linear functional is tracial and positive if and only if there exists a non-negative real $α$
  such that $f\colon x \mapsto \alpha \operatorname{Tr}(x)$. -/
theorem Module.Dual.isTracial_pos_map_iff_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsPosMap ∧ φ.IsTracial ↔ ∃ α : NNReal, φ.matrix = ((α : ℝ) : ℂ) • 1 := by
  constructor
  · simp_rw [Module.Dual.isPosMap_iff_of_matrix]
    rintro ⟨hQ, h2⟩
    by_cases h : IsEmpty n
    · refine ⟨1, ?_⟩
      haveI := h
      simp only [eq_iff_true_of_subsingleton]
    rw [not_isEmpty_iff] at h
    obtain ⟨hnn, heq⟩ := φ.tracial_posSemidef_matrix_eq_re_smul_one hQ h2 h.some
    exact ⟨⟨_, hnn⟩, heq⟩
  · rintro ⟨α, hα1⟩
    simp_rw [Module.Dual.IsPosMap, Module.Dual.IsTracial, Module.Dual.apply, hα1,
      smul_mul, one_mul, trace_smul, smul_eq_mul, star_eq_conjTranspose]
    exact ⟨fun _ => mul_nonneg (RCLike.zero_le_real.mpr (NNReal.coe_nonneg α))
        (Matrix.trace_conjTranspose_hMul_self_nonneg _),
      fun _ _ => by rw [trace_mul_comm]⟩

/--
A linear functional is tracial and positive if and only if there exists a unique non-negative real
  $α$ such that $f\colon x \mapsto \alpha \operatorname{Tr}(x)$. -/
theorem Module.Dual.isTracial_pos_map_iff'_of_matrix [Nonempty n]
    (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsPosMap ∧ φ.IsTracial ↔ ∃! α : NNReal, φ.matrix = ((α : ℝ) : ℂ) • 1 := by
  constructor
  · simp_rw [Module.Dual.isPosMap_iff_of_matrix]
    rintro ⟨hQ, h2⟩
    obtain ⟨hnn, heq⟩ :=
      φ.tracial_posSemidef_matrix_eq_re_smul_one hQ h2 (Nonempty.some ‹_›)
    refine ⟨⟨_, hnn⟩, heq, fun y hy => ?_⟩
    have hsmul : ((_ : ℝ) : ℂ) • (1 : Matrix n n ℂ) = ((y : ℝ) : ℂ) • 1 := heq ▸ hy
    rw [smul_left_injective ℂ one_ne_zero |>.eq_iff] at hsmul
    exact (Subtype.coe_inj.mp (by exact_mod_cast hsmul)).symm
  · rintro ⟨α, ⟨hα1, _⟩⟩
    simp_rw [Module.Dual.IsPosMap, Module.Dual.IsTracial, Module.Dual.apply, hα1,
      smul_mul, one_mul, trace_smul]
    exact ⟨fun _ =>  mul_nonneg (RCLike.zero_le_real.mpr (NNReal.coe_nonneg α))
        (Matrix.trace_conjTranspose_hMul_self_nonneg _),
      fun _ _ => by rw [trace_mul_comm]⟩

/--
A linear functional $f$ is tracial positive and faithful if and only if there exists a positive
  real number $\alpha$ such that $f\colon x\mapsto \alpha \operatorname{Tr}(x)$. -/
theorem Module.Dual.isTracial_faithful_pos_map_iff_of_matrix [Nonempty n]
    (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsFaithfulPosMap ∧ φ.IsTracial ↔
      ∃! α : { x : NNReal // 0 < x }, φ.matrix = (((α : NNReal) : ℝ) : ℂ) • 1 := by
  rw [Module.Dual.IsFaithfulPosMap_iff, @and_comm φ.IsPosMap, and_assoc,
    Module.Dual.isTracial_pos_map_iff'_of_matrix]
  constructor
  · rintro ⟨h1, ⟨α, hα, h⟩⟩
    have : 0 < (α : ℝ) := by
      rw [NNReal.coe_pos, pos_iff_ne_zero]
      intro HH
      rw [Module.Dual.IsFaithful] at h1
      specialize h1 ((1 : Matrix n n ℂ)ᴴ * (1 : Matrix n n ℂ))
      simp only [Matrix.conjTranspose_one, Matrix.mul_one, Module.Dual.apply,
        star_eq_conjTranspose] at h1
      simp_rw [HH, NNReal.coe_zero, Complex.ofReal_zero, zero_smul] at hα
      rw [hα, trace_zero, eq_self_iff_true, true_iff] at h1
      simp only [one_ne_zero'] at h1
    let α' : { x : NNReal // 0 < x } := ⟨α, this⟩
    have : α = α' := rfl
    use α'
    constructor
    · exact hα
    · intro y hy
      simp_rw [← Subtype.coe_inj] at hy ⊢
      exact h _ hy
  · rintro ⟨α, ⟨h1, _⟩⟩
    have : 0 < (α : NNReal) := Subtype.mem α
    constructor
    · simp_rw [Module.Dual.IsFaithful, Module.Dual.apply, h1, Matrix.smul_mul, Matrix.one_mul,
        trace_smul, smul_eq_zero, Complex.ofReal_eq_zero, NNReal.coe_eq_zero, ne_zero_of_lt this,
        false_or, star_eq_conjTranspose,
        trace_conjTranspose_hMul_self_eq_zero, forall_true_iff]
    · use α
      constructor
      · exact h1
      · intro y hy
        rw [h1, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at hy
        simp only [one_ne_zero', or_false, NNReal.coe_inj,
          Complex.ofReal_inj, NNReal.coe_inj] at hy
        exact hy.symm

theorem Matrix.ext_iff_trace' {R m n : Type _} [Semiring R] [StarRing R] [Fintype n] [Fintype m]
    (A B : Matrix m n R) :
    (∀ x, (xᴴ * A).trace = (xᴴ * B).trace) ↔ A = B := by
  classical
  constructor
  · intro h
    ext i j
    specialize h (single i j (1 : R))
    simp_rw [single_conjTranspose, star_one, Matrix.single_hMul_trace] at h
    exact h
  · intro h x
    rw [h]

theorem Module.Dual.isReal_iff {φ : Module.Dual ℂ (Matrix n n ℂ)} :
    LinearMap.IsReal φ ↔ φ.matrix.IsHermitian := by
  simp_rw [LinearMap.IsReal, Module.Dual.apply, trace_star, conjTranspose_mul,
    star_eq_conjTranspose, trace_mul_comm φ.matrix, Matrix.ext_iff_trace', IsHermitian, eq_comm]

omit [DecidableEq n] in
theorem Module.Dual.IsPosMap.isReal {φ : Module.Dual ℂ (Matrix n n ℂ)} (hφ : φ.IsPosMap) :
    LinearMap.IsReal φ := by
  classical
  rw [Module.Dual.isPosMap_iff_of_matrix] at hφ
  rw [Module.Dual.isReal_iff]
  exact hφ.1

theorem Module.Dual.pi.IsPosMap.isReal {k : Type _} [Fintype k] {s : k → Type _}
    [∀ i, Fintype (s i)] {ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
    (hψ : ∀ i, (ψ i).IsPosMap) : LinearMap.IsReal (Module.Dual.pi ψ) := by
  classical
  simp_rw [LinearMap.IsReal, Module.Dual.pi_apply, star_sum, Pi.star_apply, (hψ _).isReal _,
    forall_true_iff]

/-- A function $H \times H \to 𝕜$ defines an inner product if it satisfies the following. -/
def IsInner {H : Type _} [AddCommMonoid H] [Module 𝕜 H] (φ : H × H → 𝕜) : Prop :=
  (∀ x y : H, φ (x, y) = star (φ (y, x))) ∧
    (∀ x : H, 0 ≤ RCLike.re (φ (x, x))) ∧
      (∀ x : H, φ (x, x) = 0 ↔ x = 0) ∧
        (∀ x y z : H, φ (x + y, z) = φ (x, z) + φ (y, z)) ∧
          ∀ (x y : H) (α : 𝕜), φ (α • x, y) = starRingEnd 𝕜 α * φ (x, y)

omit [DecidableEq n] in
/--
A linear functional $f$ on $M_n$ is positive and faithful if and only if $(x,y)\mapsto f(x^*y)$
  defines an inner product on $M_n$. -/
theorem Module.Dual.isFaithfulPosMap_iff_isInner_of_matrix (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    φ.IsFaithfulPosMap ↔ IsInner fun xy : Matrix n n ℂ × Matrix n n ℂ => φ (xy.1ᴴ * xy.2) := by
  classical
  let ip := fun xy : Matrix n n ℂ × Matrix n n ℂ => φ (xy.1ᴴ * xy.2)
  have hip : ∀ x y, ip (x, y) = φ (xᴴ * y) := fun x y => rfl
  have Hip :
    (∀ x y z, ip (x + y, z) = ip (x, z) + ip (y, z)) ∧
      ∀ (x y) (α : ℂ), ip (α • x, y) = starRingEnd ℂ α * ip (x, y) := by
    simp only [ip]
    simp_rw [conjTranspose_add, Matrix.add_mul, map_add, conjTranspose_smul, Matrix.smul_mul,
      _root_.map_smul, Complex.star_def, smul_eq_mul, forall₃_true_iff,
      true_and]
  simp_rw [IsInner, ← hip, Hip, forall₃_true_iff, true_and, and_true]
  constructor
  · intro h
    simp_rw [hip, ← h.1.isReal _, star_eq_conjTranspose, conjTranspose_mul,
      conjTranspose_conjTranspose]
    have := fun x => h.1 x
    simp only [@RCLike.nonneg_def' ℂ] at this
    exact ⟨fun _ _ => trivial, ⟨fun x => (this x).2, h.2⟩⟩
  · intro h
    constructor
    · simp_rw [Module.Dual.IsPosMap, star_eq_conjTranspose, ← hip, @RCLike.nonneg_def' ℂ,
        ← @RCLike.conj_eq_iff_re ℂ _ (ip (_,_)),
        starRingEnd_apply, ← h.1, true_and]
      exact h.2.1
    · exact h.2.2

theorem Module.Dual.isFaithfulPosMap_of_matrix_tfae (φ : Module.Dual ℂ (Matrix n n ℂ)) :
    List.TFAE
      [φ.IsFaithfulPosMap, φ.matrix.PosDef,
        IsInner fun xy : Matrix n n ℂ × Matrix n n ℂ => φ (xy.1ᴴ * xy.2)] := by
  tfae_have 1 ↔ 2 := φ.isFaithfulPosMap_iff_of_matrix
  tfae_have 1 ↔ 3 := φ.isFaithfulPosMap_iff_isInner_of_matrix
  tfae_finish

end
section

variable {n : Type _} [Fintype n] [DecidableEq n] (φ : Module.Dual ℂ (Matrix n n ℂ))

/-- The normed additive group structure induced by a faithful positive functional on matrices. -/
@[reducible]
noncomputable def Module.Dual.NormedAddCommGroup [hφ : φ.IsFaithfulPosMap] :
  _root_.NormedAddCommGroup (Matrix n n ℂ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (Matrix n n ℂ) _ _ _
    { inner := fun x y => φ (xᴴ * y)
      conj_inner_symm := fun _ _ => ((φ.isFaithfulPosMap_iff_isInner_of_matrix.mp hφ).1 _ _).symm
      re_inner_nonneg := fun _ => (φ.isFaithfulPosMap_iff_isInner_of_matrix.mp hφ).2.1 _
      definite := fun _ hx => ((φ.isFaithfulPosMap_iff_isInner_of_matrix.mp hφ).2.2.1 _).mp hx
      add_left := fun _ _ _ => (φ.isFaithfulPosMap_iff_isInner_of_matrix.mp hφ).2.2.2.1 _ _ _
      smul_left := fun _ _ _ => (φ.isFaithfulPosMap_iff_isInner_of_matrix.mp hφ).2.2.2.2 _ _ _ }



variable [hφ : φ.IsFaithfulPosMap]


/-- The inner product space structure induced by a faithful positive functional on matrices. -/
@[reducible]
noncomputable def Module.Dual.InnerProductSpace :
  @_root_.InnerProductSpace ℂ (Matrix n n ℂ) _
    ((Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup) := by
  letI : _root_.NormedAddCommGroup (Matrix n n ℂ) :=
    Module.Dual.NormedAddCommGroup φ
  exact InnerProductSpace.ofCore _

scoped[Functional] attribute [instance] Module.Dual.InnerProductSpace

end

open scoped Functional

variable {k : Type _} [Fintype k] {s : k → Type _}
    [Π i, Fintype (s i)] [Π i, DecidableEq (s i)]

/-- The finite product inner-product core induced by faithful positive matrix functionals. -/
@[reducible]
noncomputable def Module.Dual.PiInnerProductCore
  {φ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [hφ : Π i, (φ i).IsFaithfulPosMap] :
  InnerProductSpace.Core ℂ (PiMat ℂ k s) := by
  letI : Π i, _root_.NormedAddCommGroup (Matrix (s i) (s i) ℂ) :=
    fun i => Module.Dual.NormedAddCommGroup (φ i)
  letI : Π i, _root_.InnerProductSpace ℂ (Matrix (s i) (s i) ℂ) :=
    fun i => Module.Dual.InnerProductSpace (φ i)
  exact
    { inner := fun x y => ∑ i, @inner ℂ (Matrix (s i) (s i) ℂ) _ (x i) (y i)
      conj_inner_symm := fun x y => by
        simp_rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact inner_conj_symm _ _
      re_inner_nonneg := fun x => by
        simp_rw [map_sum]
        exact Finset.sum_nonneg fun i _ => inner_self_nonneg
      definite := fun x hx => by
        apply PiMat.ext
        intro i
        have hsum :
            ∑ j, RCLike.re (@inner ℂ (Matrix (s j) (s j) ℂ) _ (x j) (x j)) = 0 := by
          have hcongr := congrArg RCLike.re hx
          simpa [map_sum] using hcongr
        have hnonneg :
            ∀ j ∈ Finset.univ,
              0 ≤ RCLike.re (@inner ℂ (Matrix (s j) (s j) ℂ) _ (x j) (x j)) :=
          fun j _ => inner_self_nonneg
        have hi : RCLike.re (@inner ℂ (Matrix (s i) (s i) ℂ) _ (x i) (x i)) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i (Finset.mem_univ i)
        have hnorm : ‖x i‖ ^ 2 = 0 := by
          exact
            (inner_self_eq_norm_sq (𝕜 := ℂ) (E := Matrix (s i) (s i) ℂ)
              (x := x i)).symm.trans hi
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
      add_left := fun x y z => by
        simp_rw [Pi.add_apply, inner_add_left, Finset.sum_add_distrib]
      smul_left := fun x y r => by
        simp_rw [Pi.smul_apply, inner_smul_left, Finset.mul_sum] }

/--
The normed additive group on a finite product induced by faithful positive matrix functionals.
-/
@[reducible]
noncomputable def Module.Dual.PiNormedAddCommGroup
  {φ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [_hφ : Π i, (φ i).IsFaithfulPosMap] :
  _root_.NormedAddCommGroup (PiMat ℂ k s) :=
(Module.Dual.PiInnerProductCore (φ := φ)).toNormedAddCommGroup

/-- The inner product space on a finite product induced by faithful positive matrix functionals. -/
@[reducible]
noncomputable def Module.Dual.pi.InnerProductSpace
  {φ : Π i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [hφ : Π i, (φ i).IsFaithfulPosMap] :
  @_root_.InnerProductSpace ℂ (PiMat ℂ k s) _
  ((Module.Dual.PiNormedAddCommGroup (_hφ := hφ)).toSeminormedAddCommGroup)
   := by
  letI : _root_.NormedAddCommGroup (PiMat ℂ k s) :=
    Module.Dual.PiNormedAddCommGroup (_hφ := hφ)
  letI : InnerProductSpace.Core ℂ (PiMat ℂ k s) :=
    Module.Dual.PiInnerProductCore (φ := φ)
  exact InnerProductSpace.ofCore _

scoped[Functional] attribute [instance high] Module.Dual.pi.InnerProductSpace
