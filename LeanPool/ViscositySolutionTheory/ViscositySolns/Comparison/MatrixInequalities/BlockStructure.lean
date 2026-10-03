/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.DoublingVariables

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Matrix inequalities for comparison (BlockStructure)

Part of the block-matrix development used in the doubling-of-variables
proof of comparison. Split from `MatrixInequalities.lean`; see the umbrella
module docstring.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/-- Hessian matrices on the product coordinate space `R^n × R^n`. -/
abbrev BlockHessian (n : Nat) : Type :=
  Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Real

/-- Coordinate vectors on the product space `R^n × R^n`. -/
abbrev BlockPoint (n : Nat) : Type :=
  Fin n ⊕ Fin n -> Real

/-- Convert a pair of `R^n` points into one point of the product coordinate space. -/
def doubledPointToBlockPoint (q : DoubledPoint n) : BlockPoint n :=
  Sum.elim q.1 q.2

/--
Identify the product coordinate space `R^n × R^n`, indexed by
`Fin n ⊕ Fin n`, with the coordinate space indexed by `Fin (n + n)`.
-/
def pointSumEquivBlockPoint (n : Nat) : Point (n + n) ≃ BlockPoint n :=
  Equiv.piCongrLeft (fun _ : Fin n ⊕ Fin n => Real) finSumFinEquiv.symm

@[simp]
theorem pointSumEquivBlockPoint_apply (z : Point (n + n)) (i : Fin (n + n)) :
    pointSumEquivBlockPoint n z (finSumFinEquiv.symm i) = z i := by
  simp [pointSumEquivBlockPoint]

@[simp]
theorem pointSumEquivBlockPoint_symm_apply (z : BlockPoint n) (i : Fin (n + n)) :
    (pointSumEquivBlockPoint n).symm z i = z (finSumFinEquiv.symm i) := by
  rfl

@[simp]
theorem pointSumEquivBlockPoint_apply_inl (z : Point (n + n)) (i : Fin n) :
    pointSumEquivBlockPoint n z (Sum.inl i) = z (Fin.castAdd n i) := by
  rw [← finSumFinEquiv_symm_apply_castAdd (m := n) (n := n) i]
  exact pointSumEquivBlockPoint_apply (n := n) z (Fin.castAdd n i)

@[simp]
theorem pointSumEquivBlockPoint_apply_inr (z : Point (n + n)) (i : Fin n) :
    pointSumEquivBlockPoint n z (Sum.inr i) = z (Fin.natAdd n i) := by
  rw [← finSumFinEquiv_symm_apply_natAdd (m := n) (n := n) i]
  exact pointSumEquivBlockPoint_apply (n := n) z (Fin.natAdd n i)

@[simp]
theorem pointSumEquivBlockPoint_zero :
    pointSumEquivBlockPoint n (0 : Point (n + n)) = (0 : BlockPoint n) := by
  ext i
  cases i <;> simp

@[simp]
theorem pointSumEquivBlockPoint_add (x y : Point (n + n)) :
    pointSumEquivBlockPoint n (x + y) =
      pointSumEquivBlockPoint n x + pointSumEquivBlockPoint n y := by
  ext i
  cases i <;> simp

@[simp]
theorem pointSumEquivBlockPoint_sub (x y : Point (n + n)) :
    pointSumEquivBlockPoint n (x - y) =
      pointSumEquivBlockPoint n x - pointSumEquivBlockPoint n y := by
  ext i
  cases i <;> simp

@[simp]
theorem pointSumEquivBlockPoint_smul (a : Real) (x : Point (n + n)) :
    pointSumEquivBlockPoint n (a • x) = a • pointSumEquivBlockPoint n x := by
  ext i
  cases i <;> simp

/-- Reindex a Hessian on `R^(n+n)` as a block Hessian on `R^n × R^n`. -/
def pointHessianToBlockHessian (A : Hessian (n + n)) : BlockHessian n :=
  A.submatrix finSumFinEquiv finSumFinEquiv

/-- Reindex a block Hessian on `R^n × R^n` as a Hessian on `R^(n+n)`. -/
def blockHessianToPointHessian (A : BlockHessian n) : Hessian (n + n) :=
  A.submatrix finSumFinEquiv.symm finSumFinEquiv.symm

@[simp]
theorem pointHessianToBlockHessian_apply
    (A : Hessian (n + n)) (i j : Fin n ⊕ Fin n) :
    pointHessianToBlockHessian A i j = A (finSumFinEquiv i) (finSumFinEquiv j) := by
  rfl

@[simp]
theorem blockHessianToPointHessian_apply
    (A : BlockHessian n) (i j : Fin (n + n)) :
    blockHessianToPointHessian A i j =
      A (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := by
  rfl

@[simp]
theorem pointHessianToBlockHessian_blockHessianToPointHessian
    (A : BlockHessian n) :
    pointHessianToBlockHessian (n := n) (blockHessianToPointHessian A) = A := by
  ext i j
  simp [pointHessianToBlockHessian, blockHessianToPointHessian]

@[simp]
theorem blockHessianToPointHessian_pointHessianToBlockHessian
    (A : Hessian (n + n)) :
    blockHessianToPointHessian (n := n) (pointHessianToBlockHessian A) = A := by
  ext i j
  simp [pointHessianToBlockHessian, blockHessianToPointHessian]

/--
Reindexing a Hermitian Hessian on `R^(n+n)` as a block Hessian on
`R^n × R^n` preserves Hermitian symmetry.
-/
theorem Matrix.IsHermitian.pointHessianToBlockHessian
    {A : Hessian (n + n)} (hA : A.IsHermitian) :
    (pointHessianToBlockHessian (n := n) A).IsHermitian :=
  hA.submatrix finSumFinEquiv

/--
Reindexing a Hermitian block Hessian on `R^n × R^n` as a Hessian on
`R^(n+n)` preserves Hermitian symmetry.
-/
theorem Matrix.IsHermitian.blockHessianToPointHessian
    {A : BlockHessian n} (hA : A.IsHermitian) :
    (blockHessianToPointHessian (n := n) A).IsHermitian :=
  hA.submatrix finSumFinEquiv.symm

/--
The coordinate reindexing from `Point (n + n)` to `BlockPoint n` preserves
dot products.
-/
theorem dotProduct_pointSumEquivBlockPoint
    (z w : Point (n + n)) :
    dotProduct (pointSumEquivBlockPoint n z) (pointSumEquivBlockPoint n w) =
      dotProduct z w := by
  have h :=
    Equiv.sum_comp finSumFinEquiv
      (fun i : Fin (n + n) => z i * w i)
  simpa [dotProduct, Fintype.sum_sum_type] using h

/--
Matrix-vector multiplication is preserved by reindexing a Hessian on
`R^(n+n)` as a block Hessian on `R^n × R^n`.
-/
theorem pointHessianToBlockHessian_mulVec_pointSumEquivBlockPoint
    (A : Hessian (n + n)) (z : Point (n + n)) :
    Matrix.mulVec (pointHessianToBlockHessian A) (pointSumEquivBlockPoint n z) =
      pointSumEquivBlockPoint n (Matrix.mulVec A z) := by
  ext i
  cases i with
  | inl i =>
      have h :=
        Equiv.sum_comp finSumFinEquiv
          (fun j : Fin (n + n) => A (Fin.castAdd n i) j * z j)
      simpa [Matrix.mulVec, dotProduct, pointHessianToBlockHessian,
        Fintype.sum_sum_type] using h
  | inr i =>
      have h :=
        Equiv.sum_comp finSumFinEquiv
          (fun j : Fin (n + n) => A (Fin.natAdd n i) j * z j)
      simpa [Matrix.mulVec, dotProduct, pointHessianToBlockHessian,
        Fintype.sum_sum_type] using h

/--
The quadratic form of a Hessian is unchanged by the coordinate equivalence
between `R^(n+n)` and `R^n × R^n`.
-/
theorem quadraticForm_pointHessianToBlockHessian_pointSumEquivBlockPoint
    (A : Hessian (n + n)) (z : Point (n + n)) :
    dotProduct (pointSumEquivBlockPoint n z)
        (Matrix.mulVec (pointHessianToBlockHessian A) (pointSumEquivBlockPoint n z)) =
      dotProduct z (Matrix.mulVec A z) := by
  rw [pointHessianToBlockHessian_mulVec_pointSumEquivBlockPoint]
  exact dotProduct_pointSumEquivBlockPoint z (Matrix.mulVec A z)

/-- The first coordinate of a point of `R^n × R^n`. -/
def blockPointLeft (q : BlockPoint n) : Point n :=
  q ∘ Sum.inl

/-- The second coordinate of a point of `R^n × R^n`. -/
def blockPointRight (q : BlockPoint n) : Point n :=
  q ∘ Sum.inr

@[simp]
theorem blockPointLeft_doubledPointToBlockPoint (q : DoubledPoint n) :
    blockPointLeft (doubledPointToBlockPoint q) = q.1 := by
  rfl

@[simp]
theorem blockPointRight_doubledPointToBlockPoint (q : DoubledPoint n) :
    blockPointRight (doubledPointToBlockPoint q) = q.2 := by
  rfl

@[simp]
theorem doubledPointToBlockPoint_left_right (q : BlockPoint n) :
    doubledPointToBlockPoint (blockPointLeft q, blockPointRight q) = q := by
  ext i
  cases i <;> rfl

/--
Loewner order implies the corresponding inequality of quadratic forms:
if `A ≤ B`, then for every vector `z`, `z · A z ≤ z · B z`.
-/
theorem quadraticForm_mono_of_matrix_le
    {m : Type*} [Fintype m] {A B : Matrix m m Real} (hAB : A <= B) (z : m -> Real) :
    dotProduct z (Matrix.mulVec A z) <= dotProduct z (Matrix.mulVec B z) := by
  have hpsd : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hnonneg : 0 <= dotProduct z (Matrix.mulVec (B - A) z) := by
    simpa using hpsd.dotProduct_mulVec_nonneg z
  have hquad :
      dotProduct z (Matrix.mulVec (B - A) z) =
        dotProduct z (Matrix.mulVec B z) - dotProduct z (Matrix.mulVec A z) := by
    simp [Matrix.sub_mulVec, dotProduct_sub]
  linarith

/--
Taking the same principal submatrix on both sides preserves the Loewner order.
-/
theorem matrix_le_submatrix
    {m k : Type*} {A B : Matrix m m Real}
    (hAB : A <= B) (e : k -> m) :
    A.submatrix e e <= B.submatrix e e := by
  rw [Matrix.le_iff] at hAB ⊢
  simpa [Matrix.submatrix_sub] using hAB.submatrix e

/--
The coordinate reindexing from `R^(n+n)` to `R^n × R^n` preserves the
Loewner order.
-/
theorem pointHessianToBlockHessian_mono
    {A B : Hessian (n + n)} (hAB : A <= B) :
    pointHessianToBlockHessian A <= pointHessianToBlockHessian (n := n) B :=
  matrix_le_submatrix hAB finSumFinEquiv

/-- The block diagonal matrix `[X 0; 0 -Y]`. -/
def comparisonBlockDiagonal (X Y : Hessian n) : BlockHessian n :=
  Matrix.fromBlocks X 0 0 (-Y)

/-- The block identity matrix `[I 0; 0 I]`. -/
def blockDiagonalIdentity (n : Nat) : BlockHessian n :=
  Matrix.fromBlocks (1 : Hessian n) 0 0 (1 : Hessian n)

/-- The block identity matrix is the ordinary identity matrix on `Fin n ⊕ Fin n`. -/
theorem blockDiagonalIdentity_eq_one :
    blockDiagonalIdentity n = (1 : BlockHessian n) := by
  simp [blockDiagonalIdentity,
    (Matrix.fromBlocks_one :
      Matrix.fromBlocks (1 : Hessian n) 0 0 (1 : Hessian n) = (1 : BlockHessian n))]

/--
The identity matrix on `R^(n+n)` becomes the block identity matrix on
`R^n × R^n`.
-/
theorem pointHessianToBlockHessian_one :
    pointHessianToBlockHessian (n := n) (1 : Hessian (n + n)) =
      blockDiagonalIdentity n := by
  have h :=
    Matrix.reindexLinearEquiv_one
      (R := Real) (A := Real)
      (e := (finSumFinEquiv.symm : Fin (n + n) ≃ Fin n ⊕ Fin n))
  have h' :
      pointHessianToBlockHessian (n := n) (1 : Hessian (n + n)) =
        (1 : BlockHessian n) := by
    simp [pointHessianToBlockHessian] at h ⊢
  simpa [blockDiagonalIdentity_eq_one] using h'

/--
A scalar multiple of the identity matrix on `R^(n+n)` becomes the same scalar
multiple of the block identity matrix on `R^n × R^n`.
-/
theorem pointHessianToBlockHessian_smul_one (a : Real) :
    pointHessianToBlockHessian (n := n) (a • (1 : Hessian (n + n))) =
      a • blockDiagonalIdentity n := by
  calc
    pointHessianToBlockHessian (n := n) (a • (1 : Hessian (n + n)))
        = a • pointHessianToBlockHessian (n := n) (1 : Hessian (n + n)) := by
          rfl
    _ = a • blockDiagonalIdentity n := by
          rw [pointHessianToBlockHessian_one]

/--
Reindex the two-sided matrix bounds supplied by the semiconvex matrix theorem
from `R^(n+n)` to `R^n × R^n`.

In quantified mathematical form, if `a I ≤ A ≤ B` as matrices on `R^(n+n)`,
then, after identifying `R^(n+n)` with `R^n × R^n`,
`a [I 0; 0 I] ≤ A_block ≤ B_block`.
-/
theorem pointHessianToBlockHessian_bounds_of_scalar_identity_bounds
    {a : Real} {A B : Hessian (n + n)}
    (hlower : a • (1 : Hessian (n + n)) <= A) (hupper : A <= B) :
    a • blockDiagonalIdentity n <= pointHessianToBlockHessian (n := n) A ∧
      pointHessianToBlockHessian (n := n) A <=
        pointHessianToBlockHessian (n := n) B := by
  constructor
  · have h := pointHessianToBlockHessian_mono (n := n) hlower
    simpa [pointHessianToBlockHessian_smul_one] using h
  · exact pointHessianToBlockHessian_mono (n := n) hupper

/--
The Hessian matrix of the quadratic penalty
`(α / 2) * ∑ i, (x i - y i)^2`, written in block form.
-/
def comparisonPenaltyBlock (α : Real) : BlockHessian n :=
  Matrix.fromBlocks
    (α • (1 : Hessian n))
    ((-α) • (1 : Hessian n))
    ((-α) • (1 : Hessian n))
    (α • (1 : Hessian n))

/--
The square of the Hessian matrix of the coordinate quadratic penalty.

In standard mathematical notation, if

`A = [ α I -α I ]`,
` [ -α I α I ]`

then `A^2 = 2α A`.
-/
theorem comparisonPenaltyBlock_mul_self (α : Real) :
    comparisonPenaltyBlock (n := n) α * comparisonPenaltyBlock (n := n) α =
      (2 * α) • comparisonPenaltyBlock (n := n) α := by
  rw [comparisonPenaltyBlock, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  ext i j
  cases i <;> cases j <;> simp <;> ring_nf

/--
The quadratic-penalty Hessian algebra used in the proof of Ishii's lemma.

In standard mathematical notation, if

`A = [ α I -α I ]`,
` [ -α I α I ]`

and `α ≠ 0`, then `A + α⁻¹ A^2 = 3A`.
-/
theorem comparisonPenaltyBlock_add_inv_smul_mul_self
    {α : Real} (hα : α ≠ 0) :
    comparisonPenaltyBlock (n := n) α +
        α⁻¹ • (comparisonPenaltyBlock (n := n) α * comparisonPenaltyBlock (n := n) α) =
      (3 : Real) • comparisonPenaltyBlock (n := n) α := by
  rw [comparisonPenaltyBlock_mul_self]
  ext i j
  cases i <;> cases j <;> simp [comparisonPenaltyBlock] <;> field_simp [hα] <;> ring

/-- The lower matrix bound `-(3 * α) [I 0; 0 I]`. -/
def ishiiLowerBlock (α : Real) : BlockHessian n :=
  (-(3 * α)) • blockDiagonalIdentity n

/-- The upper matrix bound `3` times the Hessian of the quadratic penalty. -/
def ishiiUpperBlock (α : Real) : BlockHessian n :=
  (3 : Real) • comparisonPenaltyBlock α

/--
The matrix relation appearing in the comparison theorem.

For `α > 0`, matrices `X` and `Y` satisfy this relation if
`[X 0; 0 -Y]` lies between the two block matrices displayed at the top of this
file. The points `x` and `y` are arguments so that this relation can be used
as a `ComparisonMatrixRelation`; the inequality itself does not depend on
them.
-/
def IshiiMatrixRelation (α : Real) (_x _y : Point n) (X Y : Hessian n) : Prop :=
  ishiiLowerBlock (n := n) α <= comparisonBlockDiagonal X Y ∧
    comparisonBlockDiagonal X Y <= ishiiUpperBlock (n := n) α

/-- The vector `(z, z)` in the product coordinate space `R^n × R^n`. -/
def doubledSameVector (z : Fin n -> Real) : Fin n ⊕ Fin n -> Real :=
  Sum.elim z z

/--
If `X` and `Y` satisfy `IshiiMatrixRelation α x y X Y`, then for every
`z : Fin n ⊕ Fin n -> Real`,

`zᵀ (ishiiLowerBlock α) z ≤ zᵀ (comparisonBlockDiagonal X Y) z`.
-/
theorem IshiiMatrixRelation.quadraticForm_lower {α : Real} {x y : Point n}
    {X Y : Hessian n} (h : IshiiMatrixRelation α x y X Y)
    (z : Fin n ⊕ Fin n -> Real) :
    dotProduct z (Matrix.mulVec (ishiiLowerBlock (n := n) α) z) <=
      dotProduct z (Matrix.mulVec (comparisonBlockDiagonal X Y) z) :=
  quadraticForm_mono_of_matrix_le h.1 z

/--
If `X` and `Y` satisfy `IshiiMatrixRelation α x y X Y`, then for every
`z : Fin n ⊕ Fin n -> Real`,

`zᵀ (comparisonBlockDiagonal X Y) z ≤ zᵀ (ishiiUpperBlock α) z`.
-/
theorem IshiiMatrixRelation.quadraticForm_upper {α : Real} {x y : Point n}
    {X Y : Hessian n} (h : IshiiMatrixRelation α x y X Y)
    (z : Fin n ⊕ Fin n -> Real) :
    dotProduct z (Matrix.mulVec (comparisonBlockDiagonal X Y) z) <=
      dotProduct z (Matrix.mulVec (ishiiUpperBlock (n := n) α) z) :=
  quadraticForm_mono_of_matrix_le h.2 z

/--
For every vector `z : Fin n -> Real`, the quadratic form of
`comparisonBlockDiagonal X Y` on `(z, z)` is
`zᵀ X z - zᵀ Y z`.
-/
theorem comparisonBlockDiagonal_quadratic_doubledSameVector
    (X Y : Hessian n) (z : Fin n -> Real) :
    dotProduct (doubledSameVector z)
        (Matrix.mulVec (comparisonBlockDiagonal X Y) (doubledSameVector z)) =
      dotProduct z (Matrix.mulVec X z) - dotProduct z (Matrix.mulVec Y z) := by
  simp [doubledSameVector, comparisonBlockDiagonal, Matrix.fromBlocks_mulVec,
    Matrix.neg_mulVec, dotProduct_neg]
  ring

/--
The coordinate dot product of a vector with itself is nonnegative.
-/
theorem dotProduct_self_nonneg {m : Type*} [Fintype m] (x : m -> Real) :
    0 <= dotProduct x x := by
  rw [dotProduct]
  exact Finset.sum_nonneg fun i _hi => mul_self_nonneg (x i)

/--
A finite entrywise bound on a Hessian gives an upper bound for its quadratic
form.

In quantified mathematical form, if `η ≥ 0` and `|Aᵢⱼ| ≤ η` for every
matrix entry, then for every vector `v`,

`⟪Av, v⟫ ≤ η n^2 ⟪v, v⟫`.
-/
theorem hessian_quadraticForm_le_of_entrywise_abs_le
    (A : Hessian n) {eta : Real} (heta : 0 <= eta)
    (hA : ∀ i j : Fin n, |A i j| <= eta) (v : Point n) :
    dotProduct (Matrix.mulVec A v) v <=
      (eta * (n : Real) * (n : Real)) * dotProduct v v := by
  have hquad :=
    abs_quadraticModel_zero_zero_le_of_entrywise_abs_le
      (n := n) (x0 := 0) (x := v) (A := A) heta hA
  have hhalf_le :
      (1 / 2 : Real) * dotProduct (Matrix.mulVec A v) v <=
        ((1 / 2 : Real) * eta * (n : Real) * (n : Real)) * ‖v‖ ^ 2 := by
    have hle_abs :
        (1 / 2 : Real) * dotProduct (Matrix.mulVec A v) v <=
          |(1 / 2 : Real) * dotProduct (Matrix.mulVec A v) v| :=
      le_abs_self _
    have hquad_eq :
        quadraticModel (n := n) 0 0 0 A v =
          (1 / 2 : Real) * dotProduct (Matrix.mulVec A v) v := by
      simp [quadraticModel]
    have hquad' :
        |(1 / 2 : Real) * dotProduct (Matrix.mulVec A v) v| <=
          ((1 / 2 : Real) * eta * (n : Real) * (n : Real)) * ‖v‖ ^ 2 := by
      simpa [hquad_eq] using hquad
    linarith
  have hdot_norm : ‖v‖ ^ 2 <= dotProduct v v :=
    norm_sq_le_dotProduct_self v
  have hcoeff_nonneg : 0 <= eta * (n : Real) * (n : Real) := by positivity
  calc
    dotProduct (Matrix.mulVec A v) v <=
        (eta * (n : Real) * (n : Real)) * ‖v‖ ^ 2 := by
      linarith
    _ <= (eta * (n : Real) * (n : Real)) * dotProduct v v := by
      exact mul_le_mul_of_nonneg_left hdot_norm hcoeff_nonneg

/--
Every real symmetric Hessian is bounded above by a scalar multiple of the
identity in the Loewner order.

In quantified mathematical form, for every symmetric matrix `A` on `R^n`,
there exists `μ ∈ R` such that `A ≤ μ I`.
-/
theorem exists_hessian_le_smul_one_of_isHermitian
    {A : Hessian n} (hA : A.IsHermitian) :
    ∃ mu : Real, A <= mu • (1 : Hessian n) := by
  let eta : Real := ∑ i : Fin n, ∑ j : Fin n, |A i j|
  let mu : Real := eta * (n : Real) * (n : Real)
  have heta_nonneg : 0 <= eta := by
    exact Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => abs_nonneg (A i j)
  have hentry : ∀ i j : Fin n, |A i j| <= eta := by
    intro i j
    calc
      |A i j| <= ∑ j : Fin n, |A i j| := by
        exact Finset.single_le_sum (fun k _hk => abs_nonneg (A i k)) (Finset.mem_univ j)
      _ <= eta := by
        exact Finset.single_le_sum
          (fun k _hk => Finset.sum_nonneg fun l _hl => abs_nonneg (A k l))
          (Finset.mem_univ i)
  refine ⟨mu, ?_⟩
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact (Matrix.isHermitian_one.smul (IsSelfAdjoint.all mu)).sub hA
  · intro v
    have hquad :
        dotProduct (Matrix.mulVec A v) v <= mu * dotProduct v v := by
      simpa [mu] using
        hessian_quadraticForm_le_of_entrywise_abs_le
          (n := n) A heta_nonneg hentry v
    have hdiffQuad :
        star v ⬝ᵥ Matrix.mulVec (mu • (1 : Hessian n) - A) v =
          mu * dotProduct v v - dotProduct (Matrix.mulVec A v) v := by
      simp [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, Matrix.one_mulVec,
        dotProduct_comm]
    rw [hdiffQuad]
    linarith

/--
Every real symmetric block Hessian on `R^n × R^n` is bounded above by a scalar
multiple of the block identity in the Loewner order.

In quantified mathematical form, for every symmetric matrix `A` on
`R^n × R^n`, there exists `μ ∈ R` such that

`A ≤ μ [I 0; 0 I]`.
-/
theorem exists_blockHessian_le_smul_blockDiagonalIdentity_of_isHermitian
    {A : BlockHessian n} (hA : A.IsHermitian) :
    ∃ mu : Real, A <= mu • blockDiagonalIdentity n := by
  rcases exists_hessian_le_smul_one_of_isHermitian
      (n := n + n) (A := blockHessianToPointHessian (n := n) A)
      (Matrix.IsHermitian.blockHessianToPointHessian (n := n) hA) with
    ⟨mu, hmu⟩
  refine ⟨mu, ?_⟩
  have hblock := pointHessianToBlockHessian_mono (n := n) hmu
  simpa [pointHessianToBlockHessian_smul_one] using hblock

/--
Young's inequality for the coordinate dot product.

In standard mathematical terms, for `ε > 0` and finite-coordinate vectors
`u` and `v`,

`⟪u, v⟫ ≤ (ε / 2) * |u|^2 + (ε⁻¹ / 2) * |v|^2`.
-/
theorem dotProduct_le_young
    {m : Type*} [Fintype m] {epsilon : Real} (hepsilon : 0 < epsilon)
    (u v : m -> Real) :
    dotProduct u v <=
      (epsilon / 2) * dotProduct u u + (epsilon⁻¹ / 2) * dotProduct v v := by
  have hnonneg : 0 <= dotProduct (epsilon • u - v) (epsilon • u - v) :=
    dotProduct_self_nonneg (epsilon • u - v)
  have hdot :
      dotProduct (epsilon • u - v) (epsilon • u - v) =
        epsilon ^ 2 * dotProduct u u - 2 * epsilon * dotProduct u v +
          dotProduct v v := by
    simp [dotProduct_sub, dotProduct_smul, dotProduct_comm]
    ring
  have heps_nonneg : 0 <= epsilon := hepsilon.le
  have hmul :
      2 * epsilon * dotProduct u v <=
        epsilon ^ 2 * dotProduct u u + dotProduct v v := by
    rw [hdot] at hnonneg
    linarith
  have hdiv := div_le_div_of_nonneg_right hmul (by positivity : 0 <= 2 * epsilon)
  have hden_pos : 0 < 2 * epsilon := by positivity
  have hden_ne : 2 * epsilon ≠ 0 := ne_of_gt hden_pos
  have hinv_eq : epsilon⁻¹ / 2 = 1 / (2 * epsilon) := by
    field_simp [ne_of_gt hepsilon]
  have hleft : (2 * epsilon * dotProduct u v) / (2 * epsilon) = dotProduct u v := by
    field_simp [hden_ne]
  have hright :
      (epsilon ^ 2 * dotProduct u u + dotProduct v v) / (2 * epsilon) =
        (epsilon / 2) * dotProduct u u + (epsilon⁻¹ / 2) * dotProduct v v := by
    rw [hinv_eq]
    field_simp [ne_of_gt hepsilon]
  simpa [hleft, hright] using hdiv

end ViscositySolns
