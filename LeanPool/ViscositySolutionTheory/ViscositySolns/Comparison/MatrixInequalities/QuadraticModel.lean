/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.MatrixInequalities.BlockStructure

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Matrix inequalities for comparison (QuadraticModel)

Part of the block-matrix development used in the doubling-of-variables
proof of comparison. Split from `MatrixInequalities.lean`; see the umbrella
module docstring.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The pure quadratic expression associated to a block Hessian on
`R^n × R^n`.
-/
def blockQuadraticModel (A : BlockHessian n) (q : BlockPoint n) : Real :=
  (1 / 2 : Real) * dotProduct (Matrix.mulVec A q) q

/--
Symmetry of the bilinear form associated to a Hermitian real matrix.

In standard mathematical terms, if `A` is symmetric, then
`⟪Ax, y⟫ = ⟪Ay, x⟫`.
-/
theorem dotProduct_mulVec_comm_of_isHermitian
    {A : BlockHessian n} (hA : A.IsHermitian) (x y : BlockPoint n) :
    dotProduct (Matrix.mulVec A x) y =
      dotProduct (Matrix.mulVec A y) x := by
  have htranspose : A.transpose = A := by
    ext i j
    simpa using hA.apply i j
  calc
    dotProduct (Matrix.mulVec A x) y = dotProduct y (Matrix.mulVec A x) :=
      dotProduct_comm _ _
    _ = dotProduct x (Matrix.mulVec A.transpose y) :=
      (Matrix.dotProduct_transpose_mulVec A x y).symm
    _ = dotProduct x (Matrix.mulVec A y) := by
      rw [htranspose]
    _ = dotProduct (Matrix.mulVec A y) x :=
      dotProduct_comm _ _

/--
Expansion of a Hermitian quadratic form at a translated point.

In standard mathematical terms, if `A` is symmetric, then for every
`ξ, h ∈ R^n × R^n`,

`(1 / 2) * ⟪A(ξ + h), ξ + h⟫ =
 (1 / 2) * ⟪Aξ, ξ⟫ + ⟪Aξ, h⟫ + (1 / 2) * ⟪Ah, h⟫`.
-/
theorem blockQuadraticModel_add
    {A : BlockHessian n} (hA : A.IsHermitian) (ξ h : BlockPoint n) :
    blockQuadraticModel A (ξ + h) =
      blockQuadraticModel A ξ + dotProduct (Matrix.mulVec A ξ) h +
        blockQuadraticModel A h := by
  have hcross :
      dotProduct (Matrix.mulVec A h) ξ =
        dotProduct (Matrix.mulVec A ξ) h :=
    dotProduct_mulVec_comm_of_isHermitian hA h ξ
  simp only [blockQuadraticModel, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  rw [hcross]
  ring

/--
The quadratic form associated to `A + ε A^2`.

In standard mathematical terms, if `A` is symmetric, then

`(1 / 2) * ⟪(A + ε A^2)ξ, ξ⟫ =
 (1 / 2) * ⟪Aξ, ξ⟫ + (ε / 2) * |Aξ|^2`.
-/
theorem blockQuadraticModel_add_smul_mul_self
    {A : BlockHessian n} (hA : A.IsHermitian) (epsilon : Real) (ξ : BlockPoint n) :
    blockQuadraticModel (A + epsilon • (A * A)) ξ =
      blockQuadraticModel A ξ +
        (epsilon / 2) * dotProduct (Matrix.mulVec A ξ) (Matrix.mulVec A ξ) := by
  have hsq :
      dotProduct (Matrix.mulVec (A * A) ξ) ξ =
        dotProduct (Matrix.mulVec A ξ) (Matrix.mulVec A ξ) := by
    rw [← Matrix.mulVec_mulVec ξ A A]
    exact dotProduct_mulVec_comm_of_isHermitian hA (Matrix.mulVec A ξ) ξ
  simp [blockQuadraticModel, Matrix.add_mulVec, Matrix.smul_mulVec, add_dotProduct,
    smul_dotProduct, hsq]
  ring

/--
A Loewner upper bound by a scalar multiple of the identity gives the
corresponding quadratic-form upper bound.

In standard mathematical terms, if `A ≤ μ I`, then

`(1 / 2) * ⟪Ah, h⟫ ≤ (μ / 2) * |h|^2`

for every vector `h`.
-/
theorem blockQuadraticModel_le_of_le_smul_identity
    {A : BlockHessian n} {mu : Real}
    (hA : A <= mu • blockDiagonalIdentity n) :
    ∀ h : BlockPoint n,
      blockQuadraticModel A h <= (mu / 2) * dotProduct h h := by
  intro h
  have hquad := quadraticForm_mono_of_matrix_le hA h
  have hleft :
      dotProduct h (Matrix.mulVec A h) =
        dotProduct (Matrix.mulVec A h) h :=
    dotProduct_comm _ _
  have hright :
      dotProduct h (Matrix.mulVec (mu • blockDiagonalIdentity n) h) =
        mu * dotProduct h h := by
    simp [blockDiagonalIdentity_eq_one, Matrix.smul_mulVec]
  rw [hleft, hright] at hquad
  dsimp [blockQuadraticModel]
  linarith

/--
The CIL quadratic comparison estimate, separated from the scalar inequalities
used to prove it.

In standard mathematical terms, let `A` be symmetric. Suppose that

`(1 / 2) * ⟪Ah, h⟫ ≤ (μ / 2) * |h|^2`

for every `h`, and suppose that

`⟪Aξ, h⟫ ≤ (ε / 2) * |Aξ|^2 + (ε⁻¹ / 2) * |h|^2`

for every `ξ` and `h`. Then for every `z` and `ξ`,

`(1 / 2) * ⟪Az, z⟫ ≤
 (1 / 2) * ⟪(A + ε A^2)ξ, ξ⟫
 + ((ε⁻¹ + μ) / 2) * |z - ξ|^2`.
-/
theorem blockQuadraticModel_le_add_smul_mul_self_add_of_bounds
    {A : BlockHessian n} (hA : A.IsHermitian) {epsilon mu : Real}
    (hbound : ∀ h : BlockPoint n,
      blockQuadraticModel A h <= (mu / 2) * dotProduct h h)
    (hyoung : ∀ ξ h : BlockPoint n,
      dotProduct (Matrix.mulVec A ξ) h <=
        (epsilon / 2) * dotProduct (Matrix.mulVec A ξ) (Matrix.mulVec A ξ) +
          (epsilon⁻¹ / 2) * dotProduct h h) :
    ∀ z ξ : BlockPoint n,
      blockQuadraticModel A z <=
        blockQuadraticModel (A + epsilon • (A * A)) ξ +
          ((epsilon⁻¹ + mu) / 2) * dotProduct (z - ξ) (z - ξ) := by
  intro z ξ
  let h : BlockPoint n := z - ξ
  have hz : z = ξ + h := by
    ext i
    simp [h]
  have hexpand :
      blockQuadraticModel A z =
        blockQuadraticModel A ξ + dotProduct (Matrix.mulVec A ξ) h +
          blockQuadraticModel A h := by
    rw [hz]
    exact blockQuadraticModel_add hA ξ h
  have hAeps :
      blockQuadraticModel (A + epsilon • (A * A)) ξ =
        blockQuadraticModel A ξ +
          (epsilon / 2) * dotProduct (Matrix.mulVec A ξ) (Matrix.mulVec A ξ) :=
    blockQuadraticModel_add_smul_mul_self hA epsilon ξ
  have hbound_h := hbound h
  have hyoung_h := hyoung ξ h
  have hdot : dotProduct h h = dotProduct (z - ξ) (z - ξ) := rfl
  rw [hexpand, hAeps]
  rw [← hdot]
  linarith

/--
The CIL quadratic comparison estimate obtained from a Loewner upper bound
`A ≤ μ I`.

In standard mathematical terms, if `A` is symmetric, `ε > 0`, and
`A ≤ μ I`, then for every `z` and `ξ`,

`(1 / 2) * ⟪Az, z⟫ ≤
 (1 / 2) * ⟪(A + ε A^2)ξ, ξ⟫
 + ((ε⁻¹ + μ) / 2) * |z - ξ|^2`.
-/
theorem blockQuadraticModel_le_add_smul_mul_self_add_of_le_smul_identity
    {A : BlockHessian n} (hHerm : A.IsHermitian) {epsilon mu : Real}
    (hepsilon : 0 < epsilon)
    (hA : A <= mu • blockDiagonalIdentity n) :
    ∀ z ξ : BlockPoint n,
      blockQuadraticModel A z <=
        blockQuadraticModel (A + epsilon • (A * A)) ξ +
          ((epsilon⁻¹ + mu) / 2) * dotProduct (z - ξ) (z - ξ) := by
  exact blockQuadraticModel_le_add_smul_mul_self_add_of_bounds
    hHerm
    (blockQuadraticModel_le_of_le_smul_identity hA)
    (fun ξ h => dotProduct_le_young hepsilon (Matrix.mulVec A ξ) h)

/--
The pure quadratic model at the origin is unchanged by the coordinate
equivalence between `R^(n+n)` and `R^n × R^n`.
-/
theorem blockQuadraticModel_pointHessianToBlockHessian_pointSumEquivBlockPoint
    (A : Hessian (n + n)) (z : Point (n + n)) :
    blockQuadraticModel (pointHessianToBlockHessian A) (pointSumEquivBlockPoint n z) =
      quadraticModel 0 0 0 A z := by
  simp [blockQuadraticModel, quadraticModel,
    quadraticForm_pointHessianToBlockHessian_pointSumEquivBlockPoint,
    dotProduct_comm]

/--
The quadratic expression of a block diagonal Hessian on `R^n × R^n`.

In quantified mathematical form, for every `x, y : R^n`,

`1 / 2 * ⟪[X 0; 0 -Y] (x, y), (x, y)⟫ =
  1 / 2 * ⟪X x, x⟫ - 1 / 2 * ⟪Y y, y⟫`.
-/
theorem blockQuadraticModel_comparisonBlockDiagonal_doubledPoint
    (X Y : Hessian n) (q : DoubledPoint n) :
    blockQuadraticModel (comparisonBlockDiagonal X Y) (doubledPointToBlockPoint q) =
      quadraticModel 0 0 0 X q.1 - quadraticModel 0 0 0 Y q.2 := by
  simp [blockQuadraticModel, quadraticModel, doubledPointToBlockPoint, comparisonBlockDiagonal,
    Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, sumElim_dotProduct_sumElim]
  ring

/--
The block Hessian of the coordinate quadratic penalty gives the coordinate
quadratic penalty.

In quantified mathematical form, for every `x, y : R^n`,

`1 / 2 * ⟪[α I -α I; -α I α I] (x, y), (x, y)⟫
 = (α / 2) * ∑ i, (x i - y i)^2`.
-/
theorem blockQuadraticModel_comparisonPenaltyBlock_doubledPoint
    (α : Real) (q : DoubledPoint n) :
    blockQuadraticModel (comparisonPenaltyBlock (n := n) α) (doubledPointToBlockPoint q) =
      quadraticPenalty α q.1 q.2 := by
  have hleft : Sum.elim q.1 q.2 ∘ Sum.inl = q.1 := rfl
  have hright : Sum.elim q.1 q.2 ∘ Sum.inr = q.2 := rfl
  simp only [blockQuadraticModel, quadraticPenalty, doubledPointToBlockPoint,
    comparisonPenaltyBlock, Matrix.fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    hleft, hright, sumElim_dotProduct_sumElim, add_dotProduct, smul_dotProduct,
    dotProduct_sub, sub_dotProduct]
  rw [dotProduct_comm q.2 q.1]
  ring

/--
The coordinate quadratic-penalty Hessian is bounded above by `2α` times the
block identity.

In quantified mathematical form, if `0 ≤ α`, then

`[αI -αI; -αI αI] ≤ 2α [I 0; 0 I]`

in the Loewner order.
-/
theorem comparisonPenaltyBlock_le_two_smul_blockDiagonalIdentity
    {α : Real} (hα : 0 <= α) :
    comparisonPenaltyBlock (n := n) α <= (2 * α) • blockDiagonalIdentity n := by
  refine Matrix.le_iff.mpr ?_
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · have hαI : (α • (1 : Hessian n)).IsHermitian :=
      Matrix.isHermitian_one.smul (IsSelfAdjoint.all α)
    have hnegαI : ((-α) • (1 : Hessian n)).IsHermitian :=
      Matrix.isHermitian_one.smul (IsSelfAdjoint.all (-α))
    have hpenalty : (comparisonPenaltyBlock (n := n) α).IsHermitian :=
      Matrix.IsHermitian.fromBlocks hαI hnegαI hαI
    have hdiag : ((2 * α) • blockDiagonalIdentity n).IsHermitian := by
      simp [blockDiagonalIdentity_eq_one]
    exact hdiag.sub hpenalty
  · intro q
    let x : Point n := blockPointLeft q
    let y : Point n := blockPointRight q
    have hq : doubledPointToBlockPoint (x, y) = q := by
      ext i
      cases i <;> rfl
    have hdiag :
        dotProduct q (Matrix.mulVec ((2 * α) • blockDiagonalIdentity n) q) =
          (2 * α) * dotProduct q q := by
      simp [blockDiagonalIdentity_eq_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hpen :
        dotProduct q (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) q) =
          2 * quadraticPenalty α x y := by
      have h :=
        blockQuadraticModel_comparisonPenaltyBlock_doubledPoint
          (n := n) α (x, y)
      rw [hq] at h
      have hdot :
          dotProduct (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) q) q =
            dotProduct q (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) q) := by
        exact dotProduct_comm _ _
      rw [blockQuadraticModel, hdot] at h
      nlinarith
    have hself :
        dotProduct q q =
          dotProduct x x + dotProduct y y := by
      rw [← hq]
      simp [doubledPointToBlockPoint, dotProduct, Fintype.sum_sum_type, x, y,
        blockPointLeft, blockPointRight]
    have hpenalty :
        quadraticPenalty α x y = (α / 2) * dotProduct (x - y) (x - y) := by
      rw [quadraticPenalty_apply]
    have hsum_nonneg : 0 <= dotProduct (x + y) (x + y) :=
      dotProduct_self_nonneg (x + y)
    have hnonneg : 0 <= α * dotProduct (x + y) (x + y) :=
      mul_nonneg hα hsum_nonneg
    have hquad :
        (2 * α) * dotProduct q q - 2 * quadraticPenalty α x y =
          α * dotProduct (x + y) (x + y) := by
      rw [hself, hpenalty]
      simp only [dotProduct_add, add_dotProduct, dotProduct_sub, sub_dotProduct]
      ring
    have hdiff :
        star q ⬝ᵥ Matrix.mulVec
            ((2 * α) • blockDiagonalIdentity n - comparisonPenaltyBlock (n := n) α) q =
          (2 * α) * dotProduct q q - 2 * quadraticPenalty α x y := by
      simp [Matrix.sub_mulVec, dotProduct_sub, hdiag, hpen]
    rw [hdiff, hquad]
    exact hnonneg

/--
The first derivative of the coordinate quadratic penalty in block form.

In standard mathematical terms, if

`A = [ α I -α I ]`,
` [ -α I α I ]`,

then `A (x, y) = (α(x - y), -α(x - y))`.
-/
theorem comparisonPenaltyBlock_mulVec_doubledPoint
    (α : Real) (q : DoubledPoint n) :
    Matrix.mulVec (comparisonPenaltyBlock (n := n) α) (doubledPointToBlockPoint q) =
      doubledPointToBlockPoint
        (quadraticPenaltyGradientLeft α q.1 q.2, quadraticPenaltyGradientRight α q.1 q.2) := by
  ext i
  cases i <;>
    simp [comparisonPenaltyBlock, doubledPointToBlockPoint, quadraticPenaltyGradientLeft,
      quadraticPenaltyGradientRight, Matrix.fromBlocks_mulVec, Matrix.smul_mulVec,
      Matrix.neg_mulVec] <;> ring_nf

/--
The left component of the first derivative of the coordinate quadratic
penalty is `α(x - y)`.
-/
theorem blockPointLeft_comparisonPenaltyBlock_mulVec_doubledPoint
    (α : Real) (q : DoubledPoint n) :
    blockPointLeft
        (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) (doubledPointToBlockPoint q)) =
      quadraticPenaltyGradientLeft α q.1 q.2 := by
  rw [comparisonPenaltyBlock_mulVec_doubledPoint]
  rfl

/--
The right component of the first derivative of the coordinate quadratic
penalty is `-α(x - y)`.
-/
theorem blockPointRight_comparisonPenaltyBlock_mulVec_doubledPoint
    (α : Real) (q : DoubledPoint n) :
    blockPointRight
        (Matrix.mulVec (comparisonPenaltyBlock (n := n) α) (doubledPointToBlockPoint q)) =
      quadraticPenaltyGradientRight α q.1 q.2 := by
  rw [comparisonPenaltyBlock_mulVec_doubledPoint]
  rfl

/--
The upper Ishii block has quadratic expression equal to three times the
coordinate quadratic penalty.
-/
theorem blockQuadraticModel_ishiiUpperBlock_doubledPoint
    (α : Real) (q : DoubledPoint n) :
    blockQuadraticModel (ishiiUpperBlock (n := n) α) (doubledPointToBlockPoint q) =
      3 * quadraticPenalty α q.1 q.2 := by
  have hpen :=
    blockQuadraticModel_comparisonPenaltyBlock_doubledPoint (n := n) α q
  dsimp [blockQuadraticModel] at hpen ⊢
  simp [ishiiUpperBlock, Matrix.smul_mulVec, smul_dotProduct] at hpen ⊢
  nlinarith

/--
For every vector `z : Fin n -> Real`, the Hessian matrix of
`(α / 2) * ∑ i, (x i - y i)^2` sends `(z, z)` to zero.
-/
theorem comparisonPenaltyBlock_mulVec_doubledSameVector
    (α : Real) (z : Fin n -> Real) :
    Matrix.mulVec (comparisonPenaltyBlock (n := n) α) (doubledSameVector z) = 0 := by
  ext i
  simp [comparisonPenaltyBlock, doubledSameVector, Matrix.fromBlocks_mulVec,
    Matrix.smul_mulVec, Matrix.neg_mulVec]

/--
For every vector `z : Fin n -> Real`, the quadratic form of the upper Ishii
block on `(z, z)` is zero.
-/
theorem ishiiUpperBlock_quadratic_doubledSameVector (α : Real) (z : Fin n -> Real) :
    dotProduct (doubledSameVector z)
        (Matrix.mulVec (ishiiUpperBlock (n := n) α) (doubledSameVector z)) = 0 := by
  simp [ishiiUpperBlock, Matrix.smul_mulVec, comparisonPenaltyBlock_mulVec_doubledSameVector]

/--
If `X` and `Y` satisfy `IshiiMatrixRelation α x y X Y`, then for every
`z : Fin n -> Real`,

`zᵀ X z ≤ zᵀ Y z`.
-/
theorem IshiiMatrixRelation.quadraticForm_left_le_right {α : Real} {x y : Point n}
    {X Y : Hessian n} (h : IshiiMatrixRelation α x y X Y) (z : Fin n -> Real) :
    dotProduct z (Matrix.mulVec X z) <= dotProduct z (Matrix.mulVec Y z) := by
  have hupper := h.quadraticForm_upper (doubledSameVector z)
  rw [comparisonBlockDiagonal_quadratic_doubledSameVector,
    ishiiUpperBlock_quadratic_doubledSameVector] at hupper
  linarith

/--
If `X` and `Y` satisfy `IshiiMatrixRelation α x y X Y`, then `X ≤ Y` in
the Loewner order.
-/
theorem IshiiMatrixRelation.left_le_right {α : Real} {x y : Point n}
    {X Y : Hessian n} (h : IshiiMatrixRelation α x y X Y) :
    X <= Y := by
  have hdiff : (ishiiUpperBlock (n := n) α - comparisonBlockDiagonal X Y).PosSemidef :=
    Matrix.le_iff.mp h.2
  have hupperHerm : (ishiiUpperBlock (n := n) α).IsHermitian := by
    have hαI : (α • (1 : Hessian n)).IsHermitian :=
      Matrix.isHermitian_one.smul (IsSelfAdjoint.all α)
    have hnegαI : ((-α) • (1 : Hessian n)).IsHermitian :=
      Matrix.isHermitian_one.smul (IsSelfAdjoint.all (-α))
    have hpenalty : (comparisonPenaltyBlock (n := n) α).IsHermitian := by
      exact Matrix.IsHermitian.fromBlocks hαI hnegαI hαI
    exact hpenalty.smul (IsSelfAdjoint.all (3 : Real))
  have hmiddleHerm : (comparisonBlockDiagonal X Y).IsHermitian := by
    have htmp :
        (ishiiUpperBlock (n := n) α -
          (ishiiUpperBlock (n := n) α - comparisonBlockDiagonal X Y)).IsHermitian :=
      hupperHerm.sub hdiff.isHermitian
    convert htmp using 1
    ext i j
    simp
  have hXHerm : X.IsHermitian := by
    exact (Matrix.isHermitian_fromBlocks_iff.mp hmiddleHerm).1
  have hYHerm : Y.IsHermitian := by
    have hnegYHerm : (-Y).IsHermitian :=
      (Matrix.isHermitian_fromBlocks_iff.mp hmiddleHerm).2.2.2
    simpa using Matrix.isHermitian_neg_iff.mp hnegYHerm
  refine Matrix.le_iff.mpr ?_
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hYHerm.sub hXHerm) ?_
  intro z
  have hquad := h.quadraticForm_left_le_right z
  have hdiffQuad :
      star z ⬝ᵥ Matrix.mulVec (Y - X) z =
        dotProduct z (Matrix.mulVec Y z) - dotProduct z (Matrix.mulVec X z) := by
    simp [Matrix.sub_mulVec, dotProduct_sub]
  rw [hdiffQuad]
  linarith

/--
The lower Ishii block bound implies `-(3 * α) I ≤ X`.
-/
theorem IshiiMatrixRelation.left_lower_bound {α : Real} {x y : Point n}
    {X Y : Hessian n} (h : IshiiMatrixRelation α x y X Y) :
    (-(3 * α)) • (1 : Hessian n) <= X := by
  have hsub := matrix_le_submatrix h.1 (Sum.inl : Fin n -> Fin n ⊕ Fin n)
  have hlower :
      Matrix.submatrix (ishiiLowerBlock (n := n) α) Sum.inl Sum.inl =
        (-(3 * α)) • (1 : Hessian n) := by
    ext i j
    by_cases hij : i = j <;>
      simp [ishiiLowerBlock, blockDiagonalIdentity, hij]
  have hmiddle :
      Matrix.submatrix (comparisonBlockDiagonal X Y) Sum.inl Sum.inl = X := by
    ext i j
    simp [comparisonBlockDiagonal]
  simpa [hlower, hmiddle] using hsub

/--
The upper Ishii block bound implies `X ≤ 3α I`.
-/
theorem IshiiMatrixRelation.left_upper_bound {α : Real} {x y : Point n}
    {X Y : Hessian n} (h : IshiiMatrixRelation α x y X Y) :
    X <= (3 * α) • (1 : Hessian n) := by
  have hsub := matrix_le_submatrix h.2 (Sum.inl : Fin n -> Fin n ⊕ Fin n)
  have hmiddle :
      Matrix.submatrix (comparisonBlockDiagonal X Y) Sum.inl Sum.inl = X := by
    ext i j
    simp [comparisonBlockDiagonal]
  have hupper :
      Matrix.submatrix (ishiiUpperBlock (n := n) α) Sum.inl Sum.inl =
        (3 * α) • (1 : Hessian n) := by
    ext i j
    simp [ishiiUpperBlock, comparisonPenaltyBlock]
    ring
  simpa [hmiddle, hupper] using hsub

/--
The upper Ishii block bound implies `-(3 * α) I ≤ Y`.
-/
theorem IshiiMatrixRelation.right_lower_bound {α : Real} {x y : Point n}
    {X Y : Hessian n} (h : IshiiMatrixRelation α x y X Y) :
    (-(3 * α)) • (1 : Hessian n) <= Y := by
  have hsub := matrix_le_submatrix h.2 (Sum.inr : Fin n -> Fin n ⊕ Fin n)
  have hneg : -Y <= (3 * α) • (1 : Hessian n) := by
    have hmiddle :
        Matrix.submatrix (comparisonBlockDiagonal X Y) Sum.inr Sum.inr = -Y := by
      ext i j
      simp [comparisonBlockDiagonal]
    have hupper :
        Matrix.submatrix (ishiiUpperBlock (n := n) α) Sum.inr Sum.inr =
          (3 * α) • (1 : Hessian n) := by
      ext i j
      simp [ishiiUpperBlock, comparisonPenaltyBlock]
      ring
    simpa [hmiddle, hupper] using hsub
  have hneg' : (-(3 * α)) • (1 : Hessian n) <= Y := by
    simpa [neg_smul] using neg_le_neg hneg
  exact hneg'

/--
The lower Ishii block bound implies `Y ≤ 3α I`.
-/
theorem IshiiMatrixRelation.right_upper_bound {α : Real} {x y : Point n}
    {X Y : Hessian n} (h : IshiiMatrixRelation α x y X Y) :
    Y <= (3 * α) • (1 : Hessian n) := by
  have hsub := matrix_le_submatrix h.1 (Sum.inr : Fin n -> Fin n ⊕ Fin n)
  have hneg : (-(3 * α)) • (1 : Hessian n) <= -Y := by
    have hlower :
        Matrix.submatrix (ishiiLowerBlock (n := n) α) Sum.inr Sum.inr =
          (-(3 * α)) • (1 : Hessian n) := by
      ext i j
      by_cases hij : i = j <;>
        simp [ishiiLowerBlock, blockDiagonalIdentity, hij]
    have hmiddle :
        Matrix.submatrix (comparisonBlockDiagonal X Y) Sum.inr Sum.inr = -Y := by
      ext i j
      simp [comparisonBlockDiagonal]
    simpa [hlower, hmiddle] using hsub
  have hneg' : Y <= (3 * α) • (1 : Hessian n) := by
    simpa [neg_smul] using neg_le_neg hneg
  exact hneg'

@[simp]
theorem comparisonBlockDiagonal_apply_left_left (X Y : Hessian n) (i j : Fin n) :
    comparisonBlockDiagonal X Y (Sum.inl i) (Sum.inl j) = X i j := by
  simp [comparisonBlockDiagonal]

@[simp]
theorem comparisonBlockDiagonal_apply_left_right (X Y : Hessian n) (i j : Fin n) :
    comparisonBlockDiagonal X Y (Sum.inl i) (Sum.inr j) = 0 := by
  simp [comparisonBlockDiagonal]

@[simp]
theorem comparisonBlockDiagonal_apply_right_left (X Y : Hessian n) (i j : Fin n) :
    comparisonBlockDiagonal X Y (Sum.inr i) (Sum.inl j) = 0 := by
  simp [comparisonBlockDiagonal]

@[simp]
theorem comparisonBlockDiagonal_apply_right_right (X Y : Hessian n) (i j : Fin n) :
    comparisonBlockDiagonal X Y (Sum.inr i) (Sum.inr j) = -Y i j := by
  simp [comparisonBlockDiagonal]

@[simp]
theorem blockDiagonalIdentity_apply_left_left (i j : Fin n) :
    blockDiagonalIdentity n (Sum.inl i) (Sum.inl j) = (1 : Hessian n) i j := by
  simp [blockDiagonalIdentity]

@[simp]
theorem blockDiagonalIdentity_apply_right_right (i j : Fin n) :
    blockDiagonalIdentity n (Sum.inr i) (Sum.inr j) = (1 : Hessian n) i j := by
  simp [blockDiagonalIdentity]

@[simp]
theorem comparisonPenaltyBlock_apply_left_left (α : Real) (i j : Fin n) :
    comparisonPenaltyBlock (n := n) α (Sum.inl i) (Sum.inl j) =
      (α • (1 : Hessian n)) i j := by
  simp [comparisonPenaltyBlock]

@[simp]
theorem comparisonPenaltyBlock_apply_left_right (α : Real) (i j : Fin n) :
    comparisonPenaltyBlock (n := n) α (Sum.inl i) (Sum.inr j) =
      ((-α) • (1 : Hessian n)) i j := by
  simp [comparisonPenaltyBlock]

@[simp]
theorem comparisonPenaltyBlock_apply_right_left (α : Real) (i j : Fin n) :
    comparisonPenaltyBlock (n := n) α (Sum.inr i) (Sum.inl j) =
      ((-α) • (1 : Hessian n)) i j := by
  simp [comparisonPenaltyBlock]

@[simp]
theorem comparisonPenaltyBlock_apply_right_right (α : Real) (i j : Fin n) :
    comparisonPenaltyBlock (n := n) α (Sum.inr i) (Sum.inr j) =
      (α • (1 : Hessian n)) i j := by
  simp [comparisonPenaltyBlock]

end ViscositySolns
