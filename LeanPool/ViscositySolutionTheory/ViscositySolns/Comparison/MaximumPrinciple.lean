/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.MatrixInequalities
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Semijets.Closure

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Declarations for the finite-dimensional maximum principle

This file contains declarations used to state the maximum principle for
semicontinuous functions. It does not assert the maximum principle as a theorem.

The intended mathematical statement is: if
`(x, y)` is a local maximum point of
`(x', y') ↦ u x' - v y' - φ (x', y')` on `C × D`, then there exist matrices
`X` and `Y` such that the jet with gradient `p` and Hessian `X` belongs to the
closed superjet of `u` at `x`, the jet with gradient `q` and Hessian `Y`
belongs to the closed subjet of `v` at `y`, and the matrices `X` and `Y`
satisfy the matrix inequality supplied by the maximum principle.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The statement that `(x, y) ∈ C × D` is a local maximum point of
`(x', y') ↦ u x' - v y' - φ (x', y')` relative to `C × D`.
-/
def HasDoubledLocalMaximumOn (C D : Set (Point n)) (u v : Point n -> Real)
    (φ : DoubledPoint n -> Real) (x y : Point n) : Prop :=
  (x, y) ∈ C ×ˢ D ∧
    IsLocalMaxOn (fun q : DoubledPoint n => u q.1 - v q.2 - φ q) (C ×ˢ D) (x, y)

/--
The block matrix relation

`lower ≤ [X 0; 0 -Y] ≤ upper`.

This is the matrix part of the two-function maximum principle. In the theorem
from the paper, `lower` is `-((1 / ε) + ‖A‖) I`, `upper` is `A + ε A^2`, and
`A` is the Hessian of the twice continuously differentiable test function at
the local maximum point.
-/
def BlockMatrixRelation (lower upper : BlockHessian n) :
    Hessian n -> Hessian n -> Prop :=
  fun X Y => lower <= comparisonBlockDiagonal X Y ∧ comparisonBlockDiagonal X Y <= upper

/--
The matrix relation appearing in CIL Theorem 3.2.

In standard mathematical terms, if `A` is the Hessian of the test function at
the doubled maximum point, `ε > 0`, and `μ` is the matrix norm bound used in
the theorem, then the conclusion is

`-((ε⁻¹) + μ) I ≤ [X 0; 0 -Y] ≤ A + ε A^2`.
-/
def CILMatrixRelation (epsilon matrixNormBound : Real) (A : BlockHessian n) :
    Hessian n -> Hessian n -> Prop :=
  BlockMatrixRelation (n := n)
    (-(epsilon⁻¹ + matrixNormBound) • blockDiagonalIdentity n)
    (A + epsilon • (A * A))

/--
Subtracting a constant from the first function preserves doubled local maximum
points.

In quantified mathematical form, for every real number `δ`, if `(x, y)` is a
local maximum point on `C × D` of
`(x', y') ↦ u x' - v y' - φ (x', y')`, then `(x, y)` is a local maximum point
on `C × D` of
`(x', y') ↦ (u x' - δ) - v y' - φ (x', y')`.
-/
theorem HasDoubledLocalMaximumOn.sub_const_left
    {C D : Set (Point n)} {u v : Point n -> Real}
    {φ : DoubledPoint n -> Real} {x y : Point n} {δ : Real}
    (h : HasDoubledLocalMaximumOn C D u v φ x y) :
    HasDoubledLocalMaximumOn C D (fun z => u z - δ) v φ x y := by
  rcases h with ⟨hxy, hmax⟩
  refine ⟨hxy, ?_⟩
  have hmono : Monotone (fun r : Real => r - δ) :=
    fun _ _ hab => sub_le_sub_right hab δ
  have hshift := hmax.comp_mono hmono
  simpa [Function.comp_def, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift

/--
Subtracting a constant from the first function does not change doubled local
maximum points.

In quantified mathematical form, for every real number `δ`, `(x, y)` is a
local maximum point on `C × D` of
`(x', y') ↦ (u x' - δ) - v y' - φ (x', y')` if and only if it is a local
maximum point on `C × D` of
`(x', y') ↦ u x' - v y' - φ (x', y')`.
-/
theorem hasDoubledLocalMaximumOn_sub_const_left_iff
    {C D : Set (Point n)} {u v : Point n -> Real}
    {φ : DoubledPoint n -> Real} {x y : Point n} {δ : Real} :
    HasDoubledLocalMaximumOn C D (fun z => u z - δ) v φ x y ↔
      HasDoubledLocalMaximumOn C D u v φ x y := by
  constructor
  · intro h
    have h' :=
      HasDoubledLocalMaximumOn.sub_const_left
        (u := fun z => u z - δ) (v := v) (φ := φ) (δ := -δ) h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
  · intro h
    exact h.sub_const_left

/--
The conclusion produced by the maximum principle at a fixed point `(x, y)`.

The fields assert the existence of matrices `X` and `Y` such that:

* `(p, X)` belongs to the closed superjet of `u` at `x` relative to `C`;
* `(q, Y)` belongs to the closed subjet of `v` at `y` relative to `D`;
* `X` and `Y` satisfy the matrix relation specified by the caller.
-/
structure ClosedSemijetPairWithMatrixRelation
    (C D : Set (Point n)) (u v : Point n -> Real) (x y p q : Point n)
    (matrixRel : Hessian n -> Hessian n -> Prop) where
  /-- The Hessian in the closed superjet of the first function. -/
  X : Hessian n
  /-- The Hessian in the closed subjet of the second function. -/
  Y : Hessian n
  superjet_mem : ({ gradient := p, hessian := X } : Jet n) ∈ ClosedSuperjet C u x
  subjet_mem : ({ gradient := q, hessian := Y } : Jet n) ∈ ClosedSubjet D v y
  matrix_relation : matrixRel X Y

/--
Subtracting a constant from the first function preserves a closed-semijet
pair with a fixed matrix relation.

In quantified mathematical form, for every real number `δ`, if there exist
matrices `X` and `Y` such that `(p, X) ∈ \bar J^{2,+}_C u(x)`,
`(q, Y) ∈ \bar J^{2,-}_D v(y)`, and `matrixRel X Y`, then the same matrices
satisfy `(p, X) ∈ \bar J^{2,+}_C (u - δ)(x)`,
`(q, Y) ∈ \bar J^{2,-}_D v(y)`, and `matrixRel X Y`.
-/
def ClosedSemijetPairWithMatrixRelation.subConstLeft
    {C D : Set (Point n)} {u v : Point n -> Real} {x y p q : Point n}
    {matrixRel : Hessian n -> Hessian n -> Prop} {δ : Real}
    (h : ClosedSemijetPairWithMatrixRelation C D u v x y p q matrixRel) :
    ClosedSemijetPairWithMatrixRelation C D (fun z => u z - δ) v x y p q matrixRel where
  X := h.X
  Y := h.Y
  superjet_mem := closedSuperjet_sub_const_of_closedSuperjet h.superjet_mem
  subjet_mem := h.subjet_mem
  matrix_relation := h.matrix_relation

/--
A precise predicate for the conclusion of the maximum principle from a
doubled local maximum.

This is a declaration, not a proved theorem. A future theorem will prove this
predicate under the hypotheses of the finite-dimensional maximum principle.
-/
def MaximumPrincipleConclusion
    (C D : Set (Point n)) (u v : Point n -> Real) (x y p q : Point n)
    (matrixRel : Hessian n -> Hessian n -> Prop) : Prop :=
  Nonempty (ClosedSemijetPairWithMatrixRelation C D u v x y p q matrixRel)

/--
The two-function maximum-principle theorem-shaped proposition.

In quantified mathematical form, this says: for every `x ∈ C` and `y ∈ D`, if
`(x, y)` is a local maximum point, relative to `C × D`, of

`(x', y') ↦ u x' - v y' - φ (x', y')`,

then there exist symmetric matrices `X` and `Y` such that

`(p x y, X) ∈ \bar J^{2,+}_C u(x)`,

`(q x y, Y) ∈ \bar J^{2,-}_D v(y)`,

and `matrixRel x y X Y`.

For an actual `C^2` test function `φ`, the intended choices are
`p x y = D_x φ(x, y)`, `q x y = -D_y φ(x, y)`, and `matrixRel x y` is the
block inequality obtained from `D^2 φ(x, y)`.
-/
def DoubledMaximumPrincipleOn
    (C D : Set (Point n)) (u v : Point n -> Real)
    (φ : DoubledPoint n -> Real) (p q : DoubledPoint n -> Point n)
    (matrixRel : DoubledPoint n -> Hessian n -> Hessian n -> Prop) : Prop :=
  ∀ x : Point n, ∀ y : Point n,
    HasDoubledLocalMaximumOn C D u v φ x y ->
      MaximumPrincipleConclusion C D u v x y (p (x, y)) (q (x, y))
        (matrixRel (x, y))

/--
The two-function maximum-principle theorem-shaped proposition with the matrix
bounds from CIL Theorem 3.2.

In quantified mathematical form, this says: for every `ε > 0`, every local
maximum point `(x, y)` of

`(x', y') ↦ u x' - v y' - φ (x', y')`

has closed semijets with first-order components `p (x, y)` and `q (x, y)`,
and with matrices `X` and `Y` satisfying

`-((ε⁻¹) + μ(x, y)) I ≤ [X 0; 0 -Y] ≤ A(x, y) + ε A(x, y)^2`.

Here `A(x, y)` is the Hessian matrix of `φ` at `(x, y)` in block form, and
`μ(x, y)` is the corresponding matrix norm bound used in the CIL statement.
-/
def CILDoubledMaximumPrincipleOn
    (C D : Set (Point n)) (u v : Point n -> Real)
    (φ : DoubledPoint n -> Real) (p q : DoubledPoint n -> Point n)
    (A : DoubledPoint n -> BlockHessian n) (matrixNormBound : DoubledPoint n -> Real) :
    Prop :=
  ∀ epsilon : Real, 0 < epsilon ->
    DoubledMaximumPrincipleOn C D u v φ p q
      (fun z : DoubledPoint n => CILMatrixRelation epsilon (matrixNormBound z) (A z))

/--
Subtracting a constant from the first function preserves the conclusion of the
maximum principle.

In quantified mathematical form, for every real number `δ`, if the maximum
principle conclusion holds for `u` and `v` at `(x, y)`, with gradients `p`,
`q`, and matrix relation `matrixRel`, then the same conclusion holds for
`x ↦ u x - δ` and `v`.
-/
theorem MaximumPrincipleConclusion.sub_const_left
    {C D : Set (Point n)} {u v : Point n -> Real} {x y p q : Point n}
    {matrixRel : Hessian n -> Hessian n -> Prop} {δ : Real}
    (h : MaximumPrincipleConclusion C D u v x y p q matrixRel) :
    MaximumPrincipleConclusion C D (fun z => u z - δ) v x y p q matrixRel := by
  rcases h with ⟨data⟩
  exact ⟨data.subConstLeft⟩

/--
Subtracting a constant from the first function preserves the two-function
maximum-principle theorem-shaped proposition.

In quantified mathematical form, for every real number `δ`, suppose that for
every local maximum point of
`(x', y') ↦ u x' - v y' - φ (x', y')` on `C × D`, the maximum-principle
conclusion holds. Then for every local maximum point of
`(x', y') ↦ (u x' - δ) - v y' - φ (x', y')` on `C × D`, the corresponding
maximum-principle conclusion holds for `x ↦ u x - δ` and `v`.
-/
theorem DoubledMaximumPrincipleOn.sub_const_left
    {C D : Set (Point n)} {u v : Point n -> Real}
    {φ : DoubledPoint n -> Real} {p q : DoubledPoint n -> Point n}
    {matrixRel : DoubledPoint n -> Hessian n -> Hessian n -> Prop} {δ : Real}
    (hMP : DoubledMaximumPrincipleOn C D u v φ p q matrixRel) :
    DoubledMaximumPrincipleOn C D (fun z => u z - δ) v φ p q matrixRel := by
  intro x y hlocal
  have hlocal_unshifted :
      HasDoubledLocalMaximumOn C D u v φ x y :=
    (hasDoubledLocalMaximumOn_sub_const_left_iff
      (C := C) (D := D) (u := u) (v := v) (φ := φ) (x := x) (y := y)
      (δ := δ)).1 hlocal
  exact (hMP x y hlocal_unshifted).sub_const_left

/--
Unpack `MaximumPrincipleConclusion` into matrices `X` and `Y`.
-/
theorem MaximumPrincipleConclusion.exists_matrices
    {C D : Set (Point n)} {u v : Point n -> Real} {x y p q : Point n}
    {matrixRel : Hessian n -> Hessian n -> Prop}
    (h : MaximumPrincipleConclusion C D u v x y p q matrixRel) :
    ∃ X Y : Hessian n,
      ({ gradient := p, hessian := X } : Jet n) ∈ ClosedSuperjet C u x ∧
      ({ gradient := q, hessian := Y } : Jet n) ∈ ClosedSubjet D v y ∧
      matrixRel X Y := by
  rcases h with ⟨data⟩
  exact ⟨data.X, data.Y, data.superjet_mem, data.subjet_mem, data.matrix_relation⟩

/--
The matrix relation in the quadratic-penalty case:
`X` and `Y` satisfy the block inequalities
`-(3 * α) [I 0; 0 I] ≤ [X 0; 0 -Y] ≤ 3 [α I -α I; -α I α I]`.
-/
def QuadraticPenaltyMatrixRelation (α : Real) (x y : Point n) :
    Hessian n -> Hessian n -> Prop :=
  fun X Y => IshiiMatrixRelation α x y X Y

/--
The CIL matrix relation specializes to the Ishii matrix relation for the
coordinate quadratic penalty.

In standard mathematical terms, for
`A = [α I -α I; -α I α I]`, the identities `A^2 = 2α A` and
`A + α⁻¹ A^2 = 3A` convert

`-((α⁻¹)⁻¹ + 2α) I ≤ [X 0; 0 -Y] ≤ A + α⁻¹ A^2`

into

`-3α I ≤ [X 0; 0 -Y] ≤ 3A`.
-/
theorem CILMatrixRelation.quadraticPenalty_of_pos
    {α : Real} (hα : 0 < α) {x y : Point n} {X Y : Hessian n}
    (h : CILMatrixRelation (n := n) α⁻¹ (2 * α)
      (comparisonPenaltyBlock (n := n) α) X Y) :
    QuadraticPenaltyMatrixRelation α x y X Y := by
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hlower :
      (-(2 * α) + -α) • blockDiagonalIdentity n = ishiiLowerBlock (n := n) α := by
    ext i j
    cases i <;> cases j <;> simp [ishiiLowerBlock, blockDiagonalIdentity] <;> ring_nf
  have hupper :
      comparisonPenaltyBlock (n := n) α +
          α⁻¹ • (comparisonPenaltyBlock (n := n) α * comparisonPenaltyBlock (n := n) α) =
        ishiiUpperBlock (n := n) α := by
    simpa [ishiiUpperBlock] using
      comparisonPenaltyBlock_add_inv_smul_mul_self (n := n) (α := α) hα_ne
  rcases h with ⟨hlo, hup⟩
  exact ⟨by simpa [CILMatrixRelation, hlower] using hlo,
    by simpa [CILMatrixRelation, hupper] using hup⟩

/--
The conclusion of Ishii's lemma for the quadratic penalty
`(α / 2) * ∑ i, (x i - y i)^2`, expressed through closed semijets.
-/
def QuadraticPenaltyIshiiConclusion
    (C D : Set (Point n)) (u v : Point n -> Real) (α : Real) (x y : Point n) :
    Prop :=
  MaximumPrincipleConclusion C D u v x y
    (quadraticPenaltyGradientLeft α x y)
    (-quadraticPenaltyGradientRight α x y)
    (QuadraticPenaltyMatrixRelation α x y)

/--
Subtracting a constant from the first function preserves the quadratic-penalty
conclusion of Ishii's lemma.

In quantified mathematical form, for every real number `δ`, if the
quadratic-penalty conclusion holds for `u` and `v` at `(x, y)` with parameter
`α`, then the same conclusion holds for `x ↦ u x - δ` and `v`.
-/
theorem QuadraticPenaltyIshiiConclusion.sub_const_left
    {C D : Set (Point n)} {u v : Point n -> Real} {α : Real} {x y : Point n}
    {δ : Real}
    (h : QuadraticPenaltyIshiiConclusion C D u v α x y) :
    QuadraticPenaltyIshiiConclusion C D (fun z => u z - δ) v α x y :=
  MaximumPrincipleConclusion.sub_const_left h

end ViscositySolns
