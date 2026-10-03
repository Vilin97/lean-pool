/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProductCoordinates.RegularizedConvolution

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Product-coordinate consequences of the semiconvex matrix lemma (MatrixLemmaBounds)

Part of the product-coordinate development connecting the semiconvex matrix
conclusion on the coordinate space `R^(n+n)` to the block-matrix notation on
`R^n × R^n`. Split from `ProductCoordinates.lean`; see the umbrella module
docstring.
-/

@[expose] public noncomputable section

open scoped MatrixOrder
open Filter

namespace ViscositySolns

variable {n : Nat}

/--
The quadratic objective on `R^(n+n)` associated to a reindexed block Hessian
is the pullback of the corresponding block-coordinate quadratic objective.

In quantified mathematical form, for every `z : R^(n+n)`,

`F(z_block) - (1 / 2) ⟪B z_block, z_block⟫`

equals

`F(z_block) - (1 / 2) ⟪B_point z, z⟫`,

where `z_block` is the image of `z` in `R^n × R^n` and `B_point` is the
matrix `B` written in `R^(n+n)` coordinates.
-/
theorem semiconvexQuadraticObjective_blockFunctionToPointFunction
    (F : BlockPoint n -> Real) (B : BlockHessian n) (z : Point (n + n)) :
    semiconvexQuadraticObjective
        (blockFunctionToPointFunction (n := n) F)
        (blockHessianToPointHessian B) z =
      F (pointSumEquivBlockPoint n z) -
        blockQuadraticModel B (pointSumEquivBlockPoint n z) := by
  have hquad :
      quadraticModel 0 0 0 (blockHessianToPointHessian B) z =
        blockQuadraticModel B (pointSumEquivBlockPoint n z) := by
    have h :=
      blockQuadraticModel_pointHessianToBlockHessian_pointSumEquivBlockPoint
        (n := n) (blockHessianToPointHessian B) z
    simpa using h.symm
  simp [blockFunctionToPointFunction, semiconvexQuadraticObjective, hquad]

/--
A global maximum of the block-coordinate quadratic objective pulls back to a
global maximum of the corresponding objective on `R^(n+n)`.
-/
theorem isMaxOn_semiconvexQuadraticObjective_blockFunctionToPointFunction
    {F : BlockPoint n -> Real} {B : BlockHessian n}
    (hmax : IsMaxOn
      (fun q : BlockPoint n => F q - blockQuadraticModel B q) Set.univ 0) :
    IsMaxOn
      (semiconvexQuadraticObjective
        (blockFunctionToPointFunction (n := n) F)
        (blockHessianToPointHessian B))
      Set.univ 0 := by
  intro z _hz
  have hblock :
      F (pointSumEquivBlockPoint n z) -
          blockQuadraticModel B (pointSumEquivBlockPoint n z) <=
        F 0 - blockQuadraticModel B 0 :=
    hmax trivial
  simpa [semiconvexQuadraticObjective_blockFunctionToPointFunction] using hblock

/--
The matrix part of a semiconvex matrix conclusion transported from
`R^(n+n)` to `R^n × R^n`.

In quantified mathematical form, suppose that
`SemiconvexMatrixConclusion lambda f B` holds on `R^(n+n)`. Then there
exists a matrix `Z` on `R^(n+n)` such that
`(0, Z) ∈ \overline J^{2,+}_{R^(n+n)} f(0)`, and after identifying
`R^(n+n)` with `R^n × R^n`, the reindexed matrix `Z_block` satisfies

`-lambda [I 0; 0 I] ≤ Z_block ≤ B_block`.
-/
theorem SemiconvexMatrixConclusion.exists_reindexed_block_bounds
    {lambda : Real} {f : Point (n + n) -> Real} {B : Hessian (n + n)}
    (h : SemiconvexMatrixConclusion (n := n + n) lambda f B) :
    ∃ Z : Hessian (n + n),
      ({ gradient := 0, hessian := Z } : Jet (n + n)) ∈
          ClosedSuperjet Set.univ f 0 ∧
        (-lambda) • blockDiagonalIdentity n <= pointHessianToBlockHessian (n := n) Z ∧
        pointHessianToBlockHessian (n := n) Z <=
          pointHessianToBlockHessian (n := n) B := by
  rcases h with ⟨Z, hZ, hlower, hupper⟩
  rcases pointHessianToBlockHessian_bounds_of_scalar_identity_bounds
      (n := n) hlower hupper with ⟨hlowerBlock, hupperBlock⟩
  exact ⟨Z, hZ, hlowerBlock, hupperBlock⟩

/--
Apply the semiconvex matrix lemma on `R^(n+n)` and immediately transport its
matrix inequalities to block coordinates on `R^n × R^n`.

In quantified mathematical form, if the semiconvex matrix lemma holds in
dimension `n + n`, if `0 ≤ lambda`, if `f : R^(n+n) -> R` is continuous and
semiconvex with constant `lambda`, and if
`B` is Hermitian and
`ξ ↦ f ξ - (1 / 2) * ⟪B ξ, ξ⟫` has a maximum at `0`, then there exists a
matrix `Z` such that `(0, Z)` belongs to the closed superjet of `f` at `0`
and

`-lambda [I 0; 0 I] ≤ Z_block ≤ B_block`.
-/
theorem SemiconvexMatrixLemmaOn.exists_reindexed_block_bounds
    {lambda : Real}
    (hlemma : SemiconvexMatrixLemmaOn (n := n + n) lambda)
    (hlambda : 0 <= lambda) {f : Point (n + n) -> Real}
    (hf : Continuous f) {B : Hessian (n + n)}
    (hB : B.IsHermitian)
    (hsemi : CoordinateSemiconvexOn lambda Set.univ f)
    (hmax : IsMaxOn (semiconvexQuadraticObjective f B) Set.univ 0) :
    ∃ Z : Hessian (n + n),
      ({ gradient := 0, hessian := Z } : Jet (n + n)) ∈
          ClosedSuperjet Set.univ f 0 ∧
        (-lambda) • blockDiagonalIdentity n <= pointHessianToBlockHessian (n := n) Z ∧
        pointHessianToBlockHessian (n := n) Z <=
          pointHessianToBlockHessian (n := n) B := by
  exact (hlemma.apply hlambda hf hB hsemi hmax).exists_reindexed_block_bounds

/--
Apply the semiconvex matrix lemma to a function on `R^n × R^n`, after writing
that function in `R^(n+n)` coordinates.

In quantified mathematical form, suppose that the semiconvex matrix lemma
holds in dimension `n + n`, that `0 ≤ lambda`, that
`F : R^n × R^n -> R` is continuous and satisfies the semiconvexity inequality
with constant `lambda`, that `B` is Hermitian, and that

`q ↦ F q - (1 / 2) ⟪B q, q⟫`

has a maximum at `0`. Then there exists a matrix `Z` on `R^(n+n)` such that
`(0, Z)` belongs to the closed superjet at `0` of the function
`z ↦ F(z_1, z_2)`, and after writing `Z` in `R^n × R^n` coordinates,

`-lambda [I 0; 0 I] ≤ Z_block ≤ B`.
-/
theorem SemiconvexMatrixLemmaOn.exists_reindexed_block_bounds_of_block
    {lambda : Real}
    (hlemma : SemiconvexMatrixLemmaOn (n := n + n) lambda)
    (hlambda : 0 <= lambda) {F : BlockPoint n -> Real}
    (hF : Continuous F) {B : BlockHessian n}
    (hB : B.IsHermitian)
    (hsemi : BlockCoordinateSemiconvexOn lambda Set.univ F)
    (hmax : IsMaxOn
      (fun q : BlockPoint n => F q - blockQuadraticModel B q) Set.univ 0) :
    ∃ Z : Hessian (n + n),
      ({ gradient := 0, hessian := Z } : Jet (n + n)) ∈
          ClosedSuperjet Set.univ (blockFunctionToPointFunction (n := n) F) 0 ∧
        (-lambda) • blockDiagonalIdentity n <= pointHessianToBlockHessian (n := n) Z ∧
        pointHessianToBlockHessian (n := n) Z <= B := by
  rcases hlemma.exists_reindexed_block_bounds
      (n := n) hlambda (Continuous.blockFunctionToPointFunction (n := n) hF)
      (Matrix.IsHermitian.blockHessianToPointHessian (n := n) hB)
      hsemi.coordinateSemiconvexOn_blockFunctionToPointFunction
      (isMaxOn_semiconvexQuadraticObjective_blockFunctionToPointFunction hmax) with
    ⟨Z, hZ, hlower, hupper⟩
  exact ⟨Z, hZ, hlower, by simpa using hupper⟩

/--
Apply the semiconvex matrix lemma to the compact regularized doubled
convolution after translating the doubled maximum point to the origin.

In quantified mathematical form, assume:

* `K` and `L` are nonempty compact subsets of `R^n`;
* `u` is upper semicontinuous on `{x0 + x | x ∈ K}`;
* `v` is lower semicontinuous on `{y0 + y | y ∈ L}`;
* `(x0, y0)` is a maximum point on the translated product set of
  `u(x) - v(y)` minus the quadratic polynomial with Hessian `A`;
* `A` is symmetric, `ε > 0`, `A ≤ μ [I 0; 0 I]`, and
  `0 ≤ ε⁻¹ + μ`.

Then the semiconvex matrix lemma applied to

`ξ ↦ regularizedDoubledConvolution (ε⁻¹ + μ) K L u_norm v_norm ξ`

produces a closed superjet at `0` whose reindexed Hessian lies between
`-(ε⁻¹ + μ)[I 0; 0 I]` and `A + ε A^2`.
-/
theorem SemiconvexMatrixLemmaOn.regularizedDoubledConvolution_block_bounds
    {epsilon mu : Real}
    (hlemma : SemiconvexMatrixLemmaOn (n := n + n) (epsilon⁻¹ + mu))
    (hlambda : 0 <= epsilon⁻¹ + mu)
    {K L : Set (Point n)} {u v : Point n -> Real}
    {x0 y0 : Point n} {φ0 : Real} {P : BlockPoint n} {A : BlockHessian n}
    (hHerm : A.IsHermitian) (hepsilon : 0 < epsilon)
    (hA : A <= mu • blockDiagonalIdentity n)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u ((fun x : Point n => x0 + x) '' K))
    (hv : LowerSemicontinuousOn v ((fun y : Point n => y0 + y) '' L))
    (h0K : (0 : Point n) ∈ K) (h0L : (0 : Point n) ∈ L)
    (hmax : IsMaxOn
      (fun q : DoubledPoint n =>
        u q.1 - v q.2 - doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A q)
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
      (x0, y0)) :
    ∃ Z : Hessian (n + n),
      ({ gradient := 0, hessian := Z } : Jet (n + n)) ∈
          ClosedSuperjet Set.univ
            (blockFunctionToPointFunction (n := n)
              (regularizedDoubledConvolution (n := n) (epsilon⁻¹ + mu) K L
                (normalizedLeftOfBlockGradient (n := n) u x0 P)
                (normalizedRightOfBlockGradient (n := n) v y0 P))) 0 ∧
        (-(epsilon⁻¹ + mu)) • blockDiagonalIdentity n <=
          pointHessianToBlockHessian (n := n) Z ∧
        pointHessianToBlockHessian (n := n) Z <= A + epsilon • (A * A) := by
  let uNorm : Point n -> Real := normalizedLeftOfBlockGradient (n := n) u x0 P
  let vNorm : Point n -> Real := normalizedRightOfBlockGradient (n := n) v y0 P
  let lambda : Real := epsilon⁻¹ + mu
  let B : BlockHessian n := A + epsilon • (A * A)
  have huNorm : UpperSemicontinuousOn uNorm K :=
    upperSemicontinuousOn_normalizedLeftOfBlockGradient (n := n) hu
  have hvNorm : LowerSemicontinuousOn vNorm L :=
    lowerSemicontinuousOn_normalizedRightOfBlockGradient (n := n) hv
  have hFcont :
      Continuous (regularizedDoubledConvolution (n := n) lambda K L uNorm vNorm) :=
    continuous_regularizedDoubledConvolution_of_isCompact
      (n := n) hKne hLne hKcompact hLcompact huNorm hvNorm
  have hFsemi :
      BlockCoordinateSemiconvexOn lambda Set.univ
        (regularizedDoubledConvolution (n := n) lambda K L uNorm vNorm) :=
    blockCoordinateSemiconvexOn_regularizedDoubledConvolution_of_isCompact
      (n := n) hKne hLne hKcompact hLcompact huNorm hvNorm
  have hAAHerm : (A * A).IsHermitian := by
    have htranspose : A.transpose = A := by
      ext i j
      simpa using hHerm.apply i j
    have h := Matrix.isHermitian_mul_conjTranspose_self A
    simpa [htranspose] using h
  have hBHerm : B.IsHermitian :=
    hHerm.add (hAAHerm.smul (IsSelfAdjoint.all epsilon))
  have hmaxReg :
      IsMaxOn
        (fun ξ : BlockPoint n =>
          regularizedDoubledConvolution (n := n) lambda K L uNorm vNorm ξ -
            blockQuadraticModel B ξ)
        Set.univ 0 := by
    exact
      isMaxOn_regularizedDoubledConvolution_normalized_sub_cilQuadratic_of_translated_mem_zero
        (n := n) (epsilon := epsilon) (mu := mu) (K := K) (L := L)
        (u := u) (v := v) (x0 := x0) (y0 := y0) (φ0 := φ0) (P := P) (A := A)
        hHerm hepsilon hA hKne hLne hKcompact hLcompact hu hv h0K h0L hmax
  simpa [uNorm, vNorm, lambda, B] using
    hlemma.exists_reindexed_block_bounds_of_block
      (n := n) hlambda hFcont hBHerm hFsemi hmaxReg

end ViscositySolns
