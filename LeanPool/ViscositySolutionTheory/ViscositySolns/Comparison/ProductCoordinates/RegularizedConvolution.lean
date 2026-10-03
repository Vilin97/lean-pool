/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProductCoordinates.Normalization

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Product-coordinate consequences of the semiconvex matrix lemma (RegularizedConvolution)

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
The regularized two-function expression used before applying the semiconvex
matrix lemma.

In standard mathematical notation this is

`(ξ, η) ↦ sup { u(x) - (lambda / 2) |x - ξ|^2 | x ∈ K }
          - inf { v(y) + (lambda / 2) |y - η|^2 | y ∈ L }`.
-/
def regularizedDoubledConvolution (lambda : Real) (K L : Set (Point n))
    (u v : Point n -> Real) : BlockPoint n -> Real :=
  fun q => compactSupConvolution lambda K u (blockPointLeft q) -
    compactInfConvolution lambda L v (blockPointRight q)

/--
The regularized two-function expression is a sum of two compact
sup-convolutions.
-/
theorem regularizedDoubledConvolution_eq_sup_add_sup_neg
    {lambda : Real} {K L : Set (Point n)} {u v : Point n -> Real} :
    regularizedDoubledConvolution (n := n) lambda K L u v =
      (fun q : BlockPoint n =>
        compactSupConvolution lambda K u (blockPointLeft q) +
          compactSupConvolution lambda L (fun x : Point n => -v x) (blockPointRight q)) := by
  funext q
  simp [regularizedDoubledConvolution, compactInfConvolution]

/--
The regularized two-function expression is semiconvex on `R^n × R^n`.

In standard mathematical terms, if `K` and `L` are nonempty compact sets,
`u` is upper semicontinuous on `K`, and `v` is lower semicontinuous on `L`,
then the function

`(ξ, η) ↦ sup_K (u(x) - (lambda / 2)|x - ξ|^2)
          - inf_L (v(y) + (lambda / 2)|y - η|^2)`

satisfies the semiconvexity inequality with constant `lambda`.
-/
theorem blockCoordinateSemiconvexOn_regularizedDoubledConvolution_of_isCompact
    {lambda : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L) :
    BlockCoordinateSemiconvexOn lambda Set.univ
      (regularizedDoubledConvolution (n := n) lambda K L u v) := by
  have huSemi :
      CoordinateSemiconvexOn lambda Set.univ
        (fun ξ : Point n => compactSupConvolution lambda K u ξ) :=
    coordinateSemiconvexOn_compactSupConvolution_of_isCompact hKne hKcompact hu
  have hvSemi :
      CoordinateSemiconvexOn lambda Set.univ
        (fun η : Point n => compactSupConvolution lambda L (fun x : Point n => -v x) η) :=
    coordinateSemiconvexOn_compactSupConvolution_of_isCompact hLne hLcompact
      (lowerSemicontinuousOn_neg_to_upperSemicontinuousOn hv)
  rw [regularizedDoubledConvolution_eq_sup_add_sup_neg]
  exact BlockCoordinateSemiconvexOn.left_right_add huSemi hvSemi

/--
The regularized two-function expression is continuous on `R^n × R^n`.
-/
theorem continuous_regularizedDoubledConvolution_of_isCompact
    {lambda : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L) :
    Continuous (regularizedDoubledConvolution (n := n) lambda K L u v) :=
  (blockCoordinateSemiconvexOn_regularizedDoubledConvolution_of_isCompact
    hKne hLne hKcompact hLcompact hu hv).continuous_univ

/--
Closed semijets and matrix bounds for a regularized doubled convolution from a
selected block diagonal Hessian.

In quantified mathematical form, let `K` and `L` be nonempty compact subsets
of `R^n`, let `u` be upper semicontinuous on `K`, and let `v` be lower
semicontinuous on `L`. Suppose `(0, Z)` belongs to the closed superjet at
`(0, 0)` of

`(ξ, η) ↦ compactSupConvolution lambda K u ξ
  - compactInfConvolution lambda L v η`,

and suppose that the block-coordinate form of `Z` is `[X 0; 0 -Y]`. If this
block-coordinate matrix lies between `lower` and `upper` in the Loewner order,
then `(0, X)` belongs to the closed superjet at `0` of the compact
sup-convolution of `u`, `(0, Y)` belongs to the closed subjet at `0` of the
compact inf-convolution of `v`, and `lower ≤ [X 0; 0 -Y] ≤ upper`.
-/
theorem closedSemijets_and_blockBounds_of_regularizedDoubledConvolution
    {lambda : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L)
    {Z : Hessian (n + n)} {X Y : Hessian n} {lower upper : BlockHessian n}
    (hdiag : pointHessianToBlockHessian (n := n) Z = comparisonBlockDiagonal X Y)
    (hlower : lower <= pointHessianToBlockHessian (n := n) Z)
    (hupper : pointHessianToBlockHessian (n := n) Z <= upper)
    (hJ : ({ gradient := 0, hessian := Z } : Jet (n + n)) ∈ ClosedSuperjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (regularizedDoubledConvolution (n := n) lambda K L u v)) 0) :
    ({ gradient := 0, hessian := X } : Jet n) ∈
        ClosedSuperjet Set.univ (fun ξ : Point n => compactSupConvolution lambda K u ξ) 0 ∧
      ({ gradient := 0, hessian := Y } : Jet n) ∈
        ClosedSubjet Set.univ (fun η : Point n => compactInfConvolution lambda L v η) 0 ∧
        lower <= comparisonBlockDiagonal X Y ∧ comparisonBlockDiagonal X Y <= upper := by
  let G : Point n -> Real := fun ξ => compactSupConvolution lambda K u ξ
  let H : Point n -> Real := fun η => compactInfConvolution lambda L v η
  have hG : Continuous G :=
    continuous_compactSupConvolution_of_isCompact hKne hKcompact hu
  have hH : Continuous H :=
    continuous_compactInfConvolution_of_isCompact hLne hLcompact hv
  have hJ' : ({ gradient := 0, hessian := Z } : Jet (n + n)) ∈ ClosedSuperjet Set.univ
      (blockFunctionToPointFunction (n := n)
        (fun q : BlockPoint n => G (blockPointLeft q) - H (blockPointRight q))) 0 := by
    exact hJ
  exact
    closedSemijets_and_blockBounds_of_blockDiagonal_closedSuperjet
      (n := n) (G := G) (H := H) hG hH hdiag hlower hupper hJ'

/--
If `x` is a maximum point for the sup-convolution kernel on `K`, and `y` is
a minimum point for the inf-convolution kernel on `L`, then the regularized
two-function value at `(ξ, η)` is the difference between the two selected
kernel values.

In quantified mathematical form, if `x ∈ K`, `y ∈ L`,

`u(z) - (lambda / 2) * |z - ξ|^2 ≤
 u(x) - (lambda / 2) * |x - ξ|^2`

for every `z ∈ K`, and

`v(y) + (lambda / 2) * |y - η|^2 ≤
 v(z) + (lambda / 2) * |z - η|^2`

for every `z ∈ L`, then

`regularizedDoubledConvolution lambda K L u v (ξ, η) =
 supConvolutionKernel lambda u ξ x - infConvolutionKernel lambda v η y`.
-/
theorem regularizedDoubledConvolution_eq_kernels_of_isMaxOn_isMinOn
    {lambda : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    {ξ η x y : Point n}
    (hx : x ∈ K)
    (hy : y ∈ L)
    (hmax : IsMaxOn (fun z : Point n => supConvolutionKernel lambda u ξ z) K x)
    (hmin : IsMinOn (fun z : Point n => infConvolutionKernel lambda v η z) L y) :
    regularizedDoubledConvolution (n := n) lambda K L u v
        (doubledPointToBlockPoint (ξ, η)) =
      supConvolutionKernel lambda u ξ x - infConvolutionKernel lambda v η y := by
  rw [regularizedDoubledConvolution, blockPointLeft_doubledPointToBlockPoint,
    blockPointRight_doubledPointToBlockPoint,
    compactSupConvolution_eq_of_isMaxOn hx hmax,
    compactInfConvolution_eq_of_isMinOn hy hmin]

/--
The value identity from
`regularizedDoubledConvolution_eq_kernels_of_isMaxOn_isMinOn`, expanded in
terms of `u`, `v`, and the two quadratic penalties.
-/
theorem regularizedDoubledConvolution_eq_values_of_isMaxOn_isMinOn
    {lambda : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    {ξ η x y : Point n}
    (hx : x ∈ K)
    (hy : y ∈ L)
    (hmax : IsMaxOn (fun z : Point n => supConvolutionKernel lambda u ξ z) K x)
    (hmin : IsMinOn (fun z : Point n => infConvolutionKernel lambda v η z) L y) :
    regularizedDoubledConvolution (n := n) lambda K L u v
        (doubledPointToBlockPoint (ξ, η)) =
      u x - v y -
        (lambda / 2) * dotProduct (x - ξ) (x - ξ) -
          (lambda / 2) * dotProduct (y - η) (y - η) := by
  rw [regularizedDoubledConvolution_eq_kernels_of_isMaxOn_isMinOn
    (n := n) hx hy hmax hmin]
  simp [supConvolutionKernel, infConvolutionKernel]
  ring

/--
The compact regularized doubled convolution has value `0` at the origin when
the normalized functions vanish at the origin, the origin belongs to both
compact sets, and the quadratic upper bound is dominated by the convolution
penalty.

In quantified mathematical form, assume `K` and `L` are nonempty compact
subsets of `R^n`, `0 ∈ K`, `0 ∈ L`, `u` is upper semicontinuous on `K`,
`v` is lower semicontinuous on `L`, `u(0) = 0`, `v(0) = 0`, and

`u(x) - v(y) ≤ quadratic_A(x, y)`

for every `x ∈ K` and `y ∈ L`. If, for every `z ∈ R^(n+n)`,

`quadratic_A(z) ≤ (lambda / 2) * |z|^2`,

then

`regularizedDoubledConvolution lambda K L u v 0 = 0`.
-/
theorem regularizedDoubledConvolution_zero_of_pointwise_bound_and_quadratic_control
    {lambda : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    {A : BlockHessian n}
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L)
    (h0K : (0 : Point n) ∈ K) (h0L : (0 : Point n) ∈ L)
    (hu0 : u 0 = 0) (hv0 : v 0 = 0)
    (hbound : ∀ x : Point n, x ∈ K -> ∀ y : Point n, y ∈ L ->
      u x - v y <= blockQuadraticModel A (doubledPointToBlockPoint (x, y)))
    (hquad0 : ∀ z : BlockPoint n,
      blockQuadraticModel A z <= (lambda / 2) * dotProduct z z) :
    regularizedDoubledConvolution (n := n) lambda K L u v 0 = 0 := by
  rcases exists_isMaxOn_supConvolutionKernel_of_isCompact
      (K := K) (u := u) (lambda := lambda) (ξ := (0 : Point n))
      hKne hKcompact hu with
    ⟨x, hx, hmax⟩
  rcases exists_isMinOn_infConvolutionKernel_of_isCompact
      (K := L) (v := v) (lambda := lambda) (ξ := (0 : Point n))
      hLne hLcompact hv with
    ⟨y, hy, hmin⟩
  have hsup_eq :
      compactSupConvolution lambda K u 0 =
        supConvolutionKernel lambda u 0 x :=
    compactSupConvolution_eq_of_isMaxOn hx hmax
  have hsup_nonneg : 0 <= compactSupConvolution lambda K u 0 := by
    rw [hsup_eq]
    have hle := hmax h0K
    simpa [supConvolutionKernel, hu0, dotProduct] using hle
  have hinf_eq :
      compactInfConvolution lambda L v 0 =
        infConvolutionKernel lambda v 0 y :=
    compactInfConvolution_eq_of_isMinOn hy hmin
  have hinf_nonpos : compactInfConvolution lambda L v 0 <= 0 := by
    rw [hinf_eq]
    have hle := hmin h0L
    simpa [infConvolutionKernel, hv0, dotProduct] using hle
  have hnonneg :
      0 <= regularizedDoubledConvolution (n := n) lambda K L u v 0 := by
    change 0 <= compactSupConvolution lambda K u (blockPointLeft (0 : BlockPoint n)) -
      compactInfConvolution lambda L v (blockPointRight (0 : BlockPoint n))
    simp [blockPointLeft, blockPointRight]
    linarith
  have hvalue :
      regularizedDoubledConvolution (n := n) lambda K L u v 0 =
        u x - v y -
          (lambda / 2) * dotProduct x x -
            (lambda / 2) * dotProduct y y := by
    have hzeroBlock :
        doubledPointToBlockPoint ((0 : Point n), (0 : Point n)) = (0 : BlockPoint n) := by
      ext i
      cases i <;> rfl
    have h :=
      regularizedDoubledConvolution_eq_values_of_isMaxOn_isMinOn
        (n := n) (lambda := lambda) (K := K) (L := L) (u := u) (v := v)
        (ξ := (0 : Point n)) (η := (0 : Point n)) hx hy hmax hmin
    simpa [hzeroBlock, sub_zero] using h
  have hupper : regularizedDoubledConvolution (n := n) lambda K L u v 0 <= 0 := by
    let z : BlockPoint n := doubledPointToBlockPoint (x, y)
    have hdot :
        dotProduct z z = dotProduct x x + dotProduct y y := by
      dsimp [z]
      rw [Matrix.dotProduct_block]
      rfl
    have hbound_xy :
        u x - v y <= blockQuadraticModel A z :=
      hbound x hx y hy
    have hquad_z :
        blockQuadraticModel A z <=
          (lambda / 2) * (dotProduct x x + dotProduct y y) := by
      simpa [hdot] using hquad0 z
    have hle_sum :
        u x - v y <=
          (lambda / 2) * dotProduct x x + (lambda / 2) * dotProduct y y := by
      have hdist :
          (lambda / 2) * (dotProduct x x + dotProduct y y) =
            (lambda / 2) * dotProduct x x + (lambda / 2) * dotProduct y y := by
        ring
      rw [hdist] at hquad_z
      exact le_trans hbound_xy hquad_z
    rw [hvalue]
    linarith
  exact le_antisymm hupper hnonneg

/--
The origin-value normalization in the CIL quadratic estimate.

In quantified mathematical form, suppose `A` is symmetric, `epsilon > 0`,
and `A ≤ mu I`. If the normalized functions vanish at `0`, the origin belongs
to both compact sets, and

`u(x) - v(y) ≤ quadratic_A(x, y)`

for every `x ∈ K` and `y ∈ L`, then the compact regularized doubled
convolution with parameter `epsilon⁻¹ + mu` has value `0` at the origin.
-/
theorem regularizedDoubledConvolution_zero_of_pointwise_bound_and_cil_quadratic
    {epsilon mu : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    {A : BlockHessian n}
    (hHerm : A.IsHermitian) (hepsilon : 0 < epsilon)
    (hA : A <= mu • blockDiagonalIdentity n)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L)
    (h0K : (0 : Point n) ∈ K) (h0L : (0 : Point n) ∈ L)
    (hu0 : u 0 = 0) (hv0 : v 0 = 0)
    (hbound : ∀ x : Point n, x ∈ K -> ∀ y : Point n, y ∈ L ->
      u x - v y <= blockQuadraticModel A (doubledPointToBlockPoint (x, y))) :
    regularizedDoubledConvolution (n := n) (epsilon⁻¹ + mu) K L u v 0 = 0 := by
  refine
    regularizedDoubledConvolution_zero_of_pointwise_bound_and_quadratic_control
      (n := n) (lambda := epsilon⁻¹ + mu) (A := A)
      hKne hLne hKcompact hLcompact hu hv h0K h0L hu0 hv0 hbound ?_
  intro z
  have h :=
    blockQuadraticModel_le_add_smul_mul_self_add_of_le_smul_identity
      (n := n) hHerm hepsilon hA z 0
  simpa [blockQuadraticModel, sub_zero] using h

/--
Pointwise quadratic bounds pass to the regularized doubled convolution.

In standard mathematical terms, suppose that for every `x ∈ K` and `y ∈ L`,

`u(x) - v(y) ≤ (1 / 2) * ⟪A (x, y), (x, y)⟫`,

and suppose that for every `z, ξ ∈ R^n × R^n`,

`(1 / 2) * ⟪A z, z⟫ ≤
 (1 / 2) * ⟪B ξ, ξ⟫ + (lambda / 2) * |z - ξ|^2`.

If `K` and `L` are nonempty compact sets, `u` is upper semicontinuous on `K`,
and `v` is lower semicontinuous on `L`, then for every `ξ ∈ R^n × R^n`,

`regularizedDoubledConvolution lambda K L u v ξ
  ≤ (1 / 2) * ⟪B ξ, ξ⟫`.

This is the compact real-valued version of the sup-convolution estimate used
in the proof of the CIL maximum principle.
-/
theorem regularizedDoubledConvolution_le_blockQuadratic_of_pointwise_bound
    {lambda : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    {A B : BlockHessian n}
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L)
    (hbound : ∀ x : Point n, x ∈ K -> ∀ y : Point n, y ∈ L ->
      u x - v y <= blockQuadraticModel A (doubledPointToBlockPoint (x, y)))
    (hquad : ∀ z ξ : BlockPoint n,
      blockQuadraticModel A z <=
        blockQuadraticModel B ξ + (lambda / 2) * dotProduct (z - ξ) (z - ξ)) :
    ∀ ξ : BlockPoint n,
      regularizedDoubledConvolution (n := n) lambda K L u v ξ <=
        blockQuadraticModel B ξ := by
  intro ξ
  let ξ₁ : Point n := blockPointLeft ξ
  let ξ₂ : Point n := blockPointRight ξ
  rcases exists_isMaxOn_supConvolutionKernel_of_isCompact
      (K := K) (u := u) (lambda := lambda) (ξ := ξ₁)
      hKne hKcompact hu with
    ⟨x, hx, hmax⟩
  rcases exists_isMinOn_infConvolutionKernel_of_isCompact
      (K := L) (v := v) (lambda := lambda) (ξ := ξ₂)
      hLne hLcompact hv with
    ⟨y, hy, hmin⟩
  have hvalue :
      regularizedDoubledConvolution (n := n) lambda K L u v ξ =
        u x - v y -
          (lambda / 2) * dotProduct (x - ξ₁) (x - ξ₁) -
            (lambda / 2) * dotProduct (y - ξ₂) (y - ξ₂) := by
    rw [← doubledPointToBlockPoint_left_right ξ]
    exact regularizedDoubledConvolution_eq_values_of_isMaxOn_isMinOn
      (n := n) hx hy hmax hmin
  let z : BlockPoint n := doubledPointToBlockPoint (x, y)
  have hdot :
      dotProduct (z - ξ) (z - ξ) =
        dotProduct (x - ξ₁) (x - ξ₁) +
          dotProduct (y - ξ₂) (y - ξ₂) := by
    rw [Matrix.dotProduct_block]
    rfl
  have hbound_xy :
      u x - v y <= blockQuadraticModel A z :=
    hbound x hx y hy
  have hquad_z :
      blockQuadraticModel A z <=
        blockQuadraticModel B ξ +
          ((lambda / 2) * dotProduct (x - ξ₁) (x - ξ₁) +
            (lambda / 2) * dotProduct (y - ξ₂) (y - ξ₂)) := by
    have h := hquad z ξ
    rw [hdot] at h
    linarith
  linarith

/--
An upper bound by a quadratic form gives a maximum of the difference at the
origin, provided equality holds at the origin.

In standard mathematical terms, if `F(ξ) ≤ (1 / 2) * ⟪B ξ, ξ⟫` for every
`ξ ∈ R^n × R^n`, and `F(0) = 0`, then

`ξ ↦ F(ξ) - (1 / 2) * ⟪B ξ, ξ⟫`

has a maximum at `0`.
-/
theorem isMaxOn_sub_blockQuadraticModel_zero_of_le
    {F : BlockPoint n -> Real} {B : BlockHessian n}
    (hle : ∀ ξ : BlockPoint n, F ξ <= blockQuadraticModel B ξ)
    (hzero : F 0 = 0) :
    IsMaxOn (fun ξ : BlockPoint n => F ξ - blockQuadraticModel B ξ) Set.univ 0 := by
  intro ξ _hξ
  have hleξ := hle ξ
  have hquad_zero : blockQuadraticModel B (0 : BlockPoint n) = 0 := by
    simp [blockQuadraticModel]
  calc
    F ξ - blockQuadraticModel B ξ <= 0 := by linarith
    _ = F 0 - blockQuadraticModel B (0 : BlockPoint n) := by
      simp [hzero, hquad_zero]

/--
The compact regularized doubled convolution satisfies the maximum condition
used before applying the semiconvex matrix lemma, once the pointwise
quadratic bound and the quadratic comparison estimate have been proved.

In standard mathematical terms, under the hypotheses of
`regularizedDoubledConvolution_le_blockQuadratic_of_pointwise_bound`, if the
regularized doubled convolution has value `0` at the origin, then

`ξ ↦ regularizedDoubledConvolution lambda K L u v ξ
      - (1 / 2) * ⟪B ξ, ξ⟫`

has a maximum at `0`.
-/
theorem isMaxOn_regularizedDoubledConvolution_sub_blockQuadratic_of_pointwise_bound
    {lambda : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    {A B : BlockHessian n}
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L)
    (hbound : ∀ x : Point n, x ∈ K -> ∀ y : Point n, y ∈ L ->
      u x - v y <= blockQuadraticModel A (doubledPointToBlockPoint (x, y)))
    (hquad : ∀ z ξ : BlockPoint n,
      blockQuadraticModel A z <=
        blockQuadraticModel B ξ + (lambda / 2) * dotProduct (z - ξ) (z - ξ))
    (hzero :
      regularizedDoubledConvolution (n := n) lambda K L u v 0 = 0) :
    IsMaxOn
      (fun ξ : BlockPoint n =>
        regularizedDoubledConvolution (n := n) lambda K L u v ξ -
          blockQuadraticModel B ξ)
      Set.univ 0 := by
  exact isMaxOn_sub_blockQuadraticModel_zero_of_le
    (n := n)
    (F := regularizedDoubledConvolution (n := n) lambda K L u v)
    (B := B)
      (regularizedDoubledConvolution_le_blockQuadratic_of_pointwise_bound
        (n := n) hKne hLne hKcompact hLcompact hu hv hbound hquad)
    hzero

/--
The compact regularized doubled convolution satisfies the maximum condition
with the CIL quadratic matrix `A + ε A^2`.

In standard mathematical terms, assume that `A` is symmetric, `ε > 0`, and
`A ≤ μ I`. If the localized functions satisfy

`u(x) - v(y) ≤ (1 / 2) * ⟪A(x, y), (x, y)⟫`

on `K × L`, and if the regularized doubled convolution with parameter
`ε⁻¹ + μ` has value `0` at the origin, then

`ξ ↦ regularizedDoubledConvolution (ε⁻¹ + μ) K L u v ξ
      - (1 / 2) * ⟪(A + ε A^2)ξ, ξ⟫`

has a maximum at `0`.
-/
theorem isMaxOn_regularizedDoubledConvolution_sub_cilQuadratic_of_pointwise_bound
    {epsilon mu : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    {A : BlockHessian n}
    (hHerm : A.IsHermitian) (hepsilon : 0 < epsilon)
    (hA : A <= mu • blockDiagonalIdentity n)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v L)
    (hbound : ∀ x : Point n, x ∈ K -> ∀ y : Point n, y ∈ L ->
      u x - v y <= blockQuadraticModel A (doubledPointToBlockPoint (x, y)))
    (hzero :
      regularizedDoubledConvolution (n := n) (epsilon⁻¹ + mu) K L u v 0 = 0) :
    IsMaxOn
      (fun ξ : BlockPoint n =>
        regularizedDoubledConvolution (n := n) (epsilon⁻¹ + mu) K L u v ξ -
          blockQuadraticModel (A + epsilon • (A * A)) ξ)
      Set.univ 0 := by
  exact isMaxOn_regularizedDoubledConvolution_sub_blockQuadratic_of_pointwise_bound
    (n := n)
    (lambda := epsilon⁻¹ + mu)
    (A := A)
    (B := A + epsilon • (A * A))
    hKne hLne hKcompact hLcompact hu hv hbound
    (blockQuadraticModel_le_add_smul_mul_self_add_of_le_smul_identity
      (n := n) hHerm hepsilon hA)
    hzero

/--
The translated and affine-normalized form of the regularized maximum
condition used in the CIL proof.

In standard mathematical terms, suppose `(x0, y0)` is a maximum on the
translated compact set
`{(x0 + x, y0 + y) | x ∈ K, y ∈ L}` of the doubled difference minus the
quadratic expansion with value `φ0`, gradient `P`, and Hessian `A`. If
`A` is symmetric, `ε > 0`, `A ≤ μI`, and the normalized compact
regularization has value `0` at the origin, then subtracting
`quadratic_{A + εA^2}` from that regularization gives a function with a
maximum at the origin.
-/
theorem isMaxOn_regularizedDoubledConvolution_normalized_sub_cilQuadratic_of_isMaxOn_expansion
    {epsilon mu : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    {x0 y0 : Point n} {φ0 : Real} {P : BlockPoint n} {A : BlockHessian n}
    (hHerm : A.IsHermitian) (hepsilon : 0 < epsilon)
    (hA : A <= mu • blockDiagonalIdentity n)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn
      (normalizedLeftOfBlockGradient (n := n) u x0 P) K)
    (hv : LowerSemicontinuousOn
      (normalizedRightOfBlockGradient (n := n) v y0 P) L)
    (hmax : IsMaxOn
      (fun q : DoubledPoint n =>
        u q.1 - v q.2 - doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A q)
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
      (x0, y0))
    (hzero :
      regularizedDoubledConvolution (n := n) (epsilon⁻¹ + mu) K L
          (normalizedLeftOfBlockGradient (n := n) u x0 P)
          (normalizedRightOfBlockGradient (n := n) v y0 P) 0 = 0) :
    IsMaxOn
      (fun ξ : BlockPoint n =>
        regularizedDoubledConvolution (n := n) (epsilon⁻¹ + mu) K L
            (normalizedLeftOfBlockGradient (n := n) u x0 P)
            (normalizedRightOfBlockGradient (n := n) v y0 P) ξ -
          blockQuadraticModel (A + epsilon • (A * A)) ξ)
      Set.univ 0 := by
  exact isMaxOn_regularizedDoubledConvolution_sub_cilQuadratic_of_pointwise_bound
    (n := n)
    (epsilon := epsilon)
    (mu := mu)
    (K := K)
    (L := L)
    (u := normalizedLeftOfBlockGradient (n := n) u x0 P)
    (v := normalizedRightOfBlockGradient (n := n) v y0 P)
    (A := A)
    hHerm hepsilon hA hKne hLne hKcompact hLcompact hu hv
    (normalized_pointwise_bound_of_isMaxOn_doubledQuadraticExpansionAt
      (n := n) (K := K) (L := L) (u := u) (v := v)
      (x0 := x0) (y0 := y0) (φ0 := φ0) (P := P) (A := A) hmax)
    hzero

/--
The normalized regularized maximum condition without an additional
origin-value hypothesis.

In standard mathematical terms, if the translated compact sets contain the
origin and the normalized functions vanish at the origin, then the value
`0` of the compact regularized doubled convolution at the origin follows from
the maximum inequality and the CIL quadratic estimate.
-/
theorem isMaxOn_regularizedDoubledConvolution_normalized_sub_cilQuadratic_of_mem_zero
    {epsilon mu : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    {x0 y0 : Point n} {φ0 : Real} {P : BlockPoint n} {A : BlockHessian n}
    (hHerm : A.IsHermitian) (hepsilon : 0 < epsilon)
    (hA : A <= mu • blockDiagonalIdentity n)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn
      (normalizedLeftOfBlockGradient (n := n) u x0 P) K)
    (hv : LowerSemicontinuousOn
      (normalizedRightOfBlockGradient (n := n) v y0 P) L)
    (h0K : (0 : Point n) ∈ K) (h0L : (0 : Point n) ∈ L)
    (hmax : IsMaxOn
      (fun q : DoubledPoint n =>
        u q.1 - v q.2 - doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A q)
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
      (x0, y0)) :
    IsMaxOn
      (fun ξ : BlockPoint n =>
        regularizedDoubledConvolution (n := n) (epsilon⁻¹ + mu) K L
            (normalizedLeftOfBlockGradient (n := n) u x0 P)
            (normalizedRightOfBlockGradient (n := n) v y0 P) ξ -
          blockQuadraticModel (A + epsilon • (A * A)) ξ)
      Set.univ 0 := by
  have hbound :
      ∀ x : Point n, x ∈ K -> ∀ y : Point n, y ∈ L ->
        normalizedLeftOfBlockGradient (n := n) u x0 P x -
            normalizedRightOfBlockGradient (n := n) v y0 P y <=
          blockQuadraticModel A (doubledPointToBlockPoint (x, y)) :=
    normalized_pointwise_bound_of_isMaxOn_doubledQuadraticExpansionAt
      (n := n) (K := K) (L := L) (u := u) (v := v)
      (x0 := x0) (y0 := y0) (φ0 := φ0) (P := P) (A := A) hmax
  have hzero :
      regularizedDoubledConvolution (n := n) (epsilon⁻¹ + mu) K L
          (normalizedLeftOfBlockGradient (n := n) u x0 P)
          (normalizedRightOfBlockGradient (n := n) v y0 P) 0 = 0 :=
    regularizedDoubledConvolution_zero_of_pointwise_bound_and_cil_quadratic
      (n := n) hHerm hepsilon hA hKne hLne hKcompact hLcompact hu hv
      h0K h0L
      (normalizedLeftOfBlockGradient_zero (n := n) u x0 P)
      (normalizedRightOfBlockGradient_zero (n := n) v y0 P)
      hbound
  exact
    isMaxOn_regularizedDoubledConvolution_normalized_sub_cilQuadratic_of_isMaxOn_expansion
      (n := n) hHerm hepsilon hA hKne hLne hKcompact hLcompact hu hv hmax hzero

/--
The previous theorem, with semicontinuity hypotheses stated for the original
functions on the translated compact neighborhoods.

In standard mathematical terms, upper semicontinuity of `u` on
`{x0 + x | x ∈ K}` and lower semicontinuity of `v` on
`{y0 + y | y ∈ L}` imply the corresponding semicontinuity hypotheses for the
translated affine-normalized functions on `K` and `L`.
-/
theorem isMaxOn_regularizedDoubledConvolution_normalized_sub_cilQuadratic_of_isMaxOn_expansion'
    {epsilon mu : Real} {K L : Set (Point n)} {u v : Point n -> Real}
    {x0 y0 : Point n} {φ0 : Real} {P : BlockPoint n} {A : BlockHessian n}
    (hHerm : A.IsHermitian) (hepsilon : 0 < epsilon)
    (hA : A <= mu • blockDiagonalIdentity n)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hu : UpperSemicontinuousOn u ((fun x : Point n => x0 + x) '' K))
    (hv : LowerSemicontinuousOn v ((fun y : Point n => y0 + y) '' L))
    (hmax : IsMaxOn
      (fun q : DoubledPoint n =>
        u q.1 - v q.2 - doubledQuadraticExpansionAt (n := n) x0 y0 φ0 P A q)
      {q : DoubledPoint n | q.1 - x0 ∈ K ∧ q.2 - y0 ∈ L}
      (x0, y0))
    (hzero :
      regularizedDoubledConvolution (n := n) (epsilon⁻¹ + mu) K L
          (normalizedLeftOfBlockGradient (n := n) u x0 P)
          (normalizedRightOfBlockGradient (n := n) v y0 P) 0 = 0) :
    IsMaxOn
      (fun ξ : BlockPoint n =>
        regularizedDoubledConvolution (n := n) (epsilon⁻¹ + mu) K L
            (normalizedLeftOfBlockGradient (n := n) u x0 P)
            (normalizedRightOfBlockGradient (n := n) v y0 P) ξ -
          blockQuadraticModel (A + epsilon • (A * A)) ξ)
      Set.univ 0 := by
  exact
    isMaxOn_regularizedDoubledConvolution_normalized_sub_cilQuadratic_of_isMaxOn_expansion
      (n := n) hHerm hepsilon hA hKne hLne hKcompact hLcompact
      (upperSemicontinuousOn_normalizedLeftOfBlockGradient (n := n) hu)
      (lowerSemicontinuousOn_normalizedRightOfBlockGradient (n := n) hv)
      hmax hzero

/--
The translated-neighborhood version of the normalized regularized maximum
condition without an additional origin-value hypothesis.

In standard mathematical terms, if `u` and `v` are semicontinuous on the
translated compact neighborhoods, if those neighborhoods contain the base
points after translation, and if `(x0, y0)` is the maximum point of the
doubled difference minus the quadratic expansion, then the regularized
maximum condition follows directly.
-/
theorem isMaxOn_regularizedDoubledConvolution_normalized_sub_cilQuadratic_of_translated_mem_zero
    {epsilon mu : Real} {K L : Set (Point n)} {u v : Point n -> Real}
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
    IsMaxOn
      (fun ξ : BlockPoint n =>
        regularizedDoubledConvolution (n := n) (epsilon⁻¹ + mu) K L
            (normalizedLeftOfBlockGradient (n := n) u x0 P)
            (normalizedRightOfBlockGradient (n := n) v y0 P) ξ -
          blockQuadraticModel (A + epsilon • (A * A)) ξ)
      Set.univ 0 := by
  exact
    isMaxOn_regularizedDoubledConvolution_normalized_sub_cilQuadratic_of_mem_zero
      (n := n) hHerm hepsilon hA hKne hLne hKcompact hLcompact
      (upperSemicontinuousOn_normalizedLeftOfBlockGradient (n := n) hu)
      (lowerSemicontinuousOn_normalizedRightOfBlockGradient (n := n) hv)
      h0K h0L hmax

end ViscositySolns
