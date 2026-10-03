/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.SupConvolution

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Semiconvexity for compact sup-convolutions

This file records the semiconvexity inequality used in the
finite-dimensional maximum-principle proof.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The coordinate semiconvexity inequality with constant `lambda`.

In quantified mathematical form, a function `f : R^n -> R` satisfies
`CoordinateSemiconvexOn lambda C f` if for every `x, y ∈ C` and every real
numbers `a, b` with `0 ≤ a`, `0 ≤ b`, and `a + b = 1`, whenever
`a x + b y ∈ C`, one has

`f (a x + b y) ≤
 a f x + b f y + (lambda / 2) a b ∑ i, (x i - y i)^2`.
-/
def CoordinateSemiconvexOn (lambda : Real) (C : Set (Point n))
    (f : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ C ->
  ∀ y : Point n, y ∈ C ->
  ∀ a b : Real, 0 <= a -> 0 <= b -> a + b = 1 ->
    a • x + b • y ∈ C ->
      f (a • x + b • y) <=
        a * f x + b * f y +
          (lambda / 2) * a * b * dotProduct (x - y) (x - y)

/--
The quadratic function added to a semiconvex function in order to obtain a
convex function.

In quantified mathematical form, this is

`x ↦ f x + (lambda / 2) * ∑ i, x_i^2`.
-/
def semiconvexConvexification (lambda : Real) (f : Point n -> Real) :
    Point n -> Real :=
  fun x => f x + quadraticModel 0 0 0 (lambda • (1 : Hessian n)) x

/--
The quadratic identity used to convert semiconvexity into convexity.

In quantified mathematical form, if `a + b = 1`, then

`Q(a x + b y) + (lambda / 2) a b ∑ i, (x_i - y_i)^2
 = a Q(x) + b Q(y)`,

where `Q(x) = (lambda / 2) * ∑ i, x_i^2`.
-/
theorem quadraticModel_scalar_identity_convex_combination
    (lambda : Real) (x y : Point n) {a b : Real} (hab : a + b = 1) :
    quadraticModel 0 0 0 (lambda • (1 : Hessian n)) (a • x + b • y) +
        (lambda / 2) * a * b * dotProduct (x - y) (x - y) =
      a * quadraticModel 0 0 0 (lambda • (1 : Hessian n)) x +
        b * quadraticModel 0 0 0 (lambda • (1 : Hessian n)) y := by
  have hb_eq : b = 1 - a := by linarith
  subst b
  simp only [quadraticModel, sub_zero, zero_add, dotProduct_add, add_dotProduct,
    smul_dotProduct, dotProduct_smul, dotProduct_sub, sub_dotProduct, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  rw [dotProduct_comm y x]
  ring

/--
The quadratic identity for an arbitrary Hessian.

In quantified mathematical form, if `a + b = 1`, then

`Q(a x + b y) =
 a Q(x) + b Q(y) - (1 / 2) a b ⟪B(x - y), x - y⟫`,

where `Q(x) = (1 / 2) * ⟪B x, x⟫`.
-/
theorem quadraticModel_zero_convex_combination
    (B : Hessian n) (x y : Point n) {a b : Real} (hab : a + b = 1) :
    quadraticModel 0 0 0 B (a • x + b • y) =
      a * quadraticModel 0 0 0 B x +
        b * quadraticModel 0 0 0 B y -
          (1 / 2 : Real) * a * b *
            dotProduct (Matrix.mulVec B (x - y)) (x - y) := by
  have hb_eq : b = 1 - a := by linarith
  subst b
  simp only [quadraticModel, sub_zero, zero_add, dotProduct_add, add_dotProduct,
    smul_dotProduct, dotProduct_smul, dotProduct_sub, sub_dotProduct,
    Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
  ring

/--
A finite entrywise bound on a Hessian gives a quadratic-form upper bound.

In quantified mathematical form, if `η ≥ 0` and `|Bᵢⱼ| ≤ η` for every
matrix entry, then for every vector `v`,

`⟪Bv, v⟫ ≤ η n^2 ⟪v, v⟫`.
-/
theorem dotProduct_mulVec_le_entrywise_abs_mul_dotProduct_self
    (B : Hessian n) {eta : Real} (heta : 0 <= eta)
    (hB : ∀ i j : Fin n, |B i j| <= eta) (v : Point n) :
    dotProduct (Matrix.mulVec B v) v <=
      (eta * (n : Real) * (n : Real)) * dotProduct v v := by
  have hquad :=
    abs_quadraticModel_zero_zero_le_of_entrywise_abs_le
      (n := n) (x0 := 0) (x := v) (A := B) heta hB
  have hhalf_le :
      (1 / 2 : Real) * dotProduct (Matrix.mulVec B v) v <=
        ((1 / 2 : Real) * eta * (n : Real) * (n : Real)) * ‖v‖ ^ 2 := by
    have hle_abs :
        (1 / 2 : Real) * dotProduct (Matrix.mulVec B v) v <=
          |(1 / 2 : Real) * dotProduct (Matrix.mulVec B v) v| :=
      le_abs_self _
    have hquad_eq :
        quadraticModel (n := n) 0 0 0 B v =
          (1 / 2 : Real) * dotProduct (Matrix.mulVec B v) v := by
      simp [quadraticModel]
    have hquad' :
        |(1 / 2 : Real) * dotProduct (Matrix.mulVec B v) v| <=
          ((1 / 2 : Real) * eta * (n : Real) * (n : Real)) * ‖v‖ ^ 2 := by
      simpa [hquad_eq] using hquad
    linarith
  have hdot_norm : ‖v‖ ^ 2 <= dotProduct v v :=
    norm_sq_le_dotProduct_self v
  have hcoeff_nonneg : 0 <= eta * (n : Real) * (n : Real) := by positivity
  calc
    dotProduct (Matrix.mulVec B v) v <=
        (eta * (n : Real) * (n : Real)) * ‖v‖ ^ 2 := by
      linarith
    _ <= (eta * (n : Real) * (n : Real)) * dotProduct v v := by
      exact mul_le_mul_of_nonneg_left hdot_norm hcoeff_nonneg

/--
The negative of a bounded quadratic form is coordinate semiconvex.

In quantified mathematical form, if `η ≥ 0` and `|Bᵢⱼ| ≤ η` for every matrix
entry, then the function

`x ↦ - (1 / 2) * ⟪Bx, x⟫`

satisfies the coordinate semiconvexity inequality with constant `η n^2` on
every set.
-/
theorem coordinateSemiconvexOn_neg_quadraticModel_of_entrywise_abs_le
    {C : Set (Point n)} (B : Hessian n) {eta : Real} (heta : 0 <= eta)
    (hB : ∀ i j : Fin n, |B i j| <= eta) :
    CoordinateSemiconvexOn (eta * (n : Real) * (n : Real)) C
      (fun x : Point n => -quadraticModel 0 0 0 B x) := by
  intro x _hx y _hy a b ha hb hab _hcombo
  have hquad :=
    quadraticModel_zero_convex_combination (n := n) B x y (a := a) (b := b) hab
  have hD :
      dotProduct (Matrix.mulVec B (x - y)) (x - y) <=
        (eta * (n : Real) * (n : Real)) * dotProduct (x - y) (x - y) :=
    dotProduct_mulVec_le_entrywise_abs_mul_dotProduct_self
      (n := n) B heta hB (x - y)
  have hab_nonneg : 0 <= a * b := mul_nonneg ha hb
  nlinarith

/--
Coordinate semiconvexity implies convexity after adding the quadratic function
`x ↦ (lambda / 2) * ∑ i, x_i^2`.

In quantified mathematical form, if `f` satisfies the coordinate
semiconvexity inequality on `C` with constant `lambda`, then
`x ↦ f x + (lambda / 2) * ∑ i, x_i^2` is convex on `C`.
-/
theorem CoordinateSemiconvexOn.convexOn_semiconvexConvexification
    {lambda : Real} {C : Set (Point n)} {f : Point n -> Real}
    (hsemi : CoordinateSemiconvexOn lambda C f) (hC : Convex Real C) :
    ConvexOn Real C (semiconvexConvexification lambda f) := by
  refine ⟨hC, ?_⟩
  intro x hx y hy a b ha hb hab
  have hcombo : a • x + b • y ∈ C := hC hx hy ha hb hab
  have hf := hsemi x hx y hy a b ha hb hab hcombo
  have hquad :=
    quadraticModel_scalar_identity_convex_combination (n := n) lambda x y (a := a) (b := b) hab
  unfold semiconvexConvexification
  simp only [smul_eq_mul]
  nlinarith

/--
Convexity after adding the quadratic function implies coordinate
semiconvexity.

In quantified mathematical form, if `C` is convex and
`x ↦ f x + (lambda / 2) * ∑ i, x_i^2` is convex on `C`, then `f` satisfies
the coordinate semiconvexity inequality on `C` with constant `lambda`.
-/
theorem ConvexOn.coordinateSemiconvexOn_of_semiconvexConvexification
    {lambda : Real} {C : Set (Point n)} {f : Point n -> Real}
    (hconv : ConvexOn Real C (semiconvexConvexification lambda f)) :
    CoordinateSemiconvexOn lambda C f := by
  intro x hx y hy a b ha hb hab hcombo
  have hconv_ineq := hconv.2 hx hy ha hb hab
  have hquad :=
    quadraticModel_scalar_identity_convex_combination (n := n) lambda x y (a := a) (b := b) hab
  unfold semiconvexConvexification at hconv_ineq
  simp only [smul_eq_mul] at hconv_ineq
  nlinarith

/--
On a convex set, coordinate semiconvexity is equivalent to convexity after
adding the quadratic function `x ↦ (lambda / 2) * ∑ i, x_i^2`.
-/
theorem coordinateSemiconvexOn_iff_convexOn_semiconvexConvexification
    {lambda : Real} {C : Set (Point n)} {f : Point n -> Real}
    (hC : Convex Real C) :
    CoordinateSemiconvexOn lambda C f ↔
      ConvexOn Real C (semiconvexConvexification lambda f) := by
  constructor
  · intro hsemi
    exact hsemi.convexOn_semiconvexConvexification hC
  · intro hconv
    exact ConvexOn.coordinateSemiconvexOn_of_semiconvexConvexification hconv

/--
A convex function is coordinate semiconvex with constant `0`.

In quantified mathematical form, if `f` is convex on `C`, then for every
`x, y ∈ C` and every `a, b ≥ 0` with `a + b = 1`, whenever
`a x + b y ∈ C`, one has

`f (a x + b y) ≤ a f x + b f y`.

This is exactly the coordinate semiconvexity inequality with the penalty term
equal to `0`.
-/
theorem ConvexOn.coordinateSemiconvexOn_zero
    {C : Set (Point n)} {f : Point n -> Real}
    (hconv : ConvexOn Real C f) :
    CoordinateSemiconvexOn (0 : Real) C f := by
  intro x hx y hy a b ha hb hab _hcombo
  have h := hconv.2 hx hy ha hb hab
  simpa using h

/--
The coordinate semiconvexity inequality is monotone in the semiconvexity
constant.

In quantified mathematical form, if `lambda ≤ mu` and `f` satisfies the
coordinate semiconvexity inequality with constant `lambda`, then `f` satisfies
the same inequality with constant `mu`.
-/
theorem CoordinateSemiconvexOn.mono
    {lambda mu : Real} {C : Set (Point n)} {f : Point n -> Real}
    (hsemi : CoordinateSemiconvexOn lambda C f) (hlambda_mu : lambda <= mu) :
    CoordinateSemiconvexOn mu C f := by
  intro x hx y hy a b ha hb hab hcombo
  have h := hsemi x hx y hy a b ha hb hab hcombo
  have hdot_nonneg : 0 <= dotProduct (x - y) (x - y) := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _hi => by
      simpa [sq] using sq_nonneg ((x - y) i)
  have hfactor_nonneg : 0 <= a * b * dotProduct (x - y) (x - y) := by
    exact mul_nonneg (mul_nonneg ha hb) hdot_nonneg
  have hcoeff : lambda / 2 <= mu / 2 := by linarith
  have hpenalty :
      (lambda / 2) * (a * b * dotProduct (x - y) (x - y)) <=
        (mu / 2) * (a * b * dotProduct (x - y) (x - y)) :=
    mul_le_mul_of_nonneg_right hcoeff hfactor_nonneg
  nlinarith

/--
The sum of two coordinate semiconvex functions is coordinate semiconvex, with
constant equal to the sum of the two constants.

In quantified mathematical form, if `f` satisfies the coordinate semiconvexity
inequality with constant `lambda` on `C`, and `g` satisfies it with constant
`mu` on `C`, then `x ↦ f x + g x` satisfies it with constant
`lambda + mu` on `C`.
-/
theorem CoordinateSemiconvexOn.add
    {lambda mu : Real} {C : Set (Point n)} {f g : Point n -> Real}
    (hf : CoordinateSemiconvexOn lambda C f)
    (hg : CoordinateSemiconvexOn mu C g) :
    CoordinateSemiconvexOn (lambda + mu) C (fun x => f x + g x) := by
  intro x hx y hy a b ha hb hab hcombo
  have hf' := hf x hx y hy a b ha hb hab hcombo
  have hg' := hg x hx y hy a b ha hb hab hcombo
  nlinarith

/--
The coordinate semiconvexity inequality restricts to subsets.

In quantified mathematical form, if `D ⊆ C` and `f` satisfies the coordinate
semiconvexity inequality on `C`, then `f` satisfies the same inequality on
`D`.
-/
theorem CoordinateSemiconvexOn.mono_set
    {lambda : Real} {C D : Set (Point n)} {f : Point n -> Real}
    (hsemi : CoordinateSemiconvexOn lambda C f) (hDC : D ⊆ C) :
    CoordinateSemiconvexOn lambda D f := by
  intro x hx y hy a b ha hb hab hcombo
  exact hsemi x (hDC hx) y (hDC hy) a b ha hb hab (hDC hcombo)

/--
The coordinate semiconvexity inequality is unchanged by replacing a function
with an equal function on the set.

In quantified mathematical form, suppose `f x = g x` for every `x ∈ C`. If
`f` satisfies the coordinate semiconvexity inequality on `C`, then `g`
satisfies the same inequality on `C`.
-/
theorem CoordinateSemiconvexOn.congr
    {lambda : Real} {C : Set (Point n)} {f g : Point n -> Real}
    (hsemi : CoordinateSemiconvexOn lambda C f)
    (hfg : ∀ x : Point n, x ∈ C -> f x = g x) :
    CoordinateSemiconvexOn lambda C g := by
  intro x hx y hy a b ha hb hab hcombo
  have h := hsemi x hx y hy a b ha hb hab hcombo
  simpa [← hfg x hx, ← hfg y hy, ← hfg (a • x + b • y) hcombo] using h

/--
Coordinate semiconvexity on all of `R^n` implies continuity.

In quantified mathematical form, if `f : R^n -> R` satisfies
`CoordinateSemiconvexOn lambda Set.univ f`, then `f` is continuous.
-/
theorem CoordinateSemiconvexOn.continuous_univ
    {lambda : Real} {f : Point n -> Real}
    (hsemi : CoordinateSemiconvexOn lambda Set.univ f) :
    Continuous f := by
  let g : Point n -> Real := semiconvexConvexification lambda f
  have hgconv : ConvexOn Real Set.univ g :=
    hsemi.convexOn_semiconvexConvexification convex_univ
  have hgcont : Continuous g := by
    exact continuousOn_univ.1 (hgconv.continuousOn isOpen_univ)
  have hquad : Continuous fun x : Point n =>
      quadraticModel 0 0 0 (lambda • (1 : Hessian n)) x :=
    continuous_quadraticModel 0 0 0 (lambda • (1 : Hessian n))
  have hf : Continuous fun x : Point n =>
      g x - quadraticModel 0 0 0 (lambda • (1 : Hessian n)) x :=
    hgcont.sub hquad
  simpa [g, semiconvexConvexification] using hf

/--
Coordinate semiconvexity on a closed ball implies continuity on the
corresponding open ball.

In quantified mathematical form, if `f : R^n -> R` satisfies the coordinate
semiconvexity inequality on `closedBall x0 R`, then `f` is continuous at each
point of `ball x0 R`, relative to `ball x0 R`. The proof applies the usual
continuity theorem for finite convex functions on open convex sets to
`x ↦ f x + (lambda / 2) |x|^2`, and then subtracts the continuous quadratic
function.
-/
theorem CoordinateSemiconvexOn.continuousOn_ball_of_closedBall
    {lambda : Real} {f : Point n -> Real} {x0 : Point n} {R : Real}
    (hsemi : CoordinateSemiconvexOn lambda (Metric.closedBall x0 R) f) :
    ContinuousOn f (Metric.ball x0 R) := by
  let g : Point n -> Real := semiconvexConvexification lambda f
  have hsemi_ball : CoordinateSemiconvexOn lambda (Metric.ball x0 R) f :=
    hsemi.mono_set Metric.ball_subset_closedBall
  have hgconv : ConvexOn Real (Metric.ball x0 R) g :=
    hsemi_ball.convexOn_semiconvexConvexification (convex_ball x0 R)
  have hgcont : ContinuousOn g (Metric.ball x0 R) :=
    hgconv.continuousOn Metric.isOpen_ball
  have hquad : Continuous fun x : Point n =>
      quadraticModel 0 0 0 (lambda • (1 : Hessian n)) x :=
    continuous_quadraticModel 0 0 0 (lambda • (1 : Hessian n))
  have hf : ContinuousOn (fun x : Point n =>
      g x - quadraticModel 0 0 0 (lambda • (1 : Hessian n)) x) (Metric.ball x0 R) :=
    hgcont.sub hquad.continuousOn
  simpa [g, semiconvexConvexification] using hf

/--
Coordinate semiconvexity on a larger closed ball implies continuity on a
smaller sphere.

In quantified mathematical form, if `f : R^n -> R` satisfies the coordinate
semiconvexity inequality on `closedBall x0 R` and `r < R`, then `f` is
continuous on `sphere x0 r`.
-/
theorem CoordinateSemiconvexOn.continuousOn_sphere_of_closedBall
    {lambda : Real} {f : Point n -> Real} {x0 : Point n} {r R : Real}
    (hsemi : CoordinateSemiconvexOn lambda (Metric.closedBall x0 R) f)
    (hrR : r < R) :
    ContinuousOn f (Metric.sphere x0 r) := by
  exact hsemi.continuousOn_ball_of_closedBall.mono fun x hx => by
    have hxdist : dist x x0 = r := by
      exact hx
    simpa [Metric.mem_ball, hxdist] using hrR

/--
The quadratic identity behind the semiconvexity of the sup-convolution
kernel.

In quantified mathematical form, if `a + b = 1`, then for every `z`, `ξ`,
and `ζ`,

`K(a ξ + b ζ, z) =
 a K(ξ, z) + b K(ζ, z)
 + (lambda / 2) a b ∑ i, (ξ i - ζ i)^2`,

where `K(ξ, z) = v z - (lambda / 2) ∑ i, (z i - ξ i)^2`.
-/
theorem supConvolutionKernel_convex_combination
    (lambda : Real) (v : Point n -> Real) (z ξ ζ : Point n)
    {a b : Real} (hab : a + b = 1) :
    supConvolutionKernel lambda v (a • ξ + b • ζ) z =
      a * supConvolutionKernel lambda v ξ z +
        b * supConvolutionKernel lambda v ζ z +
          (lambda / 2) * a * b * dotProduct (ξ - ζ) (ξ - ζ) := by
  have hb_eq : b = 1 - a := by linarith
  let dx : Point n := z - ξ
  let dy : Point n := z - ζ
  have hcenter : z - (a • ξ + b • ζ) = a • dx + b • dy := by
    ext i
    simp [dx, dy, hb_eq]
    ring
  have hdiff : ξ - ζ = dy - dx := by
    ext i
    simp [dx, dy]
  have hquad :
      dotProduct (z - (a • ξ + b • ζ)) (z - (a • ξ + b • ζ)) =
        a * dotProduct dx dx + b * dotProduct dy dy -
          a * b * dotProduct (ξ - ζ) (ξ - ζ) := by
    rw [hcenter, hdiff]
    simp only [dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul,
      dotProduct_sub, sub_dotProduct]
    rw [dotProduct_comm dx dy]
    rw [hb_eq]
    ring
  unfold supConvolutionKernel
  rw [hquad]
  rw [hb_eq]
  ring

/--
Compact sup-convolutions satisfy the coordinate semiconvexity inequality.

In quantified mathematical form, suppose that for every `ξ : R^n` there
exists `z ∈ K` at which

`x ↦ v x - (lambda / 2) * ∑ i, (x i - ξ i)^2`

has a maximum on `K`. Then `ξ ↦ compactSupConvolution lambda K v ξ` is
semiconvex on all of `R^n` with constant `lambda`.
-/
theorem coordinateSemiconvexOn_compactSupConvolution_of_exists_isMaxOn
    {K : Set (Point n)} {v : Point n -> Real} {lambda : Real}
    (hmax_exists : ∀ ξ : Point n,
      ∃ z ∈ K, IsMaxOn (fun x : Point n => supConvolutionKernel lambda v ξ x) K z) :
    CoordinateSemiconvexOn lambda Set.univ
      (fun ξ : Point n => compactSupConvolution lambda K v ξ) := by
  intro ξ _hξ ζ _hζ a b ha hb hab _hcombo
  rcases hmax_exists (a • ξ + b • ζ) with ⟨z, hzK, hmax⟩
  have hcombo_eq :
      compactSupConvolution lambda K v (a • ξ + b • ζ) =
        supConvolutionKernel lambda v (a • ξ + b • ζ) z :=
    compactSupConvolution_eq_of_isMaxOn hzK hmax
  have hξ_le :
      supConvolutionKernel lambda v ξ z <= compactSupConvolution lambda K v ξ :=
    supConvolutionKernel_le_compactSupConvolution_of_exists_isMaxOn
      (K := K) (u := v) (lambda := lambda) hmax_exists hzK
  have hζ_le :
      supConvolutionKernel lambda v ζ z <= compactSupConvolution lambda K v ζ :=
    supConvolutionKernel_le_compactSupConvolution_of_exists_isMaxOn
      (K := K) (u := v) (lambda := lambda) hmax_exists hzK
  change compactSupConvolution lambda K v (a • ξ + b • ζ) <=
    a * compactSupConvolution lambda K v ξ + b * compactSupConvolution lambda K v ζ +
      (lambda / 2) * a * b * dotProduct (ξ - ζ) (ξ - ζ)
  rw [hcombo_eq, supConvolutionKernel_convex_combination lambda v z ξ ζ hab]
  nlinarith

/--
Compactness and upper semicontinuity supply the maximum points needed for the
semiconvexity of compact sup-convolutions.

In quantified mathematical form, if `K` is nonempty and compact and `v` is
upper semicontinuous on `K`, then
`ξ ↦ compactSupConvolution lambda K v ξ` is semiconvex on all of `R^n` with
constant `lambda`.
-/
theorem coordinateSemiconvexOn_compactSupConvolution_of_isCompact
    {K : Set (Point n)} {v : Point n -> Real} {lambda : Real}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hv : UpperSemicontinuousOn v K) :
    CoordinateSemiconvexOn lambda Set.univ
      (fun ξ : Point n => compactSupConvolution lambda K v ξ) := by
  refine coordinateSemiconvexOn_compactSupConvolution_of_exists_isMaxOn ?_
  intro ξ
  exact exists_isMaxOn_supConvolutionKernel_of_isCompact hKne hKcompact hv

/--
Compact sup-convolutions are continuous.

In quantified mathematical form, if `K` is a nonempty compact subset of
`R^n` and `v` is upper semicontinuous on `K`, then

`ξ ↦ sup { v(x) - (lambda / 2) * ∑ i, (x i - ξ i)^2 | x ∈ K }`

is continuous on `R^n`.
-/
theorem continuous_compactSupConvolution_of_isCompact
    {K : Set (Point n)} {v : Point n -> Real} {lambda : Real}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hv : UpperSemicontinuousOn v K) :
    Continuous (fun ξ : Point n => compactSupConvolution lambda K v ξ) :=
  (coordinateSemiconvexOn_compactSupConvolution_of_isCompact
    hKne hKcompact hv).continuous_univ

/--
Compact inf-convolutions are continuous.

In quantified mathematical form, if `K` is a nonempty compact subset of
`R^n` and `v` is lower semicontinuous on `K`, then

`ξ ↦ inf { v(x) + (lambda / 2) * ∑ i, (x i - ξ i)^2 | x ∈ K }`

is continuous on `R^n`.
-/
theorem continuous_compactInfConvolution_of_isCompact
    {K : Set (Point n)} {v : Point n -> Real} {lambda : Real}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hv : LowerSemicontinuousOn v K) :
    Continuous (fun ξ : Point n => compactInfConvolution lambda K v ξ) := by
  have hvneg : UpperSemicontinuousOn (fun x : Point n => -v x) K :=
    lowerSemicontinuousOn_neg_to_upperSemicontinuousOn hv
  have hsup :
      Continuous (fun ξ : Point n => compactSupConvolution lambda K (fun x => -v x) ξ) :=
    continuous_compactSupConvolution_of_isCompact hKne hKcompact hvneg
  exact hsup.neg

/--
The function whose maximum at the origin is used in the semiconvex matrix
lemma.

In quantified mathematical form, for a function `f : R^n -> R` and a matrix
`B`, this is the function

`ξ ↦ f ξ - (1 / 2) * ∑ i, (B ξ i) * ξ i`.
-/
def semiconvexQuadraticObjective (f : Point n -> Real) (B : Hessian n) :
    Point n -> Real :=
  fun ξ => f ξ - quadraticModel 0 0 0 B ξ

/--
Adding the quadratic function used to convexify a semiconvex function changes
the quadratic matrix in the same amount.

In quantified mathematical form, for every `x : R^n`,

`(f x + (lambda / 2) * ∑ i, x_i^2)
 - (1 / 2) * ⟪(B + lambda I) x, x⟫
 =
 f x - (1 / 2) * ⟪B x, x⟫`.
-/
theorem semiconvexQuadraticObjective_convexification_add_scalar_identity
    (lambda : Real) (f : Point n -> Real) (B : Hessian n) (x : Point n) :
    semiconvexQuadraticObjective (semiconvexConvexification lambda f)
        (B + lambda • (1 : Hessian n)) x =
      semiconvexQuadraticObjective f B x := by
  simp only [semiconvexQuadraticObjective, semiconvexConvexification]
  have hquad :=
    quadraticModel_add (x0 := (0 : Point n)) (r := 0) (s := 0)
      (p := 0) (q := 0) (X := B) (Y := lambda • (1 : Hessian n)) x
  simp only [zero_add] at hquad
  nlinarith

/--
The maximum hypothesis for the semiconvex function is equivalent to the
corresponding maximum hypothesis for its convexification, provided the
quadratic matrix is changed from `B` to `B + lambda I`.
-/
theorem isMaxOn_semiconvexQuadraticObjective_convexification_add_scalar_identity_iff
    (lambda : Real) (f : Point n -> Real) (B : Hessian n)
    (C : Set (Point n)) (x : Point n) :
    IsMaxOn
        (semiconvexQuadraticObjective (semiconvexConvexification lambda f)
          (B + lambda • (1 : Hessian n)))
        C x ↔
      IsMaxOn (semiconvexQuadraticObjective f B) C x := by
  have hfun :
      semiconvexQuadraticObjective (semiconvexConvexification lambda f)
          (B + lambda • (1 : Hessian n)) =
        semiconvexQuadraticObjective f B := by
    funext y
    exact semiconvexQuadraticObjective_convexification_add_scalar_identity lambda f B y
  rw [hfun]

/--
The matrix conclusion in the semiconvex part of the finite-dimensional
maximum principle.

In quantified mathematical form, `SemiconvexMatrixConclusion lambda f B`
means that there exists a matrix `X` such that

* `(0, X) ∈ \overline J^{2,+}_{R^n} f(0)`;
* `-lambda I ≤ X`;
* `X ≤ B`.
-/
def SemiconvexMatrixConclusion (lambda : Real) (f : Point n -> Real)
    (B : Hessian n) : Prop :=
  ∃ X : Hessian n,
    ({ gradient := 0, hessian := X } : Jet n) ∈ ClosedSuperjet Set.univ f 0 ∧
      (-lambda) • (1 : Hessian n) <= X ∧
      X <= B

/--
Closed superjets at the origin transform under subtraction of the quadratic
function used to convexify a semiconvex function.

In quantified mathematical form, if
`(0, Z) ∈ \overline J^{2,+}_{R^n} (f + lambda |x|^2 / 2)(0)`, then
`(0, Z - lambda I) ∈ \overline J^{2,+}_{R^n} f(0)`.
-/
theorem closedSuperjet_of_closedSuperjet_semiconvexConvexification_at_zero
    (lambda : Real) (f : Point n -> Real) (Z : Hessian n)
    (hZ : ({ gradient := 0, hessian := Z } : Jet n) ∈
      ClosedSuperjet Set.univ (semiconvexConvexification lambda f) 0) :
    ({ gradient := 0, hessian := Z - lambda • (1 : Hessian n) } : Jet n) ∈
      ClosedSuperjet Set.univ f 0 := by
  let Q : Point n -> Real :=
    fun x => quadraticModel 0 0 0 (lambda • (1 : Hessian n)) x
  let A : Point n -> Jet n :=
    fun x => quadraticModelJetAt 0 0 (lambda • (1 : Hessian n)) x
  have hshift :
      ({ gradient := 0, hessian := Z } : Jet n) - A 0 ∈ ClosedSuperjet Set.univ f 0 := by
    apply closedSuperjet_sub_of_add_hasSecondOrderExpansionWithin
      (C := Set.univ) (u := f) (φ := Q) (A := A)
    · intro y _hy
      exact hasSecondOrderExpansionWithin_quadraticModel_recenter
        (C := Set.univ) 0 0 0 (lambda • (1 : Hessian n)) y
    · exact continuous_quadraticModel 0 0 0 (lambda • (1 : Hessian n))
    · exact continuous_quadraticModelJetAt 0 0 (lambda • (1 : Hessian n))
    · exact hZ
  have hjet :
      ({ gradient := 0, hessian := Z } : Jet n) - A 0 =
        ({ gradient := 0, hessian := Z - lambda • (1 : Hessian n) } : Jet n) := by
    apply (Jet.equivProd n).injective
    simp [Jet.equivProd, A, quadraticModelJetAt]
  simpa [hjet] using hshift

/--
The matrix conclusion for the convexified function with semiconvexity constant
`0` implies the matrix conclusion for the original function with
semiconvexity constant `lambda`.
-/
theorem SemiconvexMatrixConclusion.of_convexification_zero
    {lambda : Real} {f : Point n -> Real} {B : Hessian n}
    (h : SemiconvexMatrixConclusion 0
      (semiconvexConvexification lambda f) (B + lambda • (1 : Hessian n))) :
    SemiconvexMatrixConclusion lambda f B := by
  rcases h with ⟨Z, hZ, hZnonneg, hZupper⟩
  refine ⟨Z - lambda • (1 : Hessian n), ?_, ?_, ?_⟩
  · exact closedSuperjet_of_closedSuperjet_semiconvexConvexification_at_zero lambda f Z hZ
  · have hnonneg : (0 : Hessian n) <= Z := by
      simpa using hZnonneg
    calc
      (-lambda) • (1 : Hessian n) = (0 : Hessian n) - lambda • (1 : Hessian n) := by
        simp
      _ <= Z - lambda • (1 : Hessian n) := sub_le_sub_right hnonneg _
  · calc
      Z - lambda • (1 : Hessian n) <=
          (B + lambda • (1 : Hessian n)) - lambda • (1 : Hessian n) :=
        sub_le_sub_right hZupper _
      _ = B := by
        abel

/--
The semiconvex matrix lemma used in the proof of the finite-dimensional
maximum principle.

In quantified mathematical form, `SemiconvexMatrixLemmaOn lambda` says that
for every continuous function `f : R^n -> R` and every Hermitian matrix `B`, if

* `0 ≤ lambda`;
* `f` satisfies the coordinate semiconvexity inequality on all of `R^n` with
  constant `lambda`;
* `ξ ↦ f ξ - (1 / 2) * ∑ i, (B ξ i) * ξ i` has a maximum at `0` on all of
  `R^n`;

then there exists a matrix `X` such that
`(0, X) ∈ \overline J^{2,+}_{R^n} f(0)` and
`-lambda I ≤ X ≤ B`.

The proof of this proposition is the Aleksandrov/Jensen part of the
Crandall--Ishii--Lions maximum principle.
-/
def SemiconvexMatrixLemmaOn (lambda : Real) : Prop :=
  0 <= lambda ->
  ∀ f : Point n -> Real, Continuous f ->
  ∀ B : Hessian n, B.IsHermitian ->
    CoordinateSemiconvexOn lambda Set.univ f ->
      IsMaxOn (semiconvexQuadraticObjective f B) Set.univ 0 ->
        SemiconvexMatrixConclusion lambda f B

/--
The semiconvex matrix lemma in the formulation used in the appendix of the
Crandall--Ishii--Lions paper.

In quantified mathematical form, `ConvexifiedSemiconvexMatrixLemmaOn lambda`
says that for every continuous function `f : R^n -> R` and every Hermitian
matrix `B`, if

* `0 ≤ lambda`;
* `x ↦ f x + (lambda / 2) * ∑ i, x_i^2` is convex on all of `R^n`;
* `ξ ↦ f ξ - (1 / 2) * ∑ i, (B ξ i) * ξ i` has a maximum at `0` on all of
  `R^n`;

then there exists a matrix `X` such that
`(0, X) ∈ \overline J^{2,+}_{R^n} f(0)` and
`-lambda I ≤ X ≤ B`.
-/
def ConvexifiedSemiconvexMatrixLemmaOn (lambda : Real) : Prop :=
  0 <= lambda ->
  ∀ f : Point n -> Real, Continuous f ->
  ∀ B : Hessian n, B.IsHermitian ->
    ConvexOn Real Set.univ (semiconvexConvexification lambda f) ->
      IsMaxOn (semiconvexQuadraticObjective f B) Set.univ 0 ->
        SemiconvexMatrixConclusion lambda f B

/--
The paper's convexity formulation of the semiconvex matrix lemma implies the
coordinate-semiconvexity formulation.
-/
theorem SemiconvexMatrixLemmaOn.of_convexified
    {lambda : Real}
    (hlemma : ConvexifiedSemiconvexMatrixLemmaOn (n := n) lambda) :
    SemiconvexMatrixLemmaOn (n := n) lambda := by
  intro hlambda f hf B hB hsemi hmax
  exact hlemma hlambda f hf B hB
    (hsemi.convexOn_semiconvexConvexification convex_univ) hmax

/--
The coordinate-semiconvexity formulation of the semiconvex matrix lemma
implies the paper's convexity formulation.
-/
theorem ConvexifiedSemiconvexMatrixLemmaOn.of_coordinate
    {lambda : Real}
    (hlemma : SemiconvexMatrixLemmaOn (n := n) lambda) :
    ConvexifiedSemiconvexMatrixLemmaOn (n := n) lambda := by
  intro hlambda f hf B hB hconv hmax
  exact hlemma hlambda f hf B hB
    (ConvexOn.coordinateSemiconvexOn_of_semiconvexConvexification hconv) hmax

/--
The coordinate-semiconvexity and convexified formulations of the semiconvex
matrix lemma are equivalent.
-/
theorem semiconvexMatrixLemmaOn_iff_convexifiedSemiconvexMatrixLemmaOn
    {lambda : Real} :
    SemiconvexMatrixLemmaOn (n := n) lambda ↔
      ConvexifiedSemiconvexMatrixLemmaOn (n := n) lambda := by
  constructor
  · exact ConvexifiedSemiconvexMatrixLemmaOn.of_coordinate
  · exact SemiconvexMatrixLemmaOn.of_convexified

/--
Unpack `SemiconvexMatrixConclusion` into the matrix `X` and the two matrix
inequalities.
-/
theorem SemiconvexMatrixConclusion.exists_matrix
    {lambda : Real} {f : Point n -> Real} {B : Hessian n}
    (h : SemiconvexMatrixConclusion lambda f B) :
    ∃ X : Hessian n,
      ({ gradient := 0, hessian := X } : Jet n) ∈ ClosedSuperjet Set.univ f 0 ∧
        (-lambda) • (1 : Hessian n) <= X ∧
        X <= B := h

/--
Apply `SemiconvexMatrixLemmaOn` to a continuous semiconvex function whose
quadratic modification has a maximum at the origin.
-/
theorem SemiconvexMatrixLemmaOn.apply
    {lambda : Real} (hlemma : SemiconvexMatrixLemmaOn (n := n) lambda)
    (hlambda : 0 <= lambda) {f : Point n -> Real} (hf : Continuous f)
    {B : Hessian n} (hB : B.IsHermitian)
    (hsemi : CoordinateSemiconvexOn lambda Set.univ f)
    (hmax : IsMaxOn (semiconvexQuadraticObjective f B) Set.univ 0) :
    SemiconvexMatrixConclusion lambda f B :=
  hlemma hlambda f hf B hB hsemi hmax

/--
Apply `SemiconvexMatrixLemmaOn` using only coordinate semiconvexity on all of
`R^n`.

The continuity hypothesis in `SemiconvexMatrixLemmaOn` is supplied by
`CoordinateSemiconvexOn.continuous_univ`.
-/
theorem SemiconvexMatrixLemmaOn.apply_of_coordinateSemiconvexOn
    {lambda : Real} (hlemma : SemiconvexMatrixLemmaOn (n := n) lambda)
    (hlambda : 0 <= lambda) {f : Point n -> Real}
    {B : Hessian n} (hB : B.IsHermitian)
    (hsemi : CoordinateSemiconvexOn lambda Set.univ f)
    (hmax : IsMaxOn (semiconvexQuadraticObjective f B) Set.univ 0) :
    SemiconvexMatrixConclusion lambda f B :=
  hlemma.apply hlambda hsemi.continuous_univ hB hsemi hmax

/--
Apply the semiconvex matrix lemma to a compact sup-convolution.

In quantified mathematical form, suppose `K` is nonempty and compact,
`v : R^n -> R` is upper semicontinuous on `K`, `0 ≤ lambda`, `B` is
Hermitian, and
`semiconvexQuadraticObjective (ξ ↦ compactSupConvolution lambda K v ξ) B`
has a maximum at `0` on all of `R^n`. If `SemiconvexMatrixLemmaOn lambda`
holds, then there exists a matrix `X` such that

`(0, X) ∈ \overline J^{2,+}_{R^n}
  (ξ ↦ compactSupConvolution lambda K v ξ)(0)`

and `-lambda I ≤ X ≤ B`.
-/
theorem SemiconvexMatrixLemmaOn.compactSupConvolution_of_isCompact
    {lambda : Real} (hlemma : SemiconvexMatrixLemmaOn (n := n) lambda)
    (hlambda : 0 <= lambda) {K : Set (Point n)} {v : Point n -> Real}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hv : UpperSemicontinuousOn v K) {B : Hessian n}
    (hB : B.IsHermitian)
    (hmax : IsMaxOn
      (semiconvexQuadraticObjective
        (fun ξ : Point n => compactSupConvolution lambda K v ξ) B)
      Set.univ 0) :
    SemiconvexMatrixConclusion lambda
      (fun ξ : Point n => compactSupConvolution lambda K v ξ) B := by
  exact hlemma.apply_of_coordinateSemiconvexOn hlambda
    hB
    (coordinateSemiconvexOn_compactSupConvolution_of_isCompact hKne hKcompact hv)
    hmax

end ViscositySolns
