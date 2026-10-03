/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.MatrixInequalities
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Operators.Comparison
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Operators.Trace

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Operator comparison condition for the Ishii matrix inequality (IshiiCondition)

Part of the specialization of the structural continuity condition for
operators to the matrix relation used in the quadratic doubling-of-variables
argument. Split from `OperatorCondition.lean`; see the umbrella module
docstring.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/-- The zero function is a comparison modulus. -/
theorem comparisonModulus_zero : ComparisonModulus (fun _t : Real => 0) := by
  exact ComparisonModulus.zero

/--
Structural continuity condition with the matrix relation

`-(3 * α) [I 0; 0 I] ≤ [X 0; 0 -Y] ≤ 3 [α I -α I; -α I α I]`.
-/
def IshiiOperatorComparisonConditionOn (C : Set (Point n)) (R : Set Real)
    (F : Operator n) : Prop :=
  OperatorComparisonConditionOn C R IshiiMatrixRelation F

theorem IshiiOperatorComparisonConditionOn.mono_scalar_set
    {C : Set (Point n)} {R S : Set Real} {F : Operator n}
    (hF : IshiiOperatorComparisonConditionOn C S F) (hRS : R ⊆ S) :
    IshiiOperatorComparisonConditionOn C R F :=
  OperatorComparisonConditionOn.mono_scalar_set hF hRS

theorem IshiiOperatorComparisonConditionOn.mono_spatial_set
    {C D : Set (Point n)} {R : Set Real} {F : Operator n}
    (hF : IshiiOperatorComparisonConditionOn D R F) (hCD : C ⊆ D) :
    IshiiOperatorComparisonConditionOn C R F :=
  OperatorComparisonConditionOn.mono_spatial_set hF hCD

/--
Unpack the specialized structural condition.

If `α > 0`, `x, y ∈ C`, `r ∈ R`, and `X`, `Y` satisfy the Ishii block matrix
inequality, then the operator difference is bounded by the comparison modulus.
-/
theorem IshiiOperatorComparisonConditionOn.bound
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    (hF : IshiiOperatorComparisonConditionOn C R F) :
    ∃ ω : Real -> Real, ComparisonModulus ω ∧
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        F y r (quadraticPenaltyGradientLeft α x y) Y -
          F x r (quadraticPenaltyGradientLeft α x y) X <=
            ω (α * ‖x - y‖ ^ 2 + ‖x - y‖) := by
  rcases hF with ⟨ω, hω, hbound⟩
  refine ⟨ω, hω, ?_⟩
  intro α hα x hx y hy r hr X Y hXY
  simpa [quadraticPenaltyGradientLeft] using hbound α hα x hx y hy r hr X Y hXY

/--
If the operator difference in the Ishii structural condition is always
nonpositive, then the condition holds with the zero comparison modulus.
-/
theorem IshiiOperatorComparisonConditionOn.of_nonpositive_difference
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    (hF :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        F y r (quadraticPenaltyGradientLeft α x y) Y -
          F x r (quadraticPenaltyGradientLeft α x y) X <= 0) :
    IshiiOperatorComparisonConditionOn C R F := by
  refine OperatorComparisonConditionOn.of_nonpositive_difference ?_
  intro α hα x hx y hy r hr X Y hXY
  simpa [quadraticPenaltyGradientLeft] using hF α hα x hx y hy r hr X Y hXY

/--
Let `ω` be a comparison modulus which is monotone on real numbers. Suppose
that for every `α > 0`, every `x, y ∈ C`, every `r ∈ R`, and every `X`, `Y`
satisfying `IshiiMatrixRelation α x y X Y`,

`F y r (α • (x - y)) Y - F x r (α • (x - y)) X ≤ ω ‖x - y‖`.

Then `F` satisfies the Ishii structural condition, because
`‖x - y‖ ≤ α * ‖x - y‖ ^ 2 + ‖x - y‖`.
-/
theorem IshiiOperatorComparisonConditionOn.of_norm_bound
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {ω : Real -> Real}
    (hω : ComparisonModulus ω) (hmono : Monotone ω)
    (hbound :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        F y r (quadraticPenaltyGradientLeft α x y) Y -
          F x r (quadraticPenaltyGradientLeft α x y) X <= ω ‖x - y‖) :
    IshiiOperatorComparisonConditionOn C R F := by
  refine OperatorComparisonConditionOn.of_norm_bound hω hmono ?_
  intro α hα x hx y hy r hr X Y hXY
  simpa [quadraticPenaltyGradientLeft] using hbound α hα x hx y hy r hr X Y hXY

/--
Let `F a`, for `a` in a nonempty finite type, be operators. If every `F a`
satisfies the Ishii structural condition on `C` and `R`, then the pointwise
supremum operator

`(x, r, p, X) ↦ max_a F a x r p X`

also satisfies the Ishii structural condition on `C` and `R`.
-/
theorem IshiiOperatorComparisonConditionOn.supOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real} {F : ι -> Operator n}
    (hF : ∀ a : ι, IshiiOperatorComparisonConditionOn C R (F a)) :
    IshiiOperatorComparisonConditionOn C R (supOperator F) :=
  OperatorComparisonConditionOn.supOperator hF

/--
Common-modulus version for finite pointwise suprema.

Suppose one comparison modulus `ω` bounds the Ishii operator difference for
every branch `F a`. Then the pointwise supremum of the finite family `F`
satisfies `IshiiOperatorComparisonConditionOn C R`.
-/
theorem IshiiOperatorComparisonConditionOn.supOperator_of_common_modulus
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real} {F : ι -> Operator n} {ω : Real -> Real}
    (hω : ComparisonModulus ω)
    (hbound :
      ∀ a : ι,
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        F a y r (quadraticPenaltyGradientLeft α x y) Y -
            F a x r (quadraticPenaltyGradientLeft α x y) X <=
          ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)) :
    IshiiOperatorComparisonConditionOn C R (ViscositySolns.supOperator F) := by
  refine OperatorComparisonConditionOn.supOperator_of_common_modulus
    (F := F) (matrixRel := IshiiMatrixRelation) hω ?_
  intro a α hα x hx y hy r hr X Y hXY
  simpa [quadraticPenaltyGradientLeft] using
    hbound a α hα x hx y hy r hr X Y hXY

/--
Let `F a`, for `a` in a nonempty finite type, be operators. If every `F a`
satisfies the Ishii structural condition on `C` and `R`, then the pointwise
infimum operator

`(x, r, p, X) ↦ min_a F a x r p X`

also satisfies the Ishii structural condition on `C` and `R`.
-/
theorem IshiiOperatorComparisonConditionOn.infOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real} {F : ι -> Operator n}
    (hF : ∀ a : ι, IshiiOperatorComparisonConditionOn C R (F a)) :
    IshiiOperatorComparisonConditionOn C R (infOperator F) :=
  OperatorComparisonConditionOn.infOperator hF

/--
Common-modulus version for finite pointwise infima.

Suppose one comparison modulus `ω` bounds the Ishii operator difference for
every branch `F a`. Then the pointwise infimum of the finite family `F`
satisfies `IshiiOperatorComparisonConditionOn C R`.
-/
theorem IshiiOperatorComparisonConditionOn.infOperator_of_common_modulus
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real} {F : ι -> Operator n} {ω : Real -> Real}
    (hω : ComparisonModulus ω)
    (hbound :
      ∀ a : ι,
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        F a y r (quadraticPenaltyGradientLeft α x y) Y -
            F a x r (quadraticPenaltyGradientLeft α x y) X <=
          ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)) :
    IshiiOperatorComparisonConditionOn C R (ViscositySolns.infOperator F) := by
  refine OperatorComparisonConditionOn.infOperator_of_common_modulus
    (F := F) (matrixRel := IshiiMatrixRelation) hω ?_
  intro a α hα x hx y hy r hr X Y hXY
  simpa [quadraticPenaltyGradientLeft] using
    hbound a α hα x hx y hy r hr X Y hXY

/--
If two operators satisfy the Ishii structural comparison condition on the
same set `C` and scalar set `R`, then their pointwise sum satisfies the same
condition.
-/
theorem IshiiOperatorComparisonConditionOn.addOperator
    {C : Set (Point n)} {R : Set Real} {F G : Operator n}
    (hF : IshiiOperatorComparisonConditionOn C R F)
    (hG : IshiiOperatorComparisonConditionOn C R G) :
    IshiiOperatorComparisonConditionOn C R (addOperator F G) :=
  OperatorComparisonConditionOn.addOperator hF hG

/--
If an operator satisfies the Ishii structural comparison condition on `C` and
`R`, then every nonnegative scalar multiple of it satisfies the same condition.
-/
theorem IshiiOperatorComparisonConditionOn.smulOperator_nonneg
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {a : Real}
    (ha : 0 <= a) (hF : IshiiOperatorComparisonConditionOn C R F) :
    IshiiOperatorComparisonConditionOn C R (smulOperator a F) :=
  OperatorComparisonConditionOn.smulOperator_nonneg ha hF

/--
Every constant operator satisfies the Ishii structural comparison condition,
for any spatial set and scalar set.
-/
theorem IshiiOperatorComparisonConditionOn.constOperator
    (C : Set (Point n)) (R : Set Real) (c : Real) :
    IshiiOperatorComparisonConditionOn C R (constOperator (n := n) c) :=
  OperatorComparisonConditionOn.constOperator C R IshiiMatrixRelation c

/--
An operator of the form `F x r p X = G r p`, with no dependence on the
spatial variable `x` or Hessian variable `X`, satisfies the Ishii structural
condition with the zero comparison modulus.
-/
theorem ishiiOperatorComparisonConditionOn_of_independent_spatial_hessian
    (C : Set (Point n)) (R : Set Real) (G : Real -> Point n -> Real) :
    IshiiOperatorComparisonConditionOn C R
      (fun _x : Point n => fun r : Real => fun p : Point n => fun _X : Hessian n =>
        G r p) := by
  refine IshiiOperatorComparisonConditionOn.of_nonpositive_difference ?_
  intro α _hα x _hx y _hy r _hr X Y _hXY
  simp

/--
Let `G r p X` be independent of the spatial variable. Suppose that for every
`r`, `p`, `X`, and `Y`, the implication
`Y ≤ X -> G r p X ≤ G r p Y` holds. Then the operator
`F x r p X = G r p X` satisfies the Ishii structural condition with the zero
comparison modulus.
-/
theorem ishiiOperatorComparisonConditionOn_of_independent_spatial_degenerateElliptic
    (C : Set (Point n)) (R : Set Real) (G : Real -> Point n -> Hessian n -> Real)
    (hG : ∀ r : Real, ∀ p : Point n, ∀ X Y : Hessian n,
      Y <= X -> G r p X <= G r p Y) :
    IshiiOperatorComparisonConditionOn C R
      (fun _x : Point n => fun r : Real => fun p : Point n => fun X : Hessian n =>
        G r p X) := by
  refine IshiiOperatorComparisonConditionOn.of_nonpositive_difference ?_
  intro α _hα x _hx y _hy r _hr X Y hXY
  have hXYle : X <= Y := hXY.left_le_right
  have hmono : G r (quadraticPenaltyGradientLeft α x y) Y <=
      G r (quadraticPenaltyGradientLeft α x y) X :=
    hG r (quadraticPenaltyGradientLeft α x y) Y X hXYle
  simpa using sub_nonpos.mpr hmono

/--
Let `ω` be a monotone comparison modulus. Suppose that for every `x, y ∈ C`
and every `r ∈ R`,

`g y r - g x r ≤ ω ‖x - y‖`.

Then the zero-order operator `F x r p X = g x r` satisfies the Ishii
structural condition.
-/
theorem ishiiOperatorComparisonConditionOn_zeroOrderOperator_of_norm_bound
    {C : Set (Point n)} {R : Set Real} {g : Point n -> Real -> Real}
    {ω : Real -> Real} (hω : ComparisonModulus ω) (hmono : Monotone ω)
    (hg :
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
        g y r - g x r <= ω ‖x - y‖) :
    IshiiOperatorComparisonConditionOn C R (zeroOrderOperator g) := by
  refine IshiiOperatorComparisonConditionOn.of_norm_bound hω hmono ?_
  intro α _hα x hx y hy r hr X Y _hXY
  simpa [zeroOrderOperator, quadraticPenaltyGradientLeft] using hg x hx y hy r hr

/--
Let `G x r p` be a first-order operator expression. Suppose that for every
`α > 0`, every `x, y ∈ C`, every `r ∈ R`, and every `X`, `Y` satisfying
`IshiiMatrixRelation α x y X Y`, one has

`G y r (α • (x - y)) - G x r (α • (x - y))
 ≤ ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)`.

Then the first-order operator `F x r p X = G x r p` satisfies the Ishii
structural condition.
-/
theorem ishiiOperatorComparisonConditionOn_firstOrderOperator_of_bound
    {C : Set (Point n)} {R : Set Real} {G : Point n -> Real -> Point n -> Real}
    {ω : Real -> Real} (hω : ComparisonModulus ω)
    (hG :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        G y r (quadraticPenaltyGradientLeft α x y) -
            G x r (quadraticPenaltyGradientLeft α x y) <=
          ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)) :
    IshiiOperatorComparisonConditionOn C R (firstOrderOperator G) := by
  refine ⟨ω, hω, ?_⟩
  intro α hα x hx y hy r hr X Y hXY
  simpa [firstOrderOperator, quadraticPenaltyGradientLeft] using
    hG α hα x hx y hy r hr X Y hXY

/--
Let `G x X + b x · p + c x * r - f x` be an affine second-order operator.
Assume:

1. for every `z ∈ C`, the Hessian contribution is antitone in the sense that
   `Y ≤ X -> G z X ≤ G z Y`;
2. for every `α > 0`, every `x, y ∈ C`, every `r ∈ R`, and every `X`, `Y`
   satisfying `IshiiMatrixRelation α x y X Y`, the same-Hessian coefficient
   difference satisfies

`(G y X + b y · (α • (x - y)) + c y * r - f y)
 - (G x X + b x · (α • (x - y)) + c x * r - f x)
 ≤ ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)`.

Then the affine second-order operator satisfies the Ishii structural
condition. The proof uses `IshiiMatrixRelation α x y X Y -> X ≤ Y` to
replace the `Y` Hessian in the left operator by the same Hessian `X`.
-/
theorem ishiiOperatorComparisonConditionOn_affineSecondOrderOperator_of_same_hessian_bound
    {C : Set (Point n)} {R : Set Real}
    {G : Point n -> Hessian n -> Real} {b : Point n -> Point n}
    {c f : Point n -> Real} {ω : Real -> Real}
    (hω : ComparisonModulus ω)
    (hG : ∀ z : Point n, z ∈ C ->
      ∀ X Y : Hessian n, Y <= X -> G z X <= G z Y)
    (hbound :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        (G y X + dotProduct (b y) (quadraticPenaltyGradientLeft α x y) +
              c y * r - f y) -
            (G x X + dotProduct (b x) (quadraticPenaltyGradientLeft α x y) +
              c x * r - f x) <=
          ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)) :
    IshiiOperatorComparisonConditionOn C R (affineSecondOrderOperator G b c f) := by
  refine ⟨ω, hω, ?_⟩
  intro α hα x hx y hy r hr X Y hXY
  have hXYle : X <= Y := hXY.left_le_right
  have hGYX : G y Y <= G y X :=
    hG y hy Y X hXYle
  have hcoeff := hbound α hα x hx y hy r hr X Y hXY
  dsimp [affineSecondOrderOperator, quadraticPenaltyGradientLeft] at hcoeff ⊢
  linarith

/--
Let `A` be a positive semidefinite real matrix. Then the constant-coefficient
trace-form operator

`F x r p X = -trace (A * X) + b · p + c * r - f`

satisfies the Ishii structural condition with the zero comparison modulus.
-/
theorem ishiiOperatorComparisonConditionOn_const_traceSecondOrderOperator
    (C : Set (Point n)) (R : Set Real) {A : Hessian n} {b : Point n}
    {c f : Real} (hA : A.PosSemidef) :
    IshiiOperatorComparisonConditionOn C R
      (traceSecondOrderOperator (fun _x : Point n => A)
        (fun _x : Point n => b) (fun _x : Point n => c) (fun _x : Point n => f)) := by
  exact
    ishiiOperatorComparisonConditionOn_of_independent_spatial_degenerateElliptic
      (C := C) (R := R)
      (G := fun r : Real => fun p : Point n => fun X : Hessian n =>
        -Matrix.trace (A * X) + dotProduct b p + c * r - f)
      (by
        intro r p X Y hYX
        have htrace := trace_mul_antitone_of_posSemidef hA X Y hYX
        linarith)

/--
Let `ω` be a comparison modulus. Suppose that:

1. for every `z ∈ C`, the matrix `A z` is positive semidefinite;
2. for every `α > 0`, every `x, y ∈ C`, every `r ∈ R`, and every `X`, `Y`
   satisfying `IshiiMatrixRelation α x y X Y`, the same-Hessian coefficient
   difference satisfies

`(-trace ((A y) * X) + b y · (α • (x - y)) + c y * r - f y)
 - (-trace ((A x) * X) + b x · (α • (x - y)) + c x * r - f x)
 ≤ ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)`.

Then the trace-form operator
`F z r p Z = -trace ((A z) * Z) + b z · p + c z * r - f z`
satisfies the Ishii structural condition. The proof uses
`IshiiMatrixRelation α x y X Y -> X ≤ Y` and the positive semidefiniteness
of `A y` to compare the `Y`-Hessian term with the `X`-Hessian term.
-/
theorem ishiiOperatorComparisonConditionOn_traceSecondOrderOperator_of_same_hessian_bound
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {ω : Real -> Real} (hω : ComparisonModulus ω)
    (hA : ∀ z : Point n, z ∈ C -> (A z).PosSemidef)
    (hbound :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        (-Matrix.trace (A y * X) + dotProduct (b y) (quadraticPenaltyGradientLeft α x y) +
              c y * r - f y) -
            (-Matrix.trace (A x * X) + dotProduct (b x) (quadraticPenaltyGradientLeft α x y) +
              c x * r - f x) <=
          ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)) :
    IshiiOperatorComparisonConditionOn C R (traceSecondOrderOperator A b c f) := by
  refine ⟨ω, hω, ?_⟩
  intro α hα x hx y hy r hr X Y hXY
  have hXYle : X <= Y := hXY.left_le_right
  have htrace :
      -Matrix.trace (A y * Y) <= -Matrix.trace (A y * X) :=
    trace_mul_antitone_of_posSemidef (hA y hy) Y X hXYle
  have hcoeff := hbound α hα x hx y hy r hr X Y hXY
  have hcoeff' :
      -Matrix.trace (A y * X) + dotProduct (b y) (α • (x - y)) + c y * r - f y -
          (-Matrix.trace (A x * X) + dotProduct (b x) (α • (x - y)) + c x * r - f x) <=
        ω (α * ‖x - y‖ ^ 2 + ‖x - y‖) := by
    simpa [quadraticPenaltyGradientLeft] using hcoeff
  dsimp [traceSecondOrderOperator, affineSecondOrderOperator, traceHessianContribution]
  linarith

end ViscositySolns
