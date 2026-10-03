/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.OperatorCondition.IshiiCondition

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Operator comparison condition for the Ishii matrix inequality (TraceForm)

Part of the specialization of the structural continuity condition for
operators to the matrix relation used in the quadratic doubling-of-variables
argument. Split from `OperatorCondition.lean`; see the umbrella module
docstring.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The four component estimates for the trace-form operator

`F z r p Z = -trace ((A z) * Z) + b z · p + c z * r - f z`.

In quantified mathematical form, this predicate says that, for every
`α > 0`, every `x, y ∈ C`, every `r ∈ R`, and every `X`, `Y` satisfying
`IshiiMatrixRelation α x y X Y`, the trace, drift, zeroth-order, and
source-term differences are respectively bounded above by the four comparison
moduli evaluated at `α * ‖x - y‖ ^ 2 + ‖x - y‖`.
-/
def TraceSecondOrderComponentBoundsOn
    (C : Set (Point n)) (R : Set Real)
    (A : Point n -> Hessian n) (b : Point n -> Point n)
    (c f : Point n -> Real) (ωA ωb ωc ωf : Real -> Real) : Prop :=
  (∀ α : Real, 0 < α ->
    ∀ x : Point n, x ∈ C ->
    ∀ y : Point n, y ∈ C ->
    ∀ r : Real, r ∈ R ->
    ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
      -Matrix.trace (A y * X) - (-Matrix.trace (A x * X)) <=
        ωA (α * ‖x - y‖ ^ 2 + ‖x - y‖)) ∧
  (∀ α : Real, 0 < α ->
    ∀ x : Point n, x ∈ C ->
    ∀ y : Point n, y ∈ C ->
    ∀ r : Real, r ∈ R ->
    ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
      dotProduct (b y) (quadraticPenaltyGradientLeft α x y) -
          dotProduct (b x) (quadraticPenaltyGradientLeft α x y) <=
        ωb (α * ‖x - y‖ ^ 2 + ‖x - y‖)) ∧
  (∀ α : Real, 0 < α ->
    ∀ x : Point n, x ∈ C ->
    ∀ y : Point n, y ∈ C ->
    ∀ r : Real, r ∈ R ->
    ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
      c y * r - c x * r <=
        ωc (α * ‖x - y‖ ^ 2 + ‖x - y‖)) ∧
  (∀ α : Real, 0 < α ->
    ∀ x : Point n, x ∈ C ->
    ∀ y : Point n, y ∈ C ->
    ∀ r : Real, r ∈ R ->
    ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
      f x - f y <=
        ωf (α * ‖x - y‖ ^ 2 + ‖x - y‖))

/--
It is enough to prove the four trace-form component estimates with the
moduli evaluated at `‖x - y‖`, provided the four moduli are monotone.

Indeed, if `α > 0`, then
`‖x - y‖ ≤ α * ‖x - y‖ ^ 2 + ‖x - y‖`.
-/
theorem TraceSecondOrderComponentBoundsOn.of_norm_bounds
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {ωA ωb ωc ωf : Real -> Real}
    (hmonoA : Monotone ωA) (hmonob : Monotone ωb)
    (hmonoc : Monotone ωc) (hmonof : Monotone ωf)
    (htrace :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        -Matrix.trace (A y * X) - (-Matrix.trace (A x * X)) <= ωA ‖x - y‖)
    (hb :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        dotProduct (b y) (quadraticPenaltyGradientLeft α x y) -
            dotProduct (b x) (quadraticPenaltyGradientLeft α x y) <= ωb ‖x - y‖)
    (hc :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        c y * r - c x * r <= ωc ‖x - y‖)
    (hf :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        f x - f y <= ωf ‖x - y‖) :
    TraceSecondOrderComponentBoundsOn C R A b c f ωA ωb ωc ωf := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α hα x hx y hy r hr X Y hXY
    refine le_trans (htrace α hα x hx y hy r hr X Y hXY) (hmonoA ?_)
    have hsq : 0 <= ‖x - y‖ ^ 2 := sq_nonneg ‖x - y‖
    have hmul : 0 <= α * ‖x - y‖ ^ 2 := mul_nonneg hα.le hsq
    linarith
  · intro α hα x hx y hy r hr X Y hXY
    refine le_trans (hb α hα x hx y hy r hr X Y hXY) (hmonob ?_)
    have hsq : 0 <= ‖x - y‖ ^ 2 := sq_nonneg ‖x - y‖
    have hmul : 0 <= α * ‖x - y‖ ^ 2 := mul_nonneg hα.le hsq
    linarith
  · intro α hα x hx y hy r hr X Y hXY
    refine le_trans (hc α hα x hx y hy r hr X Y hXY) (hmonoc ?_)
    have hsq : 0 <= ‖x - y‖ ^ 2 := sq_nonneg ‖x - y‖
    have hmul : 0 <= α * ‖x - y‖ ^ 2 := mul_nonneg hα.le hsq
    linarith
  · intro α hα x hx y hy r hr X Y hXY
    refine le_trans (hf α hα x hx y hy r hr X Y hXY) (hmonof ?_)
    have hsq : 0 <= ‖x - y‖ ^ 2 := sq_nonneg ‖x - y‖
    have hmul : 0 <= α * ‖x - y‖ ^ 2 := mul_nonneg hα.le hsq
    linarith

/--
Let `A`, `b`, `c`, and `f` define the trace-form operator

`F z r p Z = -trace ((A z) * Z) + b z · p + c z * r - f z`.

Suppose that `A z` is positive semidefinite for every `z ∈ C`. Suppose also
that there are comparison moduli `ωA`, `ωb`, `ωc`, and `ωf` such that, for
every `α > 0`, every `x, y ∈ C`, every `r ∈ R`, and every `X`, `Y`
satisfying `IshiiMatrixRelation α x y X Y`, the following four inequalities
hold, where `s = α * ‖x - y‖ ^ 2 + ‖x - y‖`:

* `-trace ((A y) * X) - (-trace ((A x) * X)) ≤ ωA s`;
* `b y · (α • (x - y)) - b x · (α • (x - y)) ≤ ωb s`;
* `c y * r - c x * r ≤ ωc s`;
* `f x - f y ≤ ωf s`.

Then `F` satisfies the Ishii structural condition on `C` and `R`.
-/
theorem ishiiOperatorComparisonConditionOn_traceSecondOrderOperator_of_component_bounds
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {ωA ωb ωc ωf : Real -> Real}
    (hωA : ComparisonModulus ωA) (hωb : ComparisonModulus ωb)
    (hωc : ComparisonModulus ωc) (hωf : ComparisonModulus ωf)
    (hA : ∀ z : Point n, z ∈ C -> (A z).PosSemidef)
    (htrace :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        -Matrix.trace (A y * X) - (-Matrix.trace (A x * X)) <=
          ωA (α * ‖x - y‖ ^ 2 + ‖x - y‖))
    (hb :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        dotProduct (b y) (quadraticPenaltyGradientLeft α x y) -
            dotProduct (b x) (quadraticPenaltyGradientLeft α x y) <=
          ωb (α * ‖x - y‖ ^ 2 + ‖x - y‖))
    (hc :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        c y * r - c x * r <=
          ωc (α * ‖x - y‖ ^ 2 + ‖x - y‖))
    (hf :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        f x - f y <=
          ωf (α * ‖x - y‖ ^ 2 + ‖x - y‖)) :
    IshiiOperatorComparisonConditionOn C R (traceSecondOrderOperator A b c f) := by
  let ω : Real -> Real := fun t : Real => ((ωA t + ωb t) + ωc t) + ωf t
  have hω : ComparisonModulus ω :=
    (hωA.add hωb).add hωc |>.add hωf
  refine ishiiOperatorComparisonConditionOn_traceSecondOrderOperator_of_same_hessian_bound
    (ω := ω) hω hA ?_
  intro α hα x hx y hy r hr X Y hXY
  have htrace' := htrace α hα x hx y hy r hr X Y hXY
  have hb' := hb α hα x hx y hy r hr X Y hXY
  have hc' := hc α hα x hx y hy r hr X Y hXY
  have hf' := hf α hα x hx y hy r hr X Y hXY
  dsimp [ω]
  linarith

/--
Packaged form of
`ishiiOperatorComparisonConditionOn_traceSecondOrderOperator_of_component_bounds`.
-/
theorem TraceSecondOrderComponentBoundsOn.ishiiOperatorComparisonConditionOn
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {ωA ωb ωc ωf : Real -> Real}
    (hωA : ComparisonModulus ωA) (hωb : ComparisonModulus ωb)
    (hωc : ComparisonModulus ωc) (hωf : ComparisonModulus ωf)
    (hA : ∀ z : Point n, z ∈ C -> (A z).PosSemidef)
    (hbounds : TraceSecondOrderComponentBoundsOn C R A b c f ωA ωb ωc ωf) :
    IshiiOperatorComparisonConditionOn C R (traceSecondOrderOperator A b c f) := by
  exact ishiiOperatorComparisonConditionOn_traceSecondOrderOperator_of_component_bounds
    hωA hωb hωc hωf hA hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2

/--
Direct trace-form constructor from component estimates stated at the distance
scale `‖x - y‖`.

Assume the four component differences of the trace-form operator are bounded
above by monotone comparison moduli evaluated at `‖x - y‖`. If `A z` is
positive semidefinite for every `z ∈ C`, then the trace-form operator
satisfies `IshiiOperatorComparisonConditionOn C R`.
-/
theorem ishiiOperatorComparisonConditionOn_traceSecondOrderOperator_of_component_norm_bounds
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {ωA ωb ωc ωf : Real -> Real}
    (hωA : ComparisonModulus ωA) (hωb : ComparisonModulus ωb)
    (hωc : ComparisonModulus ωc) (hωf : ComparisonModulus ωf)
    (hmonoA : Monotone ωA) (hmonob : Monotone ωb)
    (hmonoc : Monotone ωc) (hmonof : Monotone ωf)
    (hA : ∀ z : Point n, z ∈ C -> (A z).PosSemidef)
    (htrace :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        -Matrix.trace (A y * X) - (-Matrix.trace (A x * X)) <= ωA ‖x - y‖)
    (hb :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        dotProduct (b y) (quadraticPenaltyGradientLeft α x y) -
            dotProduct (b x) (quadraticPenaltyGradientLeft α x y) <= ωb ‖x - y‖)
    (hc :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        c y * r - c x * r <= ωc ‖x - y‖)
    (hf :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        f x - f y <= ωf ‖x - y‖) :
    IshiiOperatorComparisonConditionOn C R (traceSecondOrderOperator A b c f) := by
  exact (TraceSecondOrderComponentBoundsOn.of_norm_bounds
    hmonoA hmonob hmonoc hmonof htrace hb hc hf).ishiiOperatorComparisonConditionOn
      hωA hωb hωc hωf hA

/--
Packaged hypotheses for a trace-form second-order operator on a spatial set
`C` and scalar set `R`.

In quantified mathematical form, this structure consists of:

* four comparison moduli `ωA`, `ωb`, `ωc`, and `ωf`;
* positive semidefiniteness of `A z` for every point `z`;
* nonnegativity of `c z` for every point `z`;
* continuity of the trace-form operator;
* the four component estimates in `TraceSecondOrderComponentBoundsOn C R`.

These hypotheses imply properness, operator continuity, and
`IshiiOperatorComparisonConditionOn C R` for
`traceSecondOrderOperator A b c f`.
-/
structure TraceSecondOrderOperatorComparisonHypothesesOn
    (C : Set (Point n)) (R : Set Real)
    (A : Point n -> Hessian n) (b : Point n -> Point n)
    (c f : Point n -> Real) where
  /-- Comparison modulus for the second-order coefficient. -/
  ωA : Real -> Real
  /-- Comparison modulus for the drift coefficient. -/
  ωb : Real -> Real
  /-- Comparison modulus for the zero-order coefficient. -/
  ωc : Real -> Real
  /-- Comparison modulus for the source term. -/
  ωf : Real -> Real
  comparisonModulus_trace : ComparisonModulus ωA
  comparisonModulus_drift : ComparisonModulus ωb
  comparisonModulus_zeroth : ComparisonModulus ωc
  comparisonModulus_source : ComparisonModulus ωf
  positive_semidefinite : ∀ z : Point n, (A z).PosSemidef
  zeroth_nonnegative : ∀ z : Point n, 0 <= c z
  operator_continuous : OperatorContinuous (traceSecondOrderOperator A b c f)
  component_bounds : TraceSecondOrderComponentBoundsOn C R A b c f ωA ωb ωc ωf

/--
Constructor for the packaged trace-form comparison hypotheses from component
estimates stated at the comparison scale
`α * ‖x - y‖ ^ 2 + ‖x - y‖`.
-/
def TraceSecondOrderOperatorComparisonHypothesesOn.ofComponentBounds
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {ωA ωb ωc ωf : Real -> Real}
    (hωA : ComparisonModulus ωA) (hωb : ComparisonModulus ωb)
    (hωc : ComparisonModulus ωc) (hωf : ComparisonModulus ωf)
    (hA : ∀ z : Point n, (A z).PosSemidef)
    (hc : ∀ z : Point n, 0 <= c z)
    (hcont : OperatorContinuous (traceSecondOrderOperator A b c f))
    (hbounds : TraceSecondOrderComponentBoundsOn C R A b c f ωA ωb ωc ωf) :
    TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f where
  ωA := ωA
  ωb := ωb
  ωc := ωc
  ωf := ωf
  comparisonModulus_trace := hωA
  comparisonModulus_drift := hωb
  comparisonModulus_zeroth := hωc
  comparisonModulus_source := hωf
  positive_semidefinite := hA
  zeroth_nonnegative := hc
  operator_continuous := hcont
  component_bounds := hbounds

/--
Constructor for the packaged trace-form comparison hypotheses from component
estimates stated at the distance scale `‖x - y‖`.

In quantified mathematical form, if the four moduli are monotone and each of
the four component differences is bounded above by the corresponding modulus
evaluated at `‖x - y‖`, then the component estimates at
`α * ‖x - y‖ ^ 2 + ‖x - y‖` follow, and hence the packaged trace-form
hypotheses hold.
-/
def TraceSecondOrderOperatorComparisonHypothesesOn.ofComponentNormBounds
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {ωA ωb ωc ωf : Real -> Real}
    (hωA : ComparisonModulus ωA) (hωb : ComparisonModulus ωb)
    (hωc : ComparisonModulus ωc) (hωf : ComparisonModulus ωf)
    (hmonoA : Monotone ωA) (hmonob : Monotone ωb)
    (hmonoc : Monotone ωc) (hmonof : Monotone ωf)
    (hA : ∀ z : Point n, (A z).PosSemidef)
    (hc_nonneg : ∀ z : Point n, 0 <= c z)
    (hcont : OperatorContinuous (traceSecondOrderOperator A b c f))
    (htrace :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        -Matrix.trace (A y * X) - (-Matrix.trace (A x * X)) <= ωA ‖x - y‖)
    (hb :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        dotProduct (b y) (quadraticPenaltyGradientLeft α x y) -
            dotProduct (b x) (quadraticPenaltyGradientLeft α x y) <= ωb ‖x - y‖)
    (hc :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        c y * r - c x * r <= ωc ‖x - y‖)
    (hf :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        f x - f y <= ωf ‖x - y‖) :
    TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f :=
  TraceSecondOrderOperatorComparisonHypothesesOn.ofComponentBounds
    hωA hωb hωc hωf hA hc_nonneg hcont
    (TraceSecondOrderComponentBoundsOn.of_norm_bounds
      hmonoA hmonob hmonoc hmonof htrace hb hc hf)

/--
Constructor for the packaged trace-form comparison hypotheses from component
estimates and continuity of the four graph-space summands.

In quantified mathematical form, the continuity hypotheses are continuity of
the functions

* `(x, r, p, X) ↦ -trace ((A x) * X)`;
* `(x, r, p, X) ↦ b x · p`;
* `(x, r, p, X) ↦ c x * r`;
* `(x, r, p, X) ↦ f x`.

Together with the component estimates at
`α * ‖x - y‖ ^ 2 + ‖x - y‖`, these hypotheses construct
`TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f`.
-/
def TraceSecondOrderOperatorComparisonHypothesesOn.ofBoundsAndContinuousSummands
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {ωA ωb ωc ωf : Real -> Real}
    (hωA : ComparisonModulus ωA) (hωb : ComparisonModulus ωb)
    (hωc : ComparisonModulus ωc) (hωf : ComparisonModulus ωf)
    (hA : ∀ z : Point n, (A z).PosSemidef)
    (hc_nonneg : ∀ z : Point n, 0 <= c z)
    (hAcont : Continuous fun z : (Point n × Real) × Jet n =>
      -Matrix.trace (A z.1.1 * z.2.hessian))
    (hbcont : Continuous fun z : (Point n × Real) × Jet n =>
      dotProduct (b z.1.1) z.2.gradient)
    (hccont : Continuous fun z : (Point n × Real) × Jet n => c z.1.1 * z.1.2)
    (hfcont : Continuous fun z : (Point n × Real) × Jet n => f z.1.1)
    (hbounds : TraceSecondOrderComponentBoundsOn C R A b c f ωA ωb ωc ωf) :
    TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f :=
  TraceSecondOrderOperatorComparisonHypothesesOn.ofComponentBounds
    hωA hωb hωc hωf hA hc_nonneg
    (operatorContinuous_traceSecondOrderOperator hAcont hbcont hccont hfcont)
    hbounds

/--
Constructor for the packaged trace-form comparison hypotheses from component
estimates stated at the distance scale `‖x - y‖` and continuity of the four
graph-space summands.
-/
def TraceSecondOrderOperatorComparisonHypothesesOn.ofNormBoundsAndContinuousSummands
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {ωA ωb ωc ωf : Real -> Real}
    (hωA : ComparisonModulus ωA) (hωb : ComparisonModulus ωb)
    (hωc : ComparisonModulus ωc) (hωf : ComparisonModulus ωf)
    (hmonoA : Monotone ωA) (hmonob : Monotone ωb)
    (hmonoc : Monotone ωc) (hmonof : Monotone ωf)
    (hA : ∀ z : Point n, (A z).PosSemidef)
    (hc_nonneg : ∀ z : Point n, 0 <= c z)
    (hAcont : Continuous fun z : (Point n × Real) × Jet n =>
      -Matrix.trace (A z.1.1 * z.2.hessian))
    (hbcont : Continuous fun z : (Point n × Real) × Jet n =>
      dotProduct (b z.1.1) z.2.gradient)
    (hccont : Continuous fun z : (Point n × Real) × Jet n => c z.1.1 * z.1.2)
    (hfcont : Continuous fun z : (Point n × Real) × Jet n => f z.1.1)
    (htrace :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        -Matrix.trace (A y * X) - (-Matrix.trace (A x * X)) <= ωA ‖x - y‖)
    (hb :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        dotProduct (b y) (quadraticPenaltyGradientLeft α x y) -
            dotProduct (b x) (quadraticPenaltyGradientLeft α x y) <= ωb ‖x - y‖)
    (hc :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        c y * r - c x * r <= ωc ‖x - y‖)
    (hf :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, IshiiMatrixRelation α x y X Y ->
        f x - f y <= ωf ‖x - y‖) :
    TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f :=
  TraceSecondOrderOperatorComparisonHypothesesOn.ofComponentNormBounds
    hωA hωb hωc hωf hmonoA hmonob hmonoc hmonof hA hc_nonneg
    (operatorContinuous_traceSecondOrderOperator hAcont hbcont hccont hfcont)
    htrace hb hc hf

theorem TraceSecondOrderOperatorComparisonHypothesesOn.proper
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f) :
    Proper (traceSecondOrderOperator A b c f) :=
  proper_traceSecondOrderOperator_of_posSemidef h.positive_semidefinite h.zeroth_nonnegative

theorem TraceSecondOrderOperatorComparisonHypothesesOn.ishiiOperatorComparisonConditionOn
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f) :
    IshiiOperatorComparisonConditionOn C R (traceSecondOrderOperator A b c f) :=
  h.component_bounds.ishiiOperatorComparisonConditionOn
    h.comparisonModulus_trace h.comparisonModulus_drift
    h.comparisonModulus_zeroth h.comparisonModulus_source
    (fun z _hz => h.positive_semidefinite z)

/--
Finite pointwise suprema of trace-form operators satisfy the Ishii structural
condition when every branch satisfies the packaged trace-form hypotheses.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.ishii_supOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real}
    {A : ι -> Point n -> Hessian n} {b : ι -> Point n -> Point n}
    {c f : ι -> Point n -> Real}
    (h : ∀ a : ι, TraceSecondOrderOperatorComparisonHypothesesOn C R
      (A a) (b a) (c a) (f a)) :
    IshiiOperatorComparisonConditionOn C R
      (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) :=
  IshiiOperatorComparisonConditionOn.supOperator fun a =>
    (h a).ishiiOperatorComparisonConditionOn

/--
Finite pointwise suprema of trace-form operators are proper when every branch
satisfies the packaged trace-form hypotheses.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.proper_supOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real}
    {A : ι -> Point n -> Hessian n} {b : ι -> Point n -> Point n}
    {c f : ι -> Point n -> Real}
    (h : ∀ a : ι, TraceSecondOrderOperatorComparisonHypothesesOn C R
      (A a) (b a) (c a) (f a)) :
    Proper
      (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) :=
  Proper.supOperator fun a => (h a).proper

/--
Finite pointwise suprema of trace-form operators are continuous when every
branch satisfies the packaged trace-form hypotheses.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.operatorContinuous_supOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real}
    {A : ι -> Point n -> Hessian n} {b : ι -> Point n -> Point n}
    {c f : ι -> Point n -> Real}
    (h : ∀ a : ι, TraceSecondOrderOperatorComparisonHypothesesOn C R
      (A a) (b a) (c a) (f a)) :
    OperatorContinuous
      (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) :=
  OperatorContinuous.supOperator fun a => (h a).operator_continuous

/--
Finite pointwise infima of trace-form operators satisfy the Ishii structural
condition when every branch satisfies the packaged trace-form hypotheses.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.ishii_infOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real}
    {A : ι -> Point n -> Hessian n} {b : ι -> Point n -> Point n}
    {c f : ι -> Point n -> Real}
    (h : ∀ a : ι, TraceSecondOrderOperatorComparisonHypothesesOn C R
      (A a) (b a) (c a) (f a)) :
    IshiiOperatorComparisonConditionOn C R
      (infOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) :=
  IshiiOperatorComparisonConditionOn.infOperator fun a =>
    (h a).ishiiOperatorComparisonConditionOn

/--
Finite pointwise infima of trace-form operators are proper when every branch
satisfies the packaged trace-form hypotheses.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.proper_infOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real}
    {A : ι -> Point n -> Hessian n} {b : ι -> Point n -> Point n}
    {c f : ι -> Point n -> Real}
    (h : ∀ a : ι, TraceSecondOrderOperatorComparisonHypothesesOn C R
      (A a) (b a) (c a) (f a)) :
    Proper
      (infOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) :=
  Proper.infOperator fun a => (h a).proper

/--
Finite pointwise infima of trace-form operators are continuous when every
branch satisfies the packaged trace-form hypotheses.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.operatorContinuous_infOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real}
    {A : ι -> Point n -> Hessian n} {b : ι -> Point n -> Point n}
    {c f : ι -> Point n -> Real}
    (h : ∀ a : ι, TraceSecondOrderOperatorComparisonHypothesesOn C R
      (A a) (b a) (c a) (f a)) :
    OperatorContinuous
      (infOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) :=
  OperatorContinuous.infOperator fun a => (h a).operator_continuous

end ViscositySolns
