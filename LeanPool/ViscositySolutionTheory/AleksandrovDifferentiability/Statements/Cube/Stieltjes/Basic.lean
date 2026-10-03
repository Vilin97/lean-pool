/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Maximal
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.FirstOrder

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Stieltjes coordinate-slice measures on source cubes

This file specializes the abstract coordinate-slice measure family from `Cube.Maximal` to the
Stieltjes measures of the project-local right derivatives of coordinate-line restrictions.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- The concrete coordinate-slice measure family obtained from Stieltjes measures of right
derivatives of coordinate-line restrictions.

The monotonicity hypothesis is global on the line parameter. For the source proof this should
eventually be supplied by applying the Stieltjes construction to a monotone extension of the
right derivative from the source interval `(-3,3)`. -/
def coordinateSliceRightDerivStieltjesMeasureFamily {n : ℕ}
    (u : SourceCubeSpace n → ℝ)
    (hmono :
      ∀ i : Fin n, ∀ y : SourceCubeSpace n,
        Monotone (rightDeriv (lineRestriction u y (sourceCoordinateVector i)))) :
    CoordinateSliceMeasureFamily n :=
  fun i y =>
    rightDerivStieltjesSecondDerivativeMeasure
      (lineRestriction u y (sourceCoordinateVector i)) (hmono i y)

/-- Source mass bounds for the concrete right-derivative Stieltjes slices supply the abstract
coordinate-slice source mass bound used by the localized maximal argument. -/
theorem CoordinateSliceSourceMassBound.of_rightDerivStieltjes {n : ℕ}
    {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ y : SourceCubeSpace n,
        Monotone (rightDeriv (lineRestriction u y (sourceCoordinateVector i)))}
    {osc : ℝ}
    (hmass :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          HasRightDerivStieltjesSourceMassBound
            (lineRestriction u y (sourceCoordinateVector i)) (hmono i y) osc) :
    CoordinateSliceSourceMassBound
      (coordinateSliceRightDerivStieltjesMeasureFamily u hmono) osc := by
  intro i y hy
  exact hmass i hy

/-- Endpoint control for the concrete right-derivative Stieltjes slices. -/
def CoordinateSliceRightDerivStieltjesEndpointControl {n : ℕ}
    (u : SourceCubeSpace n → ℝ)
    (hmono :
      ∀ i : Fin n, ∀ y : SourceCubeSpace n,
        Monotone (rightDeriv (lineRestriction u y (sourceCoordinateVector i))))
    (ρ K : ℝ) : Prop :=
  ∀ ⦃x : SourceCubeSpace n⦄,
    x ∈ sourceOpenCube n 1 →
      DifferentiableAt ℝ u x →
        ∀ i : Fin n,
          HasRightDerivStieltjesEndpointControl
            (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
            (hmono i (coordinateLineBase i x)) ρ K

/-- The concrete right-derivative Stieltjes endpoint input implies the abstract one-dimensional
endpoint-control input expected by `Cube.Maximal`. -/
theorem CoordinateSliceRightDerivStieltjesEndpointControl.coordinateSliceOneDimEndpointControl
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ y : SourceCubeSpace n,
        Monotone (rightDeriv (lineRestriction u y (sourceCoordinateVector i)))}
    {ρ K : ℝ}
    (hendpoint : CoordinateSliceRightDerivStieltjesEndpointControl u hmono ρ K) :
    CoordinateSliceOneDimEndpointControl u
      (coordinateSliceRightDerivStieltjesMeasureFamily u hmono) ρ K := by
  intro x hx hdiff i
  exact hendpoint hx hdiff i

/-- Fubini plus concrete Stieltjes source mass bounds give the per-coordinate bad-set estimate
for localized maximal slices. -/
theorem CoordinateSliceMaximalFubiniEstimate.coordinate_bound_of_rightDerivStieltjesMassBound
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ y : SourceCubeSpace n,
        Monotone (rightDeriv (lineRestriction u y (sourceCoordinateVector i)))}
    {Cmax Ccoord osc t : ℝ}
    (hfubini :
      CoordinateSliceMaximalFubiniEstimate
        (coordinateSliceRightDerivStieltjesMeasureFamily u hmono)
        (2 * Cmax) Ccoord osc t)
    (hmass :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          HasRightDerivStieltjesSourceMassBound
            (lineRestriction u y (sourceCoordinateVector i)) (hmono i y) osc)
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t) :
    ∀ i : Fin n,
      volume
          (coordinateSliceBadSet
            (coordinateSliceMaximalBadPredicate
              (coordinateSliceRightDerivStieltjesMeasureFamily u hmono)) i t) ≤
        ENNReal.ofReal (Ccoord * osc / t) :=
  hfubini.coordinate_bound_of_sourceMassBound
    (CoordinateSliceSourceMassBound.of_rightDerivStieltjes hmass) hmax ht

/-! ## Source-local clamped Stieltjes slices -/

/-- Coordinate-slice measure family obtained from the source-local clamped Stieltjes measure.

Unlike `coordinateSliceRightDerivStieltjesMeasureFamily`, this construction only asks for
monotonicity of the right derivative on the source interval `[-2,2]`, and only for line bases in
`Q_1`. Outside those bases the family is filled with the zero measure, which is harmless for the
source bad sets. -/
def coordinateSliceSourceRightDerivStieltjesMeasureFamily {n : ℕ}
    (u : SourceCubeSpace n → ℝ)
    (hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)) :
    CoordinateSliceMeasureFamily n :=
  fun i y => by
    classical
    exact
      if hy : y ∈ sourceOpenCube n 1 then
        sourceRightDerivStieltjesSecondDerivativeMeasure
          (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)) (hmono i hy)
      else
        0

/-- Source-local clamped Stieltjes slice family with the monotonicity proof supplied by ambient
convexity on `Q_3`. This is the concrete coordinate-slice measure family intended for the
convex source proof. -/
def coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    CoordinateSliceMeasureFamily n :=
  coordinateSliceSourceRightDerivStieltjesMeasureFamily u
    (fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy)

/-- Concrete convex source-local Stieltjes slices have finite mass on every bounded open
interval. -/
theorem coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily_Ioo_lt_top {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (y : SourceCubeSpace n) (a b : ℝ) :
    coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu i y
      (Set.Ioo a b) < ⊤ := by
  classical
  by_cases hy : y ∈ sourceOpenCube n 1
  · simp [coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily,
      coordinateSliceSourceRightDerivStieltjesMeasureFamily, hy,
      sourceRightDerivStieltjesSecondDerivativeMeasure_Ioo_lt_top]
  · simp [coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily,
      coordinateSliceSourceRightDerivStieltjesMeasureFamily, hy]

/-- Product-coordinate measurability obligation for the concrete convex source-local Stieltjes
maximal bad predicate. -/
def CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadPredicateMeasurable {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceMaximalBadPredicateMeasurable
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) t

/-- One-dimensional parameterized source-local maximal measurability for the concrete convex
Stieltjes slice family. -/
def CoordinateSliceConvexSourceRightDerivStieltjesSourceLocalizedMaximalMeasurable {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceSourceLocalizedMaximalMeasurable
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) t

/-- Source-window-restricted one-dimensional maximal measurability for the concrete convex
Stieltjes slice family. -/
def CoordinateSliceConvexSourceRightDerivStieltjesSourceLocalizedMaximalMeasurableOnWindow
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceSourceLocalizedMaximalMeasurableOnWindow
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) t

/-- Interval-average-exceeds measurability for the concrete convex Stieltjes slice family. -/
def CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsMeasurable
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) t

/-- Measurability obligation for the concrete convex source-local Stieltjes maximal bad sets.

This is the source-route analytic measurability input for the Fubini step, specialized to the
coordinate Stieltjes measure family supplied by convexity. -/
def CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceMaximalBadSetMeasurable
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) t

/-- Product-coordinate measurability of the concrete convex source-local Stieltjes maximal
predicate gives measurability of the ambient coordinate maximal bad sets. -/
theorem CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadPredicateMeasurable.badSetMeasurable
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (hbad :
      CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadPredicateMeasurable u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t :=
  CoordinateSliceMaximalBadPredicateMeasurable.badSetMeasurable hbad

namespace CoordinateSliceConvexSourceRightDerivStieltjesSourceLocalizedMaximalMeasurable

/-- Parameterized one-dimensional source-local maximal measurability implies the concrete
product-coordinate maximal bad-predicate measurability. -/
theorem badPredicateMeasurable
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (hbad :
      CoordinateSliceConvexSourceRightDerivStieltjesSourceLocalizedMaximalMeasurable u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadPredicateMeasurable u hu t :=
  CoordinateSliceSourceLocalizedMaximalMeasurable.badPredicateMeasurable hbad

/-- Parameterized one-dimensional source-local maximal measurability implies the concrete
ambient coordinate maximal bad-set measurability. -/
theorem badSetMeasurable
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (hbad :
      CoordinateSliceConvexSourceRightDerivStieltjesSourceLocalizedMaximalMeasurable u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t :=
  CoordinateSliceSourceLocalizedMaximalMeasurable.badSetMeasurable hbad

end CoordinateSliceConvexSourceRightDerivStieltjesSourceLocalizedMaximalMeasurable

namespace CoordinateSliceConvexSourceRightDerivStieltjesSourceLocalizedMaximalMeasurableOnWindow

/-- Source-window-restricted one-dimensional maximal measurability implies the concrete ambient
coordinate maximal bad-set measurability. -/
theorem badSetMeasurable
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (hbad :
      CoordinateSliceConvexSourceRightDerivStieltjesSourceLocalizedMaximalMeasurableOnWindow
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t :=
  CoordinateSliceSourceLocalizedMaximalMeasurableOnWindow.badSetMeasurable hbad

end CoordinateSliceConvexSourceRightDerivStieltjesSourceLocalizedMaximalMeasurableOnWindow

namespace CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable

/-- Interval-average-exceeds measurability implies the concrete ambient coordinate maximal
bad-set measurability. -/
theorem badSetMeasurable
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (havg : CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsMeasurable.badSetMeasurable havg

end CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable

/-- Source mass bounds for the clamped source-local Stieltjes slices supply the abstract
coordinate-slice source mass bound used by the localized maximal argument. -/
theorem CoordinateSliceSourceMassBound.of_sourceRightDerivStieltjes {n : ℕ}
    {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {osc : ℝ}
    (hmass :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, (hy : y ∈ sourceOpenCube n 1) →
          HasSourceRightDerivStieltjesSourceMassBound
            (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
            (hmono i hy) osc) :
    CoordinateSliceSourceMassBound
      (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono) osc := by
  classical
  intro i y hy
  have hfamily :
      coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono i y =
        sourceRightDerivStieltjesSecondDerivativeMeasure
          (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)) (hmono i hy) := by
    simp [coordinateSliceSourceRightDerivStieltjesMeasureFamily, hy]
  rw [hfamily]
  exact hmass i hy

/-- Source jump bounds for the clamped source-local Stieltjes slices supply the abstract
coordinate-slice source mass bound. -/
theorem CoordinateSliceSourceMassBound.of_sourceRightDerivStieltjesJumpBound {n : ℕ}
    {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {osc : ℝ}
    (hjump :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, (hy : y ∈ sourceOpenCube n 1) →
          sourceRightDerivStieltjesSourceJump
            (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
            (hmono i hy) ≤ 2 * osc) :
    CoordinateSliceSourceMassBound
      (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono) osc :=
  CoordinateSliceSourceMassBound.of_sourceRightDerivStieltjes fun i _ hy =>
    HasSourceRightDerivStieltjesSourceMassBound.of_sourceJump_le (hjump i hy)

/-- Symmetric endpoint bounds for the clamped Stieltjes functions of every coordinate slice imply
the abstract coordinate-slice source mass bound. -/
theorem CoordinateSliceSourceMassBound.of_sourceRightDerivStieltjesAbsFunctionBounds {n : ℕ}
    {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {osc : ℝ}
    (hlower :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, (hy : y ∈ sourceOpenCube n 1) →
          -osc ≤
            sourceRightDerivStieltjesSecondDerivativeFunction
              (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
              (hmono i hy) (-2 : ℝ))
    (hupper :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, (hy : y ∈ sourceOpenCube n 1) →
          Function.leftLim
              (sourceRightDerivStieltjesSecondDerivativeFunction
                (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
                (hmono i hy)) (2 : ℝ) ≤
            osc) :
    CoordinateSliceSourceMassBound
      (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono) osc :=
  CoordinateSliceSourceMassBound.of_sourceRightDerivStieltjes fun i _ hy =>
    HasSourceRightDerivStieltjesSourceMassBound.of_abs_function_bound
      (hlower i hy) (hupper i hy)

/-- Endpoint bounds for the ordinary right derivatives of every coordinate slice imply the
abstract coordinate-slice source mass bound. -/
theorem CoordinateSliceSourceMassBound.of_sourceRightDerivBounds {n : ℕ}
    {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {osc : ℝ}
    (hlower :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
          -osc ≤
            rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
              (-2 : ℝ))
    (hupper :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
          rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
              (2 : ℝ) ≤
            osc) :
    CoordinateSliceSourceMassBound
      (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono) osc :=
  CoordinateSliceSourceMassBound.of_sourceRightDerivStieltjes fun i _ hy =>
    HasSourceRightDerivStieltjesSourceMassBound.of_rightDeriv_bounds
      (hlower i hy) (hupper i hy)

/-- Convexity of each coordinate restriction plus endpoint secant bounds supply the abstract
coordinate-slice source mass bound. This is the slice-level form of the source proof's
one-dimensional oscillation-to-mass estimate, before the oscillation hypotheses are proved from
the cube bound. -/
theorem CoordinateSliceSourceMassBound.of_sourceRightDerivConvexSecantBounds {n : ℕ}
    {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {osc : ℝ}
    (hconv :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3)
          (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
    (hleft :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ∀ ε : ℝ, 0 < ε →
          ∃ s : ℝ, s ∈ Set.Ioo (-3 : ℝ) (-2) ∧
            -osc - ε ≤
              slope (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
                s (-2 : ℝ))
    (hright :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ∀ ε : ℝ, 0 < ε →
          ∃ s : ℝ, s ∈ Set.Ioo (2 : ℝ) 3 ∧
            slope (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
                (2 : ℝ) s ≤
              osc + ε) :
    CoordinateSliceSourceMassBound
      (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono) osc :=
  CoordinateSliceSourceMassBound.of_sourceRightDerivStieltjes fun i _ hy =>
    HasSourceRightDerivStieltjesSourceMassBound.of_convex_secant_bounds
      (hconv i hy) (hleft i hy) (hright i hy)

/-- Ambient convexity plus endpoint secant bounds supply the source mass bound for the concrete
convex source-local Stieltjes slice family. -/
theorem CoordinateSliceSourceMassBound.of_convexSourceRightDerivStieltjesSecantBounds {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {osc : ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hleft :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ∀ ε : ℝ, 0 < ε →
          ∃ s : ℝ, s ∈ Set.Ioo (-3 : ℝ) (-2) ∧
            -osc - ε ≤
              slope (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
                s (-2 : ℝ))
    (hright :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ∀ ε : ℝ, 0 < ε →
          ∃ s : ℝ, s ∈ Set.Ioo (2 : ℝ) 3 ∧
            slope (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
                (2 : ℝ) s ≤
              osc + ε) :
    CoordinateSliceSourceMassBound
      (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) osc :=
  CoordinateSliceSourceMassBound.of_sourceRightDerivConvexSecantBounds
    (fun i _ hy => ConvexOn.coordinateLineRestriction_sourceCube_three hu i hy) hleft hright

/-- Along every coordinate slice over a base in `Q_1`, the source-cube oscillation bounds all
one-dimensional value differences on the source interval `(-3,3)`. -/
theorem coordinateLine_pairwiseSub_le_sourceCubeOscillation_of_boundedOn {n : ℕ}
    {u : SourceCubeSpace n → ℝ} (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (i : Fin n) {y : SourceCubeSpace n} (hy : y ∈ sourceOpenCube n 1)
    ⦃s r : ℝ⦄ (hs : s ∈ Set.Ioo (-3 : ℝ) 3) (hr : r ∈ Set.Ioo (-3 : ℝ) 3) :
    lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i) r -
        lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i) s ≤
      sourceCubeOscillation n u := by
  have hdomain :
      lineDomain (sourceOpenCube n 3) (coordinateLineBase i y) (sourceCoordinateVector i) =
        Set.Ioo (-3 : ℝ) 3 :=
    coordinateLineDomain_sourceOpenCube_three_of_mem_sourceOpenCube_one hy
  have hsQ :
      coordinateLinePoint i (coordinateLineBase i y) s ∈ sourceOpenCube n 3 := by
    have hsLine :
        s ∈ lineDomain (sourceOpenCube n 3) (coordinateLineBase i y)
          (sourceCoordinateVector i) := by
      simpa [hdomain] using hs
    simpa [lineDomain, coordinateLinePoint] using hsLine
  have hrQ :
      coordinateLinePoint i (coordinateLineBase i y) r ∈ sourceOpenCube n 3 := by
    have hrLine :
        r ∈ lineDomain (sourceOpenCube n 3) (coordinateLineBase i y)
          (sourceCoordinateVector i) := by
      simpa [hdomain] using hr
    simpa [lineDomain, coordinateLinePoint] using hrLine
  have hval :
      HasSourceCubeValueDifferenceUpperBound n u
        (coordinateLinePoint i (coordinateLineBase i y) s) (sourceCubeOscillation n u) :=
    HasSourceCubeValueDifferenceUpperBound.of_boundedOn_sourceCubeOscillation hsQ hbounded
  simpa [lineRestriction, coordinateLinePoint] using
    hval.2 (coordinateLinePoint i (coordinateLineBase i y) r) hrQ

/-- Ambient convexity and boundedness on `Q_3` supply the source mass bound for the concrete
convex source-local Stieltjes slice family. -/
theorem CoordinateSliceSourceMassBound.of_convexSourceRightDerivStieltjes_boundedOn
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u) :
    CoordinateSliceSourceMassBound
      (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
      (sourceCubeOscillation n u) := by
  refine CoordinateSliceSourceMassBound.of_sourceRightDerivStieltjes fun i y hy => ?_
  exact HasSourceRightDerivStieltjesSourceMassBound.of_convex_pairwise_sub_le
    (ConvexOn.coordinateLineRestriction_sourceCube_three hu i hy)
    (sourceCubeOscillation_nonneg_of_boundedOn hbounded)
    (fun {s} {r} hs hr =>
      coordinateLine_pairwiseSub_le_sourceCubeOscillation_of_boundedOn
        (i := i) (y := y) hbounded hy (s := s) (r := r) hs hr)

end AleksandrovDifferentiability
