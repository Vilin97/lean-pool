/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Stieltjes.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Concrete Stieltjes endpoint and mass controls
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Each coordinate slice satisfies the source Stieltjes endpoint remainder estimates. -/
def CoordinateSliceSourceRightDerivStieltjesEndpointControl {n : ℕ}
    (u : SourceCubeSpace n → ℝ)
    (hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2))
    (ρ K : ℝ) : Prop :=
  ∀ ⦃x : SourceCubeSpace n⦄, (hx : x ∈ sourceOpenCube n 1) →
      DifferentiableAt ℝ u x →
        ∀ i : Fin n,
          HasSourceRightDerivStieltjesEndpointControl
            (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
            (hmono i hx) ρ K

/-- Exact endpoint identities for the clamped source-local right-derivative Stieltjes slices. -/
def CoordinateSliceSourceRightDerivStieltjesEndpointIdentities {n : ℕ}
    (u : SourceCubeSpace n → ℝ)
    (hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2))
    (ρ : ℝ) : Prop :=
  ∀ ⦃x : SourceCubeSpace n⦄, (hx : x ∈ sourceOpenCube n 1) →
      DifferentiableAt ℝ u x →
        ∀ i : Fin n,
          HasSourceRightDerivStieltjesEndpointIdentities
            (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
            (hmono i hx) ρ

/-- Endpoint comparison bounds for the clamped source-local right-derivative Stieltjes slices. -/
def CoordinateSliceSourceRightDerivStieltjesEndpointBounds {n : ℕ}
    (u : SourceCubeSpace n → ℝ)
    (hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2))
    (ρ : ℝ) : Prop :=
  ∀ ⦃x : SourceCubeSpace n⦄, (hx : x ∈ sourceOpenCube n 1) →
      DifferentiableAt ℝ u x →
        ∀ i : Fin n,
          HasSourceRightDerivStieltjesEndpointBounds
            (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
            (hmono i hx) ρ

/-- Exact endpoint identities imply endpoint comparison bounds slicewise. -/
theorem CoordinateSliceSourceRightDerivStieltjesEndpointIdentities.endpointBounds
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ}
    (hident : CoordinateSliceSourceRightDerivStieltjesEndpointIdentities u hmono ρ) :
    CoordinateSliceSourceRightDerivStieltjesEndpointBounds u hmono ρ := by
  intro x hx hdiff i
  exact (hident hx hdiff i).endpointBounds

/-- Slice-level endpoint comparisons imply slice-level endpoint control with constant `2`, provided
the coordinate slices are convex on the source interval. -/
theorem CoordinateSliceSourceRightDerivStieltjesEndpointBounds.endpointControl
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ}
    (hbounds : CoordinateSliceSourceRightDerivStieltjesEndpointBounds u hmono ρ)
    (hconv :
      ∀ ⦃x : SourceCubeSpace n⦄, (hx : x ∈ sourceOpenCube n 1) →
        DifferentiableAt ℝ u x →
          ∀ i : Fin n,
            ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3)
              (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i)))
    (hρ_le_one : ρ ≤ 1) :
    CoordinateSliceSourceRightDerivStieltjesEndpointControl u hmono ρ 2 := by
  intro x hx hdiff i
  exact HasSourceRightDerivStieltjesEndpointControl.of_endpointBounds
    (hbounds hx hdiff i) (hconv hx hdiff i) hρ_le_one

/-- Slice-level symmetric-remainder estimate for the clamped source-local right-derivative
Stieltjes measures. This is the remaining one-dimensional analytic input before endpoint
control. -/
def CoordinateSliceSourceRightDerivStieltjesSymmetricRemainderBound {n : ℕ}
    (u : SourceCubeSpace n → ℝ)
    (hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2))
    (ρ : ℝ) : Prop :=
  ∀ ⦃x : SourceCubeSpace n⦄, (hx : x ∈ sourceOpenCube n 1) →
      DifferentiableAt ℝ u x →
        ∀ i : Fin n,
          HasOneDimSecondDerivativeSymmetricRemainderBound
            (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
            (sourceRightDerivStieltjesSecondDerivativeMeasure
              (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
              (hmono i hx)) ρ

/-- Slice-level symmetric-remainder estimates imply slice-level endpoint control with constant
`2`. -/
theorem CoordinateSliceSourceRightDerivStieltjesSymmetricRemainderBound.endpointControl
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {ρ : ℝ}
    (hrem : CoordinateSliceSourceRightDerivStieltjesSymmetricRemainderBound u hmono ρ)
    (hρ_le_one : ρ ≤ 1) :
    CoordinateSliceSourceRightDerivStieltjesEndpointControl u hmono ρ 2 := by
  intro x hx hdiff i
  exact HasSourceRightDerivStieltjesEndpointControl.of_symmetricRemainderBound
    (hrem hx hdiff i) hρ_le_one

/-- Endpoint control for the concrete convex source-local Stieltjes slice family. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (ρ K : ℝ) : Prop :=
  CoordinateSliceSourceRightDerivStieltjesEndpointControl u
    (fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy) ρ K

/-- Exact endpoint identities for the concrete convex source-local Stieltjes slice family. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (ρ : ℝ) : Prop :=
  CoordinateSliceSourceRightDerivStieltjesEndpointIdentities u
    (fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy) ρ

/-- Endpoint comparison bounds for the concrete convex source-local Stieltjes slice family. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointBounds {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (ρ : ℝ) : Prop :=
  CoordinateSliceSourceRightDerivStieltjesEndpointBounds u
    (fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy) ρ

namespace CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities

/-- Ambient convexity supplies the concrete slicewise endpoint identities. -/
theorem of_convex
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {ρ : ℝ} (hρ_le_one : ρ ≤ 1) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities u hu ρ := by
  intro x hx _hdiff i
  exact HasSourceRightDerivStieltjesEndpointIdentities.of_convex hρ_le_one
    (ConvexOn.coordinateLineRestriction_sourceCube_three hu i hx)

/-- Concrete convex endpoint identities imply concrete endpoint comparison bounds. -/
theorem endpointBounds
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {ρ : ℝ}
    (hident : CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities u hu ρ) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointBounds u hu ρ :=
  CoordinateSliceSourceRightDerivStieltjesEndpointIdentities.endpointBounds
    (u := u)
    (hmono := fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy)
    hident

end CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities

namespace CoordinateSliceConvexSourceRightDerivStieltjesEndpointBounds

/-- Concrete convex endpoint comparisons imply concrete endpoint control with constant `2`. -/
theorem endpointControl
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {ρ : ℝ}
    (hbounds : CoordinateSliceConvexSourceRightDerivStieltjesEndpointBounds u hu ρ)
    (hρ_le_one : ρ ≤ 1) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl u hu ρ 2 :=
  CoordinateSliceSourceRightDerivStieltjesEndpointBounds.endpointControl
    (u := u)
    (hmono := fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy)
    hbounds
    (fun {_} hx _hdiff i => ConvexOn.coordinateLineRestriction_sourceCube_three hu i hx)
    hρ_le_one

end CoordinateSliceConvexSourceRightDerivStieltjesEndpointBounds

/-- Symmetric-remainder estimates for the concrete convex source-local Stieltjes slice family. -/
def CoordinateSliceConvexSourceRightDerivStieltjesSymmetricRemainderBound {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (ρ : ℝ) : Prop :=
  CoordinateSliceSourceRightDerivStieltjesSymmetricRemainderBound u
    (fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy) ρ

namespace CoordinateSliceConvexSourceRightDerivStieltjesSymmetricRemainderBound

/-- Concrete convex source-local symmetric-remainder estimates imply concrete endpoint control
with constant `2`. -/
theorem endpointControl
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {ρ : ℝ}
    (hrem : CoordinateSliceConvexSourceRightDerivStieltjesSymmetricRemainderBound u hu ρ)
    (hρ_le_one : ρ ≤ 1) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl u hu ρ 2 :=
  CoordinateSliceSourceRightDerivStieltjesSymmetricRemainderBound.endpointControl
    (u := u)
    (hmono := fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy)
    hrem hρ_le_one

end CoordinateSliceConvexSourceRightDerivStieltjesSymmetricRemainderBound

/-- The clamped source-local Stieltjes endpoint input implies the abstract one-dimensional
endpoint-control input expected by `Cube.Maximal`. -/
theorem CoordinateSliceSourceRightDerivStieltjesEndpointControl.coordinateSliceOneDimEndpointControl
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {ρ K : ℝ}
    (hendpoint : CoordinateSliceSourceRightDerivStieltjesEndpointControl u hmono ρ K) :
    CoordinateSliceOneDimEndpointControl u
      (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono) ρ K := by
  classical
  intro x hx hdiff i
  have hbase : coordinateLineBase i x ∈ sourceOpenCube n 1 :=
    coordinateLineBase_mem_sourceOpenCube_one (i := i) hx
  have hbase_idem : coordinateLineBase i (coordinateLineBase i x) = coordinateLineBase i x :=
    coordinateLineBase_idem i x
  simpa [CoordinateSliceSourceRightDerivStieltjesEndpointControl,
    HasSourceRightDerivStieltjesEndpointControl,
    coordinateSliceSourceRightDerivStieltjesMeasureFamily, hbase, hbase_idem]
    using hendpoint hx hdiff i

namespace CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl

/-- Ambient convexity supplies concrete slicewise endpoint control with constant `2`. -/
theorem of_convex
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {ρ : ℝ} (hρ_le_one : ρ ≤ 1) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl u hu ρ 2 :=
  (CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities.endpointBounds
      (CoordinateSliceConvexSourceRightDerivStieltjesEndpointIdentities.of_convex
        (u := u) (hu := hu) hρ_le_one)).endpointControl hρ_le_one

/-- The concrete convex source-local Stieltjes endpoint input implies the abstract
one-dimensional endpoint-control input expected by `Cube.Maximal`. -/
theorem coordinateSliceOneDimEndpointControl
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {ρ K : ℝ}
    (hendpoint : CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl u hu ρ K) :
    CoordinateSliceOneDimEndpointControl u
      (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) ρ K := by
  exact CoordinateSliceSourceRightDerivStieltjesEndpointControl.coordinateSliceOneDimEndpointControl
    (n := n) (u := u)
    (hmono := fun i _ hy => ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy)
    hendpoint

end CoordinateSliceConvexSourceRightDerivStieltjesEndpointControl

/-- Fubini plus clamped source-local Stieltjes source mass bounds give the per-coordinate bad-set
estimate for localized maximal slices. -/
theorem CoordinateSliceMaximalFubiniEstimate.coordinate_bound_of_sourceRightDerivStieltjesMassBound
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {Cmax Ccoord osc t : ℝ}
    (hfubini :
      CoordinateSliceMaximalFubiniEstimate
        (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono)
        (2 * Cmax) Ccoord osc t)
    (hmass :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, (hy : y ∈ sourceOpenCube n 1) →
          HasSourceRightDerivStieltjesSourceMassBound
            (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
            (hmono i hy) osc)
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t) :
    ∀ i : Fin n,
      volume
          (coordinateSliceBadSet
            (coordinateSliceMaximalBadPredicate
              (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono)) i t) ≤
        ENNReal.ofReal (Ccoord * osc / t) :=
  hfubini.coordinate_bound_of_sourceMassBound
    (CoordinateSliceSourceMassBound.of_sourceRightDerivStieltjes hmass) hmax ht

/-- Fubini plus clamped source-local Stieltjes source jump bounds give the per-coordinate bad-set
estimate for localized maximal slices. -/
theorem CoordinateSliceMaximalFubiniEstimate.coordinate_bound_of_sourceRightDerivStieltjesJumpBound
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {Cmax Ccoord osc t : ℝ}
    (hfubini :
      CoordinateSliceMaximalFubiniEstimate
        (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono)
        (2 * Cmax) Ccoord osc t)
    (hjump :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, (hy : y ∈ sourceOpenCube n 1) →
          sourceRightDerivStieltjesSourceJump
            (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
            (hmono i hy) ≤ 2 * osc)
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t) :
    ∀ i : Fin n,
      volume
          (coordinateSliceBadSet
            (coordinateSliceMaximalBadPredicate
              (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono)) i t) ≤
        ENNReal.ofReal (Ccoord * osc / t) :=
  hfubini.coordinate_bound_of_sourceMassBound
    (CoordinateSliceSourceMassBound.of_sourceRightDerivStieltjesJumpBound hjump) hmax ht

/-- Fubini plus symmetric endpoint bounds for clamped source-local Stieltjes functions give the
per-coordinate bad-set estimate for localized maximal slices. -/
theorem CoordinateSliceMaximalFubiniEstimate.coordinate_bound_of_sourceRightDerivStieltjesAbsBounds
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {Cmax Ccoord osc t : ℝ}
    (hfubini :
      CoordinateSliceMaximalFubiniEstimate
        (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono)
        (2 * Cmax) Ccoord osc t)
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
            osc)
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t) :
    ∀ i : Fin n,
      volume
          (coordinateSliceBadSet
            (coordinateSliceMaximalBadPredicate
              (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono)) i t) ≤
        ENNReal.ofReal (Ccoord * osc / t) :=
  hfubini.coordinate_bound_of_sourceMassBound
    (CoordinateSliceSourceMassBound.of_sourceRightDerivStieltjesAbsFunctionBounds
      hlower hupper) hmax ht

/-- Fubini plus endpoint bounds for the ordinary right derivatives of clamped source-local slices
give the per-coordinate bad-set estimate for localized maximal slices. -/
theorem CoordinateSliceMaximalFubiniEstimate.coordinate_bound_of_sourceRightDerivBounds
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {Cmax Ccoord osc t : ℝ}
    (hfubini :
      CoordinateSliceMaximalFubiniEstimate
        (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono)
        (2 * Cmax) Ccoord osc t)
    (hlower :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
          -osc ≤
            rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
              (-2 : ℝ))
    (hupper :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
          rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
              (2 : ℝ) ≤
            osc)
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t) :
    ∀ i : Fin n,
      volume
          (coordinateSliceBadSet
            (coordinateSliceMaximalBadPredicate
              (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono)) i t) ≤
        ENNReal.ofReal (Ccoord * osc / t) :=
  hfubini.coordinate_bound_of_sourceMassBound
    (CoordinateSliceSourceMassBound.of_sourceRightDerivBounds hlower hupper) hmax ht

/-- Fubini plus convexity and endpoint secant bounds for clamped source-local slices give the
per-coordinate bad-set estimate for localized maximal slices. -/
theorem CoordinateSliceMaximalFubiniEstimate.coordinate_bound_of_sourceRightDerivConvexSecantBounds
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {Cmax Ccoord osc t : ℝ}
    (hfubini :
      CoordinateSliceMaximalFubiniEstimate
        (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono)
        (2 * Cmax) Ccoord osc t)
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
              osc + ε)
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t) :
    ∀ i : Fin n,
      volume
          (coordinateSliceBadSet
            (coordinateSliceMaximalBadPredicate
              (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono)) i t) ≤
        ENNReal.ofReal (Ccoord * osc / t) :=
  hfubini.coordinate_bound_of_sourceMassBound
    (CoordinateSliceSourceMassBound.of_sourceRightDerivConvexSecantBounds
      hconv hleft hright) hmax ht

/-- Total bad-set estimate for clamped source-local Stieltjes slices, using convexity and
endpoint secant bounds for the coordinate restrictions to supply the source mass estimate. -/
theorem CoordinateSliceMaximalTotalBadSetEstimate.of_sourceRightDerivConvexSecantBounds
    {n : ℕ} {u : SourceCubeSpace n → ℝ}
    {hmono :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          MonotoneOn
            (rightDeriv (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
            (Set.Icc (-2 : ℝ) 2)}
    {Cmax Ccoord Cmeasure t : ℝ}
    (hdiff : volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hconv :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3)
          (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)))
    (hleft :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ∀ ε : ℝ, 0 < ε →
          ∃ s : ℝ, s ∈ Set.Ioo (-3 : ℝ) (-2) ∧
            -sourceCubeOscillation n u - ε ≤
              slope (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
                s (-2 : ℝ))
    (hright :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ∀ ε : ℝ, 0 < ε →
          ∃ s : ℝ, s ∈ Set.Ioo (2 : ℝ) 3 ∧
            slope (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
                (2 : ℝ) s ≤
              sourceCubeOscillation n u + ε)
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t)
    (hfubini :
      CoordinateSliceMaximalFubiniEstimate
        (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono)
        (2 * Cmax) Ccoord (sourceCubeOscillation n u) t)
    (hbound :
      (n : ENNReal) *
          ENNReal.ofReal (Ccoord * sourceCubeOscillation n u / t) ≤
        ENNReal.ofReal (Cmeasure * sourceCubeOscillation n u / t)) :
    CoordinateSliceMaximalTotalBadSetEstimate u
      (coordinateSliceSourceRightDerivStieltjesMeasureFamily u hmono) Cmeasure t :=
  CoordinateSliceMaximalTotalBadSetEstimate.of_fubiniEstimate
    hdiff
    (CoordinateSliceSourceMassBound.of_sourceRightDerivConvexSecantBounds
      hconv hleft hright)
    hmax ht hfubini hbound

/-- Total bad-set estimate for the concrete convex source-local Stieltjes slice family. Ambient
convexity supplies slice convexity and right-derivative monotonicity; the remaining assumptions
are the source endpoint secant estimates and the Fubini/weak-type bookkeeping. -/
theorem CoordinateSliceMaximalTotalBadSetEstimate.of_convexSourceRightDerivStieltjesSecantBounds
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {Cmax Ccoord Cmeasure t : ℝ}
    (hdiff : volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hleft :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ∀ ε : ℝ, 0 < ε →
          ∃ s : ℝ, s ∈ Set.Ioo (-3 : ℝ) (-2) ∧
            -sourceCubeOscillation n u - ε ≤
              slope (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
                s (-2 : ℝ))
    (hright :
      ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄, y ∈ sourceOpenCube n 1 →
        ∀ ε : ℝ, 0 < ε →
          ∃ s : ℝ, s ∈ Set.Ioo (2 : ℝ) 3 ∧
            slope (lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i))
                (2 : ℝ) s ≤
              sourceCubeOscillation n u + ε)
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t)
    (hfubini :
      CoordinateSliceMaximalFubiniEstimate
        (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
        (2 * Cmax) Ccoord (sourceCubeOscillation n u) t)
    (hbound :
      (n : ENNReal) *
          ENNReal.ofReal (Ccoord * sourceCubeOscillation n u / t) ≤
        ENNReal.ofReal (Cmeasure * sourceCubeOscillation n u / t)) :
    CoordinateSliceMaximalTotalBadSetEstimate u
      (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) Cmeasure t :=
  CoordinateSliceMaximalTotalBadSetEstimate.of_sourceRightDerivConvexSecantBounds
    hdiff (fun i _ hy => ConvexOn.coordinateLineRestriction_sourceCube_three hu i hy)
    hleft hright hmax ht hfubini hbound

/-- Total bad-set estimate for the concrete convex source-local Stieltjes slice family from
ambient convexity, boundedness, the localized maximal theorem, and the Fubini bookkeeping. -/
theorem CoordinateSliceMaximalTotalBadSetEstimate.of_convexSourceRightDerivStieltjes_boundedOn
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {Cmax Ccoord Cmeasure t : ℝ}
    (hdiff : volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t)
    (hfubini :
      CoordinateSliceMaximalFubiniEstimate
        (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
        (2 * Cmax) Ccoord (sourceCubeOscillation n u) t)
    (hbound :
      (n : ENNReal) *
          ENNReal.ofReal (Ccoord * sourceCubeOscillation n u / t) ≤
        ENNReal.ofReal (Cmeasure * sourceCubeOscillation n u / t)) :
    CoordinateSliceMaximalTotalBadSetEstimate u
      (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) Cmeasure t :=
  CoordinateSliceMaximalTotalBadSetEstimate.of_fubiniEstimate
    hdiff
    (CoordinateSliceSourceMassBound.of_convexSourceRightDerivStieltjes_boundedOn hu hbounded)
    hmax ht hfubini hbound

/-- Total bad-set estimate for the concrete convex source-local Stieltjes slice family from
ambient convexity, boundedness, the localized maximal theorem, and the Fubini bookkeeping, with
the finite-union constant supplied as a real coefficient inequality. -/
theorem CoordinateSliceMaximalTotalBadSetEstimate.of_convexStieltjes_boundedOn_measureConstant
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {Cmax Ccoord Cmeasure t : ℝ}
    (hdiff : volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t)
    (hfubini :
      CoordinateSliceMaximalFubiniEstimate
        (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu)
        (2 * Cmax) Ccoord (sourceCubeOscillation n u) t)
    (hmeasure : (n : ℝ) * Ccoord ≤ Cmeasure) :
    CoordinateSliceMaximalTotalBadSetEstimate u
      (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) Cmeasure t :=
  CoordinateSliceMaximalTotalBadSetEstimate.of_fubiniEstimate_of_measureConstant
    hdiff
    (CoordinateSliceSourceMassBound.of_convexSourceRightDerivStieltjes_boundedOn hu hbounded)
    hmax ht hfubini hmeasure hbounded

end AleksandrovDifferentiability
