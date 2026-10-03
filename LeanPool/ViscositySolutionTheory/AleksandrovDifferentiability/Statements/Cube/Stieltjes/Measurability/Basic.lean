/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Stieltjes.Controls

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Basic measurability interfaces for Stieltjes coordinate-slice measures

This file contains the basic endpoint and countable-interval interfaces used by the concrete
source-local Stieltjes route.
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-! ## Countable interval and endpoint measurability interfaces -/

/-- The left limit of a Stieltjes function is the supremum of its values at rational points
strictly to the left. -/
theorem stieltjesFunction_leftLim_eq_iSup_rat_lt (F : StieltjesFunction ℝ) (c : ℝ) :
    Function.leftLim F c = ⨆ q : {q' : ℚ // (q' : ℝ) < c}, F (q : ℝ) := by
  let A : Set ℝ := F '' Set.Iio c
  have hleft : Function.leftLim F c = sSup A :=
    F.mono.leftLim_eq_sSup
  rw [hleft]
  have hA_nonempty : A.Nonempty := by
    refine ⟨F (c - 1), ?_⟩
    exact ⟨c - 1, by
      change c - 1 < c
      linarith, rfl⟩
  have hA_bdd : BddAbove A := by
    refine ⟨F c, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact F.mono hr.le
  have hrat_bdd :
      BddAbove (Set.range fun q : {q' : ℚ // (q' : ℝ) < c} => F (q : ℝ)) := by
    refine ⟨F c, ?_⟩
    rintro y ⟨q, rfl⟩
    exact F.mono q.property.le
  have : Nonempty {q' : ℚ // (q' : ℝ) < c} := by
    rcases exists_rat_lt c with ⟨q, hq⟩
    exact ⟨⟨q, hq⟩⟩
  apply le_antisymm
  · refine csSup_le hA_nonempty ?_
    rintro y ⟨r, hr, rfl⟩
    rcases exists_rat_btwn (show r < c from hr) with ⟨q, hrq, hqc⟩
    calc
      F r ≤ F (q : ℝ) := F.mono hrq.le
      _ ≤ ⨆ q' : {q' : ℚ // (q' : ℝ) < c}, F (q' : ℝ) :=
        le_ciSup hrat_bdd ⟨q, hqc⟩
  · refine ciSup_le ?_
    intro q
    exact le_csSup hA_bdd ⟨(q : ℝ), q.property, rfl⟩

/-- The right limit of a monotone real function is the infimum of its values at rational points
strictly to the right. -/
theorem monotone_rightLim_eq_iInf_rat_gt {g : ℝ → ℝ} (hg : Monotone g) (c : ℝ) :
    Function.rightLim g c = ⨅ q : {q' : ℚ // c < (q' : ℝ)}, g (q : ℝ) := by
  have hright :
      Function.rightLim g c = ⨅ r : Set.Ioi c, g (r : ℝ) := by
    rw [hg.rightLim_eq_sInf]
    rw [sInf_image']
  have hbdd : BddBelow (g '' Set.Ioi c) := by
    refine ⟨g c, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact hg hr.le
  rw [hright]
  exact Real.iInf_Ioi_eq_iInf_rat_gt c hbdd hg

/-- The clamped source derivative parameter lies strictly inside the source line domain
`(-3, 3)`. -/
theorem sourceDerivativeClamp_mem_Ioo_three (s : ℝ) :
    sourceDerivativeClamp s ∈ Set.Ioo (-3 : ℝ) 3 := by
  have hs := sourceDerivativeClamp_mem_Icc s
  rcases hs with ⟨hleft, hright⟩
  constructor <;> linarith

/-- If `0 < h < 1`, then the forward point from the clamped source derivative parameter also
lies strictly inside the source line domain `(-3, 3)`. -/
theorem sourceDerivativeClamp_add_mem_Ioo_three {s h : ℝ} (hpos : 0 < h) (hlt : h < 1) :
    sourceDerivativeClamp s + h ∈ Set.Ioo (-3 : ℝ) 3 := by
  have hs := sourceDerivativeClamp_mem_Icc s
  rcases hs with ⟨hleft, hright⟩
  constructor <;> linarith

/-- Countable fixed-interval measurability for the concrete convex Stieltjes source-local
average-exceeds sets. -/
def CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (a b : ℕ → ℝ) (t : ℝ) : Prop :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalFamilyMeasurable
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) a b t

/-- Countable fixed-interval cover for the concrete convex Stieltjes source-local
average-exceeds sets. -/
def CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (a b : ℕ → ℝ) (t : ℝ) : Prop :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalCover
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) a b t

/-- Reverse-cover direction for a countable fixed-interval model of the concrete convex
Stieltjes source-local average-exceeds sets. -/
def CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalReverseCover
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (a b : ℕ → ℝ) (t : ℝ) : Prop :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) a b t

/-- Rational refinement target for concrete convex Stieltjes source-local average-exceeds
witnesses. -/
def CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsRationalRefinement
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) t

/-- Inner-rational refinement target for concrete convex Stieltjes source-local average-exceeds
witnesses. -/
def CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalRefinement
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsInnerRationalRefinement
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) t

/-- Sequential inner-rational average approximation target for concrete convex Stieltjes
source-local average-exceeds witnesses. -/
def CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalTendsto
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsInnerRationalTendsto
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) t

/-- Sequential inner-rational mass approximation target for concrete convex Stieltjes
source-local average-exceeds witnesses. -/
def CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalMassTendsto
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) : Prop :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsInnerRationalMassTendsto
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) t

namespace CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalMassTendsto

/-- Concrete convex source-local Stieltjes slices satisfy the sequential inner-rational mass
approximation target. -/
theorem of_convex
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (t : ℝ) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalMassTendsto
      u hu t := by
  intro i
  exact SourceRealIntervalAverageExceedsInnerRationalMassTendsto.of_finiteOnAdmissibleIntervals
    (μparam := coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu i)
    (t := t)
    (fun y {a b} _hab _hsub =>
      coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily_Ioo_lt_top u hu i y a b)

end CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalMassTendsto

/-- Measurability of all fixed-interval average maps for the concrete convex Stieltjes
source-local slice family. -/
def CoordinateSliceConvexSourceRightDerivStieltjesFixedIntervalAverageMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (a b : ℕ → ℝ) : Prop :=
  CoordinateSliceSourceLocalizedMaximalFixedIntervalAverageMeasurable
    (coordinateSliceConvexSourceRightDerivStieltjesMeasureFamily u hu) a b

/-- Right-continuous Stieltjes endpoint value for a concrete convex source-local slice, extended
by zero away from `Q_1`. -/
def coordinateSliceConvexSourceRightDerivStieltjesEndpointValue {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (c : ℝ) (y : SourceCubeSpace n) : ℝ :=
  by
    classical
    exact
      if hy : y ∈ sourceOpenCube n 1 then
        let v := lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)
        let hmono := ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy
        sourceRightDerivStieltjesSecondDerivativeFunction v hmono c
      else
        0

/-- Left-limit Stieltjes endpoint value for a concrete convex source-local slice, extended by zero
away from `Q_1`. -/
def coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimit {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (c : ℝ) (y : SourceCubeSpace n) : ℝ :=
  by
    classical
    exact
      if hy : y ∈ sourceOpenCube n 1 then
        let v := lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)
        let hmono := ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy
        Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono) c
      else
        0

/-- Endpoint expression for a fixed interval average of the concrete convex source-local
Stieltjes slice family. It is zero away from `Q_1`, matching the zero extension in
`coordinateSliceSourceRightDerivStieltjesMeasureFamily`. -/
def coordinateSliceConvexSourceRightDerivStieltjesEndpointAverageExpression {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (a b : ℝ) (y : SourceCubeSpace n) : ℝ :=
  by
    classical
    exact
      if hy : y ∈ sourceOpenCube n 1 then
        let v := lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)
        let hmono := ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy
        (Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono) b -
          sourceRightDerivStieltjesSecondDerivativeFunction v hmono a) / (b - a)
      else
        0

/-- Evaluation of the source-local clamped right-derivative extension for a concrete convex
coordinate slice, extended by zero away from `Q_1`. -/
def coordinateSliceConvexSourceRightDerivExtensionValue {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (_hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (s : ℝ) (y : SourceCubeSpace n) : ℝ :=
  by
    classical
    exact
      if hy : y ∈ sourceOpenCube n 1 then
        let v := lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)
        sourceRightDerivExtension v s
      else
        0

/-- A forward secant slope of a concrete convex coordinate slice, based at the clamped source
parameter and extended by zero away from `Q_1`. -/
def coordinateSliceConvexSourceSecantSlopeValue {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (_hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (s h : ℝ) (y : SourceCubeSpace n) : ℝ :=
  by
    classical
    exact
      if hy : y ∈ sourceOpenCube n 1 then
        let c := sourceDerivativeClamp s
        let v := lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)
        slope v c (c + h)
      else
        0

/-- Rational right-approximation of a Stieltjes representative evaluation by the underlying
clamped right-derivative extension. -/
def coordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApprox {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (s : ℝ) (r : {r' : ℚ // s < (r' : ℝ)})
    (y : SourceCubeSpace n) : ℝ :=
  coordinateSliceConvexSourceRightDerivExtensionValue u hu i (r : ℝ) y

/-- Rational right-approximation of the right-continuous Stieltjes endpoint value. For a fixed
endpoint `c`, the subtype index ranges over rational `q > c`. -/
def coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (c : ℝ) (q : {q' : ℚ // c < (q' : ℝ)})
    (y : SourceCubeSpace n) : ℝ :=
  by
    classical
    exact
      if hy : y ∈ sourceOpenCube n 1 then
        let v := lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)
        let hmono := ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy
        sourceRightDerivStieltjesSecondDerivativeFunction v hmono (q : ℝ)
      else
        0

/-- Rational left-approximation of the Stieltjes endpoint left limit. For a fixed endpoint `c`,
the subtype index ranges over rational `q < c`. -/
def coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (c : ℝ) (q : {q' : ℚ // (q' : ℝ) < c})
    (y : SourceCubeSpace n) : ℝ :=
  by
    classical
    exact
      if hy : y ∈ sourceOpenCube n 1 then
        let v := lineRestriction u (coordinateLineBase i y) (sourceCoordinateVector i)
        let hmono := ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc hu i hy
        sourceRightDerivStieltjesSecondDerivativeFunction v hmono (q : ℝ)
      else
        0

/-- Measurability of one right-continuous Stieltjes endpoint value for a fixed coordinate and
endpoint. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueAtMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (c : ℝ) : Prop :=
  Measurable fun y : SourceCubeSpace n =>
    coordinateSliceConvexSourceRightDerivStieltjesEndpointValue u hu i c y

/-- Measurability of one left-limit Stieltjes endpoint value for a fixed coordinate and
endpoint. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitAtMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (c : ℝ) : Prop :=
  Measurable fun y : SourceCubeSpace n =>
    coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimit u hu i c y

/-- Measurability of one endpoint-average expression for a fixed coordinate and interval. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointAverageAtMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (a b : ℝ) : Prop :=
  Measurable fun y : SourceCubeSpace n =>
    coordinateSliceConvexSourceRightDerivStieltjesEndpointAverageExpression u hu i a b y

/-- Measurability of every rational right-approximation for a fixed coordinate and endpoint. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApproxMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (c : ℝ) : Prop :=
  ∀ q : {q' : ℚ // c < (q' : ℝ)},
    Measurable fun y : SourceCubeSpace n =>
      coordinateSliceConvexSourceRightDerivStieltjesEndpointValueRatApprox u hu i c q y

/-- Measurability of every rational left-approximation for a fixed coordinate and endpoint. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApproxMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (c : ℝ) : Prop :=
  ∀ q : {q' : ℚ // (q' : ℝ) < c},
    Measurable fun y : SourceCubeSpace n =>
      coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitRatApprox u hu i c q y

/-- Measurability of one fixed clamped right-derivative extension evaluation for a concrete
convex coordinate slice. -/
def CoordinateSliceConvexSourceRightDerivExtensionValueAtMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (s : ℝ) : Prop :=
  Measurable fun y : SourceCubeSpace n =>
    coordinateSliceConvexSourceRightDerivExtensionValue u hu i s y

/-- Measurability of all fixed clamped right-derivative extension evaluations for concrete
convex coordinate slices. -/
def CoordinateSliceConvexSourceRightDerivExtensionValueMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    Prop :=
  ∀ i : Fin n, ∀ s : ℝ,
    CoordinateSliceConvexSourceRightDerivExtensionValueAtMeasurable u hu i s

/-- Measurability of one fixed forward secant slope of a concrete convex coordinate slice. -/
def CoordinateSliceConvexSourceSecantSlopeValueAtMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (s h : ℝ) : Prop :=
  Measurable fun y : SourceCubeSpace n =>
    coordinateSliceConvexSourceSecantSlopeValue u hu i s h y

/-- Standard positive forward secant step used to approximate right derivatives. -/
def sourceForwardSecantStep (m : ℕ) : ℝ :=
  ((m + 2 : ℕ) : ℝ)⁻¹

/-- The clamped right-derivative extension is represented as the infimum of the standard
forward secant slopes. This is isolated as the remaining convex-analysis identity needed to turn
secant-slope measurability into clamped-extension measurability. -/
def CoordinateSliceConvexSourceRightDerivExtensionValueSecantApprox
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    Prop :=
  ∀ i : Fin n, ∀ s : ℝ, ∀ y : SourceCubeSpace n,
    coordinateSliceConvexSourceRightDerivExtensionValue u hu i s y =
      ⨅ m : ℕ,
        coordinateSliceConvexSourceSecantSlopeValue u hu i s (sourceForwardSecantStep m) y

/-- Measurability of every rational right-approximation of a Stieltjes evaluation by the
underlying clamped right-derivative extension. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApproxMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) (s : ℝ) : Prop :=
  ∀ r : {r' : ℚ // s < (r' : ℝ)},
    Measurable fun y : SourceCubeSpace n =>
      coordinateSliceConvexSourceRightDerivStieltjesEvaluationExtensionRatApprox u hu i s r y

/-- Measurability of all right-continuous Stieltjes endpoint values for a fixed endpoint
enumeration. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (a : ℕ → ℝ) : Prop :=
  ∀ i : Fin n, ∀ k : ℕ,
    Measurable fun y : SourceCubeSpace n =>
      coordinateSliceConvexSourceRightDerivStieltjesEndpointValue u hu i (a k) y

/-- Measurability of all left-limit Stieltjes endpoint values for a fixed endpoint
enumeration. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (b : ℕ → ℝ) : Prop :=
  ∀ i : Fin n, ∀ k : ℕ,
    Measurable fun y : SourceCubeSpace n =>
      coordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimit u hu i (b k) y

/-- Measurability of the endpoint expressions representing all fixed-interval averages for the
concrete convex Stieltjes source-local slice family. -/
def CoordinateSliceConvexSourceRightDerivStieltjesEndpointAverageMeasurable
    {n : ℕ} (u : SourceCubeSpace n → ℝ) (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (a b : ℕ → ℝ) : Prop :=
  ∀ i : Fin n, ∀ k : ℕ,
    Measurable fun y : SourceCubeSpace n =>
      coordinateSliceConvexSourceRightDerivStieltjesEndpointAverageExpression
        u hu i (a k) (b k) y

/-- Fixed-endpoint measurability for each enumerated endpoint gives the packaged endpoint-value
measurability obligation. -/
theorem CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable.of_at
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a : ℕ → ℝ}
    (h :
      ∀ i : Fin n, ∀ k : ℕ,
        CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueAtMeasurable
          u hu i (a k)) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable u hu a := by
  intro i k
  exact h i k

/-- Fixed-endpoint measurability for each enumerated endpoint gives the packaged endpoint-left
limit measurability obligation. -/
theorem CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable.of_at
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {b : ℕ → ℝ}
    (h :
      ∀ i : Fin n, ∀ k : ℕ,
        CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitAtMeasurable
          u hu i (b k)) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable u hu b := by
  intro i k
  exact h i k

/-- Fixed-interval endpoint-average measurability for each enumerated interval gives the packaged
endpoint-average measurability obligation. -/
theorem CoordinateSliceConvexSourceRightDerivStieltjesEndpointAverageMeasurable.of_at
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ}
    (h :
      ∀ i : Fin n, ∀ k : ℕ,
        CoordinateSliceConvexSourceRightDerivStieltjesEndpointAverageAtMeasurable
          u hu i (a k) (b k)) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointAverageMeasurable u hu a b := by
  intro i k
  exact h i k


end AleksandrovDifferentiability
