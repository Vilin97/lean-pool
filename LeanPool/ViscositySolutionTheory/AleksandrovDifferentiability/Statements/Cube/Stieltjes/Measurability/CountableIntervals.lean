/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Stieltjes.Measurability.Endpoint

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Countable interval reductions for Stieltjes coordinate-slice maximal sets

This file connects endpoint-average measurability to fixed-interval average maps and the
countable interval formulation of the source-local maximal bad sets.
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace AleksandrovDifferentiability

namespace CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableInterval

/-- Endpoint-value and endpoint-left-limit measurability gives endpoint-average measurability. -/
theorem endpointAverageMeasurable_of_endpointValue_leftLimit
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ}
    (hleft :
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointLeftLimitMeasurable u hu b)
    (hvalue :
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointValueMeasurable u hu a) :
    CoordinateSliceConvexSourceRightDerivStieltjesEndpointAverageMeasurable u hu a b :=
  CoordinateSliceStieltjesEndpointAverageMeasurable.of_endpointValue_leftLimit hleft hvalue

/-- Endpoint-expression measurability gives fixed-interval average-map measurability for genuine
intervals. -/
theorem fixedIntervalAverageMeasurable_of_endpointAverage
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ}
    (hab : ∀ k : ℕ, a k < b k)
    (hend :
      CoordinateSliceConvexSourceRightDerivStieltjesEndpointAverageMeasurable u hu a b) :
    CoordinateSliceConvexSourceRightDerivStieltjesFixedIntervalAverageMeasurable u hu a b := by
  intro i k
  convert hend i k using 1
  ext y
  exact coordinateSliceConvexSourceRightDerivStieltjes_average_eq_endpointAverageExpression
    i (hab k) y

/-- Measurable fixed-interval average maps give the concrete convex Stieltjes countable-interval
measurability input. -/
theorem measurable_of_averageMaps
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (havg :
      CoordinateSliceConvexSourceRightDerivStieltjesFixedIntervalAverageMeasurable u hu a b) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
      u hu a b t :=
  CoordinateSliceAverageExceedsCountableIntervalFamily.of_measurableAverage havg

/-- An admissible interval enumeration and the concrete reverse-cover direction give the
countable fixed-interval representation for convex Stieltjes slices. -/
theorem cover_of_reverseCover
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hadm : SourceAdmissibleIntervalEnumeration a b)
    (hreverse :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalReverseCover
        u hu a b t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
      u hu a b t :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalCover.of_reverseCover
    hadm hreverse

/-- A rational interval enumeration and rational refinement give the concrete reverse-cover
direction for convex Stieltjes slices. -/
theorem reverseCover_of_rationalRefinement
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (hrefine :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsRationalRefinement
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalReverseCover
      u hu a b t :=
  by
    open CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover in
    exact of_rationalRefinement henum hrefine

/-- Inner-rational refinement gives the concrete rational-refinement target for convex Stieltjes
slices. -/
theorem rationalRefinement_of_inner
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (hrefine :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalRefinement
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsRationalRefinement u hu t := by
  exact CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement.of_inner hrefine

/-- Sequential inner-rational approximation gives the concrete inner-rational refinement target
for convex Stieltjes slices. -/
theorem innerRationalRefinement_of_tendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (happrox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalRefinement
      u hu t :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement.inner_of_tendsto
    happrox

/-- Sequential inner-rational mass approximation gives the concrete inner-rational refinement
target for convex Stieltjes slices. -/
theorem innerRationalRefinement_of_massTendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (hmassApprox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalMassTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalRefinement
      u hu t :=
  innerRationalRefinement_of_tendsto
    (CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement.tendsto_of_massTendsto
      hmassApprox)

/-- Sequential inner-rational approximation gives the concrete rational-refinement target for
convex Stieltjes slices. -/
theorem rationalRefinement_of_tendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (happrox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsRationalRefinement u hu t :=
  rationalRefinement_of_inner (innerRationalRefinement_of_tendsto happrox)

/-- Sequential inner-rational mass approximation gives the concrete rational-refinement target
for convex Stieltjes slices. -/
theorem rationalRefinement_of_massTendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {t : ℝ}
    (hmassApprox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalMassTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsRationalRefinement u hu t :=
  rationalRefinement_of_inner (innerRationalRefinement_of_massTendsto hmassApprox)

/-- A rational interval enumeration and inner-rational refinement give the concrete reverse-cover
direction for convex Stieltjes slices. -/
theorem reverseCover_of_innerRationalRefinement
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (hrefine :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalRefinement
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalReverseCover
      u hu a b t :=
  reverseCover_of_rationalRefinement henum (rationalRefinement_of_inner hrefine)

/-- A rational interval enumeration and sequential inner-rational approximation give the concrete
reverse-cover direction for convex Stieltjes slices. -/
theorem reverseCover_of_tendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (happrox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalReverseCover
      u hu a b t :=
  reverseCover_of_innerRationalRefinement henum
    (innerRationalRefinement_of_tendsto happrox)

/-- A rational interval enumeration and sequential inner-rational mass approximation give the
concrete reverse-cover direction for convex Stieltjes slices. -/
theorem reverseCover_of_massTendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (hmassApprox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalMassTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalReverseCover
      u hu a b t :=
  reverseCover_of_innerRationalRefinement henum
    (innerRationalRefinement_of_massTendsto hmassApprox)

/-- A rational interval enumeration and rational refinement give the concrete countable
fixed-interval representation for convex Stieltjes slices. -/
theorem cover_of_rationalRefinement
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (hrefine :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsRationalRefinement
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
      u hu a b t :=
  cover_of_reverseCover henum.admissible
    (reverseCover_of_rationalRefinement henum hrefine)

/-- A rational interval enumeration and inner-rational refinement give the concrete countable
fixed-interval representation for convex Stieltjes slices. -/
theorem cover_of_innerRationalRefinement
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (hrefine :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalRefinement
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
      u hu a b t :=
  cover_of_rationalRefinement henum (rationalRefinement_of_inner hrefine)

/-- A rational interval enumeration and sequential inner-rational approximation give the concrete
countable fixed-interval representation for convex Stieltjes slices. -/
theorem cover_of_tendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (happrox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
      u hu a b t :=
  cover_of_innerRationalRefinement henum
    (innerRationalRefinement_of_tendsto happrox)

/-- A rational interval enumeration and sequential inner-rational mass approximation give the
concrete countable fixed-interval representation for convex Stieltjes slices. -/
theorem cover_of_massTendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (hmassApprox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalMassTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
      u hu a b t :=
  cover_of_innerRationalRefinement henum
    (innerRationalRefinement_of_massTendsto hmassApprox)

/-- A countable fixed-interval representation gives the concrete convex Stieltjes
average-exceeds measurability input. -/
theorem averageExceedsMeasurable
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
        u hu a b t)
    (hcover :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
        u hu a b t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable u hu t :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsMeasurable.of_countableIntervalFamily
    hfixed hcover

/-- Fixed-interval measurability plus the reverse-cover direction gives the concrete convex
Stieltjes average-exceeds measurability input. -/
theorem averageExceedsMeasurable_of_reverseCover
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
        u hu a b t)
    (hadm : SourceAdmissibleIntervalEnumeration a b)
    (hreverse :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalReverseCover
        u hu a b t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable u hu t :=
  averageExceedsMeasurable hfixed (cover_of_reverseCover hadm hreverse)

/-- Fixed-interval measurability plus rational refinement gives the concrete convex Stieltjes
average-exceeds measurability input. -/
theorem averageExceedsMeasurable_of_rationalRefinement
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
        u hu a b t)
    (henum : SourceRationalIntervalEnumeration a b)
    (hrefine :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsRationalRefinement
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable u hu t :=
  averageExceedsMeasurable hfixed (cover_of_rationalRefinement henum hrefine)

/-- Fixed-interval measurability plus inner-rational refinement gives the concrete convex
Stieltjes average-exceeds measurability input. -/
theorem averageExceedsMeasurable_of_innerRationalRefinement
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
        u hu a b t)
    (henum : SourceRationalIntervalEnumeration a b)
    (hrefine :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalRefinement
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable u hu t :=
  averageExceedsMeasurable_of_rationalRefinement hfixed henum
    (rationalRefinement_of_inner hrefine)

/-- Fixed-interval measurability plus sequential inner-rational approximation gives the concrete
convex Stieltjes average-exceeds measurability input. -/
theorem averageExceedsMeasurable_of_tendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
        u hu a b t)
    (henum : SourceRationalIntervalEnumeration a b)
    (happrox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable u hu t :=
  averageExceedsMeasurable_of_innerRationalRefinement hfixed henum
    (innerRationalRefinement_of_tendsto happrox)

/-- Fixed-interval measurability plus sequential inner-rational mass approximation gives the
concrete convex Stieltjes average-exceeds measurability input. -/
theorem averageExceedsMeasurable_of_massTendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
        u hu a b t)
    (henum : SourceRationalIntervalEnumeration a b)
    (hmassApprox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalMassTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsMeasurable u hu t :=
  averageExceedsMeasurable_of_innerRationalRefinement hfixed henum
    (innerRationalRefinement_of_massTendsto hmassApprox)

/-- A countable fixed-interval representation is enough for the concrete ambient coordinate
maximal bad-set measurability. -/
theorem badSetMeasurable
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
        u hu a b t)
    (hcover :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalCover
        u hu a b t) :
    CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t :=
  (averageExceedsMeasurable hfixed hcover).badSetMeasurable

/-- Fixed-interval measurability plus the reverse-cover direction is enough for the concrete
ambient coordinate maximal bad-set measurability. -/
theorem badSetMeasurable_of_reverseCover
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
        u hu a b t)
    (hadm : SourceAdmissibleIntervalEnumeration a b)
    (hreverse :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalReverseCover
        u hu a b t) :
    CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t :=
  (averageExceedsMeasurable_of_reverseCover hfixed hadm hreverse).badSetMeasurable

/-- Fixed-interval measurability plus rational refinement is enough for the concrete ambient
coordinate maximal bad-set measurability. -/
theorem badSetMeasurable_of_rationalRefinement
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
        u hu a b t)
    (henum : SourceRationalIntervalEnumeration a b)
    (hrefine :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsRationalRefinement
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t :=
  (averageExceedsMeasurable_of_rationalRefinement hfixed henum hrefine).badSetMeasurable

/-- Fixed-interval measurability plus inner-rational refinement is enough for the concrete
ambient coordinate maximal bad-set measurability. -/
theorem badSetMeasurable_of_innerRationalRefinement
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
        u hu a b t)
    (henum : SourceRationalIntervalEnumeration a b)
    (hrefine :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalRefinement
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t :=
  (averageExceedsMeasurable_of_innerRationalRefinement hfixed henum hrefine).badSetMeasurable

/-- Fixed-interval measurability plus sequential inner-rational approximation is enough for the
concrete ambient coordinate maximal bad-set measurability. -/
theorem badSetMeasurable_of_tendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
        u hu a b t)
    (henum : SourceRationalIntervalEnumeration a b)
    (happrox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t :=
  (averageExceedsMeasurable_of_tendsto hfixed henum happrox).badSetMeasurable

/-- Fixed-interval measurability plus sequential inner-rational mass approximation is enough for
the concrete ambient coordinate maximal bad-set measurability. -/
theorem badSetMeasurable_of_massTendsto
    {n : ℕ} {u : SourceCubeSpace n → ℝ} {hu : ConvexOn ℝ (sourceOpenCube n 3) u}
    {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableIntervalMeasurable
        u hu a b t)
    (henum : SourceRationalIntervalEnumeration a b)
    (hmassApprox :
      CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsInnerRationalMassTendsto
        u hu t) :
    CoordinateSliceConvexSourceRightDerivStieltjesMaximalBadSetMeasurable u hu t :=
  (averageExceedsMeasurable_of_massTendsto hfixed henum hmassApprox).badSetMeasurable

end CoordinateSliceConvexSourceRightDerivStieltjesAverageExceedsCountableInterval

end AleksandrovDifferentiability
