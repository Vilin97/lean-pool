/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.OneDimSecondDerivative.Controls
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.QuadraticTrap.RealScalar
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Basic.Sets
public import Mathlib.MeasureTheory.Integral.Prod

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Localized maximal slice predicates on source cubes

This file connects the one-dimensional localized maximal-function notation to the source-cube
coordinate-slice bad predicate used in the upper-contact estimate.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- Quantitative product-measure Fubini estimate with a transverse support set.

If a measurable set `s ⊆ A × univ` has every vertical fiber over `A` bounded by `B`, and the
transverse set `A` has measure at most `C`, then the product measure of `s` is at most `C * B`.
This is the measure-theoretic core of the source proof's passage from one-dimensional coordinate
line estimates to coordinate bad-set estimates. -/
theorem prod_measure_le_mul_of_fiber_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    {s : Set (α × β)} {A : Set α} {C B : ENNReal}
    (hs : MeasurableSet s) (hA : MeasurableSet A)
    (hsupport : s ⊆ A ×ˢ Set.univ)
    (hAmeasure : μ A ≤ C)
    (hfiber : ∀ a ∈ A, ν (Prod.mk a ⁻¹' s) ≤ B) :
    μ.prod ν s ≤ C * B := by
  have hpoint :
      ∀ a : α, ν (Prod.mk a ⁻¹' s) ≤ A.indicator (fun _ => B) a := by
    intro a
    by_cases ha : a ∈ A
    · simpa [Set.indicator_of_mem ha] using hfiber a ha
    · have hempty : Prod.mk a ⁻¹' s = ∅ := by
        ext b
        constructor
        · intro hb
          exact (ha ((hsupport hb).1)).elim
        · intro hb
          exact hb.elim
      simp [hempty, ha]
  calc
    μ.prod ν s = ∫⁻ a, ν (Prod.mk a ⁻¹' s) ∂μ := Measure.prod_apply hs
    _ ≤ ∫⁻ a, A.indicator (fun _ => B) a ∂μ := lintegral_mono hpoint
    _ = B * μ A := lintegral_indicator_const hA B
    _ ≤ B * C := by gcongr
    _ = C * B := by rw [mul_comm]

/-- A family of one-dimensional measures assigned to every coordinate direction and coordinate
line base. In the source proof these will be the distributional second derivative measures of
the convex restrictions `s ↦ u(y + s e_i)`. -/
abbrev CoordinateSliceMeasureFamily (n : ℕ) :=
  Fin n → SourceCubeSpace n → Measure ℝ

/-- Concrete source-route slice bad predicate from localized maximal functions of a coordinate
slice measure family. -/
def coordinateSliceMaximalBadPredicate {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) : CoordinateSliceBadPredicate n :=
  fun i y s t => sourceLocalizedMaximalBadPredicate (μslice i y) s t

/-- One-dimensional bad set on the coordinate line with base `y`, direction `i`, and threshold
`t`. This is the fiber set appearing in the Fubini step for `E_i(t)`. -/
def coordinateSliceLineBadSet {n : ℕ} (μslice : CoordinateSliceMeasureFamily n)
    (i : Fin n) (y : SourceCubeSpace n) (t : ℝ) : Set ℝ :=
  sourceLocalizedMaximalBadSet (μslice i y) t

/-- Product-coordinate measurability obligation for the concrete localized maximal slice
predicate. -/
def CoordinateSliceMaximalBadPredicateMeasurable {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (t : ℝ) : Prop :=
  CoordinateSliceBadPredicateMeasurable (coordinateSliceMaximalBadPredicate μslice) t

/-- One-dimensional parameterized measurability obligation for every coordinate slice family.

For each coordinate direction `i`, the parameter is the coordinate-line base `y`, and the
one-dimensional source-local maximal bad predicate is measurable in `(y,s)`. -/
def CoordinateSliceSourceLocalizedMaximalMeasurable {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (t : ℝ) : Prop :=
  ∀ i : Fin n, SourceLocalizedMaximalBadPredicateMeasurable (μslice i) t

/-- Source-window-restricted one-dimensional measurability obligation for every coordinate slice
family. This is sufficient for the cube bad sets, since their coordinate parameter lies in
`sourceMaximalWindow`. -/
def CoordinateSliceSourceLocalizedMaximalMeasurableOnWindow {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (t : ℝ) : Prop :=
  ∀ i : Fin n, SourceLocalizedMaximalBadPredicateMeasurableOnWindow (μslice i) t

/-- Interval-average-exceeds measurability obligation for every coordinate slice family. -/
def CoordinateSliceSourceLocalizedMaximalAverageExceedsMeasurable {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (t : ℝ) : Prop :=
  ∀ i : Fin n, SourceLocalizedMaximalAverageExceedsMeasurable (μslice i) t

/-- Coordinate version of countable fixed-interval measurability for source-local maximal
average-exceeds sets. -/
def CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalFamilyMeasurable {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (a b : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ i : Fin n,
    SourceLocalizedMaximalAverageExceedsCountableIntervalFamilyMeasurable (μslice i) a b t

/-- Coordinate version of the assertion that the source average-exceeds set is represented by a
countable fixed-interval family. -/
def CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalCover {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (a b : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ i : Fin n,
    sourceLocalizedMaximalAverageExceedsSet (μslice i) t =
      sourceLocalizedMaximalAverageExceedsCountableIntervalSet (μslice i) a b t

/-- Coordinate version of the reverse-cover assertion for a countable fixed-interval family. -/
def CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (a b : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ i : Fin n,
    SourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover (μslice i) a b t

/-- Coordinate version of rational refinement for source-local average-exceeds witnesses. -/
def CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (t : ℝ) : Prop :=
  ∀ i : Fin n,
    SourceLocalizedMaximalAverageExceedsRationalRefinement (μslice i) t

/-- Coordinate version of inner-rational refinement for source-local average-exceeds witnesses. -/
def CoordinateSliceSourceLocalizedMaximalAverageExceedsInnerRationalRefinement {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (t : ℝ) : Prop :=
  ∀ i : Fin n,
    SourceRealIntervalAverageExceedsInnerRationalRefinement (μslice i) t

/-- Coordinate version of sequential inner-rational average approximation. -/
def CoordinateSliceSourceLocalizedMaximalAverageExceedsInnerRationalTendsto {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (t : ℝ) : Prop :=
  ∀ i : Fin n,
    SourceRealIntervalAverageExceedsInnerRationalTendsto (μslice i) t

/-- Coordinate version of sequential inner-rational mass approximation. -/
def CoordinateSliceSourceLocalizedMaximalAverageExceedsInnerRationalMassTendsto {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (t : ℝ) : Prop :=
  ∀ i : Fin n,
    SourceRealIntervalAverageExceedsInnerRationalMassTendsto (μslice i) t

/-- Measurability of all fixed-interval coordinate averages. -/
def CoordinateSliceSourceLocalizedMaximalFixedIntervalAverageMeasurable {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (a b : ℕ → ℝ) : Prop :=
  ∀ i : Fin n, ∀ k : ℕ,
    Measurable fun y : SourceCubeSpace n =>
      openIntervalMeasureAverage (μslice i y) (a k) (b k)

/-- Measurability obligation for the source-route coordinate maximal bad sets.

This names the analytic measurability input needed by the Fubini step. It deliberately only
records measurability of the ambient coordinate bad sets `E_i(t)`; the product chart and
transverse Fubini bookkeeping are proved separately below. -/
def CoordinateSliceMaximalBadSetMeasurable {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (t : ℝ) : Prop :=
  ∀ i : Fin n,
    MeasurableSet (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t)

/-- Joint product-coordinate measurability of the maximal bad predicate gives measurability of
the ambient coordinate maximal bad sets. -/
theorem CoordinateSliceMaximalBadPredicateMeasurable.badSetMeasurable {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {t : ℝ}
    (hbad : CoordinateSliceMaximalBadPredicateMeasurable μslice t) :
    CoordinateSliceMaximalBadSetMeasurable μslice t :=
  hbad.coordinateSliceBadSet

/-- Parameterized one-dimensional maximal measurability supplies the product-coordinate
measurability of the coordinate maximal bad predicate. -/
theorem CoordinateSliceSourceLocalizedMaximalMeasurable.badPredicateMeasurable {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {t : ℝ}
    (hbad : CoordinateSliceSourceLocalizedMaximalMeasurable μslice t) :
    CoordinateSliceMaximalBadPredicateMeasurable μslice t := by
  intro i
  simpa [CoordinateSliceMaximalBadPredicateMeasurable, CoordinateSliceBadPredicateMeasurable,
    SourceLocalizedMaximalBadPredicateMeasurable, coordinateSliceMaximalBadPredicate] using hbad i

/-- Parameterized one-dimensional maximal measurability supplies measurability of the ambient
coordinate maximal bad sets. -/
theorem CoordinateSliceSourceLocalizedMaximalMeasurable.badSetMeasurable {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {t : ℝ}
    (hbad : CoordinateSliceSourceLocalizedMaximalMeasurable μslice t) :
    CoordinateSliceMaximalBadSetMeasurable μslice t :=
  hbad.badPredicateMeasurable.badSetMeasurable

/-- Source-window-restricted one-dimensional maximal measurability supplies measurability of the
ambient coordinate maximal bad sets. -/
theorem CoordinateSliceSourceLocalizedMaximalMeasurableOnWindow.badSetMeasurable {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {t : ℝ}
    (hbad : CoordinateSliceSourceLocalizedMaximalMeasurableOnWindow μslice t) :
    CoordinateSliceMaximalBadSetMeasurable μslice t := by
  intro i
  have hcoord :
      Continuous (fun x : SourceCubeSpace n => (coordinateLineBase i x, x i)) :=
    (continuous_coordinateLineBase i).prodMk (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  have hpre :
      MeasurableSet
        ((fun x : SourceCubeSpace n => (coordinateLineBase i x, x i)) ⁻¹'
          {p : SourceCubeSpace n × ℝ |
            p.2 ∈ sourceMaximalWindow ∧
              sourceLocalizedMaximalBadPredicate (μslice i p.1) p.2 t}) :=
    (hbad i).preimage hcoord.measurable
  convert (isOpen_sourceOpenCube (n := n) 1).measurableSet.inter hpre using 1
  ext x
  constructor
  · intro hx
    have hxi_window : x i ∈ sourceMaximalWindow := by
      have hxi_abs : |x i| < 1 := by
        simpa using hx.1 i
      simpa [sourceMaximalWindow] using (abs_lt.mp hxi_abs)
    exact ⟨hx.1, hxi_window, hx.2⟩
  · rintro ⟨hxQ, _hwindow, hbadx⟩
    exact ⟨hxQ, hbadx⟩

/-- Interval-average-exceeds measurability supplies measurability of the ambient coordinate
maximal bad sets. -/
theorem CoordinateSliceSourceLocalizedMaximalAverageExceedsMeasurable.badSetMeasurable {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {t : ℝ}
    (havg : CoordinateSliceSourceLocalizedMaximalAverageExceedsMeasurable μslice t) :
    CoordinateSliceMaximalBadSetMeasurable μslice t :=
  CoordinateSliceSourceLocalizedMaximalMeasurableOnWindow.badSetMeasurable
    (fun i =>
      SourceLocalizedMaximalBadPredicateMeasurableOnWindow.of_averageExceeds (havg i))

/-- A countable fixed-interval representation of the source average-exceeds sets gives the
coordinate average-exceeds measurability input. -/
theorem CoordinateSliceSourceLocalizedMaximalAverageExceedsMeasurable.of_countableIntervalFamily
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {a b : ℕ → ℝ} {t : ℝ}
    (hfixed :
      CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalFamilyMeasurable
        μslice a b t)
    (hcover :
      CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalCover μslice a b t) :
    CoordinateSliceSourceLocalizedMaximalAverageExceedsMeasurable μslice t :=
  fun i =>
    SourceLocalizedMaximalAverageExceedsMeasurable.of_countableIntervalFamily
      (hfixed i) (hcover i)

/-- An admissible interval enumeration plus the coordinate reverse-cover direction gives the
coordinate countable-interval representation. -/
theorem CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalCover.of_reverseCover
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {a b : ℕ → ℝ} {t : ℝ}
    (hadm : SourceAdmissibleIntervalEnumeration a b)
    (hreverse :
      CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover
        μslice a b t) :
    CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalCover μslice a b t :=
  fun i =>
    sourceLocalizedMaximalAverageExceedsCountableIntervalCover_of_reverseCover
      hadm (hreverse i)

namespace CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement

/-- Coordinate sequential inner-rational mass approximation gives coordinate sequential
inner-rational average approximation. -/
theorem tendsto_of_massTendsto
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {t : ℝ}
    (hmassApprox :
      CoordinateSliceSourceLocalizedMaximalAverageExceedsInnerRationalMassTendsto μslice t) :
    CoordinateSliceSourceLocalizedMaximalAverageExceedsInnerRationalTendsto μslice t :=
  fun i => SourceRealIntervalAverageExceedsInnerRationalTendsto.of_massTendsto (hmassApprox i)

/-- Coordinate sequential inner-rational approximation gives coordinate inner-rational
refinement. -/
theorem inner_of_tendsto
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {t : ℝ}
    (happrox :
      CoordinateSliceSourceLocalizedMaximalAverageExceedsInnerRationalTendsto μslice t) :
    CoordinateSliceSourceLocalizedMaximalAverageExceedsInnerRationalRefinement μslice t :=
  fun i =>
    SourceRealIntervalAverageExceedsInnerRationalRefinement.of_tendsto (happrox i)

/-- Coordinate inner-rational refinement gives coordinate rational refinement. -/
theorem of_inner
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {t : ℝ}
    (hrefine :
      CoordinateSliceSourceLocalizedMaximalAverageExceedsInnerRationalRefinement μslice t) :
    CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement μslice t :=
  fun i =>
    SourceLocalizedMaximalAverageExceedsRationalRefinement.of_realInterval
      (SourceRealIntervalAverageExceedsRationalRefinement.of_inner (hrefine i))

end CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement

namespace CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover

/-- Coordinate inner-rational refinement gives coordinate rational refinement. -/
theorem rationalRefinement_of_inner
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {t : ℝ}
    (hrefine :
      CoordinateSliceSourceLocalizedMaximalAverageExceedsInnerRationalRefinement μslice t) :
    CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement μslice t :=
  CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement.of_inner hrefine

/-- A rational interval enumeration and coordinate rational refinement give the coordinate
reverse-cover direction. -/
theorem of_rationalRefinement
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {a b : ℕ → ℝ} {t : ℝ}
    (henum : SourceRationalIntervalEnumeration a b)
    (hrefine :
      CoordinateSliceSourceLocalizedMaximalAverageExceedsRationalRefinement μslice t) :
    CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover
      μslice a b t :=
  fun i =>
    SourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover.of_rationalRefinement
      henum (hrefine i)

end CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalReverseCover

/-- Measurable fixed-interval coordinate averages give the coordinate countable-interval
measurability input. -/
theorem CoordinateSliceAverageExceedsCountableIntervalFamily.of_measurableAverage
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {a b : ℕ → ℝ} {t : ℝ}
    (havg : CoordinateSliceSourceLocalizedMaximalFixedIntervalAverageMeasurable μslice a b) :
    CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalFamilyMeasurable
      μslice a b t :=
  fun i =>
    SourceLocalizedMaximalAverageExceedsCountableIntervalFamilyMeasurable.of_measurableAverage
      (havg i)

/-- A countable fixed-interval representation of the source average-exceeds sets is enough for
coordinate maximal bad-set measurability. -/
theorem CoordinateSliceAverageExceedsCountableIntervalFamily.badSetMeasurable
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {a b : ℕ → ℝ}
    {t : ℝ}
    (hfixed :
      CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalFamilyMeasurable
        μslice a b t)
    (hcover :
      CoordinateSliceSourceLocalizedMaximalAverageExceedsCountableIntervalCover μslice a b t) :
    CoordinateSliceMaximalBadSetMeasurable μslice t :=
  (CoordinateSliceSourceLocalizedMaximalAverageExceedsMeasurable.of_countableIntervalFamily
    hfixed hcover).badSetMeasurable

/-- Uniform source mass bound for every coordinate slice over bases in `Q_1`. In the source
proof this comes from the one-dimensional convex second-derivative mass estimate applied to
`s ↦ u(y + s e_i)`, and the bound by `osc_{Q_3} u`. -/
def CoordinateSliceSourceMassBound {n : ℕ} (μslice : CoordinateSliceMeasureFamily n)
    (osc : ℝ) : Prop :=
  ∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
    y ∈ sourceOpenCube n 1 → HasOneDimSecondDerivativeSourceMassBound (μslice i y) osc

@[simp]
theorem mem_coordinateSliceLineBadSet {n : ℕ} {μslice : CoordinateSliceMeasureFamily n}
    {i : Fin n} {y : SourceCubeSpace n} {t s : ℝ} :
    s ∈ coordinateSliceLineBadSet μslice i y t ↔
      s ∈ sourceMaximalWindow ∧ sourceLocalizedMaximalBadPredicate (μslice i y) s t :=
  Iff.rfl

/-- Membership in a coordinate-line maximal bad set is equivalent to the existence of one
source-admissible interval through the line parameter whose slice-measure average exceeds the
threshold. -/
theorem mem_coordinateSliceLineBadSet_iff_exists_average_gt {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {i : Fin n} {y : SourceCubeSpace n} {t s : ℝ} :
    s ∈ coordinateSliceLineBadSet μslice i y t ↔
      s ∈ sourceMaximalWindow ∧
        ∃ a b : ℝ,
          a < b ∧ Set.Ioo a b ⊆ sourceMaximalDomain ∧ s ∈ Set.Ioo a b ∧
            t < openIntervalMeasureAverage (μslice i y) a b := by
  constructor
  · intro hsbad
    exact ⟨hsbad.1,
      (sourceLocalizedMaximalBadPredicate_iff_exists_average_gt_of_mem_window
        (μ := μslice i y) hsbad.1).mp hsbad.2⟩
  · rintro ⟨hswindow, hinterval⟩
    exact ⟨hswindow,
      (sourceLocalizedMaximalBadPredicate_iff_exists_average_gt_of_mem_window
        (μ := μslice i y) hswindow).mpr hinterval⟩

/-- Product-chart preimage of the concrete coordinate bad set for direction `i`. -/
def coordinateSliceBadSetProductModel {n : ℕ} (μslice : CoordinateSliceMeasureFamily n)
    (i : Fin n) (t : ℝ) : Set (SourceTransverseSpace i × ℝ) :=
  sourceCoordinateChartMap i ⁻¹'
    coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t

@[simp]
theorem mem_coordinateSliceBadSetProductModel {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {i : Fin n} {t : ℝ}
    {p : SourceTransverseSpace i × ℝ} :
    p ∈ coordinateSliceBadSetProductModel μslice i t ↔
      sourceCoordinateChartPoint i p.1 p.2 ∈
        coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t :=
  Iff.rfl

/-- Measurability of the product-model bad set follows from measurability of the ambient
coordinate bad set and continuity of the coordinate chart. -/
theorem MeasurableSet.coordinateSliceBadSetProductModel {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {i : Fin n} {t : ℝ}
    (hbad : MeasurableSet (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t)) :
    MeasurableSet (coordinateSliceBadSetProductModel μslice i t) :=
  hbad.preimage (continuous_sourceCoordinateChartMap i).measurable

/-- Product-model version of the coordinate-slice Fubini bound for one fixed coordinate.

The data `A`, `S`, and `base` represent a transverse product chart for the coordinate bad set:
`S` is the product-model preimage of the coordinate bad set, `A` is the allowed transverse set,
and `base a` is the source-cube base point of the coordinate line over `a`. Once this geometric
data is available, the quantitative estimate follows from
`prod_measure_le_mul_of_fiber_bound` and the one-dimensional line bounds. -/
theorem coordinateSliceBadSet_measure_le_of_productModel {n : ℕ}
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {μslice : CoordinateSliceMeasureFamily n} {i : Fin n} {Ctrans t : ℝ} {B : ENNReal}
    {A : Set α} {S : Set (α × ℝ)} {base : α → SourceCubeSpace n}
    (hbad_le :
      volume (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t) ≤
        μ.prod (volume : Measure ℝ) S)
    (hS : MeasurableSet S) (hA : MeasurableSet A)
    (hsupport : S ⊆ A ×ˢ Set.univ)
    (hAmeasure : μ A ≤ ENNReal.ofReal Ctrans)
    (hbase : ∀ a ∈ A, base a ∈ sourceOpenCube n 1)
    (hsection :
      ∀ a ∈ A,
        Prod.mk a ⁻¹' S ⊆ coordinateSliceLineBadSet μslice i (base a) t)
    (hline :
      ∀ j : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          volume (coordinateSliceLineBadSet μslice j y t) ≤ B) :
    volume (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t) ≤
      ENNReal.ofReal Ctrans * B := by
  refine hbad_le.trans ?_
  refine prod_measure_le_mul_of_fiber_bound
    (μ := μ) (ν := (volume : Measure ℝ)) (s := S) (A := A)
    (C := ENNReal.ofReal Ctrans) (B := B)
    hS hA hsupport hAmeasure ?_
  intro a ha
  exact (measure_mono (hsection a ha)).trans (hline i (hbase a ha))

/-- Membership in the concrete coordinate bad set is membership in `Q_1` together with membership
of the coordinate parameter in the corresponding one-dimensional localized maximal bad set. -/
theorem mem_coordinateSliceBadSet_maximal_iff {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {i : Fin n} {t : ℝ}
    {x : SourceCubeSpace n} :
    x ∈ coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t ↔
      x ∈ sourceOpenCube n 1 ∧
        x i ∈ coordinateSliceLineBadSet μslice i (coordinateLineBase i x) t := by
  constructor
  · intro hx
    rcases hx with ⟨hxQ, hxBad⟩
    have hxi_abs : |x i| < 1 := by
      simpa using hxQ i
    have hxi_window : x i ∈ sourceMaximalWindow := by
      simpa [sourceMaximalWindow] using (abs_lt.mp hxi_abs)
    exact ⟨hxQ, hxi_window, hxBad⟩
  · rintro ⟨hxQ, hxiBad⟩
    exact ⟨hxQ, hxiBad.2⟩

/-- Ambient coordinate maximal bad-set membership in interval-average form. This is the
source-proof description of `E_i(t)`: a point of `Q_1` is bad in coordinate direction `i` iff
some source-admissible interval through its coordinate parameter has average larger than `t`. -/
theorem mem_coordinateSliceBadSet_maximal_iff_exists_average_gt {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {i : Fin n} {t : ℝ}
    {x : SourceCubeSpace n} :
    x ∈ coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t ↔
      x ∈ sourceOpenCube n 1 ∧
        ∃ a b : ℝ,
          a < b ∧ Set.Ioo a b ⊆ sourceMaximalDomain ∧ x i ∈ Set.Ioo a b ∧
            t < openIntervalMeasureAverage (μslice i (coordinateLineBase i x)) a b := by
  constructor
  · intro hx
    rcases mem_coordinateSliceBadSet_maximal_iff.mp hx with ⟨hxQ, hline⟩
    exact ⟨hxQ, (mem_coordinateSliceLineBadSet_iff_exists_average_gt.mp hline).2⟩
  · rintro ⟨hxQ, hinterval⟩
    have hxi_window : x i ∈ sourceMaximalWindow := by
      have hxi_abs : |x i| < 1 := by
        simpa using hxQ i
      simpa [sourceMaximalWindow] using (abs_lt.mp hxi_abs)
    exact mem_coordinateSliceBadSet_maximal_iff.mpr
      ⟨hxQ, mem_coordinateSliceLineBadSet_iff_exists_average_gt.mpr
        ⟨hxi_window, hinterval⟩⟩

/-- The product-model coordinate bad set is supported over the transverse unit cube. -/
theorem coordinateSliceBadSetProductModel_subset_transverse {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {i : Fin n} {t : ℝ} :
    coordinateSliceBadSetProductModel μslice i t ⊆
      sourceTransverseOpenCube i 1 ×ˢ Set.univ := by
  intro p hp
  have hxQ :
      sourceCoordinateChartPoint i p.1 p.2 ∈ sourceOpenCube n 1 :=
    (mem_coordinateSliceBadSet_maximal_iff.mp hp).1
  exact ⟨(sourceCoordinateChartPoint_mem_sourceOpenCube_iff.mp hxQ).1, trivial⟩

/-- Each product-model vertical fiber is contained in the corresponding one-dimensional line bad
set. -/
theorem coordinateSliceBadSetProductModel_section_subset_lineBadSet {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {i : Fin n} {t : ℝ}
    {a : SourceTransverseSpace i} :
    Prod.mk a ⁻¹' coordinateSliceBadSetProductModel μslice i t ⊆
      coordinateSliceLineBadSet μslice i (sourceTransverseEmbed i a) t := by
  intro s hs
  have hx :=
    (mem_coordinateSliceBadSet_maximal_iff.mp hs).2
  simpa [sourceCoordinateChartMap] using hx

/-- The transverse unit cube has finite Lebesgue measure. -/
theorem sourceTransverseOpenCube_volume_lt_top {n : ℕ} (i : Fin n) :
    volume (sourceTransverseOpenCube i 1) < ⊤ :=
  (isBounded_sourceTransverseOpenCube i (by norm_num)).measure_lt_top

/-- The finite transverse volume gives an admissible transverse Fubini constant for the canonical
transverse unit cube. -/
theorem sourceTransverseOpenCube_volume_le_ofReal_toReal {n : ℕ} (i : Fin n) :
    volume (sourceTransverseOpenCube i 1) ≤
      ENNReal.ofReal (volume (sourceTransverseOpenCube i 1)).toReal := by
  rw [ENNReal.ofReal_toReal (sourceTransverseOpenCube_volume_lt_top i).ne]

/-- There exists a real transverse constant bounding the Lebesgue measure of every coordinate
transverse unit cube. This is the constant-existence form needed before choosing a cleaner
closed-form scalar in the final source estimate. -/
theorem exists_forall_sourceTransverseOpenCube_volume_le_ofReal {n : ℕ} :
    ∃ Ctrans : ℝ,
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans := by
  classical
  refine ⟨∑ i : Fin n, (volume (sourceTransverseOpenCube i 1)).toReal, ?_⟩
  intro i
  refine (sourceTransverseOpenCube_volume_le_ofReal_toReal i).trans ?_
  exact ENNReal.ofReal_le_ofReal (Finset.single_le_sum
    (fun j _ => ENNReal.toReal_nonneg
      (a := volume (sourceTransverseOpenCube j 1)))
    (Finset.mem_univ i))

/-- There exists a nonnegative real transverse constant bounding the Lebesgue measure of every
coordinate transverse unit cube. -/
theorem exists_nonneg_forall_sourceTransverseOpenCube_volume_le_ofReal {n : ℕ} :
    ∃ Ctrans : ℝ,
      0 ≤ Ctrans ∧
        ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans := by
  classical
  refine ⟨∑ i : Fin n, (volume (sourceTransverseOpenCube i 1)).toReal, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ =>
      ENNReal.toReal_nonneg (a := volume (sourceTransverseOpenCube i 1))
  · intro i
    refine (sourceTransverseOpenCube_volume_le_ofReal_toReal i).trans ?_
    exact ENNReal.ofReal_le_ofReal (Finset.single_le_sum
      (fun j _ => ENNReal.toReal_nonneg
        (a := volume (sourceTransverseOpenCube j 1)))
      (Finset.mem_univ i))

/-- The canonical coordinate chart from transverse coordinates and the distinguished coordinate
is Lebesgue-measure preserving. -/
theorem sourceCoordinateChartMap_measurePreserving {n : ℕ} (i : Fin n) :
    MeasurePreserving (sourceCoordinateChartMap i)
      ((volume : Measure (SourceTransverseSpace i)).prod (volume : Measure ℝ))
      (volume : Measure (SourceCubeSpace n)) := by
  have hlin :
      MeasurePreserving (sourceCoordinateChartLinearIsometryEquiv i)
        (volume : Measure (WithLp 2 (SourceTransverseSpace i × ℝ)))
        (volume : Measure (SourceCubeSpace n)) :=
    LinearIsometryEquiv.measurePreserving (sourceCoordinateChartLinearIsometryEquiv i)
  have hto :
      MeasurePreserving
        (WithLp.toLp 2 : SourceTransverseSpace i × ℝ →
          WithLp 2 (SourceTransverseSpace i × ℝ))
        ((volume : Measure (SourceTransverseSpace i)).prod (volume : Measure ℝ))
        (volume : Measure (WithLp 2 (SourceTransverseSpace i × ℝ))) := by
    simpa [MeasureTheory.Measure.volume_eq_prod] using
      (WithLp.volume_preserving_toLp (SourceTransverseSpace i) ℝ)
  convert hlin.comp hto using 1
  funext p
  simp [sourceCoordinateChartMap, sourceCoordinateChartLinearIsometryEquiv,
    sourceCoordinateChartLinearMap]

/-- Fixed-coordinate product-model Fubini estimate specialized to the canonical coordinate chart.
The remaining hypotheses are exactly the measurable/product-measure facts about that chart. -/
theorem coordinateSliceBadSet_measure_le_of_coordinateProductModel {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {i : Fin n} {Ctrans t : ℝ} {B : ENNReal}
    (hbad_le :
      volume (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t) ≤
        (volume : Measure (SourceTransverseSpace i)).prod (volume : Measure ℝ)
          (coordinateSliceBadSetProductModel μslice i t))
    (hS : MeasurableSet (coordinateSliceBadSetProductModel μslice i t))
    (hAmeasure :
      volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hline :
      ∀ j : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          volume (coordinateSliceLineBadSet μslice j y t) ≤ B) :
    volume (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t) ≤
      ENNReal.ofReal Ctrans * B :=
  coordinateSliceBadSet_measure_le_of_productModel
    (μ := (volume : Measure (SourceTransverseSpace i)))
    (A := sourceTransverseOpenCube i 1)
    (S := coordinateSliceBadSetProductModel μslice i t)
    (base := sourceTransverseEmbed i)
    hbad_le hS (isOpen_sourceTransverseOpenCube i 1).measurableSet
    coordinateSliceBadSetProductModel_subset_transverse hAmeasure
    (fun _a ha => sourceTransverseEmbed_mem_sourceOpenCube (by norm_num) ha)
    (fun _a _ha => coordinateSliceBadSetProductModel_section_subset_lineBadSet)
    hline

/-- If the canonical coordinate chart is measure-preserving, then the ambient coordinate bad set
has the same measure as its product-model preimage. -/
theorem coordinateSliceBadSet_measure_eq_productModel_of_chartMeasurePreserving {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {i : Fin n} {t : ℝ}
    (hchart :
      MeasurePreserving (sourceCoordinateChartMap i)
        ((volume : Measure (SourceTransverseSpace i)).prod (volume : Measure ℝ))
        (volume : Measure (SourceCubeSpace n)))
    (hbad :
      NullMeasurableSet
        (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t)
        (volume : Measure (SourceCubeSpace n))) :
    (volume : Measure (SourceTransverseSpace i)).prod (volume : Measure ℝ)
        (coordinateSliceBadSetProductModel μslice i t) =
      volume (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t) := by
  simpa [coordinateSliceBadSetProductModel] using hchart.measure_preimage hbad

/-- Fixed-coordinate product-model Fubini estimate using a measure-preserving coordinate chart.
The remaining assumptions are measurability of the ambient coordinate bad set, the chart
measure-preserving fact, and the transverse-volume bound. -/
theorem coordinateSliceBadSet_measure_le_of_coordinateChartMeasurePreserving {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {i : Fin n} {Ctrans t : ℝ} {B : ENNReal}
    (hchart :
      MeasurePreserving (sourceCoordinateChartMap i)
        ((volume : Measure (SourceTransverseSpace i)).prod (volume : Measure ℝ))
        (volume : Measure (SourceCubeSpace n)))
    (hbad :
      MeasurableSet (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t))
    (hAmeasure :
      volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hline :
      ∀ j : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
        y ∈ sourceOpenCube n 1 →
          volume (coordinateSliceLineBadSet μslice j y t) ≤ B) :
    volume (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t) ≤
      ENNReal.ofReal Ctrans * B := by
  refine coordinateSliceBadSet_measure_le_of_coordinateProductModel
    (i := i) (B := B) ?_
    (MeasurableSet.coordinateSliceBadSetProductModel
      (μslice := μslice) (i := i) (t := t) hbad)
    hAmeasure hline
  rw [coordinateSliceBadSet_measure_eq_productModel_of_chartMeasurePreserving
    (μslice := μslice) (i := i) (t := t) hchart hbad.nullMeasurableSet]

end AleksandrovDifferentiability
