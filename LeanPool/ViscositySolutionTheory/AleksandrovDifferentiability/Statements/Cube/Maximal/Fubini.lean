/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Maximal.Basic
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Measure
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Cube.Oscillation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Coordinate-slice maximal Fubini estimates
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-- A uniform measure bound on line sections controls each coordinate bad set by Fubini. -/
def CoordinateSliceMaximalTransverseFubiniEstimate {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (Ctrans t : ℝ) : Prop :=
  ∀ B : ENNReal,
    (∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
      y ∈ sourceOpenCube n 1 →
        volume (coordinateSliceLineBadSet μslice i y t) ≤ B) →
    ∀ i : Fin n,
      volume (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t) ≤
        ENNReal.ofReal Ctrans * B

/-- The transverse Fubini estimate follows from the canonical coordinate product model once the
chart measurability, chart measure comparison, and transverse-volume bound are supplied. -/
theorem CoordinateSliceMaximalTransverseFubiniEstimate.of_coordinateProductModel {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {Ctrans t : ℝ}
    (hbad_le :
      ∀ i : Fin n,
        volume (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t) ≤
          (volume : Measure (SourceTransverseSpace i)).prod (volume : Measure ℝ)
            (coordinateSliceBadSetProductModel μslice i t))
    (hS : ∀ i : Fin n, MeasurableSet (coordinateSliceBadSetProductModel μslice i t))
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans) :
    CoordinateSliceMaximalTransverseFubiniEstimate μslice Ctrans t := by
  intro B hline i
  exact coordinateSliceBadSet_measure_le_of_coordinateProductModel
    (i := i) (B := B) (hbad_le i) (hS i) (hAmeasure i) hline

/-- The transverse Fubini estimate follows from measure-preserving canonical coordinate charts,
measurability of the coordinate bad sets, and the transverse-volume bound. -/
theorem CoordinateSliceMaximalTransverseFubiniEstimate.of_coordinateChartMeasurePreserving
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {Ctrans t : ℝ}
    (hchart :
      ∀ i : Fin n,
        MeasurePreserving (sourceCoordinateChartMap i)
          ((volume : Measure (SourceTransverseSpace i)).prod (volume : Measure ℝ))
          (volume : Measure (SourceCubeSpace n)))
    (hbad :
      ∀ i : Fin n,
        MeasurableSet (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t))
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans) :
    CoordinateSliceMaximalTransverseFubiniEstimate μslice Ctrans t := by
  intro B hline i
  exact coordinateSliceBadSet_measure_le_of_coordinateChartMeasurePreserving
    (i := i) (B := B) (hchart i) (hbad i) (hAmeasure i) hline

/-- The transverse Fubini estimate follows from coordinate bad-set measurability and transverse
volume bounds; the canonical coordinate charts are measure-preserving. -/
theorem CoordinateSliceMaximalTransverseFubiniEstimate.of_coordinateBadSetMeasurable
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {Ctrans t : ℝ}
    (hbad :
      ∀ i : Fin n,
        MeasurableSet (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t))
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans) :
    CoordinateSliceMaximalTransverseFubiniEstimate μslice Ctrans t :=
  CoordinateSliceMaximalTransverseFubiniEstimate.of_coordinateChartMeasurePreserving
    (fun i => sourceCoordinateChartMap_measurePreserving i) hbad hAmeasure

/-- Named-obligation version of
`CoordinateSliceMaximalTransverseFubiniEstimate.of_coordinateBadSetMeasurable`. -/
theorem CoordinateSliceMaximalTransverseFubiniEstimate.of_badSetMeasurable
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {Ctrans t : ℝ}
    (hbad : CoordinateSliceMaximalBadSetMeasurable μslice t)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans) :
    CoordinateSliceMaximalTransverseFubiniEstimate μslice Ctrans t :=
  CoordinateSliceMaximalTransverseFubiniEstimate.of_coordinateBadSetMeasurable
    hbad hAmeasure

/-- If the coordinate bad sets are measurable, then some real transverse constant gives the
transverse Fubini estimate. This is the constant-existence form of the source Fubini step. -/
theorem exists_coordinateSliceMaximalTransverseFubiniEstimate_of_coordinateBadSetMeasurable
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {t : ℝ}
    (hbad :
      ∀ i : Fin n,
        MeasurableSet (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t)) :
    ∃ Ctrans : ℝ, CoordinateSliceMaximalTransverseFubiniEstimate μslice Ctrans t := by
  rcases exists_forall_sourceTransverseOpenCube_volume_le_ofReal (n := n) with
    ⟨Ctrans, hAmeasure⟩
  exact ⟨Ctrans,
    CoordinateSliceMaximalTransverseFubiniEstimate.of_coordinateBadSetMeasurable
      hbad hAmeasure⟩

/-- Named-obligation version of the existential transverse Fubini step. -/
theorem CoordinateSliceMaximalBadSetMeasurable.exists_transverseFubiniEstimate
    {n : ℕ} {μslice : CoordinateSliceMeasureFamily n} {t : ℝ}
    (hbad : CoordinateSliceMaximalBadSetMeasurable μslice t) :
    ∃ Ctrans : ℝ, CoordinateSliceMaximalTransverseFubiniEstimate μslice Ctrans t :=
  exists_coordinateSliceMaximalTransverseFubiniEstimate_of_coordinateBadSetMeasurable hbad

/-- The one-dimensional localized maximal estimate plus the source mass bound controls each
coordinate-line bad fiber. -/
theorem CoordinateSliceSourceMassBound.lineBadSet_measure_le {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {osc C t : ℝ}
    (hmass : CoordinateSliceSourceMassBound μslice osc)
    (hmax : LocalizedMaximalEstimateStatement C) (ht : 0 < t)
    (i : Fin n) {y : SourceCubeSpace n} (hy : y ∈ sourceOpenCube n 1) :
    volume (coordinateSliceLineBadSet μslice i y t) ≤
      ENNReal.ofReal (2 * C * osc / t) :=
  (hmass i hy).sourceBadSet_measure_le hmax ht

/-- Endpoint control for the concrete localized-maximal slice predicate. This is the exact
one-dimensional convex estimate still to be proved from the distributional second derivative
measure of the slice. -/
def CoordinateSliceMaximalEndpointControl {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (μslice : CoordinateSliceMeasureFamily n)
    (ρ K t : ℝ) : Prop :=
  CoordinateSliceEndpointQuadraticControl u (coordinateSliceMaximalBadPredicate μslice) ρ K t

/-- Coordinate-slice version of the one-dimensional endpoint-control input. The constant `K`
is a multiplier for the maximal threshold `t`, matching the source estimate
`\tilde u(±h e_i) <= C t h^2`. -/
def CoordinateSliceOneDimEndpointControl {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (μslice : CoordinateSliceMeasureFamily n)
    (ρ K : ℝ) : Prop :=
  ∀ ⦃x : SourceCubeSpace n⦄,
    x ∈ sourceOpenCube n 1 →
      DifferentiableAt ℝ u x →
        ∀ i : Fin n,
          HasOneDimSecondDerivativeEndpointControl
            (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i))
            (μslice i (coordinateLineBase i x)) ρ K

/-- For a coordinate line through a point of `Q_1`, the parameters that stay in `Q_3` are exactly
the source interval `(-3,3)`. -/
theorem coordinateLineDomain_sourceOpenCube_three_of_mem_sourceOpenCube_one {n : ℕ}
    {i : Fin n} {x : SourceCubeSpace n} (hx : x ∈ sourceOpenCube n 1) :
    lineDomain (sourceOpenCube n 3) (coordinateLineBase i x) (sourceCoordinateVector i) =
      Set.Ioo (-3 : ℝ) 3 := by
  ext s
  constructor
  · intro hs
    have hi := hs i
    have habs : |s| < 3 := by
      simpa [lineDomain, sourceOpenCube, sourceCoordinateVector, coordinateLineBase] using hi
    simpa using (abs_lt.mp habs)
  · intro hs j
    by_cases hji : j = i
    · subst hji
      have habs : |s| < 3 := by
        simpa using (abs_lt.mpr hs)
      simpa [lineDomain, sourceOpenCube, sourceCoordinateVector, coordinateLineBase] using habs
    · have hxj : |x j| < 1 := by
        simpa using hx j
      have hxj3 : |x j| < 3 := by linarith
      simpa [lineDomain, sourceOpenCube, sourceCoordinateVector, coordinateLineBase, hji] using hxj3

/-- Convexity on the source cube restricts to convexity of every coordinate slice over a base in
`Q_1`, with the source interval `(-3,3)` as line domain. -/
theorem ConvexOn.coordinateLineRestriction_sourceCube_three {n : ℕ}
    {u : SourceCubeSpace n → ℝ} (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) {y : SourceCubeSpace n} (hy : y ∈ sourceOpenCube n 1) :
    ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3)
      (AleksandrovDifferentiability.lineRestriction u
        (coordinateLineBase i y) (sourceCoordinateVector i)) := by
  have hline :
      ConvexOn ℝ
        (lineDomain (sourceOpenCube n 3) (coordinateLineBase i y) (sourceCoordinateVector i))
        (AleksandrovDifferentiability.lineRestriction u
          (coordinateLineBase i y) (sourceCoordinateVector i)) :=
    AleksandrovDifferentiability.ConvexOn.lineRestriction
      (x := coordinateLineBase i y) (v := sourceCoordinateVector i) hu
  simpa [coordinateLineDomain_sourceOpenCube_three_of_mem_sourceOpenCube_one hy] using hline

/-- Convexity on the source cube supplies the monotonicity hypothesis needed for the
source-local clamped Stieltjes measure of each coordinate slice. -/
theorem ConvexOn.coordinateLineRightDeriv_monotoneOn_sourceIcc {n : ℕ}
    {u : SourceCubeSpace n → ℝ} (hu : ConvexOn ℝ (sourceOpenCube n 3) u)
    (i : Fin n) {y : SourceCubeSpace n} (hy : y ∈ sourceOpenCube n 1) :
    MonotoneOn
      (rightDeriv (AleksandrovDifferentiability.lineRestriction u
        (coordinateLineBase i y) (sourceCoordinateVector i)))
      (Set.Icc (-2 : ℝ) 2) :=
  ConvexOn.monotoneOn_projectRightDeriv_sourceIcc
    (ConvexOn.coordinateLineRestriction_sourceCube_three hu i hy)

/-- The one-dimensional endpoint-control estimate for every coordinate slice supplies the
concrete endpoint-control input used by the source upper-contact inclusion. -/
theorem CoordinateSliceOneDimEndpointControl.coordinateSliceMaximalEndpointControl {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {μslice : CoordinateSliceMeasureFamily n}
    {ρ K t : ℝ}
    (hendpoint : CoordinateSliceOneDimEndpointControl u μslice ρ K)
    (hu : ConvexOn ℝ (sourceOpenCube n 3) u) :
    CoordinateSliceMaximalEndpointControl u μslice ρ (K * t) t := by
  intro x hxQ hderiv hnot i h hh hρ
  have hp :
      SubgradientOn (sourceOpenCube n 3) u x (frechetGradient u x) :=
    AleksandrovDifferentiability.ConvexOn.sourceCube_subgradientOn_frechetGradient hu
      (sourceOpenCube_one_subset_interior_three hxQ) hderiv
  have hbase :
      coordinateLineBase i x + x i • sourceCoordinateVector i = x := by
    simpa [coordinateLinePoint] using coordinateLinePoint_base_self i x
  have hp_at :
      SubgradientOn (sourceOpenCube n 3) u
        (coordinateLineBase i x + x i • sourceCoordinateVector i) (frechetGradient u x) := by
    simpa [hbase] using hp
  have hlineDomain :
      lineDomain (sourceOpenCube n 3) (coordinateLineBase i x) (sourceCoordinateVector i) =
        Set.Ioo (-3 : ℝ) 3 :=
    coordinateLineDomain_sourceOpenCube_three_of_mem_sourceOpenCube_one hxQ
  have hlineSub :
      SubgradientOn (Set.Ioo (-3 : ℝ) 3)
        (lineRestriction u (coordinateLineBase i x) (sourceCoordinateVector i)) (x i)
        (inner ℝ (frechetGradient u x) (sourceCoordinateVector i)) := by
    simpa [hlineDomain] using
      (hp_at.lineRestriction_subgradientOn_at
        (x := coordinateLineBase i x) (v := sourceCoordinateVector i) (t := x i))
  have hxi_abs : |x i| < 1 := by
    simpa using hxQ i
  have hxi : x i ∈ sourceMaximalWindow := by
    simpa [sourceMaximalWindow] using (abs_lt.mp hxi_abs)
  have hone :=
    hendpoint hxQ hderiv i hxi hlineSub (hnot i) hh hρ
  simpa [mul_assoc] using hone

/-- Total bad-set measure estimate for the concrete localized-maximal slice predicate. This is
the exact Fubini plus weak-type estimate still to be proved from the one-dimensional localized
maximal theorem and the source mass bound for slice second-derivative measures. -/
def CoordinateSliceMaximalTotalBadSetEstimate {n : ℕ}
    (u : SourceCubeSpace n → ℝ) (μslice : CoordinateSliceMeasureFamily n) (C t : ℝ) : Prop :=
  volume
      (upperContactEstimateTotalBadSet u (coordinateSliceMaximalBadPredicate μslice) t) ≤
    ENNReal.ofReal (C * sourceCubeOscillation n u / t)

/-- The concrete localized-maximal total-bad-set estimate is monotone in the dimensional
constant. -/
theorem CoordinateSliceMaximalTotalBadSetEstimate.mono_constant {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {μslice : CoordinateSliceMeasureFamily n}
    {C C' t : ℝ}
    (h : CoordinateSliceMaximalTotalBadSetEstimate u μslice C t)
    (hCC' : C ≤ C') (ht : 0 < t) (hosc : 0 ≤ sourceCubeOscillation n u) :
    CoordinateSliceMaximalTotalBadSetEstimate u μslice C' t := by
  refine h.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hscale : 0 ≤ sourceCubeOscillation n u / t := div_nonneg hosc ht.le
  have hmul := mul_le_mul_of_nonneg_right hCC' hscale
  calc
    C * sourceCubeOscillation n u / t =
        C * (sourceCubeOscillation n u / t) := by ring
    _ ≤ C' * (sourceCubeOscillation n u / t) := hmul
    _ = C' * sourceCubeOscillation n u / t := by ring

/-- Boundedness supplies the oscillation nonnegativity needed for monotonicity of the concrete
localized-maximal total-bad-set estimate. -/
theorem CoordinateSliceMaximalTotalBadSetEstimate.mono_constant_of_boundedOn {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {μslice : CoordinateSliceMeasureFamily n}
    {C C' t : ℝ}
    (h : CoordinateSliceMaximalTotalBadSetEstimate u μslice C t)
    (hCC' : C ≤ C') (ht : 0 < t) (hbounded : BoundedOn (sourceOpenCube n 3) u) :
    CoordinateSliceMaximalTotalBadSetEstimate u μslice C' t :=
  h.mono_constant hCC' ht (sourceCubeOscillation_nonneg_of_boundedOn hbounded)

/-- Constant-bound finite-union assembly for the concrete localized-maximal total bad set. The
remaining Fubini work should provide the coordinate bounds; this theorem packages the null
non-differentiability set and finite union over coordinate directions. -/
theorem CoordinateSliceMaximalTotalBadSetEstimate.of_coordinate_bound {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {μslice : CoordinateSliceMeasureFamily n} {C t : ℝ}
    {B : ENNReal}
    (hdiff : volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hcoord :
      ∀ i : Fin n,
        volume (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t) ≤ B)
    (hbound : (n : ENNReal) * B ≤ ENNReal.ofReal (C * sourceCubeOscillation n u / t)) :
    CoordinateSliceMaximalTotalBadSetEstimate u μslice C t :=
  (volume_upperContactEstimateTotalBadSet_le_card_mul_of_coordinate_bound hdiff hcoord).trans
    hbound

/-- The remaining per-coordinate Fubini obligation for localized maximal bad sets. It says that
uniform one-dimensional bad-fiber bounds imply coordinate bad-set bounds. The constants are kept
separate because the Fubini step may introduce a dimensional factor. -/
def CoordinateSliceMaximalFubiniEstimate {n : ℕ}
    (μslice : CoordinateSliceMeasureFamily n) (Cline Ccoord osc t : ℝ) : Prop :=
  (∀ i : Fin n, ∀ ⦃y : SourceCubeSpace n⦄,
      y ∈ sourceOpenCube n 1 →
        volume (coordinateSliceLineBadSet μslice i y t) ≤
          ENNReal.ofReal (Cline * osc / t)) →
    ∀ i : Fin n,
      volume (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t) ≤
        ENNReal.ofReal (Ccoord * osc / t)

/-- The transverse Fubini estimate plus a real-valued constant comparison supplies the older
packaged per-coordinate Fubini estimate. -/
theorem CoordinateSliceMaximalTransverseFubiniEstimate.fubiniEstimate {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {Ctrans Cline Ccoord osc t : ℝ}
    (htrans : CoordinateSliceMaximalTransverseFubiniEstimate μslice Ctrans t)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hC : Ctrans * Cline ≤ Ccoord) (hscale : 0 ≤ osc / t) :
    CoordinateSliceMaximalFubiniEstimate μslice Cline Ccoord osc t := by
  intro hline i
  have hcoord := htrans (ENNReal.ofReal (Cline * osc / t)) hline i
  refine hcoord.trans ?_
  have hleft :
      ENNReal.ofReal Ctrans * ENNReal.ofReal (Cline * osc / t) =
        ENNReal.ofReal (Ctrans * (Cline * osc / t)) := by
    rw [ENNReal.ofReal_mul hCtrans_nonneg]
  have hreal :
      Ctrans * (Cline * osc / t) ≤ Ccoord * osc / t := by
    have hscaled := mul_le_mul_of_nonneg_right hC hscale
    calc
      Ctrans * (Cline * osc / t) = (Ctrans * Cline) * (osc / t) := by ring
      _ ≤ Ccoord * (osc / t) := hscaled
      _ = Ccoord * osc / t := by ring
  rw [hleft]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Coordinate bad-set measurability, the transverse-volume bound, and a scalar constant
comparison supply the older packaged Fubini estimate used by the maximal-slice assembly. -/
theorem CoordinateSliceMaximalFubiniEstimate.of_badSetMeasurable {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {Ctrans Cline Ccoord osc t : ℝ}
    (hbad : CoordinateSliceMaximalBadSetMeasurable μslice t)
    (hAmeasure :
      ∀ i : Fin n, volume (sourceTransverseOpenCube i 1) ≤ ENNReal.ofReal Ctrans)
    (hCtrans_nonneg : 0 ≤ Ctrans)
    (hC : Ctrans * Cline ≤ Ccoord) (hscale : 0 ≤ osc / t) :
    CoordinateSliceMaximalFubiniEstimate μslice Cline Ccoord osc t :=
  (CoordinateSliceMaximalTransverseFubiniEstimate.of_badSetMeasurable
    hbad hAmeasure).fubiniEstimate hCtrans_nonneg hC hscale

/-- Source mass bounds plus the localized maximal estimate supply the line-fiber hypotheses
needed by `CoordinateSliceMaximalFubiniEstimate`. -/
theorem CoordinateSliceMaximalFubiniEstimate.coordinate_bound_of_sourceMassBound {n : ℕ}
    {μslice : CoordinateSliceMeasureFamily n} {Cmax Ccoord osc t : ℝ}
    (hfubini : CoordinateSliceMaximalFubiniEstimate μslice (2 * Cmax) Ccoord osc t)
    (hmass : CoordinateSliceSourceMassBound μslice osc)
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t) :
    ∀ i : Fin n,
      volume (coordinateSliceBadSet (coordinateSliceMaximalBadPredicate μslice) i t) ≤
        ENNReal.ofReal (Ccoord * osc / t) :=
  hfubini fun i y hy => by
    simpa [mul_assoc] using hmass.lineBadSet_measure_le hmax ht i hy

/-- Assembly from the per-coordinate Fubini estimate to the concrete localized-maximal total
bad-set estimate. -/
theorem CoordinateSliceMaximalTotalBadSetEstimate.of_fubiniEstimate {n : ℕ}
    {u : SourceCubeSpace n → ℝ} {μslice : CoordinateSliceMeasureFamily n}
    {Cmax Ccoord Cmeasure t : ℝ}
    (hdiff : volume (sourceOpenCube n 1 \ firstOrderDifferentiabilitySet u) = 0)
    (hmass : CoordinateSliceSourceMassBound μslice (sourceCubeOscillation n u))
    (hmax : LocalizedMaximalEstimateStatement Cmax) (ht : 0 < t)
    (hfubini :
      CoordinateSliceMaximalFubiniEstimate μslice (2 * Cmax) Ccoord
        (sourceCubeOscillation n u) t)
    (hbound :
      (n : ENNReal) *
          ENNReal.ofReal (Ccoord * sourceCubeOscillation n u / t) ≤
        ENNReal.ofReal (Cmeasure * sourceCubeOscillation n u / t)) :
    CoordinateSliceMaximalTotalBadSetEstimate u μslice Cmeasure t :=
  CoordinateSliceMaximalTotalBadSetEstimate.of_coordinate_bound hdiff
    (hfubini.coordinate_bound_of_sourceMassBound hmass hmax ht) hbound

end AleksandrovDifferentiability
