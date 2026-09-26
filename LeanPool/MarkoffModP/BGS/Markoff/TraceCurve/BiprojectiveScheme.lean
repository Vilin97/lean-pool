/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.AlgebraicGeometry.ConstantOpenGlueData
public import LeanPool.MarkoffModP.BGS.AlgebraicGeometry.SpecRingEquiv
public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.ChartLocalization
public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.ProjectiveChart
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The biprojective trace curve as a glued scheme

The published trace curve has four standard affine charts.  This module glues the corresponding
affine hypersurface schemes along their common Laurent torus, using the explicit coordinate
inversions already proved for the chart rings.
-/

@[expose] public section

namespace BGS.Markoff

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- One affine equation chart of the biprojective trace curve. -/
def weightedSplitTraceAffineCurveSpec (alpha beta : K) (d e : ℕ) : Scheme :=
  Spec (CommRingCat.of (WeightedSplitTraceAffineCoordinateRing alpha beta d e))

/-- The Laurent torus open in an affine equation chart. -/
def weightedSplitTraceLaurentCurveSpec (alpha beta : K) (d e : ℕ) : Scheme :=
  Spec (CommRingCat.of (WeightedSplitTraceLaurentCoordinateRing alpha beta d e))

/-- The torus-open immersion into an affine equation chart. -/
def weightedSplitTraceLaurentCurveOpenImmersion (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceLaurentCurveSpec alpha beta d e ⟶
      weightedSplitTraceAffineCurveSpec alpha beta d e :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
      (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)))

instance weightedSplitTraceLaurentCurveOpenImmersion_isOpen
    (alpha beta : K) (d e : ℕ) :
    IsOpenImmersion (weightedSplitTraceLaurentCurveOpenImmersion alpha beta d e) := by
  dsimp only [weightedSplitTraceLaurentCurveOpenImmersion,
    weightedSplitTraceLaurentCurveSpec, weightedSplitTraceAffineCurveSpec,
    WeightedSplitTraceLaurentCoordinateRing]
  infer_instance

/-- First-coordinate inversion on the raw Laurent curve scheme. -/
def weightedSplitTraceLeftInversionLaurentCurveSchemeIso
    (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceLaurentCurveSpec alpha beta d e ≅
      weightedSplitTraceLaurentCurveSpec alpha beta d e :=
  BGS.specIsoOfRingEquiv
    (weightedSplitTraceLeftInversionLaurentEquiv alpha beta d e)

/-- Second-coordinate inversion between the two weight orderings of the raw Laurent curve. -/
def weightedSplitTraceRightInversionLaurentCurveSchemeIso
    (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceLaurentCurveSpec alpha beta d e ≅
      weightedSplitTraceLaurentCurveSpec beta alpha d e :=
  BGS.specIsoOfRingEquiv
    (weightedSplitTraceRightInversionLaurentEquiv alpha beta d e)

/-- Raw affine equation scheme used by each standard projective chart. -/
def weightedSplitTraceProjectiveChartScheme
    (alpha beta : K) (d e : ℕ) : WeightedSplitTraceProjectiveChart → Scheme
  | .affine | .invertFirst => weightedSplitTraceAffineCurveSpec alpha beta d e
  | .invertSecond | .invertBoth => weightedSplitTraceAffineCurveSpec beta alpha d e

/-- Raw Laurent overlap in each standard projective chart. -/
def weightedSplitTraceProjectiveChartOpen
    (alpha beta : K) (d e : ℕ) : WeightedSplitTraceProjectiveChart → Scheme
  | .affine | .invertFirst => weightedSplitTraceLaurentCurveSpec alpha beta d e
  | .invertSecond | .invertBoth => weightedSplitTraceLaurentCurveSpec beta alpha d e

/-- The Laurent-open immersion in each raw projective chart. -/
def weightedSplitTraceProjectiveChartOpenImmersion
    (alpha beta : K) (d e : ℕ) (i : WeightedSplitTraceProjectiveChart) :
    weightedSplitTraceProjectiveChartOpen alpha beta d e i ⟶
      weightedSplitTraceProjectiveChartScheme alpha beta d e i := by
  cases i with
  | affine | invertFirst => exact weightedSplitTraceLaurentCurveOpenImmersion alpha beta d e
  | invertSecond | invertBoth => exact weightedSplitTraceLaurentCurveOpenImmersion beta alpha d e

instance weightedSplitTraceProjectiveChartOpenImmersion_isOpen
    (alpha beta : K) (d e : ℕ) (i : WeightedSplitTraceProjectiveChart) :
    IsOpenImmersion (weightedSplitTraceProjectiveChartOpenImmersion alpha beta d e i) := by
  cases i with
  | affine | invertFirst =>
      exact weightedSplitTraceLaurentCurveOpenImmersion_isOpen alpha beta d e
  | invertSecond | invertBoth =>
      exact weightedSplitTraceLaurentCurveOpenImmersion_isOpen beta alpha d e

/-- Every raw chart overlap identified with the Laurent curve in the original coordinates. -/
def weightedSplitTraceProjectiveChartOpenIsoCommon
    (alpha beta : K) (d e : ℕ) (i : WeightedSplitTraceProjectiveChart) :
    weightedSplitTraceProjectiveChartOpen alpha beta d e i ≅
      weightedSplitTraceLaurentCurveSpec alpha beta d e := by
  let left := weightedSplitTraceLeftInversionLaurentCurveSchemeIso alpha beta d e
  let right := weightedSplitTraceRightInversionLaurentCurveSchemeIso alpha beta d e
  cases i with
  | affine => exact Iso.refl _
  | invertFirst => exact left
  | invertSecond => exact right.symm
  | invertBoth => exact right.symm.trans left

/-- Four-chart gluing datum for the biprojective trace curve itself. -/
def weightedSplitTraceBiprojectiveCurveGlueData
    (alpha beta : K) (d e : ℕ) : Scheme.GlueData :=
  BGS.constantOpenGlueDataOfCommonTarget
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceProjectiveChartScheme alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceProjectiveChartOpen alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceProjectiveChartOpenImmersion alpha beta d e i.down)
    (weightedSplitTraceLaurentCurveSpec alpha beta d e)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceProjectiveChartOpenIsoCommon alpha beta d e i.down)

/-- The biprojective trace curve obtained by gluing its four standard affine equation charts. -/
def weightedSplitTraceBiprojectiveCurve (alpha beta : K) (d e : ℕ) : Scheme :=
  (weightedSplitTraceBiprojectiveCurveGlueData alpha beta d e).glued

/-- Open immersion of a standard raw chart into the biprojective trace curve. -/
def weightedSplitTraceProjectiveChartMap
    (alpha beta : K) (d e : ℕ) (i : WeightedSplitTraceProjectiveChartIndex) :
    weightedSplitTraceProjectiveChartScheme alpha beta d e i.down ⟶
      weightedSplitTraceBiprojectiveCurve alpha beta d e :=
  (weightedSplitTraceBiprojectiveCurveGlueData alpha beta d e).ι i

instance weightedSplitTraceProjectiveChartMap_isOpen
    (alpha beta : K) (d e : ℕ) (i : WeightedSplitTraceProjectiveChartIndex) :
    IsOpenImmersion (weightedSplitTraceProjectiveChartMap alpha beta d e i) :=
  Scheme.GlueData.ι_isOpenImmersion
    (weightedSplitTraceBiprojectiveCurveGlueData alpha beta d e) i

/-- The four raw affine charts jointly cover the biprojective trace curve. -/
theorem weightedSplitTraceProjectiveChartMap_jointly_surjective
    (alpha beta : K) (d e : ℕ)
    (x : (weightedSplitTraceBiprojectiveCurve alpha beta d e).carrier) :
    ∃ (i : WeightedSplitTraceProjectiveChartIndex)
      (y : (weightedSplitTraceProjectiveChartScheme alpha beta d e i.down).carrier),
      weightedSplitTraceProjectiveChartMap alpha beta d e i y = x :=
  (weightedSplitTraceBiprojectiveCurveGlueData alpha beta d e).ι_jointly_surjective x

end

end BGS.Markoff
