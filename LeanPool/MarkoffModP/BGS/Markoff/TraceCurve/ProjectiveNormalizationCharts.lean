/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.AlgebraicGeometry.ConstantOpenGlueData
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.LaurentNormalization
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.ProjectiveChart
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Affine normalization charts and their overlap immersions

This module packages the integral-closure rings from the trace-cover endgame as explicit affine
schemes.  Their common torus overlaps are literal principal-open localizations, with open immersion
maps into the affine normalization charts.  The previously proved normalization transitions are
then conjugated onto these concrete overlap schemes.

The four-chart `Scheme.GlueData` is deliberately not asserted here: Mathlib requires explicit maps
on pullbacks of triple overlaps.  The objects, open immersions, transition isomorphisms, and their
ring-level cocycle constructed below are the inputs for that remaining categorical assembly.
-/

namespace BGS.Markoff

open AlgebraicGeometry

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- Explicit affine `Spec` model of the normalization of one trace-cover chart. -/
def weightedSplitTraceAffineNormalizationSpec (alpha beta : K) (d e : ℕ) : Scheme :=
  Spec (CommRingCat.of (WeightedSplitTraceAffineNormalizationRing alpha beta d e))

/-- Principal-open ring in the affine normalization obtained by inverting the original coordinate
product. -/
abbrev WeightedSplitTraceAffineNormalizationLaurentOpenRing
    (alpha beta : K) (d e : ℕ) :=
  Localization.Away
    (algebraMap (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
      (WeightedSplitTraceAffineNormalizationRing alpha beta d e)
      (weightedSplitTraceAffineCoordinateProduct alpha beta d e))

/-- The common torus overlap as an explicit affine scheme. -/
def weightedSplitTraceAffineNormalizationLaurentOpenSpec
    (alpha beta : K) (d e : ℕ) : Scheme :=
  Spec (CommRingCat.of
    (WeightedSplitTraceAffineNormalizationLaurentOpenRing alpha beta d e))

/-- The principal-open immersion of the normalized torus overlap into an affine normalization
chart. -/
def weightedSplitTraceAffineNormalizationLaurentOpenImmersion
    (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceAffineNormalizationLaurentOpenSpec alpha beta d e ⟶
      weightedSplitTraceAffineNormalizationSpec alpha beta d e :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (WeightedSplitTraceAffineNormalizationRing alpha beta d e)
      (WeightedSplitTraceAffineNormalizationLaurentOpenRing alpha beta d e)))

instance weightedSplitTraceAffineNormalizationLaurentOpenImmersion_isOpen
    (alpha beta : K) (d e : ℕ) :
    IsOpenImmersion
      (weightedSplitTraceAffineNormalizationLaurentOpenImmersion alpha beta d e) := by
  dsimp only [weightedSplitTraceAffineNormalizationLaurentOpenImmersion,
    weightedSplitTraceAffineNormalizationLaurentOpenSpec,
    weightedSplitTraceAffineNormalizationSpec,
    WeightedSplitTraceAffineNormalizationLaurentOpenRing]
  infer_instance

/-- First-coordinate inversion on the concrete principal-open normalization chart. -/
def weightedSplitTraceLeftAffineNormalizationOpenEquiv_of_irreducible
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    WeightedSplitTraceAffineNormalizationLaurentOpenRing alpha beta d e ≃+*
      WeightedSplitTraceAffineNormalizationLaurentOpenRing alpha beta d e := by
  letI : IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) :=
    weightedSplitTraceLaurentCoordinateRing_isDomain alpha beta d e hd he hbeta h
  exact conjugatedLeftNormalizationOpenEquiv alpha beta d e
    (weightedSplitTraceAffineNormalizationLaurentOpenEquiv_of_irreducible
      alpha beta d e hd he hbeta h)

/-- Second-coordinate inversion between the two concrete principal-open normalization charts. -/
def weightedSplitTraceRightAffineNormalizationOpenEquiv_of_irreducible
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e)) :
    WeightedSplitTraceAffineNormalizationLaurentOpenRing beta alpha d e ≃+*
      WeightedSplitTraceAffineNormalizationLaurentOpenRing alpha beta d e := by
  letI : IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) :=
    weightedSplitTraceLaurentCoordinateRing_isDomain alpha beta d e hd he hbeta h
  letI : IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e) :=
    weightedSplitTraceLaurentCoordinateRing_isDomain beta alpha d e hd he halpha hswap
  exact conjugatedRightNormalizationOpenEquiv alpha beta d e
    (weightedSplitTraceAffineNormalizationLaurentOpenEquiv_of_irreducible
      alpha beta d e hd he hbeta h)
    (weightedSplitTraceAffineNormalizationLaurentOpenEquiv_of_irreducible
      beta alpha d e hd he halpha hswap)

/-- Scheme automorphism of the concrete overlap induced by first-coordinate inversion. -/
def weightedSplitTraceLeftAffineNormalizationOpenSchemeIso_of_irreducible
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    weightedSplitTraceAffineNormalizationLaurentOpenSpec alpha beta d e ≅
    weightedSplitTraceAffineNormalizationLaurentOpenSpec alpha beta d e :=
  BGS.specIsoOfRingEquiv
    (weightedSplitTraceLeftAffineNormalizationOpenEquiv_of_irreducible
      alpha beta d e hd he hbeta h)

/-- Contravariant scheme isomorphism of concrete overlaps induced by second-coordinate inversion. -/
def weightedSplitTraceRightAffineNormalizationOpenSchemeIso_of_irreducible
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e)) :
    weightedSplitTraceAffineNormalizationLaurentOpenSpec alpha beta d e ≅
      weightedSplitTraceAffineNormalizationLaurentOpenSpec beta alpha d e :=
  BGS.specIsoOfRingEquiv
    (weightedSplitTraceRightAffineNormalizationOpenEquiv_of_irreducible
      alpha beta d e hd he halpha hbeta h hswap)

/-- The affine normalization scheme used by each of the four standard charts.  Inverting the
second coordinate swaps the two weights. -/
def weightedSplitTraceNormalizationChartScheme
    (alpha beta : K) (d e : ℕ) : WeightedSplitTraceProjectiveChart → Scheme
  | .affine | .invertFirst => weightedSplitTraceAffineNormalizationSpec alpha beta d e
  | .invertSecond | .invertBoth => weightedSplitTraceAffineNormalizationSpec beta alpha d e

/-- The common torus open inside each standard normalization chart. -/
def weightedSplitTraceNormalizationChartOpen
    (alpha beta : K) (d e : ℕ) : WeightedSplitTraceProjectiveChart → Scheme
  | .affine | .invertFirst => weightedSplitTraceAffineNormalizationLaurentOpenSpec alpha beta d e
  | .invertSecond | .invertBoth =>
      weightedSplitTraceAffineNormalizationLaurentOpenSpec beta alpha d e

/-- Principal-open immersion from each chart's torus overlap into that affine normalization
chart. -/
def weightedSplitTraceNormalizationChartOpenImmersion
    (alpha beta : K) (d e : ℕ) (i : WeightedSplitTraceProjectiveChart) :
    weightedSplitTraceNormalizationChartOpen alpha beta d e i ⟶
      weightedSplitTraceNormalizationChartScheme alpha beta d e i := by
  cases i with
  | affine | invertFirst =>
      exact weightedSplitTraceAffineNormalizationLaurentOpenImmersion alpha beta d e
  | invertSecond | invertBoth =>
      exact weightedSplitTraceAffineNormalizationLaurentOpenImmersion beta alpha d e

instance weightedSplitTraceNormalizationChartOpenImmersion_isOpen
    (alpha beta : K) (d e : ℕ) (i : WeightedSplitTraceProjectiveChart) :
    IsOpenImmersion
      (weightedSplitTraceNormalizationChartOpenImmersion alpha beta d e i) := by
  cases i with
  | affine | invertFirst =>
      exact weightedSplitTraceAffineNormalizationLaurentOpenImmersion_isOpen alpha beta d e
  | invertSecond | invertBoth =>
      exact weightedSplitTraceAffineNormalizationLaurentOpenImmersion_isOpen beta alpha d e

/-- Every chart overlap, expressed in its own coordinates, identified with the normalized Laurent
scheme in the original `(alpha, beta)` coordinates.  The four cases encode no inversion, first
inversion, second inversion, and both inversions respectively. -/
def weightedSplitTraceNormalizationChartOpenIsoCommon
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e))
    (i : WeightedSplitTraceProjectiveChart) :
    weightedSplitTraceNormalizationChartOpen alpha beta d e i ≅
      Spec (CommRingCat.of (WeightedSplitTraceLaurentNormalizationRing alpha beta d e)) := by
  letI : IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) :=
    weightedSplitTraceLaurentCoordinateRing_isDomain alpha beta d e hd he hbeta h
  letI : IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e) :=
    weightedSplitTraceLaurentCoordinateRing_isDomain beta alpha d e hd he halpha hswap
  let openA := weightedSplitTraceAffineNormalizationLaurentOpenSchemeIso_of_irreducible
    alpha beta d e hd he hbeta h
  let openB := weightedSplitTraceAffineNormalizationLaurentOpenSchemeIso_of_irreducible
    beta alpha d e hd he halpha hswap
  let left := weightedSplitTraceLeftInversionLaurentNormalizationSchemeIso alpha beta d e
  let right := weightedSplitTraceRightInversionLaurentNormalizationSchemeIso alpha beta d e
  cases i with
  | affine => exact openA.symm
  | invertFirst => exact openA.symm.trans left
  | invertSecond => exact openB.symm.trans right.symm
  | invertBoth => exact (openB.symm.trans right.symm).trans left

/-- The actual four-chart gluing datum for the normalized trace-cover charts.  The pullback-level
triple-overlap maps are supplied by `constantOpenGlueDataOfCommonTarget`; they are not assumed. -/
def weightedSplitTraceProjectiveNormalizationGlueData
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e)) :
    Scheme.GlueData :=
  BGS.constantOpenGlueDataOfCommonTarget
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartScheme alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartOpen alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartOpenImmersion alpha beta d e i.down)
    (Spec (CommRingCat.of (WeightedSplitTraceLaurentNormalizationRing alpha beta d e)))
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartOpenIsoCommon
        alpha beta d e hd he halpha hbeta h hswap i.down)

/-- The four affine normalization charts glued along their normalized torus opens. -/
def weightedSplitTraceProjectiveNormalization
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e)) : Scheme :=
  (weightedSplitTraceProjectiveNormalizationGlueData
    alpha beta d e hd he halpha hbeta h hswap).glued

/-- Open immersion of a standard affine normalization chart into the glued normalization. -/
def weightedSplitTraceNormalizationChartMap
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e))
    (i : WeightedSplitTraceProjectiveChartIndex) :
    weightedSplitTraceNormalizationChartScheme alpha beta d e i.down ⟶
      weightedSplitTraceProjectiveNormalization
        alpha beta d e hd he halpha hbeta h hswap :=
  (weightedSplitTraceProjectiveNormalizationGlueData
    alpha beta d e hd he halpha hbeta h hswap).ι i

instance weightedSplitTraceNormalizationChartMap_isOpen
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e))
    (i : WeightedSplitTraceProjectiveChartIndex) :
    IsOpenImmersion (weightedSplitTraceNormalizationChartMap
      alpha beta d e hd he halpha hbeta h hswap i) := by
  dsimp only [weightedSplitTraceNormalizationChartMap]
  exact Scheme.GlueData.ι_isOpenImmersion
    (weightedSplitTraceProjectiveNormalizationGlueData
      alpha beta d e hd he halpha hbeta h hswap) i

/-- The four standard affine normalization charts cover the glued normalization. -/
theorem weightedSplitTraceNormalizationChartMap_jointly_surjective
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e))
    (x : (weightedSplitTraceProjectiveNormalization
      alpha beta d e hd he halpha hbeta h hswap).carrier) :
    ∃ (i : WeightedSplitTraceProjectiveChartIndex)
      (y : (weightedSplitTraceNormalizationChartScheme alpha beta d e i.down).carrier),
      weightedSplitTraceNormalizationChartMap
        alpha beta d e hd he halpha hbeta h hswap i y = x :=
  (weightedSplitTraceProjectiveNormalizationGlueData
    alpha beta d e hd he halpha hbeta h hswap).ι_jointly_surjective x

end

end BGS.Markoff
