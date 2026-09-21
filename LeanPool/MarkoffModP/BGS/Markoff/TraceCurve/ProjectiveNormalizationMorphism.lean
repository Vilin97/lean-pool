/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.BiprojectiveScheme
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.ProjectiveNormalizationCharts

/-!
# The normalization morphism on trace-curve charts

This module connects the integral-closure charts to the raw biprojective trace curve.  The key
point is the explicit principal-open square: localization of the affine normalization map agrees
with normalization of the Laurent chart.  The coordinate inversions are then checked to commute
with the raw-to-normalized Laurent map.
-/

namespace BGS.Markoff

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- Canonical ring map from an affine trace chart to its integral closure. -/
def weightedSplitTraceAffineNormalizationRingHom (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceAffineCoordinateRing alpha beta d e →+*
      WeightedSplitTraceAffineNormalizationRing alpha beta d e :=
  algebraMap _ _

/-- Canonical localization map from an affine normalization to its Laurent principal open. -/
def weightedSplitTraceAffineNormalizationAwayRingHom (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceAffineNormalizationRing alpha beta d e →+*
      WeightedSplitTraceAffineNormalizationLaurentOpenRing alpha beta d e :=
  algebraMap _ _

/-- Canonical ring map from an affine trace chart to its Laurent principal open. -/
def weightedSplitTraceAffineLaurentRingHom (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceAffineCoordinateRing alpha beta d e →+*
      WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
  algebraMap _ _

/-- Canonical ring map from the raw Laurent chart to its normalization. -/
def weightedSplitTraceLaurentNormalizationRingHom (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceLaurentCoordinateRing alpha beta d e →+*
      WeightedSplitTraceLaurentNormalizationRing alpha beta d e :=
  algebraMap _ _

/-- Inverse of the comparison between the localized affine normalization and normalized Laurent
ring. -/
def weightedSplitTraceAffineOpenInverseRingHom_of_irreducible
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    WeightedSplitTraceLaurentNormalizationRing alpha beta d e →+*
      WeightedSplitTraceAffineNormalizationLaurentOpenRing alpha beta d e :=
  (weightedSplitTraceAffineNormalizationLaurentOpenEquiv_of_irreducible
    alpha beta d e hd he hbeta h).symm.toRingHom

/-- Before applying the integral-closure comparison, the two routes from the affine chart to the
localized affine normalization are equal by the scalar-tower law. -/
theorem weightedSplitTraceRawPrincipalOpenSquare
    (alpha beta : K) (d e : ℕ)
    [IsDomain (WeightedSplitTraceAffineCoordinateRing alpha beta d e)] :
    (integralClosureAwayMap
        (weightedSplitTraceAffineCoordinateProduct alpha beta d e)).comp
        (weightedSplitTraceAffineLaurentRingHom alpha beta d e) =
      (weightedSplitTraceAffineNormalizationAwayRingHom alpha beta d e).comp
        (weightedSplitTraceAffineNormalizationRingHom alpha beta d e) := by
  apply DFunLike.ext _ _
  intro r
  simp [integralClosureAwayMap, weightedSplitTraceAffineLaurentRingHom,
    weightedSplitTraceAffineNormalizationAwayRingHom,
    weightedSplitTraceAffineNormalizationRingHom]
  exact IsScalarTower.algebraMap_apply _ _ _ r

/-- Ring-level affine-chart square for the normalization map. -/
theorem weightedSplitTraceAffineNormalizationRingSquare
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    (weightedSplitTraceAffineNormalizationAwayRingHom alpha beta d e).comp
        (weightedSplitTraceAffineNormalizationRingHom alpha beta d e) =
      (weightedSplitTraceAffineOpenInverseRingHom_of_irreducible
          alpha beta d e hd he hbeta h).comp
        ((weightedSplitTraceLaurentNormalizationRingHom alpha beta d e).comp
          (weightedSplitTraceAffineLaurentRingHom alpha beta d e)) := by
  letI : IsDomain (WeightedSplitTraceAffineCoordinateRing alpha beta d e) :=
    weightedSplitTraceAffineCoordinateRing_isDomain alpha beta d e h
  let E := weightedSplitTraceAffineNormalizationLaurentOpenEquiv_of_irreducible
    alpha beta d e hd he hbeta h
  apply DFunLike.ext _ _
  intro r
  apply E.injective
  dsimp only [weightedSplitTraceAffineOpenInverseRingHom_of_irreducible]
  change E (((weightedSplitTraceAffineNormalizationAwayRingHom alpha beta d e).comp
      (weightedSplitTraceAffineNormalizationRingHom alpha beta d e)) r) =
    E (E.symm (((weightedSplitTraceLaurentNormalizationRingHom alpha beta d e).comp
      (weightedSplitTraceAffineLaurentRingHom alpha beta d e)) r))
  rw [E.apply_symm_apply]
  have hc := integralClosureAwayEquiv_comp_map
    (weightedSplitTraceAffineCoordinateProduct alpha beta d e)
    (weightedSplitTraceAffineCoordinateProduct_ne_zero_of_irreducible
      alpha beta d e hd he hbeta h)
  have hr := weightedSplitTraceRawPrincipalOpenSquare alpha beta d e
  rw [← DFunLike.congr_fun hr r]
  exact DFunLike.congr_fun hc ((weightedSplitTraceAffineLaurentRingHom alpha beta d e) r)

/-- The affine normalization chart maps to the corresponding raw affine curve chart. -/
def weightedSplitTraceAffineIntegralClosureToCurve (alpha beta : K) (d e : ℕ) :
    weightedSplitTraceAffineNormalizationSpec alpha beta d e ⟶
      weightedSplitTraceAffineCurveSpec alpha beta d e :=
  Spec.map (CommRingCat.ofHom
    (weightedSplitTraceAffineNormalizationRingHom alpha beta d e))

/-- The normalized common Laurent chart maps to the raw Laurent chart. -/
def weightedSplitTraceLaurentNormalizationToCurve (alpha beta : K) (d e : ℕ) :
    Spec (CommRingCat.of (WeightedSplitTraceLaurentNormalizationRing alpha beta d e)) ⟶
      weightedSplitTraceLaurentCurveSpec alpha beta d e :=
  Spec.map (CommRingCat.ofHom
    (weightedSplitTraceLaurentNormalizationRingHom alpha beta d e))

/-- Scheme-level affine-chart square for the normalization map. -/
theorem weightedSplitTraceAffineNormalizationSquare
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    weightedSplitTraceAffineNormalizationLaurentOpenImmersion alpha beta d e ≫
        weightedSplitTraceAffineIntegralClosureToCurve alpha beta d e =
      (weightedSplitTraceAffineNormalizationLaurentOpenSchemeIso_of_irreducible
          alpha beta d e hd he hbeta h).inv ≫
        weightedSplitTraceLaurentNormalizationToCurve alpha beta d e ≫
        weightedSplitTraceLaurentCurveOpenImmersion alpha beta d e := by
  change
    Spec.map (CommRingCat.ofHom
        (weightedSplitTraceAffineNormalizationAwayRingHom alpha beta d e)) ≫
      Spec.map (CommRingCat.ofHom
        (weightedSplitTraceAffineNormalizationRingHom alpha beta d e)) =
    Spec.map (CommRingCat.ofHom
        (weightedSplitTraceAffineOpenInverseRingHom_of_irreducible
          alpha beta d e hd he hbeta h)) ≫
      Spec.map (CommRingCat.ofHom
        (weightedSplitTraceLaurentNormalizationRingHom alpha beta d e)) ≫
      Spec.map (CommRingCat.ofHom
        (weightedSplitTraceAffineLaurentRingHom alpha beta d e))
  exact BGS.specMap_two_eq_three_of_comp_eq
    (weightedSplitTraceAffineNormalizationRingHom alpha beta d e)
    (weightedSplitTraceAffineNormalizationAwayRingHom alpha beta d e)
    (weightedSplitTraceAffineLaurentRingHom alpha beta d e)
    (weightedSplitTraceLaurentNormalizationRingHom alpha beta d e)
    (weightedSplitTraceAffineOpenInverseRingHom_of_irreducible
      alpha beta d e hd he hbeta h)
    (weightedSplitTraceAffineNormalizationRingSquare alpha beta d e hd he hbeta h)

/-- First-coordinate inversion commutes with the raw-to-normalized Laurent ring map. -/
theorem weightedSplitTraceLeftLaurentNormalizationRingSquare
    (alpha beta : K) (d e : ℕ)
    [IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)]
    [IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e)] :
    (weightedSplitTraceLeftInversionLaurentNormalizationEquiv alpha beta d e).toRingHom.comp
        (weightedSplitTraceLaurentNormalizationRingHom alpha beta d e) =
      (weightedSplitTraceLaurentNormalizationRingHom alpha beta d e).comp
        (weightedSplitTraceLeftInversionLaurentEquiv alpha beta d e).toRingHom :=
  integralClosureFractionRingEquiv_comp_algebraMap
    (weightedSplitTraceLeftInversionLaurentEquiv alpha beta d e)

/-- Second-coordinate inversion commutes with the raw-to-normalized Laurent ring maps. -/
theorem weightedSplitTraceRightLaurentNormalizationRingSquare
    (alpha beta : K) (d e : ℕ)
    [IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)]
    [IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e)] :
    (weightedSplitTraceRightInversionLaurentNormalizationEquiv alpha beta d e).toRingHom.comp
        (weightedSplitTraceLaurentNormalizationRingHom beta alpha d e) =
      (weightedSplitTraceLaurentNormalizationRingHom alpha beta d e).comp
        (weightedSplitTraceRightInversionLaurentEquiv alpha beta d e).toRingHom :=
  integralClosureFractionRingEquiv_comp_algebraMap
    (weightedSplitTraceRightInversionLaurentEquiv alpha beta d e)

/-- Scheme-level naturality of first-coordinate inversion. -/
@[reassoc]
theorem weightedSplitTraceLeftLaurentNormalizationSquare
    (alpha beta : K) (d e : ℕ)
    [IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)]
    [IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e)] :
    (weightedSplitTraceLeftInversionLaurentNormalizationSchemeIso alpha beta d e).hom ≫
        weightedSplitTraceLaurentNormalizationToCurve alpha beta d e =
      weightedSplitTraceLaurentNormalizationToCurve alpha beta d e ≫
        (weightedSplitTraceLeftInversionLaurentCurveSchemeIso alpha beta d e).hom := by
  change
    Spec.map (CommRingCat.ofHom
        (weightedSplitTraceLeftInversionLaurentNormalizationEquiv alpha beta d e).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (weightedSplitTraceLaurentNormalizationRingHom alpha beta d e)) =
    Spec.map (CommRingCat.ofHom
        (weightedSplitTraceLaurentNormalizationRingHom alpha beta d e)) ≫
      Spec.map (CommRingCat.ofHom
        (weightedSplitTraceLeftInversionLaurentEquiv alpha beta d e).toRingHom)
  exact BGS.specMap_two_eq_two_of_comp_eq
    (weightedSplitTraceLaurentNormalizationRingHom alpha beta d e)
    (weightedSplitTraceLeftInversionLaurentNormalizationEquiv alpha beta d e).toRingHom
    (weightedSplitTraceLeftInversionLaurentEquiv alpha beta d e).toRingHom
    (weightedSplitTraceLaurentNormalizationRingHom alpha beta d e)
    (weightedSplitTraceLeftLaurentNormalizationRingSquare alpha beta d e)

/-- Scheme-level naturality of second-coordinate inversion. -/
@[reassoc]
theorem weightedSplitTraceRightLaurentNormalizationSquare
    (alpha beta : K) (d e : ℕ)
    [IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)]
    [IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e)] :
    (weightedSplitTraceRightInversionLaurentNormalizationSchemeIso alpha beta d e).hom ≫
        weightedSplitTraceLaurentNormalizationToCurve beta alpha d e =
      weightedSplitTraceLaurentNormalizationToCurve alpha beta d e ≫
        (weightedSplitTraceRightInversionLaurentCurveSchemeIso alpha beta d e).hom := by
  change
    Spec.map (CommRingCat.ofHom
        (weightedSplitTraceRightInversionLaurentNormalizationEquiv alpha beta d e).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (weightedSplitTraceLaurentNormalizationRingHom beta alpha d e)) =
    Spec.map (CommRingCat.ofHom
        (weightedSplitTraceLaurentNormalizationRingHom alpha beta d e)) ≫
      Spec.map (CommRingCat.ofHom
        (weightedSplitTraceRightInversionLaurentEquiv alpha beta d e).toRingHom)
  exact BGS.specMap_two_eq_two_of_comp_eq
    (weightedSplitTraceLaurentNormalizationRingHom beta alpha d e)
    (weightedSplitTraceRightInversionLaurentNormalizationEquiv alpha beta d e).toRingHom
    (weightedSplitTraceRightInversionLaurentEquiv alpha beta d e).toRingHom
    (weightedSplitTraceLaurentNormalizationRingHom alpha beta d e)
    (weightedSplitTraceRightLaurentNormalizationRingSquare alpha beta d e)

/-- Inverse form of second-coordinate naturality, oriented for the swapped affine charts. -/
@[reassoc]
theorem weightedSplitTraceRightLaurentNormalizationInverseSquare
    (alpha beta : K) (d e : ℕ)
    [IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)]
    [IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e)] :
    (weightedSplitTraceRightInversionLaurentNormalizationSchemeIso alpha beta d e).inv ≫
        weightedSplitTraceLaurentNormalizationToCurve alpha beta d e ≫
        (weightedSplitTraceRightInversionLaurentCurveSchemeIso alpha beta d e).hom =
      weightedSplitTraceLaurentNormalizationToCurve beta alpha d e := by
  rw [← weightedSplitTraceRightLaurentNormalizationSquare alpha beta d e]
  simp

/-- Compatibility square for the chart obtained by inverting the first coordinate. -/
theorem weightedSplitTraceFirstInvertedNormalizationSquare
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e)) :
    weightedSplitTraceAffineNormalizationLaurentOpenImmersion alpha beta d e ≫
        weightedSplitTraceAffineIntegralClosureToCurve alpha beta d e =
      ((weightedSplitTraceAffineNormalizationLaurentOpenSchemeIso_of_irreducible
          alpha beta d e hd he hbeta h).symm.trans
        (weightedSplitTraceLeftInversionLaurentNormalizationSchemeIso alpha beta d e)).hom ≫
        weightedSplitTraceLaurentNormalizationToCurve alpha beta d e ≫
        (weightedSplitTraceLeftInversionLaurentCurveSchemeIso alpha beta d e).inv ≫
        weightedSplitTraceLaurentCurveOpenImmersion alpha beta d e := by
  letI : IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) :=
    weightedSplitTraceLaurentCoordinateRing_isDomain alpha beta d e hd he hbeta h
  letI : IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e) :=
    weightedSplitTraceLaurentCoordinateRing_isDomain beta alpha d e hd he halpha hswap
  calc
    _ = (weightedSplitTraceAffineNormalizationLaurentOpenSchemeIso_of_irreducible
          alpha beta d e hd he hbeta h).inv ≫
        weightedSplitTraceLaurentNormalizationToCurve alpha beta d e ≫
        weightedSplitTraceLaurentCurveOpenImmersion alpha beta d e :=
      weightedSplitTraceAffineNormalizationSquare alpha beta d e hd he hbeta h
    _ = _ := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rw [weightedSplitTraceLeftLaurentNormalizationSquare_assoc alpha beta d e]
      simp

/-- Compatibility square for the chart obtained by inverting the second coordinate. -/
theorem weightedSplitTraceSecondInvertedNormalizationSquare
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e)) :
    weightedSplitTraceAffineNormalizationLaurentOpenImmersion beta alpha d e ≫
        weightedSplitTraceAffineIntegralClosureToCurve beta alpha d e =
      ((weightedSplitTraceAffineNormalizationLaurentOpenSchemeIso_of_irreducible
          beta alpha d e hd he halpha hswap).symm.trans
        (weightedSplitTraceRightInversionLaurentNormalizationSchemeIso alpha beta d e).symm).hom ≫
        weightedSplitTraceLaurentNormalizationToCurve alpha beta d e ≫
        (weightedSplitTraceRightInversionLaurentCurveSchemeIso alpha beta d e).hom ≫
        weightedSplitTraceLaurentCurveOpenImmersion beta alpha d e := by
  letI : IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) :=
    weightedSplitTraceLaurentCoordinateRing_isDomain alpha beta d e hd he hbeta h
  letI : IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e) :=
    weightedSplitTraceLaurentCoordinateRing_isDomain beta alpha d e hd he halpha hswap
  calc
    _ = (weightedSplitTraceAffineNormalizationLaurentOpenSchemeIso_of_irreducible
          beta alpha d e hd he halpha hswap).inv ≫
        weightedSplitTraceLaurentNormalizationToCurve beta alpha d e ≫
        weightedSplitTraceLaurentCurveOpenImmersion beta alpha d e :=
      weightedSplitTraceAffineNormalizationSquare beta alpha d e hd he halpha hswap
    _ = _ := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rw [weightedSplitTraceRightLaurentNormalizationInverseSquare_assoc alpha beta d e]

/-- Compatibility square for the chart obtained by inverting both coordinates. -/
theorem weightedSplitTraceBothInvertedNormalizationSquare
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e)) :
    weightedSplitTraceAffineNormalizationLaurentOpenImmersion beta alpha d e ≫
        weightedSplitTraceAffineIntegralClosureToCurve beta alpha d e =
      (((weightedSplitTraceAffineNormalizationLaurentOpenSchemeIso_of_irreducible
          beta alpha d e hd he halpha hswap).symm.trans
        (weightedSplitTraceRightInversionLaurentNormalizationSchemeIso alpha beta d e).symm).trans
        (weightedSplitTraceLeftInversionLaurentNormalizationSchemeIso alpha beta d e)).hom ≫
        weightedSplitTraceLaurentNormalizationToCurve alpha beta d e ≫
        ((weightedSplitTraceRightInversionLaurentCurveSchemeIso alpha beta d e).symm.trans
          (weightedSplitTraceLeftInversionLaurentCurveSchemeIso alpha beta d e)).inv ≫
        weightedSplitTraceLaurentCurveOpenImmersion beta alpha d e := by
  letI : IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) :=
    weightedSplitTraceLaurentCoordinateRing_isDomain alpha beta d e hd he hbeta h
  letI : IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e) :=
    weightedSplitTraceLaurentCoordinateRing_isDomain beta alpha d e hd he halpha hswap
  calc
    _ = (weightedSplitTraceAffineNormalizationLaurentOpenSchemeIso_of_irreducible
          beta alpha d e hd he halpha hswap).inv ≫
        weightedSplitTraceLaurentNormalizationToCurve beta alpha d e ≫
        weightedSplitTraceLaurentCurveOpenImmersion beta alpha d e :=
      weightedSplitTraceAffineNormalizationSquare beta alpha d e hd he halpha hswap
    _ = _ := by
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc]
      rw [weightedSplitTraceLeftLaurentNormalizationSquare_assoc alpha beta d e]
      simp only [Iso.hom_inv_id_assoc]
      rw [weightedSplitTraceRightLaurentNormalizationInverseSquare_assoc alpha beta d e]

/-- Raw target map for each of the four affine normalization charts. -/
def weightedSplitTraceNormalizationChartToProjectiveChart
    (alpha beta : K) (d e : ℕ) :
    (i : WeightedSplitTraceProjectiveChart) →
      weightedSplitTraceNormalizationChartScheme alpha beta d e i ⟶
        weightedSplitTraceProjectiveChartScheme alpha beta d e i
  | .affine | .invertFirst => weightedSplitTraceAffineIntegralClosureToCurve alpha beta d e
  | .invertSecond | .invertBoth => weightedSplitTraceAffineIntegralClosureToCurve beta alpha d e

/-- All four affine normalization maps restrict to the same raw Laurent normalization map under
the chosen common-overlap identifications. -/
theorem weightedSplitTraceNormalizationChartCompatibility
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e))
    (i : WeightedSplitTraceProjectiveChart) :
    weightedSplitTraceNormalizationChartOpenImmersion alpha beta d e i ≫
        weightedSplitTraceNormalizationChartToProjectiveChart alpha beta d e i =
      (weightedSplitTraceNormalizationChartOpenIsoCommon
          alpha beta d e hd he halpha hbeta h hswap i).hom ≫
        weightedSplitTraceLaurentNormalizationToCurve alpha beta d e ≫
        (weightedSplitTraceProjectiveChartOpenIsoCommon alpha beta d e i).inv ≫
        weightedSplitTraceProjectiveChartOpenImmersion alpha beta d e i := by
  cases i with
  | affine =>
      exact weightedSplitTraceAffineNormalizationSquare alpha beta d e hd he hbeta h
  | invertFirst =>
      dsimp [weightedSplitTraceNormalizationChartOpenImmersion,
        weightedSplitTraceNormalizationChartToProjectiveChart,
        weightedSplitTraceNormalizationChartOpenIsoCommon,
        weightedSplitTraceProjectiveChartOpenIsoCommon,
        weightedSplitTraceProjectiveChartOpenImmersion]
      exact weightedSplitTraceFirstInvertedNormalizationSquare
        alpha beta d e hd he halpha hbeta h hswap
  | invertSecond =>
      dsimp [weightedSplitTraceNormalizationChartOpenImmersion,
        weightedSplitTraceNormalizationChartToProjectiveChart,
        weightedSplitTraceNormalizationChartOpenIsoCommon,
        weightedSplitTraceProjectiveChartOpenIsoCommon,
        weightedSplitTraceProjectiveChartOpenImmersion]
      exact weightedSplitTraceSecondInvertedNormalizationSquare
        alpha beta d e hd he halpha hbeta h hswap
  | invertBoth =>
      dsimp [weightedSplitTraceNormalizationChartOpenImmersion,
        weightedSplitTraceNormalizationChartToProjectiveChart,
        weightedSplitTraceNormalizationChartOpenIsoCommon,
        weightedSplitTraceProjectiveChartOpenIsoCommon,
        weightedSplitTraceProjectiveChartOpenImmersion]
      exact weightedSplitTraceBothInvertedNormalizationSquare
        alpha beta d e hd he halpha hbeta h hswap

/-- The global morphism from the glued integral-closure charts to the raw biprojective trace
curve, descended from the four compatible affine normalization maps. -/
def weightedSplitTraceProjectiveNormalizationToBiprojectiveCurve
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e)) :
    weightedSplitTraceProjectiveNormalization
        alpha beta d e hd he halpha hbeta h hswap ⟶
      weightedSplitTraceBiprojectiveCurve alpha beta d e :=
  BGS.constantOpenGlueDataOfCommonTargetMap
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartScheme alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartOpen alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceProjectiveChartScheme alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceProjectiveChartOpen alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartOpenImmersion alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceProjectiveChartOpenImmersion alpha beta d e i.down)
    (Spec (CommRingCat.of (WeightedSplitTraceLaurentNormalizationRing alpha beta d e)))
    (weightedSplitTraceLaurentCurveSpec alpha beta d e)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartOpenIsoCommon
        alpha beta d e hd he halpha hbeta h hswap i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceProjectiveChartOpenIsoCommon alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartToProjectiveChart alpha beta d e i.down)
    (weightedSplitTraceLaurentNormalizationToCurve alpha beta d e)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartCompatibility
        alpha beta d e hd he halpha hbeta h hswap i.down)

/-- On every standard affine chart, the global normalization morphism is the canonical affine
integral-closure map followed by the corresponding raw chart inclusion. -/
@[reassoc]
theorem weightedSplitTraceNormalizationChartMap_toBiprojectiveCurve
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e))
    (i : WeightedSplitTraceProjectiveChartIndex) :
    weightedSplitTraceNormalizationChartMap
        alpha beta d e hd he halpha hbeta h hswap i ≫
      weightedSplitTraceProjectiveNormalizationToBiprojectiveCurve
        alpha beta d e hd he halpha hbeta h hswap =
    weightedSplitTraceNormalizationChartToProjectiveChart alpha beta d e i.down ≫
      weightedSplitTraceProjectiveChartMap alpha beta d e i := by
  exact BGS.constantOpenGlueDataOfCommonTargetMap_chart
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartScheme alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartOpen alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceProjectiveChartScheme alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceProjectiveChartOpen alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartOpenImmersion alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceProjectiveChartOpenImmersion alpha beta d e i.down)
    (Spec (CommRingCat.of (WeightedSplitTraceLaurentNormalizationRing alpha beta d e)))
    (weightedSplitTraceLaurentCurveSpec alpha beta d e)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartOpenIsoCommon
        alpha beta d e hd he halpha hbeta h hswap i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceProjectiveChartOpenIsoCommon alpha beta d e i.down)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartToProjectiveChart alpha beta d e i.down)
    (weightedSplitTraceLaurentNormalizationToCurve alpha beta d e)
    (fun i : WeightedSplitTraceProjectiveChartIndex ↦
      weightedSplitTraceNormalizationChartCompatibility
        alpha beta d e hd he halpha hbeta h hswap i.down)
    i

end

end BGS.Markoff
