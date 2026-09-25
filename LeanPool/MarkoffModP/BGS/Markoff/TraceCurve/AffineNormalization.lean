/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.WeightedOddCoprimeIrreducibility
public import Mathlib.AlgebraicGeometry.Normalization

/-!
# Affine normalization of the weighted trace cover

This module constructs the actual relative normalization of the irreducible affine trace-cover
scheme inside its fraction field.  It connects the proved polynomial irreducibility theorem to
Mathlib's scheme-theoretic normalization construction.

This is only the affine normalization.  The endgame still requires compatible normalizations of
the other three biprojective charts, their gluing into a proper curve, the boundary-branch labels,
and the genus and Hasse--Weil estimates.
-/

@[expose] public section

namespace BGS.Markoff

open CategoryTheory
open AlgebraicGeometry

noncomputable section

variable {K : Type*} [Field K]

/-- Coordinate ring of the weighted denominator-cleared affine trace cover. -/
abbrev WeightedSplitTraceAffineCoordinateRing (alpha beta : K) (d e : ℕ) :=
  MvPolynomial (Fin 2) K ⧸ Ideal.span {splitTraceCoverPolynomial alpha beta d e}

/-- Irreducibility of the defining polynomial makes the affine coordinate ring a domain. -/
theorem weightedSplitTraceAffineCoordinateRing_isDomain
    (alpha beta : K) (d e : ℕ)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    IsDomain (WeightedSplitTraceAffineCoordinateRing alpha beta d e) := by
  let I : Ideal (MvPolynomial (Fin 2) K) :=
    Ideal.span {splitTraceCoverPolynomial alpha beta d e}
  have hprime : I.IsPrime :=
    (Ideal.span_singleton_prime h.ne_zero).mpr h.prime
  exact (Ideal.Quotient.isDomain_iff_prime I).mpr hprime

/-- The generic-point morphism from the fraction field to the irreducible affine curve. -/
def weightedSplitTraceAffineGenericPointMorphism
    (alpha beta : K) (d e : ℕ)
    [IsDomain (WeightedSplitTraceAffineCoordinateRing alpha beta d e)] :
    Spec (CommRingCat.of
      (FractionRing (WeightedSplitTraceAffineCoordinateRing alpha beta d e))) ⟶
      Spec (CommRingCat.of (WeightedSplitTraceAffineCoordinateRing alpha beta d e)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
      (FractionRing (WeightedSplitTraceAffineCoordinateRing alpha beta d e))))

/-- The relative normalization of the affine trace cover inside its fraction field. -/
def weightedSplitTraceAffineNormalization
    (alpha beta : K) (d e : ℕ)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) : Scheme := by
  letI : IsDomain (WeightedSplitTraceAffineCoordinateRing alpha beta d e) :=
    weightedSplitTraceAffineCoordinateRing_isDomain alpha beta d e h
  exact (weightedSplitTraceAffineGenericPointMorphism alpha beta d e).normalization

/-- The integral morphism from the affine normalization to the original affine curve. -/
def weightedSplitTraceAffineNormalizationToCurve
    (alpha beta : K) (d e : ℕ)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    weightedSplitTraceAffineNormalization alpha beta d e h ⟶
      Spec (CommRingCat.of
        (WeightedSplitTraceAffineCoordinateRing alpha beta d e)) := by
  letI : IsDomain (WeightedSplitTraceAffineCoordinateRing alpha beta d e) :=
    weightedSplitTraceAffineCoordinateRing_isDomain alpha beta d e h
  exact (weightedSplitTraceAffineGenericPointMorphism alpha beta d e).fromNormalization

instance weightedSplitTraceAffineNormalizationToCurve_isIntegral
    (alpha beta : K) (d e : ℕ)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    IsIntegralHom (weightedSplitTraceAffineNormalizationToCurve alpha beta d e h) := by
  dsimp [weightedSplitTraceAffineNormalizationToCurve,
    weightedSplitTraceAffineNormalization]
  infer_instance

instance weightedSplitTraceAffineNormalization_isIntegral
    (alpha beta : K) (d e : ℕ)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    IsIntegral (weightedSplitTraceAffineNormalization alpha beta d e h) := by
  let : IsDomain (WeightedSplitTraceAffineCoordinateRing alpha beta d e) :=
    weightedSplitTraceAffineCoordinateRing_isDomain alpha beta d e h
  dsimp [weightedSplitTraceAffineNormalization]
  infer_instance

instance weightedSplitTraceAffineNormalization_isReduced
    (alpha beta : K) (d e : ℕ)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    IsReduced (weightedSplitTraceAffineNormalization alpha beta d e h) := by
  let : IsDomain (WeightedSplitTraceAffineCoordinateRing alpha beta d e) :=
    weightedSplitTraceAffineCoordinateRing_isDomain alpha beta d e h
  dsimp [weightedSplitTraceAffineNormalization]
  infer_instance

/-- The actual geometric affine normalization in the paper's positive-exponent range, obtained by
combining absolute irreducibility with the relative-normalization construction. -/
def weightedSplitTraceGeometricAffineNormalization
    (alpha beta : K) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hnondegenerate : alpha * beta ≠ 1)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e) (heChar : (e : K) ≠ 0) : Scheme := by
  let phi : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hirred := splitTraceCoverPolynomial_absolutelyIrreducible_of_positiveExponents
    alpha beta halpha hbeta hnondegenerate e d he hd heChar
  rw [map_splitTraceCoverPolynomial phi alpha beta d e] at hirred
  exact weightedSplitTraceAffineNormalization (phi alpha) (phi beta) d e hirred

/-- The two affine normalizations needed for all four standard charts of the biprojective closure.
The first-coordinate inversion preserves the weights, while the second-coordinate inversion swaps
them.  This pair is not yet a glued projective scheme. -/
def weightedSplitTraceGeometricChartNormalizations
    (alpha beta : K) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hnondegenerate : alpha * beta ≠ 1)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e) (heChar : (e : K) ≠ 0) :
    Scheme × Scheme :=
  (weightedSplitTraceGeometricAffineNormalization alpha beta halpha hbeta
      hnondegenerate d e hd he heChar,
    weightedSplitTraceGeometricAffineNormalization beta alpha hbeta halpha
      (by simpa [mul_comm] using hnondegenerate) d e hd he heChar)

end

end BGS.Markoff
