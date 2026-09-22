/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveSupportRank
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveBidegreeBridge
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageBaseChange
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageGaloisBound
import Mathlib.Tactic

/-!
# The Corvaja--Zannier source-to-powered-image index bound

This module transports the Galois stabilizer count from algebraically closed
constants back to the original constant field.  Absolute irreducibility makes
the powered-image degree invariant under this extension of constants, while
the semantic non-subtorus hypothesis supplies the rank-two support determinant.
-/

namespace BGS.CorvajaZannier

noncomputable section

/-- The exact source-to-powered-image bound, with separability of the two power
maps expressed by nonvanishing of the exponent casts. -/
theorem finrank_poweredImageOverFirst_le_twice_bidegree_of_nonzero_natCast
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hnot : BGS.External.TorusCurveNotSubtorusTranslate f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmK : (m : K) ≠ 0) (hnK : (n : K) ≠ 0) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (PoweredImageOverFirst f m n)
        (PlaneCurveFunctionField f) ≤
      2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f := by
  let A := AlgebraicClosure K
  let fA : MvPolynomial (Fin 2) A :=
    MvPolynomial.map (algebraMap K A) f
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure habsolute
  have hfA : Irreducible fA := habsolute
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : IsDomain (PlaneCurveCoordinateRing fA) :=
    planeCurveCoordinateRing_isDomain hfA
  have hpartialFirstA : MvPolynomial.pderiv 0 fA ≠ 0 := by
    rw [MvPolynomial.pderiv_map]
    intro hzero
    apply hpartialFirst
    exact MvPolynomial.map_injective (algebraMap K A)
      (algebraMap K A).injective (by simpa using hzero)
  have hpartialSecondA : MvPolynomial.pderiv 1 fA ≠ 0 := by
    rw [MvPolynomial.pderiv_map]
    intro hzero
    apply hpartialSecond
    exact MvPolynomial.map_injective (algebraMap K A)
      (algebraMap K A).injective (by simpa using hzero)
  have hrank : PlaneCurveSupportHasRankTwo f :=
    planeCurveSupportHasRankTwo_of_absoluteIrreducible_notSubtorusTranslate
      habsolute hnot
  have hsupp : fA.support = f.support :=
    MvPolynomial.support_map_of_injective f (algebraMap K A).injective
  have hrankA : PlaneCurveSupportHasRankTwo fA := by
    obtain ⟨r, s, t, hr, hs, ht, hdet⟩ := hrank
    refine ⟨r, s, t, ?_, ?_, ?_, hdet⟩
    · rwa [hsupp]
    · rwa [hsupp]
    · rwa [hsupp]
  have hmA : (m : A) ≠ 0 := by
    rw [← map_natCast (algebraMap K A)]
    simpa using (algebraMap K A).injective.ne hmK
  have hnA : (n : A) ≠ 0 := by
    rw [← map_natCast (algebraMap K A)]
    simpa using (algebraMap K A).injective.ne hnK
  have hindexBaseChange :
      Module.finrank (PoweredCoordinateImageField f m n)
          (PlaneCurveFunctionField f) =
        Module.finrank (PoweredCoordinateImageField fA m n)
          (PlaneCurveFunctionField fA) :=
    finrank_poweredCoordinateImageField_eq_baseChange
      (E := A) habsolute hf hpartialSecond m hm n
  have hdegreeFirst : MvPolynomial.degreeOf 0 fA =
      MvPolynomial.degreeOf 0 f :=
    degreeOf_map_eq_of_injective (algebraMap K A)
      (algebraMap K A).injective 0 f
  have hdegreeSecond : MvPolynomial.degreeOf 1 fA =
      MvPolynomial.degreeOf 1 f :=
    degreeOf_map_eq_of_injective (algebraMap K A)
      (algebraMap K A).injective 1 f
  change Module.finrank (PoweredImageOverFirst f m n)
      (PlaneCurveFunctionField f) ≤
    2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f
  rw [finrank_poweredImageOverFirst_eq_imageField]
  calc
    Module.finrank (PoweredCoordinateImageField f m n)
        (PlaneCurveFunctionField f) =
      Module.finrank (PoweredCoordinateImageField fA m n)
        (PlaneCurveFunctionField fA) := hindexBaseChange
    _ ≤ 2 * MvPolynomial.degreeOf 0 fA * MvPolynomial.degreeOf 1 fA :=
      finrank_poweredCoordinateImageField_le_twice_bidegree_isAlgClosed
        hfA hpartialFirstA hpartialSecondA hrankA m n hm hn hmA hnA
    _ = 2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f := by
      rw [hdegreeFirst, hdegreeSecond]

/-- Prime-to-characteristic powers satisfy the exact Corvaja--Zannier
source-to-powered-image index bound. -/
theorem finrank_poweredImageOverFirst_le_twice_bidegree
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [CharP K p]
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hnot : BGS.External.TorusCurveNotSubtorusTranslate f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmPrime : ¬ p ∣ m) (hnPrime : ¬ p ∣ n) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (PoweredImageOverFirst f m n)
        (PlaneCurveFunctionField f) ≤
      2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f := by
  apply finrank_poweredImageOverFirst_le_twice_bidegree_of_nonzero_natCast
    habsolute hnot hpartialFirst hpartialSecond m n hm hn
  · rwa [ne_eq, CharP.cast_eq_zero_iff K p]
  · rwa [ne_eq, CharP.cast_eq_zero_iff K p]

end

end BGS.CorvajaZannier
