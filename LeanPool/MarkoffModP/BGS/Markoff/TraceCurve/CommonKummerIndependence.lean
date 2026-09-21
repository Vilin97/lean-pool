/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Kummer
import LeanPool.MarkoffModP.BGS.Markoff.Incidence.CoordinateRing

/-!
# Kummer-class independence for common cover primes

When a prime divides both cover exponents, the successive norm-degree argument used for coprime
covers loses exactly the common-prime information.  This module begins the required replacement
by treating the exceptional prime `2` directly.  In the quadratic presentation of the degree-one
trace curve, it proves that the product of the two torus coordinates remains nonsquare.

The odd common-prime classes and the roots-of-unity eigencharacter descent are deliberately not
assumed here; they remain the next noncoprime wall.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

private lemma ratFunc_sigma_ratio_not_square
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (z : RatFunc K) :
    z ^ 2 ≠
      (1 - RatFunc.C sigma * RatFunc.X) / (1 - RatFunc.X) := by
  intro hpow
  have hdenPoly : (1 - X : K[X]) ≠ 0 := by
    intro h
    have hval := congrArg (Polynomial.eval (0 : K)) h
    simp at hval
  have hdenRat : (1 - RatFunc.X : RatFunc K) ≠ 0 := by
    simpa [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C] using
      (map_ne_zero_iff (algebraMap K[X] (RatFunc K))
        (RatFunc.algebraMap_injective K)).mpr hdenPoly
  have hcrossRat :
      algebraMap K[X] (RatFunc K) (z.num ^ 2 * (1 - X)) =
        algebraMap K[X] (RatFunc K) ((1 - C sigma * X) * z.denom ^ 2) := by
    simp only [map_mul, map_pow, map_sub, map_one, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C]
    have hzden : algebraMap K[X] (RatFunc K) z.denom ≠ 0 :=
      (map_ne_zero_iff (algebraMap K[X] (RatFunc K))
        (RatFunc.algebraMap_injective K)).mpr z.denom_ne_zero
    rw [← RatFunc.num_div_denom z] at hpow
    field_simp [hzden, hdenRat] at hpow
    simpa [mul_assoc, mul_left_comm, mul_comm] using hpow
  have hcross : z.num ^ 2 * (1 - X) =
      (1 - C sigma * X) * z.denom ^ 2 :=
    (RatFunc.algebraMap_injective K) hcrossRat
  let l : K[X] := normalizedSplitTraceEisensteinPrime sigma
  have hlIrred : Irreducible l :=
    normalizedSplitTraceEisensteinPrime_irreducible sigma hsigma
  have hlPrime : Prime l := hlIrred.prime
  have hlNotDvdDenPoly : ¬ l ∣ (1 - X : K[X]) := by
    intro h
    apply normalizedSplitTraceEisensteinPrime_not_dvd_leading
      sigma hsigma hnondegenerate
    simpa [l, normalizedSplitTraceLeadingCoefficient] using
      (dvd_mul_of_dvd_right h X)
  have hlDvdNumSq : l ∣ z.num ^ 2 := by
    have hprod : l ∣ z.num ^ 2 * (1 - X) := by
      rw [hcross]
      refine ⟨-(z.denom ^ 2), ?_⟩
      simp [l, normalizedSplitTraceEisensteinPrime]
      ring
    exact (hlPrime.dvd_mul.mp hprod).resolve_right hlNotDvdDenPoly
  have hlDvdNum : l ∣ z.num := hlPrime.dvd_of_dvd_pow hlDvdNumSq
  have hlNotDvdDen : ¬ l ∣ z.denom := by
    intro hlDvdDen
    exact hlIrred.not_isUnit
      (z.isCoprime_num_denom.isUnit_of_dvd' hlDvdNum hlDvdDen)
  obtain ⟨num', hnum⟩ := hlDvdNum
  have hlNe : l ≠ 0 := hlIrred.ne_zero
  have hcancel : l * (num' ^ 2 * (1 - X)) = -(z.denom ^ 2) := by
    apply mul_left_cancel₀ hlNe
    calc
      l * (l * (num' ^ 2 * (1 - X))) =
          (l * num') ^ 2 * (1 - X) := by ring
      _ = z.num ^ 2 * (1 - X) := by rw [← hnum]
      _ = (1 - C sigma * X) * z.denom ^ 2 := hcross
      _ = l * (-(z.denom ^ 2)) := by
        simp [l, normalizedSplitTraceEisensteinPrime]
        ring
  have hlDvdDenSq : l ∣ z.denom ^ 2 := by
    refine ⟨-(num' ^ 2 * (1 - X)), ?_⟩
    calc
      z.denom ^ 2 = -(l * (num' ^ 2 * (1 - X))) := by rw [hcancel]; simp
      _ = l * (-(num' ^ 2 * (1 - X))) := by ring
  exact hlNotDvdDen (hlPrime.dvd_of_dvd_pow hlDvdDenSq)

private lemma ratFunc_X_mul_splitTraceRadicand_eq_sigma_ratio
    (sigma : K) :
    RatFunc.X * splitTraceRadicand sigma =
      (1 - RatFunc.C sigma * RatFunc.X) / (1 - RatFunc.X) := by
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hOneSubX : (1 - RatFunc.X : RatFunc K) ≠ 0 := by
    intro h
    have honeX : (1 : RatFunc K) = RatFunc.X := sub_eq_zero.mp h
    have hdegree := congrArg RatFunc.intDegree honeX
    norm_num at hdegree
  simp only [splitTraceRadicand, splitTraceRadicandNumerator,
    splitTraceRadicandDenominator, map_sub, map_one, map_mul,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  field_simp [hX, hOneSubX]

private lemma splitTraceRadicand_mul_X_mul_splitTraceRadicand_intDegree
    (sigma : K) (hsigma : sigma ≠ 0) :
    (splitTraceRadicand sigma *
      (RatFunc.X * splitTraceRadicand sigma)).intDegree = -1 := by
  have hr : splitTraceRadicand sigma ≠ 0 :=
    splitTraceRadicand_ne_zero sigma hsigma
  rw [RatFunc.intDegree_mul hr (mul_ne_zero RatFunc.X_ne_zero hr),
    RatFunc.intDegree_mul RatFunc.X_ne_zero hr,
    RatFunc.intDegree_X, splitTraceRadicand_intDegree sigma hsigma]
  norm_num

/-- The sole two-primary residue class left invisible by the four boundary
valuations is nevertheless nontrivial: on the degree-one trace curve, the
product of the two torus coordinates is not a square. -/
theorem splitTraceCoordinateProduct_quadraticPresentation_not_isSquare
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (h2 : (2 : K) ≠ 0) :
    ¬ IsSquare (algebraMap (RatFunc K)
      (AdjoinRoot (adjoinSquarePolynomial (splitTraceRadicand sigma)))
        (RatFunc.X * splitTraceRadicand sigma)) := by
  let f : RatFunc K := splitTraceRadicand sigma
  let g : RatFunc K := RatFunc.X * splitTraceRadicand sigma
  have hf0 : f ≠ 0 := splitTraceRadicand_ne_zero sigma hsigma
  have hg0 : g ≠ 0 := mul_ne_zero RatFunc.X_ne_zero hf0
  have hf : ¬ IsSquare f := by
    rintro ⟨z, hz⟩
    exact RatFunc.pow_ne_of_not_dvd_intDegree f hf0 2
      (by rw [splitTraceRadicand_intDegree sigma hsigma]; norm_num) z
      (by simpa [pow_two] using hz.symm)
  have hg : ¬ IsSquare g := by
    rintro ⟨z, hz⟩
    apply ratFunc_sigma_ratio_not_square sigma hsigma hnondegenerate z
    rw [← ratFunc_X_mul_splitTraceRadicand_eq_sigma_ratio sigma]
    simpa [g, pow_two] using hz.symm
  have hfg0 : f * g ≠ 0 := mul_ne_zero hf0 hg0
  have hfg : ¬ IsSquare (f * g) := by
    rintro ⟨z, hz⟩
    exact RatFunc.pow_ne_of_not_dvd_intDegree (f * g) hfg0 2
      (by
        change ¬ (2 : ℤ) ∣
          (splitTraceRadicand sigma *
            (RatFunc.X * splitTraceRadicand sigma)).intDegree
        rw [splitTraceRadicand_mul_X_mul_splitTraceRadicand_intDegree sigma hsigma]
        norm_num) z
      (by simpa [pow_two] using hz.symm)
  have h2Rat : (2 : RatFunc K) ≠ 0 := by
    intro hzero
    apply h2
    apply FaithfulSMul.algebraMap_injective K (RatFunc K)
    simpa only [map_ofNat, map_zero] using hzero
  have hnotMapped : ¬ IsSquare
      (algebraMap (RatFunc K) (AdjoinRoot (adjoinSquarePolynomial f)) g) :=
    not_isSquare_algebraMap_adjoinSquare_of_independent
      (F := RatFunc K) (f := f) (g := g) h2Rat hf hg hfg
  simpa only [f, g] using hnotMapped

end

end BGS.Markoff
