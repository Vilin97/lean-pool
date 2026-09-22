/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Algebra.KummerEigencharacterDescent
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.OddCommonPrimeIndependence
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.PositiveCoprimeIrreducibility

/-!
# The split trace Kummer tower for arbitrary positive exponents

This module combines cyclic eigencharacter descent with the trace curve's explicit Kummer-class
calculations.  It handles primes common to both covering exponents, proving that the second
radicand remains non-power after adjoining an arbitrary positive root of the first coordinate.
Consequently the second Kummer polynomial is irreducible without a coprimality assumption, under
the explicit roots-of-unity hypotheses used by the descent.
-/

namespace BGS.Markoff

open Polynomial AdjoinRoot

noncomputable section

variable {K : Type*} [Field K]

private lemma two_ne_zero_of_primitive_even_root
    {e : ℕ} (he : 0 < e) (h2e : 2 ∣ e) {zeta : K}
    (hzeta : IsPrimitiveRoot zeta e) : (2 : K) ≠ 0 := by
  let zetaTwo := zeta ^ (e / 2)
  have hfactor : e = (e / 2) * 2 := (Nat.div_mul_cancel h2e).symm
  have hzetaTwo : IsPrimitiveRoot zetaTwo 2 := hzeta.pow he hfactor
  intro htwo
  have hnegOne : (-1 : K) = 1 := by
    rw [neg_eq_iff_add_eq_zero]
    simpa [one_add_one_eq_two] using htwo
  apply hzetaTwo.ne_one (by norm_num)
  rw [hzetaTwo.eq_neg_one_of_two_right, hnegOne]

private lemma splitTraceBaseUV_not_square
    (sigma : K) (hsigma : sigma ≠ 0)
    (c : SplitTraceBaseFunctionField K sigma) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    c ^ 2 ≠ splitTraceBaseU sigma * splitTraceBaseV sigma := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let baseField := SplitTraceBaseFunctionField K sigma
  let U : baseField := splitTraceBaseU sigma
  let V : baseField := splitTraceBaseV sigma
  have hV : V ≠ 0 := by
    change AdjoinRoot.root (splitTraceBaseKummerPolynomial sigma) ≠ 0
    exact (root_X_pow_sub_C_ne_zero_iff hBaseIrred).mpr
      (splitTraceRadicand_ne_zero sigma hsigma)
  have hU : U ≠ 0 := by
    exact (map_ne_zero_iff _ (algebraMap (RatFunc K) baseField).injective).mpr
      RatFunc.X_ne_zero
  have hUV : U * V ≠ 0 := mul_ne_zero hU hV
  intro hpow
  have hc : c ≠ 0 := by
    intro hc
    apply hUV
    simpa [hc] using hpow.symm
  let : Module.Finite (RatFunc K) baseField :=
    (monic_X_pow_sub_C _ (by norm_num : (2 : ℕ) ≠ 0)).finite_adjoinRoot
  have hnorm := congrArg (Algebra.norm (RatFunc K)) hpow
  rw [map_pow] at hnorm
  have hnormC : Algebra.norm (RatFunc K) c ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hc
  have hdegree := congrArg RatFunc.intDegree hnorm
  rw [RatFunc.intDegree_pow _ hnormC,
    norm_splitTraceBaseU_mul_V_intDegree sigma hsigma] at hdegree
  omega

/-- The second trace radicand is not a common-prime power after adjoining an arbitrary
positive `e`-th root of the first coordinate. -/
theorem splitTraceXiRadicand_not_primePower_of_commonPrime
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (i : K) (hi : i ^ 2 = -1)
    (e : ℕ) (he : 0 < e) (zeta : K) (hzeta : IsPrimitiveRoot zeta e)
    (q : ℕ) (hq : q.Prime) (hqe : q ∣ e)
    (z : letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
          ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
        letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
          ⟨splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
            sigma hsigma i hi e he⟩
        SplitTraceEtaFunctionField K sigma e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
        sigma hsigma i hi e he⟩
    z ^ q ≠ splitTraceXiRadicand sigma e := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma hsigma i hi e he
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let baseField := SplitTraceBaseFunctionField K sigma
  let etaField := SplitTraceEtaFunctionField K sigma e
  let U : baseField := splitTraceBaseU sigma
  let V : baseField := splitTraceBaseV sigma
  have hV : V ≠ 0 := by
    change AdjoinRoot.root (splitTraceBaseKummerPolynomial sigma) ≠ 0
    exact (root_X_pow_sub_C_ne_zero_iff hBaseIrred).mpr
      (splitTraceRadicand_ne_zero sigma hsigma)
  have hU : U ≠ 0 := by
    exact (map_ne_zero_iff _ (algebraMap (RatFunc K) baseField).injective).mpr
      RatFunc.X_ne_zero
  have hUV : U * V ≠ 0 := mul_ne_zero hU hV
  intro hpow
  have hzetaBase : IsPrimitiveRoot (algebraMap K baseField zeta) e :=
    hzeta.map_of_injective (algebraMap K baseField).injective
  have hpowBase : z ^ q = algebraMap baseField etaField (U * V) := by
    change z ^ q = algebraMap (SplitTraceBaseFunctionField K sigma)
      (SplitTraceEtaFunctionField K sigma e)
        (splitTraceBaseU sigma * splitTraceBaseV sigma)
    exact hpow
  obtain ⟨k, hklt, hdiv, c, hc⟩ :=
    BGS.Algebra.exists_rootMonomial_of_primePower_mem_base
      (v := splitTraceBaseV sigma)
      (ζ := algebraMap K (SplitTraceBaseFunctionField K sigma) zeta)
      (a := splitTraceBaseU sigma * splitTraceBaseV sigma)
      he hzetaBase (by simpa [splitTraceEtaKummerPolynomial] using hEtaIrred)
        hq hqe z hpowBase
  have hc' : z = algebraMap baseField etaField c *
      AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e) ^ k := by
    change z = algebraMap baseField etaField c *
      AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e) ^ k at hc
    exact hc
  let r := q * k / e
  have hrlt : r < q := by
    apply (Nat.div_lt_iff_lt_mul he).2
    simpa [Nat.mul_comm] using (Nat.mul_lt_mul_left hq.pos).2 hklt
  have hqk : e * r = q * k := by
    exact Nat.mul_div_cancel' hdiv
  have hetaRoot :
      (AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e)) ^ e =
        algebraMap baseField etaField V := by
    apply sub_eq_zero.mp
    have h := AdjoinRoot.eval₂_root (splitTraceEtaKummerPolynomial sigma e)
    rw [splitTraceEtaKummerPolynomial] at h
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [← AdjoinRoot.algebraMap_eq] at h
    exact h
  have hetaPow : (AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e)) ^ (q * k) =
      algebraMap baseField etaField (V ^ r) := by
    calc
      (AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e)) ^ (q * k) =
          (AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e)) ^ (e * r) := by
            rw [hqk]
      _ = ((AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e)) ^ e) ^ r := by
            rw [pow_mul]
      _ = (algebraMap baseField etaField V) ^ r := by
            rw [hetaRoot]
      _ = algebraMap baseField etaField (V ^ r) := by rw [map_pow]
  have hbaseEq : c ^ q * V ^ r = U * V := by
    apply (algebraMap baseField etaField).injective
    calc
      algebraMap baseField etaField (c ^ q * V ^ r) =
          (algebraMap baseField etaField c) ^ q *
            (AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e)) ^ (q * k) := by
              rw [map_mul, map_pow, hetaPow]
      _ = (algebraMap baseField etaField c *
            AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e) ^ k) ^ q := by
              rw [mul_pow, ← pow_mul, Nat.mul_comm q k]
      _ = z ^ q := by rw [← hc']
      _ = algebraMap baseField etaField (U * V) := by
        simpa [splitTraceXiRadicand, U, V, baseField, etaField] using hpow
  by_cases hqTwo : q = 2
  · subst q
    have h2 : (2 : K) ≠ 0 :=
      two_ne_zero_of_primitive_even_root he hqe hzeta
    have hrCases : r = 0 ∨ r = 1 := by
      generalize hrr : r = rr at hrlt ⊢
      omega
    rcases hrCases with hrZero | hrOne
    · apply splitTraceBaseUV_not_square sigma hsigma c
      simpa [hrZero, U, V, baseField] using hbaseEq
    · have hcSquareU : c ^ 2 = U := by
        apply mul_right_cancel₀ hV
        simpa [hrOne, pow_one, mul_assoc] using hbaseEq
      have hnot := splitTraceCoordinateProduct_quadraticPresentation_not_isSquare
        sigma hsigma hnondegenerate h2
      apply hnot
      change IsSquare (algebraMap (RatFunc K) baseField
        (RatFunc.X * splitTraceRadicand sigma))
      refine ⟨c * V, ?_⟩
      have hrootSquare : V ^ 2 =
          algebraMap (RatFunc K) baseField (splitTraceRadicand sigma) := by
        change AdjoinRoot.root (X ^ 2 - C (splitTraceRadicand sigma)) ^ 2 = _
        exact root_X_pow_sub_C_pow 2 (splitTraceRadicand sigma)
      calc
        algebraMap (RatFunc K) baseField
            (RatFunc.X * splitTraceRadicand sigma) =
            U * algebraMap (RatFunc K) baseField (splitTraceRadicand sigma) := by
              simp [U, baseField, splitTraceBaseU]
        _ = U * V ^ 2 := by rw [hrootSquare]
        _ = c ^ 2 * V ^ 2 := by rw [hcSquareU]
        _ = (c * V) * (c * V) := by ring
  · by_cases hrZero : r = 0
    · apply splitTraceBaseCoordinates_mixedPower_ne_oddPrimePower
        sigma hsigma hnondegenerate q 1 0 hq hqTwo hq.one_lt hq.pos (by simp) c
      simpa [hrZero, U, V, baseField] using hbaseEq
    · have hrPositive : 0 < r := Nat.pos_of_ne_zero hrZero
      have hrLe : r ≤ q := Nat.le_of_lt hrlt
      have hEq : (c * V) ^ q = (U * V) ^ 1 * V ^ (q - r) := by
        rw [mul_pow, pow_one]
        have hv : V ^ q = V ^ r * V ^ (q - r) := by
          rw [← pow_add, Nat.add_sub_of_le hrLe]
        calc
          c ^ q * V ^ q = c ^ q * (V ^ r * V ^ (q - r)) := by rw [hv]
          _ = (c ^ q * V ^ r) * V ^ (q - r) := by rw [mul_assoc]
          _ = (U * V) * V ^ (q - r) := by rw [hbaseEq]
      apply splitTraceBaseCoordinates_mixedPower_ne_oddPrimePower
        sigma hsigma hnondegenerate q 1 (q - r) hq hqTwo hq.one_lt
          (Nat.sub_lt (Nat.pos_of_ne_zero hq.ne_zero) hrPositive) (by simp) (c * V)
      simpa [U, V, baseField] using hEq

/-- With a primitive `e`-th root in the constant field, the xi Kummer polynomial is
irreducible for arbitrary positive exponents; coprimality is no longer required. -/
theorem splitTraceXiKummerPolynomial_irreducible_of_primitiveRoot
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (i : K) (hi : i ^ 2 = -1)
    (e d : ℕ) (he : 0 < e) (hd : 0 < d)
    (zeta : K) (hzeta : IsPrimitiveRoot zeta e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
        sigma hsigma i hi e he⟩
    Irreducible (splitTraceXiKummerPolynomial sigma e d) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma hsigma i hi e he
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  rw [splitTraceXiKummerPolynomial]
  apply X_pow_sub_C_irreducible_of_sqrt_neg_one
    (algebraMap K (SplitTraceEtaFunctionField K sigma e) i)
  · rw [← map_pow, hi, map_neg, map_one]
  · exact hd.ne'
  · intro q hq hqd z
    by_cases hqe : q ∣ e
    · exact splitTraceXiRadicand_not_primePower_of_commonPrime
        sigma hsigma hnondegenerate i hi e he zeta hzeta q hq hqe z
    · exact splitTraceXiRadicand_not_primePower_of_sqrt_neg_one
        sigma hsigma i hi e he q hq hqe z

/-- The roots of the arbitrary positive-exponent Kummer tower satisfy the cleared affine cover
equation. -/
theorem generalSplitTraceKummerTower_cover_maps_to_zero_of_primitiveRoot
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (i : K) (hi : i ^ 2 = -1)
    (e d : ℕ) (he : 0 < e) (hd : 0 < d)
    (zeta : K) (hzeta : IsPrimitiveRoot zeta e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
        sigma hsigma i hi e he⟩
    letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) :=
      ⟨splitTraceXiKummerPolynomial_irreducible_of_primitiveRoot
        sigma hsigma hnondegenerate i hi e d he hd zeta hzeta⟩
    generalSplitTracePolynomialToKummerTop sigma e d
      (splitTraceCoverPolynomial (1 : K) sigma d e) = 0 := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma hsigma i hi e he
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred := splitTraceXiKummerPolynomial_irreducible_of_primitiveRoot
    sigma hsigma hnondegenerate i hi e d he hd zeta hzeta
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  let baseToXi : SplitTraceBaseFunctionField K sigma →+*
      SplitTraceXiFunctionField K sigma e d :=
    (algebraMap (SplitTraceEtaFunctionField K sigma e)
      (SplitTraceXiFunctionField K sigma e d)).comp
      (algebraMap (SplitTraceBaseFunctionField K sigma)
        (SplitTraceEtaFunctionField K sigma e))
  have hBase := splitTraceBaseU_V_equation sigma hsigma
  have hBaseTop := congrArg baseToXi hBase
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero] at hBaseTop
  have hEtaRoot :
      (AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e)) ^ e =
        algebraMap (SplitTraceBaseFunctionField K sigma)
          (SplitTraceEtaFunctionField K sigma e) (splitTraceBaseV sigma) := by
    apply sub_eq_zero.mp
    have h := AdjoinRoot.eval₂_root (splitTraceEtaKummerPolynomial sigma e)
    rw [splitTraceEtaKummerPolynomial] at h
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [← AdjoinRoot.algebraMap_eq] at h
    exact h
  have hEtaTop := congrArg
    (algebraMap (SplitTraceEtaFunctionField K sigma e)
      (SplitTraceXiFunctionField K sigma e d)) hEtaRoot
  simp only [map_pow] at hEtaTop
  have hXiRoot :
      splitTraceXiRoot sigma e d ^ d =
        algebraMap (SplitTraceEtaFunctionField K sigma e)
          (SplitTraceXiFunctionField K sigma e d) (splitTraceXiRadicand sigma e) := by
    apply sub_eq_zero.mp
    have h := AdjoinRoot.eval₂_root (splitTraceXiKummerPolynomial sigma e d)
    rw [splitTraceXiKummerPolynomial] at h
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [← AdjoinRoot.algebraMap_eq] at h
    exact h
  have hCover := eval_splitTraceCoverPolynomial_of_powerRootRelations
    (splitTraceBaseElementInXiField sigma e d
      (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma) (RatFunc.C sigma)))
    (splitTraceBaseElementInXiField sigma e d (splitTraceBaseU sigma))
    (splitTraceBaseElementInXiField sigma e d (splitTraceBaseV sigma))
    (splitTraceXiRoot sigma e d) (splitTraceEtaRootInXiField sigma e d) d e
    (by simpa [baseToXi, splitTraceBaseElementInXiField] using hBaseTop)
    (by simpa [splitTraceEtaRootInXiField, splitTraceBaseElementInXiField, baseToXi]
      using hEtaTop)
    (by simpa [splitTraceXiRadicand, splitTraceBaseElementInXiField, baseToXi,
      splitTraceXiRoot] using hXiRoot)
  have hsigmaTop :
      splitTraceBaseElementInXiField sigma e d
          (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma) (RatFunc.C sigma)) =
        algebraMap K (SplitTraceXiFunctionField K sigma e d) sigma := by
    change algebraMap (SplitTraceEtaFunctionField K sigma e)
        (SplitTraceXiFunctionField K sigma e d)
          (algebraMap (SplitTraceBaseFunctionField K sigma)
            (SplitTraceEtaFunctionField K sigma e)
              (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma)
                (algebraMap K (RatFunc K) sigma))) = _
    rw [← IsScalarTower.algebraMap_apply K (RatFunc K)
      (SplitTraceBaseFunctionField K sigma)]
    rw [← IsScalarTower.algebraMap_apply K
      (SplitTraceBaseFunctionField K sigma) (SplitTraceEtaFunctionField K sigma e)]
    rw [← IsScalarTower.algebraMap_apply K
      (SplitTraceEtaFunctionField K sigma e) (SplitTraceXiFunctionField K sigma e d)]
  rw [hsigmaTop] at hCover
  simpa [generalSplitTracePolynomialToKummerTop, MvPolynomial.aeval_def,
    splitTraceCoverPolynomial] using hCover

private lemma arbitrarySplitTraceCoverPolynomial_ne_zero
    (sigma : K) (d e : ℕ) (hd : 0 < d) :
    splitTraceCoverPolynomial (1 : K) sigma d e ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(0 : K), (1 : K)]) hzero
  rw [eval_splitTraceCoverPolynomial] at heval
  norm_num [hd.ne'] at heval

/-- The normalized split trace-cover polynomial is irreducible for arbitrary positive exponents
over a field containing a square root of `-1` and a primitive `e`-th root of unity. -/
theorem splitTraceCoverPolynomial_irreducible_of_primitiveRoot
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (i : K) (hi : i ^ 2 = -1)
    (e d : ℕ) (he : 0 < e) (hd : 0 < d)
    (zeta : K) (hzeta : IsPrimitiveRoot zeta e) :
    Irreducible (splitTraceCoverPolynomial (1 : K) sigma d e) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma hsigma i hi e he
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred := splitTraceXiKummerPolynomial_irreducible_of_primitiveRoot
    sigma hsigma hnondegenerate i hi e d he hd zeta hzeta
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  let : IsDomain (SplitTraceXiFunctionField K sigma e d) :=
    AdjoinRoot.isDomain_of_prime hXiIrred.prime
  let f : MvPolynomial (Fin 2) K →+* SplitTraceXiFunctionField K sigma e d :=
    (generalSplitTracePolynomialToKummerTop sigma e d).toRingHom
  let I : Ideal (MvPolynomial (Fin 2) K) :=
    Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e}
  have hCoverZero :
      generalSplitTracePolynomialToKummerTop sigma e d
        (splitTraceCoverPolynomial (1 : K) sigma d e) = 0 :=
    generalSplitTraceKummerTower_cover_maps_to_zero_of_primitiveRoot
      sigma hsigma hnondegenerate i hi e d he hd zeta hzeta
  have hI_le : I ≤ RingHom.ker f := by
    change Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e} ≤ RingHom.ker f
    rw [Ideal.span_le]
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst p
    exact hCoverZero
  have hker_le : RingHom.ker f ≤ I := by
    intro p hp
    apply generalSplitTracePolynomialSyntacticNormalForm_division
      sigma hsigma i hi e d he hd hnondegenerate p
    apply (generalSplitTracePolynomialSyntacticNormalForm_eq_zero_iff
      sigma hsigma i hi e d he hd p).2
    exact hp
  let quotientToTop : MvPolynomial (Fin 2) K ⧸ I →+*
      SplitTraceXiFunctionField K sigma e d :=
    Ideal.Quotient.lift I f hI_le
  have hInjective : Function.Injective quotientToTop :=
    RingHom.lift_injective_of_ker_le_ideal I hI_le hker_le
  let : IsDomain (MvPolynomial (Fin 2) K ⧸ I) :=
    hInjective.isDomain quotientToTop
  have hprimeIdeal : I.IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  have hprimeElement : Prime (splitTraceCoverPolynomial (1 : K) sigma d e) :=
    (Ideal.span_singleton_prime
      (arbitrarySplitTraceCoverPolynomial_ne_zero sigma d e hd)).1 (by
        simpa [I] using hprimeIdeal)
  exact irreducible_iff_prime.mpr hprimeElement

end

end BGS.Markoff
