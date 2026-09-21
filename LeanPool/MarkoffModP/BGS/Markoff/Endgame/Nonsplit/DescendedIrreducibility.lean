/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Endgame.Nonsplit.DescendedTraceCurve
import LeanPool.MarkoffModP.BGS.Algebra.ClearedLinearFractionalSubstitution

/-!
# Absolute irreducibility of the descended nonsplit trace curve

The descended coordinates are `(z, u)`, whereas the split cover uses `(u, w)`.  We therefore
keep `u` as the outer polynomial variable and treat the Cayley change `w = (z-δ^p)/(z-δ)` as
an automorphism of the rational function coefficient field.
-/

namespace BGS.Markoff

noncomputable section

open Polynomial

/-- View a bivariate polynomial as a polynomial in coordinate `1`, with coefficients in
coordinate `0`.  This is the coordinate order needed after the descended curve's `(z,u)`
coordinates are compared with the split cover's `(u,w)` coordinates. -/
def finTwoSecondToIteratedPolynomial {K : Type*} [Field K] :
    MvPolynomial (Fin 2) K ≃+* Polynomial K[X] :=
  (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.trans
    (finTwoToIteratedPolynomial (K := K))

@[simp]
theorem finTwoSecondToIteratedPolynomial_X_zero
    {K : Type*} [Field K] :
    finTwoSecondToIteratedPolynomial (K := K) (MvPolynomial.X 0) = C X := by
  simp [finTwoSecondToIteratedPolynomial, MvPolynomial.renameEquiv_apply]

@[simp]
theorem finTwoSecondToIteratedPolynomial_X_one
    {K : Type*} [Field K] :
    finTwoSecondToIteratedPolynomial (K := K) (MvPolynomial.X 1) = X := by
  simp [finTwoSecondToIteratedPolynomial, MvPolynomial.renameEquiv_apply]

@[simp]
theorem finTwoSecondToIteratedPolynomial_C
    {K : Type*} [Field K] (r : K) :
    finTwoSecondToIteratedPolynomial (K := K) (MvPolynomial.C r) = C (C r) := by
  simp [finTwoSecondToIteratedPolynomial, MvPolynomial.renameEquiv_apply]

/-- The descended coordinate-order equivalence commutes with scalar extension. -/
theorem finTwoSecondToIteratedPolynomial_map
    {K L : Type*} [Field K] [Field L] (phi : K →+* L)
    (P : MvPolynomial (Fin 2) K) :
    finTwoSecondToIteratedPolynomial (K := L) (MvPolynomial.map phi P) =
      (finTwoSecondToIteratedPolynomial (K := K) P).map
        (Polynomial.mapRingHom phi) := by
  let lhs : MvPolynomial (Fin 2) K →+* L[X][X] :=
    (finTwoSecondToIteratedPolynomial (K := L)).toRingHom.comp
      (MvPolynomial.map phi)
  let rhs : MvPolynomial (Fin 2) K →+* L[X][X] :=
    (Polynomial.mapRingHom (Polynomial.mapRingHom phi)).comp
      (finTwoSecondToIteratedPolynomial (K := K)).toRingHom
  have heq : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs, RingHom.comp_apply]
    · intro i
      fin_cases i <;> simp [lhs, rhs, RingHom.comp_apply]
  exact DFunLike.congr_fun heq P

theorem finTwoSecondToIteratedPolynomial_splitTraceCoverPolynomial
    {K : Type*} [Field K] (alpha beta : K) (e d : ℕ) :
    finTwoSecondToIteratedPolynomial
        (splitTraceCoverPolynomial alpha beta e d) =
      C (C alpha * X ^ e) * X ^ (2 * d) + C (C beta * X ^ e) -
        C (X ^ (2 * e) + 1) * X ^ d := by
  simp [splitTraceCoverPolynomial]
  ring

theorem finTwoToIteratedPolynomial_splitTraceCoverPolynomial_general
    {K : Type*} [Field K] (alpha beta : K) (e d : ℕ) :
    finTwoToIteratedPolynomial
        (splitTraceCoverPolynomial alpha beta e d) =
      monomial (2 * e) (-(X ^ d)) +
        monomial e (C alpha * X ^ (2 * d) + C beta) + C (-(X ^ d)) := by
  simp [splitTraceCoverPolynomial, ← C_mul_X_pow_eq_monomial]
  ring

theorem finTwoToIteratedPolynomial_splitTraceCoverPolynomial_general_natDegree
    {K : Type*} [Field K] (alpha beta : K) (e d : ℕ) (he : 0 < e) :
    (finTwoToIteratedPolynomial
      (splitTraceCoverPolynomial alpha beta e d)).natDegree = 2 * e := by
  rw [finTwoToIteratedPolynomial_splitTraceCoverPolynomial_general]
  have htwoNe : 2 * e ≠ e := by omega
  have heTwoNe : e ≠ 2 * e := by omega
  have heNe : e ≠ 0 := by omega
  have htwoZero : 2 * e ≠ 0 := by omega
  have hcoeff :
      (monomial (2 * e) (-(X ^ d)) +
          monomial e (C alpha * X ^ (2 * d) + C beta) + C (-(X ^ d))).coeff
          (2 * e) = -(X ^ d) := by
    rw [coeff_add, coeff_add, coeff_monomial, if_pos rfl,
      coeff_monomial, if_neg heTwoNe, coeff_C_ne_zero htwoZero]
    simp
  have hnonzero : -(X ^ d : Polynomial K) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero d X_ne_zero)
  apply le_antisymm
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_monomial_le _
      · exact (natDegree_monomial_le _).trans (by omega)
    · simp
  · exact le_natDegree_of_ne_zero (by rwa [hcoeff])

theorem descendedIteratedPolynomial_isPrimitive_of_isCoprime
    {K : Type*} [Field K] (Q N : Polynomial K) (e : ℕ) (he : 0 < e)
    (hcoprime : IsCoprime Q N) :
    (monomial (2 * e) (-Q) + monomial e N + C (-Q)).IsPrimitive := by
  rw [isPrimitive_iff_isUnit_of_C_dvd]
  intro g hg
  have hall := (C_dvd_iff_dvd_coeff g _).mp hg
  have heNe : e ≠ 0 := he.ne'
  have htwoNe : 2 * e ≠ e := by omega
  have hcoeffZero :
      (monomial (2 * e) (-Q) + monomial e N + C (-Q)).coeff 0 = -Q := by
    simp [coeff_add, coeff_monomial, heNe]
  have hcoeffE :
      (monomial (2 * e) (-Q) + monomial e N + C (-Q)).coeff e = N := by
    rw [coeff_add, coeff_add, coeff_monomial, if_neg htwoNe,
      coeff_monomial, if_pos rfl, coeff_C_ne_zero heNe]
    simp
  have hgQ : g ∣ Q := by
    have : g ∣ -Q := hcoeffZero ▸ hall 0
    simpa using this.neg_right
  have hgN : g ∣ N := hcoeffE ▸ hall e
  exact hcoprime.isUnit_of_dvd' hgQ hgN

section DescendedFormula

variable (p : ℕ) [Fact p.Prime]

private abbrev F := ZMod p
private abbrev E := quadraticFiniteField p

def extendedCayleyNumeratorFactor : Polynomial (E p) :=
  X - C (quadraticNonbaseElement p ^ p)

def extendedCayleyDenominatorFactor : Polynomial (E p) :=
  X - C (quadraticNonbaseElement p)

def extendedSeededCayleyNumerator (s : (E p)ˣ) (d : ℕ) : Polynomial (E p) :=
  C (s : E p) * extendedCayleyNumeratorFactor p ^ (2 * d) +
    C ((s : E p) ^ p) * extendedCayleyDenominatorFactor p ^ (2 * d)

def extendedCayleyNormFactor : Polynomial (E p) :=
  extendedCayleyNumeratorFactor p * extendedCayleyDenominatorFactor p

theorem extendedCayleyNormFactor_isCoprime_extendedSeededCayleyNumerator
    (s : (E p)ˣ) (d : ℕ) (hd : 0 < d) :
    IsCoprime (extendedCayleyNormFactor p)
      (extendedSeededCayleyNumerator p s d) := by
  have hnonbase : quadraticNonbaseElement p ^ p ≠ quadraticNonbaseElement p :=
    quadraticNonbaseElement_frobenius_ne_self p
  have hleftDifference :
      quadraticNonbaseElement p ^ p - quadraticNonbaseElement p ≠ 0 :=
    sub_ne_zero.mpr hnonbase
  have hrightDifference :
      quadraticNonbaseElement p - quadraticNonbaseElement p ^ p ≠ 0 :=
    sub_ne_zero.mpr hnonbase.symm
  have hleftEval :
      (extendedSeededCayleyNumerator p s d).eval
          (quadraticNonbaseElement p ^ p) ≠ 0 := by
    simp [extendedSeededCayleyNumerator, extendedCayleyNumeratorFactor,
      extendedCayleyDenominatorFactor, hleftDifference,
      show 2 * d ≠ 0 by omega]
  have hrightEval :
      (extendedSeededCayleyNumerator p s d).eval
          (quadraticNonbaseElement p) ≠ 0 := by
    simp [extendedSeededCayleyNumerator, extendedCayleyNumeratorFactor,
      extendedCayleyDenominatorFactor, hrightDifference,
      show 2 * d ≠ 0 by omega]
  have hleft : IsCoprime (extendedCayleyNumeratorFactor p)
      (extendedSeededCayleyNumerator p s d) := by
    apply (irreducible_X_sub_C (quadraticNonbaseElement p ^ p)).coprime_iff_not_dvd.mpr
    rw [dvd_iff_isRoot, IsRoot]
    exact hleftEval
  have hright : IsCoprime (extendedCayleyDenominatorFactor p)
      (extendedSeededCayleyNumerator p s d) := by
    apply (irreducible_X_sub_C (quadraticNonbaseElement p)).coprime_iff_not_dvd.mpr
    rw [dvd_iff_isRoot, IsRoot]
    exact hrightEval
  exact IsCoprime.mul_left hleft hright

theorem finTwoSecondToIteratedPolynomial_map_univariateInFirstCoordinate
    {K L : Type*} [Field K] [Field L] (phi : K →+* L) (P : Polynomial K) :
    finTwoSecondToIteratedPolynomial
        (MvPolynomial.map phi (univariateInFirstCoordinate P)) = C (P.map phi) := by
  classical
  have hmap : P.map phi =
      P.support.sum fun n ↦ C (phi (P.coeff n)) * X ^ n := by
    ext n
    simp [coeff_map]
  simp [finTwoSecondToIteratedPolynomial, univariateInFirstCoordinate,
    Polynomial.sum_def, MvPolynomial.renameEquiv_apply, hmap]

theorem finTwoSecondToIteratedPolynomial_map_seededNonsplitDescendedPolynomial
    (s : (E p)ˣ) (d e : ℕ) :
    finTwoSecondToIteratedPolynomial
        (MvPolynomial.map (algebraMap (F p) (E p))
          (seededNonsplitDescendedPolynomial p s d e)) =
      monomial (2 * e) (-(extendedCayleyNormFactor p ^ d)) +
        monomial e (extendedSeededCayleyNumerator p s d) +
          C (-(extendedCayleyNormFactor p ^ d)) := by
  rw [seededNonsplitDescendedPolynomial]
  simp only [map_sub, map_mul, map_pow, map_add, map_one,
    finTwoSecondToIteratedPolynomial_map_univariateInFirstCoordinate,
    map_X, finTwoSecondToIteratedPolynomial_X_one]
  rw [seededCayleyTraceNumeratorPolynomial_map, quadraticCayleyNormPolynomial_map]
  simp [← C_mul_X_pow_eq_monomial, extendedSeededCayleyNumerator, extendedCayleyNormFactor,
    extendedCayleyNumeratorFactor, extendedCayleyDenominatorFactor,
    Nat.mul_comm]
  ring

theorem cayleyTransport_splitIteratedPolynomial
    {K : Type*} [Field K] (alpha beta r t : K) (e d : ℕ) (hrt : r ≠ t)
    (hdet : (1 : K) * (-t) - (-r) * 1 ≠ 0) :
    let phi := BGS.Algebra.ratFuncLinearFractionalEquiv
      (1 : K) (-r) 1 (-t) hdet
    let A : RatFunc K := RatFunc.X - RatFunc.C r
    let B : RatFunc K := RatFunc.X - RatFunc.C t
    let Q : Polynomial K := (X - C r) * (X - C t)
    let N : Polynomial K := C alpha * (X - C r) ^ (2 * d) +
      C beta * (X - C t) ^ (2 * d)
    C (B ^ (2 * d)) *
        ((finTwoToIteratedPolynomial
          (splitTraceCoverPolynomial alpha beta e d)).map
            (algebraMap K[X] (RatFunc K))).map phi.toRingHom =
      (monomial (2 * e) (-(Q ^ d)) + monomial e N + C (-(Q ^ d))).map
        (algebraMap K[X] (RatFunc K)) := by
  have hphi (f : K[X]) :
      (BGS.Algebra.ratFuncLinearFractionalEquiv
          (1 : K) (-r) 1 (-t) hdet).toRingEquiv.toRingHom
          (algebraMap K[X] (RatFunc K) f) =
        aeval (BGS.Algebra.ratFuncLinearFractionalValue
          (1 : K) (-r) 1 (-t)) f := by
    change BGS.Algebra.ratFuncLinearFractionalEquiv
        (1 : K) (-r) 1 (-t) hdet (algebraMap K[X] (RatFunc K) f) = _
    exact BGS.Algebra.ratFuncLinearFractionalEquiv_apply_algebraMap
      (1 : K) (-r) 1 (-t) hdet f
  have hconst (x : K) :
      BGS.Algebra.ratFuncLinearFractionalEquiv
          (1 : K) (-r) 1 (-t) hdet (RatFunc.C x) = RatFunc.C x := by
    change BGS.Algebra.ratFuncLinearFractionalEquiv
        (1 : K) (-r) 1 (-t) hdet (algebraMap K (RatFunc K) x) =
      algebraMap K (RatFunc K) x
    exact (BGS.Algebra.ratFuncLinearFractionalEquiv
      (1 : K) (-r) 1 (-t) hdet).commutes x
  dsimp only
  rw [finTwoToIteratedPolynomial_splitTraceCoverPolynomial_general]
  simp only [← C_mul_X_pow_eq_monomial, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_neg, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
  rw [hphi]
  simp [BGS.Algebra.ratFuncLinearFractionalValue, aeval_def,
    eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    ← C_mul_X_pow_eq_monomial]
  rw [hconst, hconst]
  let A : RatFunc K := RatFunc.X - RatFunc.C r
  let B : RatFunc K := RatFunc.X - RatFunc.C t
  let q : RatFunc K := A / B
  have hqExpanded :
      (RatFunc.X + -RatFunc.C r) / (RatFunc.X + -RatFunc.C t) = q := by
    simp [q, A, B, sub_eq_add_neg]
  have hB : RatFunc.X - RatFunc.C t ≠ (0 : RatFunc K) := by
    simpa only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using
      RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero t)
  rw [hqExpanded]
  have hqD : B ^ (2 * d) * q ^ d = (A * B) ^ d := by
    have hB' : B ≠ 0 := by simpa [B] using hB
    dsimp only [q]
    rw [pow_mul, ← mul_pow]
    congr 1
    field_simp [hB']
  have hqTwoD : B ^ (2 * d) * q ^ (2 * d) = A ^ (2 * d) := by
    have hB' : B ≠ 0 := by simpa [B] using hB
    dsimp only [q]
    rw [← mul_pow]
    congr 1
    field_simp [hB']
  have hmiddle :
      B ^ (2 * d) * (RatFunc.C alpha * q ^ (2 * d) + RatFunc.C beta) =
        RatFunc.C alpha * A ^ (2 * d) + RatFunc.C beta * B ^ (2 * d) := by
    calc
      _ = RatFunc.C alpha * (B ^ (2 * d) * q ^ (2 * d)) +
          RatFunc.C beta * B ^ (2 * d) := by ring
      _ = _ := by rw [hqTwoD]
  have hnegative : B ^ (2 * d) * (-q ^ d) = -(A * B) ^ d := by
    rw [mul_neg, hqD]
  calc
    _ = C (B ^ (2 * d) * (-q ^ d)) * X ^ (2 * e) +
          C (B ^ (2 * d) *
            (RatFunc.C alpha * q ^ (2 * d) + RatFunc.C beta)) * X ^ e +
          C (B ^ (2 * d) * (-q ^ d)) := by
      dsimp [B]
      simp only [map_add, map_sub, map_mul, map_pow, map_neg]
      ring
    _ = _ := by
      rw [hnegative, hmiddle]
      dsimp [A, B]
      simp only [map_add, map_mul, map_pow, map_sub, map_neg]
      ring

/-- Irreducibility descends through the nonsplit Cayley model after any field extension of
the quadratic splitting field.  This is the algebraic core used below with an algebraic
closure as the target field. -/
theorem map_seededNonsplitDescendedPolynomial_irreducible_of_map_splitCover
    {L : Type*} [Field L] (ι : E p →+* L) (s : (E p)ˣ) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e)
    (hcover : Irreducible
      (MvPolynomial.map ι
        (splitTraceCoverPolynomial (s : E p) ((s : E p) ^ p) e d))) :
    Irreducible
      (MvPolynomial.map (ι.comp (algebraMap (F p) (E p)))
        (seededNonsplitDescendedPolynomial p s d e)) := by
  let alpha : L := ι (s : E p)
  let beta : L := ι ((s : E p) ^ p)
  let r : L := ι (quadraticNonbaseElement p ^ p)
  let t : L := ι (quadraticNonbaseElement p)
  have hsplit :
      MvPolynomial.map ι
          (splitTraceCoverPolynomial (s : E p) ((s : E p) ^ p) e d) =
        splitTraceCoverPolynomial alpha beta e d := by
    simp [splitTraceCoverPolynomial, alpha, beta]
  have hq : Irreducible
      (finTwoToIteratedPolynomial
        (splitTraceCoverPolynomial alpha beta e d)) := by
    have := hcover.map (finTwoToIteratedPolynomial (K := L))
    rwa [hsplit] at this
  have hqPrimitive :
      (finTwoToIteratedPolynomial
        (splitTraceCoverPolynomial alpha beta e d)).IsPrimitive := by
    apply hq.isPrimitive
    rw [finTwoToIteratedPolynomial_splitTraceCoverPolynomial_general_natDegree
      alpha beta e d he]
    omega
  have hqFraction : Irreducible
      ((finTwoToIteratedPolynomial
          (splitTraceCoverPolynomial alpha beta e d)).map
        (algebraMap L[X] (RatFunc L))) :=
    hqPrimitive.irreducible_iff_irreducible_map_fraction_map.mp hq
  have hrt : r ≠ t := by
    exact ι.injective.ne (quadraticNonbaseElement_frobenius_ne_self p)
  have hdet : (1 : L) * (-t) - (-r) * 1 ≠ 0 := by
    rw [show (1 : L) * (-t) - (-r) * 1 = r - t by ring]
    exact sub_ne_zero.mpr hrt
  let phi := BGS.Algebra.ratFuncLinearFractionalEquiv
    (1 : L) (-r) 1 (-t) hdet
  have hqTransported : Irreducible
      (((finTwoToIteratedPolynomial
          (splitTraceCoverPolynomial alpha beta e d)).map
        (algebraMap L[X] (RatFunc L))).map phi.toRingHom) := by
    exact hqFraction.map (Polynomial.mapAlgEquiv phi)
  let A : RatFunc L := RatFunc.X - RatFunc.C r
  let B : RatFunc L := RatFunc.X - RatFunc.C t
  let Q : Polynomial L := (X - C r) * (X - C t)
  let N : Polynomial L :=
    C alpha * (X - C r) ^ (2 * d) + C beta * (X - C t) ^ (2 * d)
  let R : Polynomial L[X] :=
    monomial (2 * e) (-(Q ^ d)) + monomial e N + C (-(Q ^ d))
  have hB : B ≠ 0 := by
    dsimp [B, t]
    simpa only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using
      RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero (ι (quadraticNonbaseElement p)))
  have hscale : IsUnit (C (B ^ (2 * d)) : Polynomial (RatFunc L)) := by
    rw [Polynomial.isUnit_C]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hB)
  have hRFraction : Irreducible (R.map (algebraMap L[X] (RatFunc L))) := by
    rw [← cayleyTransport_splitIteratedPolynomial alpha beta r t e d hrt hdet]
    exact (irreducible_isUnit_mul hscale).2 hqTransported
  have hcoprime : IsCoprime Q N := by
    have h := (extendedCayleyNormFactor_isCoprime_extendedSeededCayleyNumerator
      p s d hd).map (Polynomial.mapRingHom ι)
    simpa [Q, N, alpha, beta, r, t, extendedCayleyNormFactor,
      extendedSeededCayleyNumerator, extendedCayleyNumeratorFactor,
      extendedCayleyDenominatorFactor] using h
  have hRPrimitive : R.IsPrimitive := by
    have hcoprimePow : IsCoprime (Q ^ d) N := hcoprime.pow_left
    have hprimitive :=
      descendedIteratedPolynomial_isPrimitive_of_isCoprime (Q ^ d) N e he hcoprimePow
    simpa only [R] using hprimitive
  have hR : Irreducible R :=
    hRPrimitive.irreducible_iff_irreducible_map_fraction_map.mpr hRFraction
  have hdescendedIterated :
      finTwoSecondToIteratedPolynomial
          (MvPolynomial.map (ι.comp (algebraMap (F p) (E p)))
            (seededNonsplitDescendedPolynomial p s d e)) = R := by
    rw [← MvPolynomial.map_map]
    rw [finTwoSecondToIteratedPolynomial_map]
    rw [finTwoSecondToIteratedPolynomial_map_seededNonsplitDescendedPolynomial]
    simp [R, Q, N, alpha, beta, r, t, extendedCayleyNormFactor,
      extendedSeededCayleyNumerator, extendedCayleyNumeratorFactor,
      extendedCayleyDenominatorFactor]
  have hback := hR.map (finTwoSecondToIteratedPolynomial (K := L)).symm
  simpa [← hdescendedIterated] using hback

/-- Absolute irreducibility of the descended nonsplit trace curve follows from absolute
irreducibility of its split cover.  The proof applies the split-cover premise over the
quadratic field's algebraic closure, performs the explicit Cayley descent there, and then
uses uniqueness of algebraic closures over the base field. -/
theorem seededNonsplitDescendedPolynomial_absolutelyIrreducible_of_splitCover
    (s : (E p)ˣ) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hcover : Irreducible
      (MvPolynomial.map
        (algebraMap (E p) (AlgebraicClosure (E p)))
        (splitTraceCoverPolynomial (s : E p) ((s : E p) ^ p) e d))) :
    Irreducible
      (MvPolynomial.map
        (algebraMap (F p) (AlgebraicClosure (F p)))
        (seededNonsplitDescendedPolynomial p s d e)) := by
  let K := AlgebraicClosure (E p)
  have hdescendedOverK : Irreducible
      (MvPolynomial.map
        ((algebraMap (E p) K).comp (algebraMap (F p) (E p)))
        (seededNonsplitDescendedPolynomial p s d e)) := by
    exact map_seededNonsplitDescendedPolynomial_irreducible_of_map_splitCover
      p (algebraMap (E p) K) s d e hd he hcover
  let closureEquiv : K ≃ₐ[F p] AlgebraicClosure (F p) :=
    IsAlgClosure.equivOfAlgebraic (F p) (E p) K (AlgebraicClosure (F p))
  have hmapped := hdescendedOverK.map
    (MvPolynomial.mapAlgEquiv (Fin 2) closureEquiv)
  have hcomp :
      (closureEquiv : K →+* AlgebraicClosure (F p)).comp
          ((algebraMap (E p) K).comp (algebraMap (F p) (E p))) =
        algebraMap (F p) (AlgebraicClosure (F p)) := by
    ext x
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact closureEquiv.commutes x
  have hmapped' : Irreducible
      (MvPolynomial.map
        ((closureEquiv : K →+* AlgebraicClosure (F p)).comp
          ((algebraMap (E p) K).comp (algebraMap (F p) (E p))))
        (seededNonsplitDescendedPolynomial p s d e)) := by
    simpa only [MvPolynomial.mapAlgEquiv_apply, MvPolynomial.map_map] using hmapped
  rw [hcomp] at hmapped'
  exact hmapped'

end DescendedFormula

end


end BGS.Markoff
