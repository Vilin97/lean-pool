/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneAffineRationalPlaceComparison
import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointLeadingCoefficient
import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncParameterPole
import LeanPool.MarkoffModP.BGS.HasseWeil.GeneralSquareFieldStepanovCount
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# Rational normalization places and affine exceptional fibers

This file begins the reverse comparison from degree-one normalization places
to affine rational points.  It supplies the two finite-place counting APIs
needed independently of the remaining local-center argument:

* degree-one finite places of `K(X)` are canonically equivalent to `K`;
* rational finite places whose base coordinate is a zero of a polynomial `R`
  are bounded by `#Z(R)` times the function-field degree.

For a plane equation, the exceptional base polynomial is the product of the
second-coordinate leading coefficient and the derivative resultant.  The
leading-coefficient factor is necessary: the derivative resultant alone need
not detect degree drop after specialization, especially in positive
characteristic.
-/

open scoped Polynomial

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier Polynomial

variable (K : Type*) [Field K] [DecidableEq K]

private def linearNormalizedPrime (a : K) : NormalizedPrimePolynomial K :=
  ⟨Polynomial.X - Polynomial.C a, Polynomial.prime_X_sub_C a,
    (Polynomial.monic_X_sub_C a).normalize_eq_self⟩

/-- Degree-one finite places of `K(X)` are exactly the linear primes
`X - a`, hence are canonically parametrized by `a : K`. -/
def ratFuncRationalFinitePlaceEquiv : RatFuncRationalFinitePlace K ≃ K where
  toFun P := -((finitePlaceNormalizedPrime P.1 : K[X]).coeff 0)
  invFun a := ⟨normalizedPrimeFinitePlace (K := K) (linearNormalizedPrime K a), by
    simp [ratFuncFinitePlaceDegree, linearNormalizedPrime]⟩
  left_inv P := by
    apply Subtype.ext
    let r := finitePlaceNormalizedPrime P.1
    have hrNatDegree : (r : K[X]).natDegree = 1 := by
      simpa [r, ratFuncFinitePlaceDegree] using P.2
    have hrDegree : (r : K[X]).degree = 1 := by
      simpa [hrNatDegree] using
        (Polynomial.degree_eq_natDegree r.property.1.ne_zero)
    have hrMonic : (r : K[X]).Monic := by
      rw [← r.property.2]
      exact Polynomial.monic_normalize r.property.1.ne_zero
    have hr : (r : K[X]) =
        Polynomial.X - Polynomial.C (-((r : K[X]).coeff 0)) := by
      simpa [hrMonic.leadingCoeff] using
        (Polynomial.eq_X_add_C_of_degree_eq_one hrDegree)
    symm
    calc
      P.1 = normalizedPrimeFinitePlace (K := K) r :=
        (normalizedPrimeFinitePlace_finitePlaceNormalizedPrime P.1).symm
      _ = normalizedPrimeFinitePlace (K := K)
          (linearNormalizedPrime K (-((r : K[X]).coeff 0))) := by
        congr 1
        exact Subtype.ext hr
  right_inv a := by
    simp [linearNormalizedPrime]

end


noncomputable section

open BGS.CorvajaZannier Polynomial

variable {K : Type*} [Field K]

/-- The base polynomial containing both the critical fibers and the fibers
where the second-coordinate degree drops. -/
noncomputable def secondCoordinateAffineExceptionalPolynomial
    (f : MvPolynomial (Fin 2) K) : Polynomial K :=
  (planeCurvePolynomialInSecondCoordinate f).leadingCoeff *
    secondCoordinateCriticalResultant f

theorem secondCoordinateAffineExceptionalPolynomial_ne_zero
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    secondCoordinateAffineExceptionalPolynomial f ≠ 0 := by
  have hF0 : planeCurvePolynomialInSecondCoordinate f ≠ 0 := by
    intro hzero
    have hdegree : (planeCurvePolynomialInSecondCoordinate f).natDegree = 0 := by
      rw [hzero, Polynomial.natDegree_zero]
    have hpos : 0 < (planeCurvePolynomialInSecondCoordinate f).natDegree := by
      simpa using degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond
    omega
  exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hF0)
    (secondCoordinateCriticalResultant_ne_zero hf hpartialSecond)

theorem secondCoordinateAffineExceptionalPolynomial_natDegree_le
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree) :
    (secondCoordinateAffineExceptionalPolynomial f).natDegree ≤
      firstDegree + (2 * secondDegree - 1) * firstDegree := by
  calc
    (secondCoordinateAffineExceptionalPolynomial f).natDegree ≤
        (planeCurvePolynomialInSecondCoordinate f).leadingCoeff.natDegree +
          (secondCoordinateCriticalResultant f).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ firstDegree + (2 * secondDegree - 1) * firstDegree := by
      exact Nat.add_le_add
        (planeCurvePolynomialInSecondCoordinate_coeff_natDegree_le hdegree _)
        (secondCoordinateCriticalResultant_natDegree_le hdegree)

theorem secondCoordinateAffineExceptionalBase_card_le
    [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    Fintype.card {a : K //
        (secondCoordinateAffineExceptionalPolynomial f).eval a = 0} ≤
      firstDegree + (2 * secondDegree - 1) * firstDegree := by
  exact (polynomialEvalZeroSubtype_card_le_natDegree
    (secondCoordinateAffineExceptionalPolynomial f)
    (secondCoordinateAffineExceptionalPolynomial_ne_zero hf hpartialSecond)).trans
      (secondCoordinateAffineExceptionalPolynomial_natDegree_le hdegree)

end


noncomputable section

open BGS.CorvajaZannier IsDedekindDomain

variable (K : Type*) [Field K] [DecidableEq K]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
  [DecidableEq (RatFunc K)]

local instance rationalComparisonConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance rationalComparisonConstantScalarTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) rationalComparisonPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance rationalComparisonPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance rationalComparisonFiniteClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance rationalComparisonPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance rationalComparisonFiniteClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance rationalComparisonFiniteClosureNoZeroSMulDivisors :
    NoZeroSMulDivisors K[X] (RatFuncFiniteIntegralClosure K L) where
  eq_zero_or_eq_zero_of_smul_eq_zero h := smul_eq_zero.mp h

local instance rationalComparisonFiniteClosureDedekind :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) L
    (RatFuncFiniteIntegralClosure K L)

local instance rationalComparisonFiniteClosureFractionRing :
    IsFractionRing (RatFuncFiniteIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension K[X] (RatFunc K) L
    (RatFuncFiniteIntegralClosure K L)

local instance rationalComparisonFiniteClosureConstantAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure K L) :=
  RingHom.toAlgebra ((algebraMap K[X]
    (RatFuncFiniteIntegralClosure K L)).comp (algebraMap K K[X]))

local instance rationalComparisonFiniteClosureConstantTower :
    IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance rationalComparisonFiniteClosureConstantTowerToField :
    IsScalarTower K (RatFuncFiniteIntegralClosure K L) L := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  rw [IsScalarTower.algebraMap_apply K (RatFunc K) L]
  rfl

/-- At a rational finite place, a nonconstant regular function has a unique
constant residue representative, expressed by positive order of the
difference. -/
theorem exists_constant_sub_finitePlaceOrder_pos_of_nonnegative
    (q : FiniteExtensionRationalFinitePlace K L) (z : L)
    (hz : z ≠ 0)
    (hnotConstant : ∀ c : K, z ≠ algebraMap K L c)
    (hregular : 0 ≤ finitePlaceOrder q.1 z) :
    ∃ c : K, 0 < finitePlaceOrder q.1 (z - algebraMap K L c) := by
  by_cases hpos : 0 < finitePlaceOrder q.1 z
  · exact ⟨0, by simpa using hpos⟩
  have hzero : finitePlaceOrder q.1 z = 0 :=
    le_antisymm (not_lt.mp hpos) hregular
  have horders :
      finiteExtensionPrincipalDivisor K L z (.inl q.1) =
        finiteExtensionPrincipalDivisor K L 1 (.inl q.1) := by
    rw [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder, hzero,
      finiteExtensionPrincipalDivisor_one]
    rfl
  obtain ⟨c, hc⟩ :=
    exists_constant_finiteExtensionPlaceOrder_sub_mul_eq_zero_or_lt
      K L (.inl q.1) q.2 z 1 hz one_ne_zero horders
  refine ⟨c, ?_⟩
  rcases hc with hconstant | hstrict
  · exact (hnotConstant c (by simpa using sub_eq_zero.mp hconstant)).elim
  · rw [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder, hzero] at hstrict
    simpa only [mul_one,
      finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder] using hstrict

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- Nonnegative finite-place order is equivalent to regularity in the
canonical valuation subring; this direction is the one needed below. -/
theorem mem_valuationSubringAtPrime_of_finitePlaceOrder_nonnegative
    (q : HeightOneSpectrum (RatFuncFiniteIntegralClosure K L))
    (z : L) (hz : z ≠ 0) (hregular : 0 ≤ finitePlaceOrder q z) :
    z ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L q := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  change q.valuation L z ≤ 1
  rw [valuation_eq_exp_neg_finitePlaceOrder q z hz, ← WithZero.exp_zero]
  exact WithZero.exp_le_exp.mpr (by omega)

omit [DecidableEq (RatFunc K)] in
/-- The full lying-over fiber above a rational finite base place has at most
the extension degree many primes. -/
theorem rationalBasePlace_primesOver_card_le_finrank
    (P : RatFuncRationalFinitePlace K) :
    Fintype.card
        (P.1.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L)) ≤
      Module.finrank (RatFunc K) L := by
  letI : Fintype
      (P.1.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L)) :=
    Set.Finite.fintype (IsDedekindDomain.primesOver_finite P.1.asIdeal
      (RatFuncFiniteIntegralClosure K L))
  let e : P.1.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L) ≃
      ↥(IsDedekindDomain.primesOverFinset P.1.asIdeal
        (RatFuncFiniteIntegralClosure K L)) :=
    Equiv.setCongr
      (IsDedekindDomain.coe_primesOverFinset P.1.ne_bot
        (RatFuncFiniteIntegralClosure K L)).symm
  calc
    Fintype.card
        (P.1.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L)) =
        Fintype.card ↥(IsDedekindDomain.primesOverFinset P.1.asIdeal
          (RatFuncFiniteIntegralClosure K L)) := Fintype.card_congr e
    _ = (IsDedekindDomain.primesOverFinset P.1.asIdeal
          (RatFuncFiniteIntegralClosure K L)).card := Fintype.card_coe _
    _ ≤ Module.finrank (RatFunc K) L :=
      Ideal.card_primesOverFinset_le_finrank
        (RatFuncFiniteIntegralClosure K L) (RatFunc K) L P.1.ne_bot

/-- The first-coordinate value of the rational base place below a rational
finite extension place. -/
def rationalFinitePlaceBaseCoordinate
    (Q : FiniteExtensionRationalFinitePlace K L) : K :=
  ratFuncRationalFinitePlaceEquiv K
    (rationalFinitePlaceToBaseFiber K L Q).1

/-- Rational finite places whose base coordinate is a zero of `R`. -/
abbrev RationalFinitePlaceOverPolynomialZeros (R : Polynomial K) :=
  {Q : FiniteExtensionRationalFinitePlace K L //
    R.eval (rationalFinitePlaceBaseCoordinate K L Q) = 0}

/-- A base polynomial with `r` rational roots accounts for at most
`r * [L : K(X)]` rational finite places. -/
theorem rationalFinitePlaceOverPolynomialZeros_card_le
    [Fintype K] (R : Polynomial K) :
    Nat.card (RationalFinitePlaceOverPolynomialZeros K L R) ≤
      Fintype.card {a : K // R.eval a = 0} *
        Module.finrank (RatFunc K) L := by
  let baseZero := {P : RatFuncRationalFinitePlace K //
    R.eval (ratFuncRationalFinitePlaceEquiv K P) = 0}
  letI : Fintype (RationalFinitePlaceOverPolynomialZeros K L R) :=
    Fintype.ofFinite _
  letI : Fintype baseZero := Fintype.ofFinite baseZero
  letI (P : baseZero) :
      Fintype (P.1.1.asIdeal.primesOver
        (RatFuncFiniteIntegralClosure K L)) :=
    Set.Finite.fintype (IsDedekindDomain.primesOver_finite P.1.1.asIdeal
      (RatFuncFiniteIntegralClosure K L))
  let embedding : RationalFinitePlaceOverPolynomialZeros K L R →
      Sigma (fun P : baseZero => P.1.1.asIdeal.primesOver
        (RatFuncFiniteIntegralClosure K L)) := fun Q =>
    ⟨⟨(rationalFinitePlaceToBaseFiber K L Q.1).1, Q.2⟩,
      (rationalFinitePlaceToBaseFiber K L Q.1).2⟩
  have embedding_injective : Function.Injective embedding := by
    intro Q S hQS
    apply Subtype.ext
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    have hIdeals := congrArg
      (fun z : Sigma (fun P : baseZero => P.1.1.asIdeal.primesOver
        (RatFuncFiniteIntegralClosure K L)) => z.2.1) hQS
    simpa [embedding, rationalFinitePlaceToBaseFiber] using hIdeals
  let baseEquiv : baseZero ≃ {a : K // R.eval a = 0} :=
    Equiv.subtypeEquiv (ratFuncRationalFinitePlaceEquiv K) (by
      intro P
      rfl)
  calc
    Nat.card (RationalFinitePlaceOverPolynomialZeros K L R) =
        Fintype.card (RationalFinitePlaceOverPolynomialZeros K L R) :=
      Nat.card_eq_fintype_card
    _ ≤ Fintype.card (Sigma (fun P : baseZero =>
          P.1.1.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L))) :=
      Fintype.card_le_of_injective embedding embedding_injective
    _ = ∑ P : baseZero, Fintype.card
          (P.1.1.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L)) :=
      Fintype.card_sigma
    _ ≤ ∑ _P : baseZero, Module.finrank (RatFunc K) L := by
      exact Finset.sum_le_sum fun P _ =>
        rationalBasePlace_primesOver_card_le_finrank K L P.1
    _ = Fintype.card baseZero * Module.finrank (RatFunc K) L := by
      simp
    _ = Fintype.card {a : K // R.eval a = 0} *
        Module.finrank (RatFunc K) L := by
      rw [Fintype.card_congr baseEquiv]

/-- Rational finite places whose base coordinate avoids the zero locus of
`R`. -/
abbrev RationalFinitePlaceAwayFromPolynomialZeros (R : Polynomial K) :=
  {Q : FiniteExtensionRationalFinitePlace K L //
    R.eval (rationalFinitePlaceBaseCoordinate K L Q) ≠ 0}

/-- Rational finite places split as the places away from `R = 0` and the
places over `R = 0`. -/
theorem rationalFinitePlace_card_eq_away_add_overPolynomialZeros
    [Finite K] (R : Polynomial K) :
    Nat.card (FiniteExtensionRationalFinitePlace K L) =
      Nat.card (RationalFinitePlaceAwayFromPolynomialZeros K L R) +
        Nat.card (RationalFinitePlaceOverPolynomialZeros K L R) := by
  classical
  calc
    Nat.card (FiniteExtensionRationalFinitePlace K L) =
        Nat.card
          (RationalFinitePlaceOverPolynomialZeros K L R ⊕
            RationalFinitePlaceAwayFromPolynomialZeros K L R) :=
      Nat.card_congr
        (Equiv.sumCompl (fun Q : FiniteExtensionRationalFinitePlace K L =>
          R.eval (rationalFinitePlaceBaseCoordinate K L Q) = 0)).symm
    _ = Nat.card (RationalFinitePlaceOverPolynomialZeros K L R) +
        Nat.card (RationalFinitePlaceAwayFromPolynomialZeros K L R) :=
      Nat.card_sum
    _ = Nat.card (RationalFinitePlaceAwayFromPolynomialZeros K L R) +
        Nat.card (RationalFinitePlaceOverPolynomialZeros K L R) :=
      Nat.add_comm _ _

/-- Abstract reverse counting principle.  An injective center map from the
rational finite places away from `R = 0` into a finite type `A`, together with
the bad-fiber and infinity estimates, bounds every rational place. -/
theorem finiteExtensionRationalPlaceCount_le_natCard_add_polynomialZeros_of_away_injective
    [Fintype K] (R : Polynomial K) (A : Type*) [Finite A]
    (center : RationalFinitePlaceAwayFromPolynomialZeros K L R → A)
    (hcenter : Function.Injective center) :
    finiteExtensionRationalPlaceCount K L ≤
      Nat.card A +
        Fintype.card {a : K // R.eval a = 0} *
          Module.finrank (RatFunc K) L +
        Module.finrank (RatFunc K) L := by
  classical
  have hgood :
      Nat.card (RationalFinitePlaceAwayFromPolynomialZeros K L R) ≤
        Nat.card A :=
    Nat.card_le_card_of_injective center hcenter
  have hbad := rationalFinitePlaceOverPolynomialZeros_card_le K L R
  have hinfinity := rationalInfinityPlace_card_le_finrank K L
  rw [finiteExtensionRationalPlaceCount, Nat.card_sum,
    rationalFinitePlace_card_eq_away_add_overPolynomialZeros
      (K := K) (L := L) R]
  omega

/-- A base polynomial that does not vanish at the rational base coordinate
of a rational finite extension place becomes a unit in that place's
valuation subring. -/
theorem rationalFinitePlacePolynomial_isUnit_of_eval_baseCoordinate_ne_zero
    (Q : FiniteExtensionRationalFinitePlace K L) (R : Polynomial K)
    (hR : R.eval (rationalFinitePlaceBaseCoordinate K L Q) ≠ 0) :
    let V := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L Q.1
    letI : Algebra K[X] V := RingHom.toAlgebra
      ((algebraMap (RatFuncFiniteIntegralClosure K L) V).comp
        (algebraMap K[X] (RatFuncFiniteIntegralClosure K L)))
    IsUnit (algebraMap K[X] V R) := by
  let B := RatFuncFiniteIntegralClosure K L
  let V := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L Q.1
  letI : Algebra K[X] V := RingHom.toAlgebra
    ((algebraMap (RatFuncFiniteIntegralClosure K L) V).comp
      (algebraMap K[X] (RatFuncFiniteIntegralClosure K L)))
  dsimp only
  by_contra hunit
  have hmax : algebraMap K[X] V R ∈ IsLocalRing.maximalIdeal V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hunit
  have hqB : algebraMap K[X] B R ∈ Q.1.asIdeal := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal V Q.1.asIdeal]
    exact hmax
  have hbase : R ∈
      (IsDedekindDomain.HeightOneSpectrum.under K[X] Q.1).asIdeal := hqB
  let P : RatFuncRationalFinitePlace K :=
    (rationalFinitePlaceToBaseFiber K L Q).1
  let a : K := ratFuncRationalFinitePlaceEquiv K P
  have hP : P = (ratFuncRationalFinitePlaceEquiv K).symm a := by
    exact (Equiv.symm_apply_apply (ratFuncRationalFinitePlaceEquiv K) P).symm
  have hspan : R ∈ Ideal.span {Polynomial.X - Polynomial.C a} := by
    change R ∈ P.1.asIdeal at hbase
    rw [hP] at hbase
    exact hbase
  have heval : R.eval a = 0 := by
    have hker : R ∈ RingHom.ker (Polynomial.evalRingHom a) := by
      rw [Polynomial.ker_evalRingHom]
      exact hspan
    simpa [RingHom.mem_ker] using hker
  exact hR heval

/-- The residue of the rational-function parameter at a rational finite
extension place is its recorded base coordinate. -/
theorem rationalFinitePlaceBaseCoordinate_residue
    (Q : FiniteExtensionRationalFinitePlace K L) :
    let B := RatFuncFiniteIntegralClosure K L
    let V := HeightOneSpectrum.valuationSubringAtPrime L Q.1
    letI : Algebra K[X] V := RingHom.toAlgebra
      ((algebraMap B V).comp (algebraMap K[X] B))
    letI : Algebra K V := RingHom.toAlgebra
      ((algebraMap B V).comp (algebraMap K B))
    letI : IsScalarTower K K[X] V := IsScalarTower.of_algebraMap_eq' rfl
    let m := IsLocalRing.maximalIdeal V
    algebraMap K m.ResidueField (rationalFinitePlaceBaseCoordinate K L Q) =
      algebraMap V m.ResidueField (algebraMap K[X] V Polynomial.X) := by
  let B := RatFuncFiniteIntegralClosure K L
  let V := HeightOneSpectrum.valuationSubringAtPrime L Q.1
  letI : Algebra K[X] V := RingHom.toAlgebra
    ((algebraMap B V).comp (algebraMap K[X] B))
  letI : Algebra K V := RingHom.toAlgebra
    ((algebraMap B V).comp (algebraMap K B))
  letI : IsScalarTower K K[X] V := IsScalarTower.of_algebraMap_eq' rfl
  let m := IsLocalRing.maximalIdeal V
  dsimp only
  let P : RatFuncRationalFinitePlace K :=
    (rationalFinitePlaceToBaseFiber K L Q).1
  let a : K := ratFuncRationalFinitePlaceEquiv K P
  have hP : P = (ratFuncRationalFinitePlaceEquiv K).symm a := by
    exact (Equiv.symm_apply_apply (ratFuncRationalFinitePlaceEquiv K) P).symm
  have hlinear : Polynomial.X - Polynomial.C a ∈
      (HeightOneSpectrum.under K[X] Q.1).asIdeal := by
    change Polynomial.X - Polynomial.C a ∈ P.1.asIdeal
    rw [hP]
    exact Ideal.mem_span_singleton_self (Polynomial.X - Polynomial.C a)
  have hB : algebraMap K[X] B (Polynomial.X - Polynomial.C a) ∈
      Q.1.asIdeal := hlinear
  have hV : algebraMap B V
      (algebraMap K[X] B (Polynomial.X - Polynomial.C a)) ∈ m := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal V Q.1.asIdeal] at hB
    exact hB
  have hzero : algebraMap V m.ResidueField
      (algebraMap K[X] V (Polynomial.X - Polynomial.C a)) = 0 := by
    apply Ideal.algebraMap_residueField_eq_zero.mpr
    change algebraMap B V
      (algebraMap K[X] B (Polynomial.X - Polynomial.C a)) ∈ m
    exact hV
  have ha : a = rationalFinitePlaceBaseCoordinate K L Q := rfl
  rw [← ha]
  have htower : ∀ c : K, algebraMap K V c =
      algebraMap K[X] V (Polynomial.C c) := by
    intro c
    exact (IsScalarTower.algebraMap_apply K K[X] V c).symm
  simp only [map_sub] at hzero
  rw [← htower a,
    ← IsScalarTower.algebraMap_apply K V m.ResidueField a] at hzero
  exact (sub_eq_zero.mp hzero).symm

end


noncomputable section

open BGS.CorvajaZannier IsDedekindDomain Polynomial


variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {f : MvPolynomial (Fin 2) K}

omit [Fintype K] in
/-- Away from the leading-coefficient zero locus, the second plane
coordinate is regular in the valuation subring of a rational finite place.
The proof makes the specialized leading coefficient a unit, obtains a monic
equation over the valuation ring, and uses its integral closedness. -/
theorem planeCurveSecondCoordinate_mem_valuationSubringAtPrime_of_affineExceptional_ne_zero
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    ∀ Q : FiniteExtensionRationalFinitePlace K (PlaneCurveFunctionField f),
      (secondCoordinateAffineExceptionalPolynomial f).eval
          (rationalFinitePlaceBaseCoordinate K (PlaneCurveFunctionField f) Q) ≠ 0 →
        planeCurveFunction f 1 ∈
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
            (PlaneCurveFunctionField f) Q.1 := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let E := PlaneCurveFunctionField f
  letI : Algebra (RatFunc K) E :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : Algebra K[X] E :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) E).comp
        (algebraMap K[X] (RatFunc K)))
  letI : IsScalarTower K[X] (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (RatFunc K) E :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) E :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  let B := RatFuncFiniteIntegralClosure K E
  letI : Module.Finite K[X] B :=
    Module.IsNoetherian.finite K[X] B
  letI : Module.IsTorsionFree K[X] E :=
    Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) E
  letI : Module.IsTorsionFree K[X] B :=
    IsIntegralClosure.isTorsionFree K[X] E
  letI : NoZeroSMulDivisors K[X] B :=
    { eq_zero_or_eq_zero_of_smul_eq_zero := fun h => smul_eq_zero.mp h }
  letI : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) E B
  letI : IsFractionRing B E :=
    IsIntegralClosure.isFractionRing_of_finite_extension K[X]
      (RatFunc K) E B
  dsimp only
  intro Q hgood
  let V := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E Q.1
  letI : Algebra K[X] V := RingHom.toAlgebra
    ((algebraMap B V).comp (algebraMap K[X] B))
  letI : IsScalarTower K[X] V E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let F : K[X][X] := planeCurvePolynomialInSecondCoordinate f
  let G : V[X] := F.map (algebraMap K[X] V)
  have hlcEval : F.leadingCoeff.eval
      (rationalFinitePlaceBaseCoordinate K E Q) ≠ 0 := by
    change ((planeCurvePolynomialInSecondCoordinate f).leadingCoeff *
      secondCoordinateCriticalResultant f).eval
        (rationalFinitePlaceBaseCoordinate K E Q) ≠ 0 at hgood
    rw [Polynomial.eval_mul] at hgood
    exact (mul_ne_zero_iff.mp hgood).1
  have hlcUnit : IsUnit (algebraMap K[X] V F.leadingCoeff) :=
    rationalFinitePlacePolynomial_isUnit_of_eval_baseCoordinate_ne_zero
      K E Q F.leadingCoeff hlcEval
  have hGLeading : G.leadingCoeff = algebraMap K[X] V F.leadingCoeff := by
    have hinjective : Function.Injective (algebraMap K[X] V) := by
      intro p q hpq
      apply FaithfulSMul.algebraMap_injective K[X] E
      have hmap := congrArg (algebraMap V E) hpq
      simpa only [IsScalarTower.algebraMap_apply K[X] V E] using hmap
    exact Polynomial.leadingCoeff_map_of_injective hinjective F
  have hGUnit : IsUnit G.leadingCoeff := by
    rw [hGLeading]
    exact hlcUnit
  have hroot : Polynomial.aeval (planeCurveFunction f 1) G = 0 := by
    have hroot0 :=
      aeval_planeCurvePolynomialInSecondCoordinate_ratFunc_eq_zero
        hf hpartialSecond
    dsimp only at hroot0
    rw [Polynomial.aeval_def]
    change Polynomial.eval₂ (algebraMap V E) (planeCurveFunction f 1)
      (F.map (algebraMap K[X] V)) = 0
    rw [Polynomial.eval₂_map,
      ← IsScalarTower.algebraMap_eq K[X] V E]
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      ← IsScalarTower.algebraMap_eq K[X] (RatFunc K) E] at hroot0
    exact hroot0
  let H : V[X] := hGUnit.unit⁻¹ • G
  have hHMonic : H.Monic :=
    Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hGUnit
  have hHRoot : Polynomial.aeval (planeCurveFunction f 1) H = 0 := by
    change Polynomial.aeval (planeCurveFunction f 1)
      (hGUnit.unit⁻¹ • G) = 0
    rw [Units.smul_def, map_smul, hroot, smul_zero]
  have hintegral : IsIntegral V (planeCurveFunction f 1) :=
    ⟨H, hHMonic, hHRoot⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintegral
  exact hy ▸ y.2

/-- The affine residue center of a rational finite normalization place away
from the leading-coefficient/discriminant locus.  Both plane coordinates are
regular there, and the degree-one residue field identifies their residue
classes with unique constants in `K`. -/
noncomputable def planeCurveGoodRationalFinitePlaceCenter
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    RationalFinitePlaceAwayFromPolynomialZeros K
      (PlaneCurveFunctionField f)
      (secondCoordinateAffineExceptionalPolynomial f) →
        AffinePlaneCurvePoint f := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let E := PlaneCurveFunctionField f
  letI : Algebra (RatFunc K) E :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : Algebra K[X] E :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) E).comp
        (algebraMap K[X] (RatFunc K)))
  letI : IsScalarTower K[X] (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (RatFunc K) E :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) E :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  let B := RatFuncFiniteIntegralClosure K E
  letI : Module.Finite K[X] B := Module.IsNoetherian.finite K[X] B
  letI : Module.IsTorsionFree K[X] E :=
    Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) E
  letI : Module.IsTorsionFree K[X] B :=
    IsIntegralClosure.isTorsionFree K[X] E
  letI : NoZeroSMulDivisors K[X] B :=
    { eq_zero_or_eq_zero_of_smul_eq_zero := fun h => smul_eq_zero.mp h }
  letI : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) E B
  letI : IsFractionRing B E :=
    IsIntegralClosure.isFractionRing_of_finite_extension K[X]
      (RatFunc K) E B
  letI : Algebra K B := RingHom.toAlgebra
    ((algebraMap K[X] B).comp (algebraMap K K[X]))
  letI : IsScalarTower K K[X] B := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      have h := congrArg
        (fun g : Polynomial K →+* E => g (Polynomial.C c))
        (ratFuncSpecialization_comp_polynomial_algebraMap
          (planeCurveFunction f 0) hx)
      simpa [E, planeCurveFirstCoordinateRatFuncAlgebra] using h.symm)
  letI : IsScalarTower K K[X] E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      rw [IsScalarTower.algebraMap_apply K (RatFunc K) E,
        IsScalarTower.algebraMap_apply K K[X] (RatFunc K)]
      rfl)
  letI : IsScalarTower K B E := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rw [IsScalarTower.algebraMap_apply K K[X] E]
    rfl)
  dsimp only
  intro Q
  let V := HeightOneSpectrum.valuationSubringAtPrime E Q.1.1
  letI : Algebra K[X] V := RingHom.toAlgebra
    ((algebraMap B V).comp (algebraMap K[X] B))
  letI : IsScalarTower K[X] V E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra K V := RingHom.toAlgebra
    ((algebraMap B V).comp (algebraMap K B))
  letI : IsScalarTower K B V := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K V E := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rw [IsScalarTower.algebraMap_apply K B E]
    rfl)
  let m := IsLocalRing.maximalIdeal V
  have hglobalResidue : Function.Surjective
      (algebraMap K Q.1.1.asIdeal.ResidueField) :=
    finiteExtensionFinitePlace_constantResidue_surjective_of_degree_one
      K E Q.1.1 Q.1.2
  have hresidue : Function.Surjective
      (algebraMap K m.ResidueField) :=
    localizationAtPrime_constantResidue_surjective
      (C := K) (R := B) (S := V) Q.1.1 hglobalResidue
  let xv : V := algebraMap K[X] V Polynomial.X
  have hxv : (xv : E) = planeCurveFunction f 0 := by
    rw [show (xv : E) = algebraMap K[X] E Polynomial.X by
      exact IsScalarTower.algebraMap_apply K[X] V E Polynomial.X]
    have h := congrArg
      (fun g : Polynomial K →+* E => g Polynomial.X)
      (ratFuncSpecialization_comp_polynomial_algebraMap
        (planeCurveFunction f 0) hx)
    change ratFuncSpecialization (planeCurveFunction f 0) hx
      (algebraMap K[X] (RatFunc K) Polynomial.X) = planeCurveFunction f 0
    simpa using h
  have hymem : planeCurveFunction f 1 ∈ V :=
    planeCurveSecondCoordinate_mem_valuationSubringAtPrime_of_affineExceptional_ne_zero
      hf hpartialSecond Q.1 Q.2
  let yv : V := ⟨planeCurveFunction f 1, hymem⟩
  let a : K := rationalFinitePlaceBaseCoordinate K E Q.1
  have ha : algebraMap K m.ResidueField a =
      algebraMap V m.ResidueField xv := by
    exact rationalFinitePlaceBaseCoordinate_residue K E Q.1
  let b : K := Classical.choose
    (hresidue (algebraMap V m.ResidueField yv))
  have hb : algebraMap K m.ResidueField b =
      algebraMap V m.ResidueField yv := Classical.choose_spec
        (hresidue (algebraMap V m.ResidueField yv))
  let evalV : MvPolynomial (Fin 2) K →+* V :=
    MvPolynomial.eval₂Hom (algebraMap K V) ![xv, yv]
  have hfV : evalV f = 0 := by
    apply Subtype.ext
    simp only [evalV, MvPolynomial.coe_eval₂Hom]
    change algebraMap V E
      (MvPolynomial.eval₂ (algebraMap K V) ![xv, yv] f) = 0
    rw [MvPolynomial.eval₂_comp_left,
      ← IsScalarTower.algebraMap_eq K V E]
    have hcoordinatesE : (algebraMap V E) ∘ ![xv, yv] =
        ![(xv : E), (yv : E)] := by
      funext i
      fin_cases i <;> rfl
    rw [hcoordinatesE, hxv]
    change MvPolynomial.eval₂ (algebraMap K E)
      ![planeCurveFunction f 0, planeCurveFunction f 1] f = 0
    have hcoordinates : planeCurveFunction f =
        ![planeCurveFunction f 0, planeCurveFunction f 1] := by
      funext i
      fin_cases i <;> rfl
    rw [← hcoordinates]
    exact eval₂_planeCurveFunction_eq_zero f
  let evalK : MvPolynomial (Fin 2) K →+* K :=
    MvPolynomial.eval₂Hom (RingHom.id K) ![a, b]
  have hcomp : (algebraMap K m.ResidueField).comp evalK =
      (algebraMap V m.ResidueField).comp evalV := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, evalK, evalV,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      exact (IsScalarTower.algebraMap_apply K V m.ResidueField c).symm
    · intro i
      fin_cases i
      · simpa [evalK, evalV] using ha
      · simpa [evalK, evalV] using hb
  refine ⟨(a, b), ?_⟩
  change evalK f = 0
  apply (algebraMap K m.ResidueField).injective
  rw [map_zero]
  calc
    algebraMap K m.ResidueField (evalK f) =
        ((algebraMap K m.ResidueField).comp evalK) f := rfl
    _ = ((algebraMap V m.ResidueField).comp evalV) f := by rw [hcomp]
    _ = algebraMap V m.ResidueField (evalV f) := rfl
    _ = 0 := by rw [hfV, map_zero]

omit [Fintype K] in
/-- The first coordinate of the affine residue center is the base coordinate
of the rational finite place. -/
theorem planeCurveGoodRationalFinitePlaceCenter_firstCoordinate
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    ∀ Q : RationalFinitePlaceAwayFromPolynomialZeros K
        (PlaneCurveFunctionField f)
        (secondCoordinateAffineExceptionalPolynomial f),
      (planeCurveGoodRationalFinitePlaceCenter hf hpartialSecond Q).1.1 =
        rationalFinitePlaceBaseCoordinate K (PlaneCurveFunctionField f) Q.1 := by
  classical
  dsimp only
  intro Q
  rfl

omit [Fintype K] in
/-- The second coordinate of the affine center represents the residue class
of the second plane coordinate in the local residue field. -/
theorem planeCurveGoodRationalFinitePlaceCenter_secondCoordinate_residue
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    ∀ Q : RationalFinitePlaceAwayFromPolynomialZeros K
        (PlaneCurveFunctionField f)
        (secondCoordinateAffineExceptionalPolynomial f),
      let E := PlaneCurveFunctionField f
      let B := RatFuncFiniteIntegralClosure K E
      let V := HeightOneSpectrum.valuationSubringAtPrime E Q.1.1
      letI : Algebra K[X] V := RingHom.toAlgebra
        ((algebraMap B V).comp (algebraMap K[X] B))
      letI : Algebra K B := RingHom.toAlgebra
        ((algebraMap K[X] B).comp (algebraMap K K[X]))
      letI : Algebra K V := RingHom.toAlgebra
        ((algebraMap B V).comp (algebraMap K B))
      let m := IsLocalRing.maximalIdeal V
      algebraMap K m.ResidueField
          (planeCurveGoodRationalFinitePlaceCenter hf hpartialSecond Q).1.2 =
        algebraMap V m.ResidueField
          (⟨planeCurveFunction f 1,
            planeCurveSecondCoordinate_mem_valuationSubringAtPrime_of_affineExceptional_ne_zero
              hf hpartialSecond Q.1 Q.2⟩ : V) := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let E := PlaneCurveFunctionField f
  letI : Algebra (RatFunc K) E :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : Algebra K[X] E := RingHom.toAlgebra
    ((algebraMap (RatFunc K) E).comp (algebraMap K[X] (RatFunc K)))
  letI : IsScalarTower K[X] (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (RatFunc K) E :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) E :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  let B := RatFuncFiniteIntegralClosure K E
  letI : Module.Finite K[X] B := Module.IsNoetherian.finite K[X] B
  letI : Module.IsTorsionFree K[X] E :=
    Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) E
  letI : Module.IsTorsionFree K[X] B :=
    IsIntegralClosure.isTorsionFree K[X] E
  letI : NoZeroSMulDivisors K[X] B :=
    { eq_zero_or_eq_zero_of_smul_eq_zero := fun h => smul_eq_zero.mp h }
  letI : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) E B
  letI : IsFractionRing B E :=
    IsIntegralClosure.isFractionRing_of_finite_extension K[X] (RatFunc K) E B
  letI : Algebra K B := RingHom.toAlgebra
    ((algebraMap K[X] B).comp (algebraMap K K[X]))
  letI : IsScalarTower K K[X] B := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      have h := congrArg
        (fun g : Polynomial K →+* E => g (Polynomial.C c))
        (ratFuncSpecialization_comp_polynomial_algebraMap
          (planeCurveFunction f 0) hx)
      simpa [E, planeCurveFirstCoordinateRatFuncAlgebra] using h.symm)
  letI : IsScalarTower K K[X] E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      rw [IsScalarTower.algebraMap_apply K (RatFunc K) E,
        IsScalarTower.algebraMap_apply K K[X] (RatFunc K)]
      rfl)
  letI : IsScalarTower K B E := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rw [IsScalarTower.algebraMap_apply K K[X] E]
    rfl)
  dsimp only
  intro Q
  let V := HeightOneSpectrum.valuationSubringAtPrime E Q.1.1
  letI : Algebra K[X] V := RingHom.toAlgebra
    ((algebraMap B V).comp (algebraMap K[X] B))
  letI : IsScalarTower K[X] V E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra K V := RingHom.toAlgebra
    ((algebraMap B V).comp (algebraMap K B))
  letI : IsScalarTower K B V := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K V E := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rw [IsScalarTower.algebraMap_apply K B E]
    rfl)
  let m := IsLocalRing.maximalIdeal V
  have hglobalResidue : Function.Surjective
      (algebraMap K Q.1.1.asIdeal.ResidueField) :=
    finiteExtensionFinitePlace_constantResidue_surjective_of_degree_one
      K E Q.1.1 Q.1.2
  have hresidue : Function.Surjective (algebraMap K m.ResidueField) :=
    localizationAtPrime_constantResidue_surjective
      (C := K) (R := B) (S := V) Q.1.1 hglobalResidue
  let yv : V := ⟨planeCurveFunction f 1,
    planeCurveSecondCoordinate_mem_valuationSubringAtPrime_of_affineExceptional_ne_zero
      hf hpartialSecond Q.1 Q.2⟩
  change algebraMap K m.ResidueField
      (Classical.choose (hresidue (algebraMap V m.ResidueField yv))) =
    algebraMap V m.ResidueField yv
  exact Classical.choose_spec
    (hresidue (algebraMap V m.ResidueField yv))

omit [Fintype K] in
/-- A good rational finite place admits a coordinate-ring map into its
valuation ring.  The map is the canonical inclusion in the function field,
and the inverse image of the local maximal ideal is exactly the maximal ideal
of its affine residue center. -/
theorem exists_planeCurveGoodRationalFinitePlace_centeredCoordinateRingHom
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    ∀ Q : RationalFinitePlaceAwayFromPolynomialZeros K
        (PlaneCurveFunctionField f)
        (secondCoordinateAffineExceptionalPolynomial f),
      let A := PlaneCurveCoordinateRing f
      let E := PlaneCurveFunctionField f
      let V := HeightOneSpectrum.valuationSubringAtPrime E Q.1.1
      ∃ φ : A →+* V,
        (∀ r : A, ((φ r : V) : E) = algebraMap A E r) ∧
          Ideal.comap φ (IsLocalRing.maximalIdeal V) =
            (affinePlaneCurvePointMaximalIdeal f
              (planeCurveGoodRationalFinitePlaceCenter
                hf hpartialSecond Q)).asIdeal := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let A := PlaneCurveCoordinateRing f
  let E := PlaneCurveFunctionField f
  letI : Algebra (RatFunc K) E :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : Algebra K[X] E := RingHom.toAlgebra
    ((algebraMap (RatFunc K) E).comp (algebraMap K[X] (RatFunc K)))
  letI : IsScalarTower K[X] (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (RatFunc K) E :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) E :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  let B := RatFuncFiniteIntegralClosure K E
  letI : Module.Finite K[X] B := Module.IsNoetherian.finite K[X] B
  letI : Module.IsTorsionFree K[X] E :=
    Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) E
  letI : Module.IsTorsionFree K[X] B :=
    IsIntegralClosure.isTorsionFree K[X] E
  letI : NoZeroSMulDivisors K[X] B :=
    { eq_zero_or_eq_zero_of_smul_eq_zero := fun h => smul_eq_zero.mp h }
  letI : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) E B
  letI : IsFractionRing B E :=
    IsIntegralClosure.isFractionRing_of_finite_extension K[X] (RatFunc K) E B
  letI : Algebra K B := RingHom.toAlgebra
    ((algebraMap K[X] B).comp (algebraMap K K[X]))
  letI : IsScalarTower K K[X] B := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      have h := congrArg
        (fun g : Polynomial K →+* E => g (Polynomial.C c))
        (ratFuncSpecialization_comp_polynomial_algebraMap
          (planeCurveFunction f 0) hx)
      simpa [E, planeCurveFirstCoordinateRatFuncAlgebra] using h.symm)
  letI : IsScalarTower K K[X] E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      rw [IsScalarTower.algebraMap_apply K (RatFunc K) E,
        IsScalarTower.algebraMap_apply K K[X] (RatFunc K)]
      rfl)
  letI : IsScalarTower K B E := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rw [IsScalarTower.algebraMap_apply K K[X] E]
    rfl)
  dsimp only
  intro Q
  let V := HeightOneSpectrum.valuationSubringAtPrime E Q.1.1
  letI : Algebra K[X] V := RingHom.toAlgebra
    ((algebraMap B V).comp (algebraMap K[X] B))
  letI : IsScalarTower K[X] V E := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra K V := RingHom.toAlgebra
    ((algebraMap B V).comp (algebraMap K B))
  letI : IsScalarTower K B V := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K V E := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rw [IsScalarTower.algebraMap_apply K B E]
    rfl)
  let m := IsLocalRing.maximalIdeal V
  let xv : V := algebraMap K[X] V Polynomial.X
  have hxv : (xv : E) = planeCurveFunction f 0 := by
    rw [show (xv : E) = algebraMap K[X] E Polynomial.X by
      exact IsScalarTower.algebraMap_apply K[X] V E Polynomial.X]
    have h := congrArg
      (fun g : Polynomial K →+* E => g Polynomial.X)
      (ratFuncSpecialization_comp_polynomial_algebraMap
        (planeCurveFunction f 0) hx)
    change ratFuncSpecialization (planeCurveFunction f 0) hx
      (algebraMap K[X] (RatFunc K) Polynomial.X) = planeCurveFunction f 0
    simpa using h
  have hymem : planeCurveFunction f 1 ∈ V :=
    planeCurveSecondCoordinate_mem_valuationSubringAtPrime_of_affineExceptional_ne_zero
      hf hpartialSecond Q.1 Q.2
  let yv : V := ⟨planeCurveFunction f 1, hymem⟩
  let evalV : MvPolynomial (Fin 2) K →+* V :=
    MvPolynomial.eval₂Hom (algebraMap K V) ![xv, yv]
  have hfV : evalV f = 0 := by
    apply Subtype.ext
    simp only [evalV, MvPolynomial.coe_eval₂Hom]
    change algebraMap V E
      (MvPolynomial.eval₂ (algebraMap K V) ![xv, yv] f) = 0
    rw [MvPolynomial.eval₂_comp_left,
      ← IsScalarTower.algebraMap_eq K V E]
    have hcoordinatesE : (algebraMap V E) ∘ ![xv, yv] =
        ![(xv : E), (yv : E)] := by
      funext i
      fin_cases i <;> rfl
    rw [hcoordinatesE, hxv]
    change MvPolynomial.eval₂ (algebraMap K E)
      ![planeCurveFunction f 0, planeCurveFunction f 1] f = 0
    have hcoordinates : planeCurveFunction f =
        ![planeCurveFunction f 0, planeCurveFunction f 1] := by
      funext i
      fin_cases i <;> rfl
    rw [← hcoordinates]
    exact eval₂_planeCurveFunction_eq_zero f
  let φ : A →+* V := Ideal.Quotient.lift (Ideal.span {f}) evalV (by
    intro g hg
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hg
    rw [map_mul, hfV, zero_mul])
  have hφE : ∀ r : A, ((φ r : V) : E) = algebraMap A E r := by
    intro r
    suffices (algebraMap V E).comp φ = algebraMap A E by
      exact DFunLike.congr_fun this r
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, φ, Ideal.Quotient.lift_mk, evalV,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      change algebraMap V E (algebraMap K V c) = algebraMap K E c
      exact (IsScalarTower.algebraMap_apply K V E c).symm
    · intro i
      simp only [RingHom.comp_apply, φ, Ideal.Quotient.lift_mk, evalV,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      fin_cases i
      · change (xv : E) = planeCurveFunction f 0
        exact hxv
      · change (yv : E) = planeCurveFunction f 1
        rfl
  let z := planeCurveGoodRationalFinitePlaceCenter hf hpartialSecond Q
  have hfirst : algebraMap K m.ResidueField z.1.1 =
      algebraMap V m.ResidueField xv := by
    rw [planeCurveGoodRationalFinitePlaceCenter_firstCoordinate
      hf hpartialSecond Q]
    exact rationalFinitePlaceBaseCoordinate_residue K E Q.1
  have hsecond : algebraMap K m.ResidueField z.1.2 =
      algebraMap V m.ResidueField yv := by
    exact planeCurveGoodRationalFinitePlaceCenter_secondCoordinate_residue
      hf hpartialSecond Q
  have hrescomp : (algebraMap V m.ResidueField).comp φ =
      (algebraMap K m.ResidueField).comp (planeCurvePointEval f z) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, φ, Ideal.Quotient.lift_mk, evalV,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
        planeCurvePointEval, Ideal.Quotient.lift_mk]
      exact (IsScalarTower.algebraMap_apply K V m.ResidueField c).symm
    · intro i
      fin_cases i
      · simpa [φ, evalV, planeCurvePointEval, z] using hfirst.symm
      · simpa [φ, evalV, planeCurvePointEval, z] using hsecond.symm
  refine ⟨φ, hφE, ?_⟩
  apply Ideal.ext
  intro r
  change φ r ∈ m ↔ planeCurvePointEval f z r = 0
  rw [← Ideal.algebraMap_residueField_eq_zero]
  have hr := DFunLike.congr_fun hrescomp r
  simp only [RingHom.comp_apply] at hr
  rw [hr]
  constructor
  · intro h
    apply (algebraMap K m.ResidueField).injective
    simpa using h
  · intro h
    simp [h]


omit [Fintype K] in
/-- Avoiding the derivative resultant forces the affine residue center to lie
in the partial-`Y` smooth locus. -/
theorem planeCurveGoodRationalFinitePlaceCenter_partialY_ne_zero
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    ∀ Q : RationalFinitePlaceAwayFromPolynomialZeros K
        (PlaneCurveFunctionField f)
        (secondCoordinateAffineExceptionalPolynomial f),
      MvPolynomial.eval
        ![(planeCurveGoodRationalFinitePlaceCenter hf hpartialSecond Q).1.1,
          (planeCurveGoodRationalFinitePlaceCenter hf hpartialSecond Q).1.2]
        (MvPolynomial.pderiv 1 f) ≠ 0 := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  letI : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  dsimp only
  intro Q hzero
  let z := planeCurveGoodRationalFinitePlaceCenter hf hpartialSecond Q
  have hresultant : (secondCoordinateCriticalResultant f).eval z.1.1 = 0 :=
    secondCoordinateCriticalResultant_eval_eq_zero_of_common_zero
      hpartialSecond z.1.1 z.1.2 z.2 (by simpa [z] using hzero)
  have hgood := Q.2
  change ((planeCurvePolynomialInSecondCoordinate f).leadingCoeff *
      secondCoordinateCriticalResultant f).eval
        (rationalFinitePlaceBaseCoordinate K (PlaneCurveFunctionField f) Q.1) ≠ 0
    at hgood
  rw [Polynomial.eval_mul] at hgood
  have hresultantBase : (secondCoordinateCriticalResultant f).eval
      (rationalFinitePlaceBaseCoordinate K (PlaneCurveFunctionField f) Q.1) ≠ 0 :=
    (mul_ne_zero_iff.mp hgood).2
  apply hresultantBase
  rw [← planeCurveGoodRationalFinitePlaceCenter_firstCoordinate
    hf hpartialSecond Q]
  exact hresultant

/-- At a good rational finite place, the normalization valuation ring is
the unique valuation ring dominating its smooth affine residue center. -/
theorem planeCurveGoodRationalFinitePlace_valuationSubring_eq_dominating
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    ∀ Q : RationalFinitePlaceAwayFromPolynomialZeros K
        (PlaneCurveFunctionField f)
        (secondCoordinateAffineExceptionalPolynomial f),
      HeightOneSpectrum.valuationSubringAtPrime
          (PlaneCurveFunctionField f) Q.1.1 =
        dominatingValuationSubring
          (affinePlaneCurvePointMaximalIdeal f
            (planeCurveGoodRationalFinitePlaceCenter hf hpartialSecond Q)) := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let A := PlaneCurveCoordinateRing f
  let E := PlaneCurveFunctionField f
  letI : Algebra (RatFunc K) E :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : Algebra K[X] E := RingHom.toAlgebra
    ((algebraMap (RatFunc K) E).comp (algebraMap K[X] (RatFunc K)))
  letI : IsScalarTower K[X] (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (RatFunc K) E :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) E :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  let B := RatFuncFiniteIntegralClosure K E
  letI : Module.Finite K[X] B := Module.IsNoetherian.finite K[X] B
  letI : Module.IsTorsionFree K[X] E :=
    Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) E
  letI : Module.IsTorsionFree K[X] B :=
    IsIntegralClosure.isTorsionFree K[X] E
  letI : NoZeroSMulDivisors K[X] B :=
    { eq_zero_or_eq_zero_of_smul_eq_zero := fun h => smul_eq_zero.mp h }
  letI : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) E B
  letI : IsFractionRing B E :=
    IsIntegralClosure.isFractionRing_of_finite_extension K[X] (RatFunc K) E B
  dsimp only
  intro Q
  let z := planeCurveGoodRationalFinitePlaceCenter hf hpartialSecond Q
  let m := affinePlaneCurvePointMaximalIdeal f z
  let V := HeightOneSpectrum.valuationSubringAtPrime E Q.1.1
  let D := dominatingValuationSubring (A := A) (L := E) m
  obtain ⟨φ, hφE, hcenter⟩ :=
    exists_planeCurveGoodRationalFinitePlace_centeredCoordinateRingHom
      hf hpartialSecond Q
  let eCenter := affinePlaneCurvePoint_residueAlgEquiv K z
  letI : Finite m.asIdeal.ResidueField :=
    Finite.of_injective eCenter eCenter.injective
  let r0 : A := planeCurveCoordinate f 0 - algebraMap K A z.1.1
  have hr0mem : r0 ∈ m.asIdeal :=
    firstCoordinate_sub_mem_affinePlaneCurvePointMaximalIdeal z
  have hr0mapEq : algebraMap A E r0 =
      planeCurveFunction f 0 - algebraMap K E z.1.1 := by
    simp only [r0, map_sub]
    rfl
  have hr0map : algebraMap A E r0 ≠ 0 := by
    rw [hr0mapEq]
    exact firstCoordinate_sub_affinePoint_ne_zero hf hpartialSecond z
  have hr0 : r0 ≠ 0 := by
    intro hzero
    apply hr0map
    rw [hzero, map_zero]
  have hm0 : m.asIdeal ≠ ⊥ := by
    intro hm
    apply hr0
    simpa [hm] using hr0mem
  have hsmooth : planeCurvePartialY f ∉ m.asIdeal := by
    change planeCurvePointEval f z (planeCurvePartialY f) ≠ 0
    change MvPolynomial.eval ![z.1.1, z.1.2]
      (MvPolynomial.pderiv 1 f) ≠ 0
    exact planeCurveGoodRationalFinitePlaceCenter_partialY_ne_zero
      hf hpartialSecond Q
  letI : IsDiscreteValuationRing (Localization.AtPrime m.asIdeal) :=
    planeCurveClosedPoint_localization_isDiscreteValuationRing
      K hf m hm0 hsmooth
  let Wsub : Subalgebra A E :=
    Localization.subalgebra.ofField E m.asIdeal.primeCompl
      m.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsDiscreteValuationRing Wsub :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (IsLocalization.algEquiv m.asIdeal.primeCompl
        (Localization.AtPrime m.asIdeal) Wsub).toRingEquiv
  let W : ValuationSubring E :=
    ValuationSubring.ofSubring Wsub.toSubring fun x => by
      simpa [IsLocalization.IsInteger] using
        ValuationRing.isInteger_or_isInteger Wsub x
  letI : Algebra A W := Wsub.algebra'
  letI : IsLocalization m.asIdeal.primeCompl W :=
    Localization.subalgebra.isLocalization_ofField E
      m.asIdeal.primeCompl m.asIdeal.primeCompl_le_nonZeroDivisors
  let eW : Wsub ≃+* W :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  letI : IsDiscreteValuationRing W :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eW
  have hWV : W ≤ V := by
    intro x hx
    change x ∈ Wsub at hx
    rcases hx with ⟨a, s, hs, rfl⟩
    have haV : algebraMap A E a ∈ V := by
      rw [← hφE a]
      exact (φ a).property
    have hsV : algebraMap A E s ∈ V := by
      rw [← hφE s]
      exact (φ s).property
    let sv : V := φ s
    have hsvNot : sv ∉ IsLocalRing.maximalIdeal V := by
      intro hsv
      apply hs
      rw [← hcenter]
      exact hsv
    have hsvUnit : IsUnit sv := by
      by_contra hunit
      apply hsvNot
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hunit
    have hinvV : (algebraMap A E s)⁻¹ ∈ V := by
      have h := Submonoid.inv_mem_of_isUnit (S := V) hsvUnit
      rwa [hφE s] at h
    exact V.toSubring.mul_mem haV hinvV
  have hV : V ≠ ⊤ := by
    change HeightOneSpectrum.valuationSubringAtPrime E Q.1.1 ≠ ⊤
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  have hWVeq : W = V :=
    ValuationSubring.eq_of_le_of_ne_top W hWV hV
  have hWD : W ≤ D := by
    intro x hx
    change x ∈ Wsub at hx
    rcases hx with ⟨a, s, hs, rfl⟩
    have haD : algebraMap A E a ∈ D :=
      range_le_dominatingValuationSubring m ⟨a, rfl⟩
    have hsD : algebraMap A E s ∈ D :=
      range_le_dominatingValuationSubring m ⟨s, rfl⟩
    let sd : D := ⟨algebraMap A E s, hsD⟩
    have hsdNot : sd ∉ IsLocalRing.maximalIdeal D := by
      intro hsd
      apply hs
      rw [pointIdeal_eq_comap_dominatingValuationSubring_maximalIdeal
        (A := A) (L := E)]
      exact hsd
    have hsdUnit : IsUnit sd := by
      by_contra hunit
      apply hsdNot
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hunit
    have hinvD : (algebraMap A E s)⁻¹ ∈ D :=
      Submonoid.inv_mem_of_isUnit (S := D) hsdUnit
    exact D.toSubring.mul_mem haD hinvD
  have hrNonunits : algebraMap A E r0 ∈ D.nonunits :=
    algebraMap_mem_dominatingValuationSubring_nonunits_of_mem
      (A := A) (L := E) m r0 hr0mem
  have hD : D ≠ ⊤ := by
    intro htop
    have hnontrivial : D.valuation.IsNontrivial :=
      (Valuation.isNontrivial_iff_exists_lt_one D.valuation).2
        ⟨algebraMap A E r0, hr0map, hrNonunits⟩
    exact ((ValuationSubring.eq_top_iff D).mp htop) hnontrivial
  have hWDeq : W = D :=
    ValuationSubring.eq_of_le_of_ne_top W hWD hD
  exact hWVeq.symm.trans hWDeq

/-- The residue-center map is injective on the good rational finite
places: smoothness makes the local DVR, hence the dominating valuation ring,
unique. -/
theorem planeCurveGoodRationalFinitePlaceCenter_injective
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    Function.Injective
      (planeCurveGoodRationalFinitePlaceCenter hf hpartialSecond) := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let E := PlaneCurveFunctionField f
  letI : Algebra (RatFunc K) E :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : Algebra K[X] E := RingHom.toAlgebra
    ((algebraMap (RatFunc K) E).comp (algebraMap K[X] (RatFunc K)))
  letI : IsScalarTower K[X] (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (RatFunc K) E :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) E :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  dsimp only
  intro Q R hcenter
  apply Subtype.ext
  apply Subtype.ext
  apply HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := E)
  rw [Valuation.isEquiv_iff_valuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  calc
    HeightOneSpectrum.valuationSubringAtPrime E Q.1.1 =
        dominatingValuationSubring
          (affinePlaneCurvePointMaximalIdeal f
            (planeCurveGoodRationalFinitePlaceCenter hf hpartialSecond Q)) :=
      planeCurveGoodRationalFinitePlace_valuationSubring_eq_dominating
        hf hpartialSecond Q
    _ = dominatingValuationSubring
          (affinePlaneCurvePointMaximalIdeal f
            (planeCurveGoodRationalFinitePlaceCenter hf hpartialSecond R)) := by
      rw [hcenter]
    _ = HeightOneSpectrum.valuationSubringAtPrime E R.1.1 :=
      (planeCurveGoodRationalFinitePlace_valuationSubring_eq_dominating
        hf hpartialSecond R).symm

/-- Plane-curve specialization of the bad-fiber estimate.  Rational finite
places over a base fiber where either the second-coordinate leading
coefficient vanishes or the second-coordinate derivative has a common root
are controlled only by the bidegree. -/
theorem planeCurveExceptionalRationalFinitePlace_card_le
    {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    Nat.card (RationalFinitePlaceOverPolynomialZeros K
      (PlaneCurveFunctionField f)
      (secondCoordinateAffineExceptionalPolynomial f)) ≤
      (firstDegree + (2 * secondDegree - 1) * firstDegree) *
        secondDegree := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  letI : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  dsimp only
  calc
    Nat.card (RationalFinitePlaceOverPolynomialZeros K
        (PlaneCurveFunctionField f)
        (secondCoordinateAffineExceptionalPolynomial f)) ≤
        Fintype.card {a : K //
          (secondCoordinateAffineExceptionalPolynomial f).eval a = 0} *
          Module.finrank (RatFunc K) (PlaneCurveFunctionField f) :=
      rationalFinitePlaceOverPolynomialZeros_card_le K
        (PlaneCurveFunctionField f)
        (secondCoordinateAffineExceptionalPolynomial f)
    _ ≤ (firstDegree + (2 * secondDegree - 1) * firstDegree) *
        secondDegree := by
      apply Nat.mul_le_mul
      · exact secondCoordinateAffineExceptionalBase_card_le
          hdegree hf hpartialSecond
      · rw [finrank_planeCurveFunctionField_over_ratFunc_eq_degreeOf_second
          hf hpartialSecond]
        exact degreeOf_second_le_of_hasBidegreeAtMost hdegree

/-- Conditional reverse affine-normalization comparison.  Once the geometric
center construction is supplied as an injection from rational finite places
away from the leading-coefficient/discriminant locus, the total rational
place count is bounded by affine points, the exceptional finite fibers, and
the places at infinity. -/
theorem finiteExtensionRationalPlaceCount_le_affine_add_exceptional_of_away_injective
    {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    ∀ (center : RationalFinitePlaceAwayFromPolynomialZeros K
        (PlaneCurveFunctionField f)
        (secondCoordinateAffineExceptionalPolynomial f) →
          AffinePlaneCurvePoint f),
      Function.Injective center →
        finiteExtensionRationalPlaceCount K (PlaneCurveFunctionField f) ≤
          Fintype.card (AffinePlaneCurvePoint f) +
            (firstDegree + (2 * secondDegree - 1) * firstDegree) *
              secondDegree + secondDegree := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  letI : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  dsimp only
  intro center hcenter
  have hgeneric :=
    finiteExtensionRationalPlaceCount_le_natCard_add_polynomialZeros_of_away_injective
      (K := K) (L := PlaneCurveFunctionField f)
      (secondCoordinateAffineExceptionalPolynomial f)
      (AffinePlaneCurvePoint f) center hcenter
  have hroots := secondCoordinateAffineExceptionalBase_card_le
    hdegree hf hpartialSecond
  have hrank : Module.finrank (RatFunc K) (PlaneCurveFunctionField f) ≤
      secondDegree := by
    rw [finrank_planeCurveFunctionField_over_ratFunc_eq_degreeOf_second
      hf hpartialSecond]
    exact degreeOf_second_le_of_hasBidegreeAtMost hdegree
  rw [Nat.card_eq_fintype_card] at hgeneric
  nlinarith

/-- Unconditional reverse affine-normalization comparison.  Good rational
finite places inject into affine rational points, exceptional finite fibers
are controlled by the leading-coefficient/resultant polynomial, and infinity
contributes at most the second-coordinate degree. -/
theorem finiteExtensionRationalPlaceCount_le_affine_add_exceptional
    {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    finiteExtensionRationalPlaceCount K (PlaneCurveFunctionField f) ≤
      Fintype.card (AffinePlaneCurvePoint f) +
        (firstDegree + (2 * secondDegree - 1) * firstDegree) *
          secondDegree + secondDegree := by
  classical
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  letI : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  dsimp only
  exact finiteExtensionRationalPlaceCount_le_affine_add_exceptional_of_away_injective
    hdegree hf hpartialSecond
    (planeCurveGoodRationalFinitePlaceCenter hf hpartialSecond)
    (planeCurveGoodRationalFinitePlaceCenter_injective hf hpartialSecond)

end

end BGS.HasseWeil
