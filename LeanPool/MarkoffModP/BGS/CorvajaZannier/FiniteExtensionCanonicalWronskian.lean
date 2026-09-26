/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindDifferentDivisor
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLocalWronskian
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPolynomialHeight
public import Mathlib.Tactic

/-!
# The global Wronskian divisor and the finite different degree

This module supplies two exact global pieces of the Corvaja--Zannier
Wronskian argument for a finite separable extension of `K(X)`.

First, a global derivation gives one global Wronskian element.  Replacing it
at a place by a local-parameter derivation changes the order by exactly the
triangular multiple of the change-of-parameter coefficient.  Accordingly,
the local Wronskians form the sum of the principal divisor of the global
Wronskian and a triangular multiple of a canonical correction divisor.  The
product formula then proves that its degree is exactly the triangular
multiple of the canonical degree.

Second, for an integral primitive element in the finite integral closure,
the weighted degree of the finite different is bounded by the degree of its
power-basis discriminant.  This is obtained without an abstract norm-of-ideal
interface: ideal multiplicities are identified with finite-place orders, and
the existing exhaustive norm formula evaluates their weighted sum.

What is deliberately not asserted here is a Riemann--Hurwitz theorem, an
identification of the correction divisor at the places above infinity, or a
plane-curve genus/boundary estimate.  Those are the remaining geometric
inputs needed to derive the final bound `canonicalDegree + |S| <= 2ab`.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial
open IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) canonicalWronskianPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance canonicalWronskianPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  ⟨fun r s x => by
    simp only [Algebra.smul_def]
    rw [map_mul]
    change (algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) *
      algebraMap (RatFunc K) L s) * x =
      algebraMap K[X] L r * (algebraMap (RatFunc K) L s * x)
    rw [show algebraMap K[X] L r =
      algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) r) by rfl]
    ring⟩

local instance canonicalWronskianFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance canonicalWronskianPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance canonicalWronskianFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance canonicalWronskianFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

/-! ## The finite different and the discriminant degree -/

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
private theorem finiteExtensionFinitePrincipalDivisor_algebraMap_apply
    (d : RatFuncFiniteIntegralClosure K L) (hd : d ≠ 0)
    (q : FiniteExtensionFinitePlace K L) :
    finiteExtensionFinitePrincipalDivisor K L
        (algebraMap (RatFuncFiniteIntegralClosure K L) L d) q =
      (multiplicity q.asIdeal (Ideal.span {d}) : ℤ) := by
  let e := ratFuncFiniteIntegralClosureFractionRingEquiv K L
  have hrepr :
      e.symm (algebraMap (RatFuncFiniteIntegralClosure K L) L d) =
        algebraMap (RatFuncFiniteIntegralClosure K L)
          (FractionRing (RatFuncFiniteIntegralClosure K L)) d := by
    apply e.injective
    rw [e.apply_symm_apply, e.commutes]
  rw [finiteExtensionFinitePrincipalDivisor_apply, hrepr,
    finitePlaceOrder_algebraMap_eq_multiplicity q d hd]

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
private theorem finiteExtensionFinitePrincipalDivisor_algebraMap_eq_mapRange
    (d : RatFuncFiniteIntegralClosure K L) (hd : d ≠ 0) :
    finiteExtensionFinitePrincipalDivisor K L
        (algebraMap (RatFuncFiniteIntegralClosure K L) L d) =
      (idealMultiplicityDivisor (Ideal.span {d})
          (by simpa [Ideal.span_singleton_eq_bot] using hd)).mapRange
        (fun n : ℕ => (n : ℤ)) (by simp) := by
  ext q
  rw [finiteExtensionFinitePrincipalDivisor_algebraMap_apply K L d hd,
    Finsupp.mapRange_apply, idealMultiplicityDivisor_apply]

/-- The weighted degree of the principal ideal of an integral element is the
finite-place degree sum of that element in the exhaustive `K(X)` model. -/
theorem idealMultiplicityWeightedDegree_eq_finiteExtensionFiniteDirectDegreeSum
    (d : RatFuncFiniteIntegralClosure K L) (hd : d ≠ 0) :
    ((idealMultiplicityDivisor (Ideal.span {d})
          (by simpa [Ideal.span_singleton_eq_bot] using hd)).sum
        (fun q e => e * q.asIdeal.inertiaDeg K[X] *
          ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q)) : ℤ) =
      finiteExtensionFiniteDirectDegreeSum K L
        (algebraMap (RatFuncFiniteIntegralClosure K L) L d) := by
  rw [finiteExtensionFiniteDirectDegreeSum,
    finiteExtensionFinitePrincipalDivisor_algebraMap_eq_mapRange K L d hd,
    Finsupp.sum_mapRange_index (fun q => by simp)]

omit [DecidableEq (RatFunc K)] in
/-- The finite different degree is bounded by the finite degree of the
minimal-polynomial derivative of an integral primitive element. -/
theorem finiteDifferentDegree_le_minpolyDerivativeDegree
    (x : RatFuncFiniteIntegralClosure K L)
    (hx : Algebra.adjoin (RatFunc K)
      {algebraMap (RatFuncFiniteIntegralClosure K L) L x} = ⊤) :
    ((differentMultiplicityDivisor K[X] (RatFuncFiniteIntegralClosure K L)
          (differentIdeal_ne_bot_of_primitiveElement
            (A := K[X]) (K := RatFunc K) (L := L)
            (B := RatFuncFiniteIntegralClosure K L) x hx)).sum
        (fun q e => e * q.asIdeal.inertiaDeg K[X] *
          ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q)) : ℤ) ≤
      finiteExtensionFiniteDirectDegreeSum K L
        (algebraMap (RatFuncFiniteIntegralClosure K L) L
          (Polynomial.aeval x (Polynomial.derivative (minpoly K[X] x)))) := by
  classical
  let d : RatFuncFiniteIntegralClosure K L :=
    Polynomial.aeval x (Polynomial.derivative (minpoly K[X] x))
  have hd : d ≠ 0 := by
    simpa [d] using minpolyDerivative_ne_zero
      (A := K[X]) (K := RatFunc K) (L := L) x
  have hbound := differentMultiplicityWeightedSum_le_minpolyDerivative
    (A := K[X]) (K := RatFunc K) (L := L)
    (B := RatFuncFiniteIntegralClosure K L) x hx
    (fun q => q.asIdeal.inertiaDeg K[X] *
      ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q))
  have hcast :
      (((differentMultiplicityDivisor K[X]
            (RatFuncFiniteIntegralClosure K L)
            (differentIdeal_ne_bot_of_primitiveElement
              (A := K[X]) (K := RatFunc K) (L := L)
              (B := RatFuncFiniteIntegralClosure K L) x hx)).sum
          (fun q e => e * q.asIdeal.inertiaDeg K[X] *
            ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q)) : ℕ) : ℤ) ≤
        (((idealMultiplicityDivisor (Ideal.span {d})
            (by
              simpa [d] using minpolyDerivative_span_ne_bot
                (A := K[X]) (K := RatFunc K) (L := L)
                (B := RatFuncFiniteIntegralClosure K L) x)).sum
          (fun q e => e * q.asIdeal.inertiaDeg K[X] *
            ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q)) : ℕ) : ℤ) := by
    exact_mod_cast (show
      (differentMultiplicityDivisor K[X]
            (RatFuncFiniteIntegralClosure K L)
            (differentIdeal_ne_bot_of_primitiveElement
              (A := K[X]) (K := RatFunc K) (L := L)
              (B := RatFuncFiniteIntegralClosure K L) x hx)).sum
          (fun q e => e * q.asIdeal.inertiaDeg K[X] *
            ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q)) ≤
        (idealMultiplicityDivisor (Ideal.span {d})
            (by
              simpa [d] using minpolyDerivative_span_ne_bot
                (A := K[X]) (K := RatFunc K) (L := L)
                (B := RatFuncFiniteIntegralClosure K L) x)).sum
          (fun q e => e * q.asIdeal.inertiaDeg K[X] *
            ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q)) by
      simpa only [d, Nat.mul_assoc] using hbound)
  have hcast' :
      (differentMultiplicityDivisor K[X]
            (RatFuncFiniteIntegralClosure K L)
            (differentIdeal_ne_bot_of_primitiveElement
              (A := K[X]) (K := RatFunc K) (L := L)
              (B := RatFuncFiniteIntegralClosure K L) x hx)).sum
          (fun q e => (e : ℤ) * q.asIdeal.inertiaDeg K[X] *
            ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q)) ≤
        (idealMultiplicityDivisor (Ideal.span {d})
            (by
              simpa [d] using minpolyDerivative_span_ne_bot
                (A := K[X]) (K := RatFunc K) (L := L)
                (B := RatFuncFiniteIntegralClosure K L) x)).sum
          (fun q e => (e : ℤ) * q.asIdeal.inertiaDeg K[X] *
            ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q)) := by
    simpa only [Nat.cast_finsupp_sum, Nat.cast_mul] using hcast
  rw [idealMultiplicityWeightedDegree_eq_finiteExtensionFiniteDirectDegreeSum
    K L d hd] at hcast'
  simpa only [d] using hcast'

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
private theorem ratFunc_intDegree_neg_one_pow (m : ℕ) :
    ((-1 : RatFunc K) ^ m).intDegree = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero m (by simp)) (by simp), ih]
      simp

omit [DecidableEq (RatFunc K)] in
/-- The finite degree of the integral minimal-polynomial derivative is exactly
the rational-function degree of the associated power-basis discriminant. -/
theorem finiteExtensionMinpolyDerivativeDegree_eq_powerBasisDiscriminantDegree
    (x : RatFuncFiniteIntegralClosure K L)
    (hx : Algebra.adjoin (RatFunc K)
      {algebraMap (RatFuncFiniteIntegralClosure K L) L x} = ⊤) :
    finiteExtensionFiniteDirectDegreeSum K L
        (algebraMap (RatFuncFiniteIntegralClosure K L) L
          (Polynomial.aeval x (Polynomial.derivative (minpoly K[X] x)))) =
      (Algebra.discr (RatFunc K)
        (PowerBasis.ofAdjoinEqTop'
          (Algebra.IsIntegral.isIntegral
            (algebraMap (RatFuncFiniteIntegralClosure K L) L x)) hx).basis).intDegree := by
  classical
  let d : RatFuncFiniteIntegralClosure K L :=
    Polynomial.aeval x (Polynomial.derivative (minpoly K[X] x))
  let y : L := algebraMap (RatFuncFiniteIntegralClosure K L) L d
  have hd : d ≠ 0 := by
    simpa [d] using minpolyDerivative_ne_zero
      (A := K[X]) (K := RatFunc K) (L := L) x
  have hy : y ≠ 0 :=
    (IsFractionRing.injective (RatFuncFiniteIntegralClosure K L) L).ne hd
  have hnorm : Algebra.norm (RatFunc K) y ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hy
  rw [show algebraMap (RatFuncFiniteIntegralClosure K L) L
      (Polynomial.aeval x (Polynomial.derivative (minpoly K[X] x))) = y by rfl,
    finiteExtensionFiniteDirectDegreeSum_eq_grouped K L y hy,
    finiteExtensionFinitePlaceDegreeSum_eq_normFinitePlaceDegreeSum K L y hy,
    ratFuncExhaustiveFinitePlaceDegreeSum_eq_intDegree _ hnorm]
  have hdisc := discr_powerBasisOfPrimitiveElement_eq_norm_minpolyDerivative
    (A := K[X]) (K := RatFunc K) (L := L)
    (B := RatFuncFiniteIntegralClosure K L) x hx
  change Algebra.discr (RatFunc K)
      (PowerBasis.ofAdjoinEqTop'
        (Algebra.IsIntegral.isIntegral
          (algebraMap (RatFuncFiniteIntegralClosure K L) L x)) hx).basis =
    (-1) ^ (Module.finrank (RatFunc K) L *
        (Module.finrank (RatFunc K) L - 1) / 2) * Algebra.norm (RatFunc K) y at hdisc
  have hdegree := congrArg RatFunc.intDegree hdisc
  rw [RatFunc.intDegree_mul (pow_ne_zero _ (by simp)) hnorm,
    ratFunc_intDegree_neg_one_pow K] at hdegree
  omega

omit [DecidableEq (RatFunc K)] in
/-- The finite different degree is bounded by the power-basis discriminant
degree of any integral primitive element. -/
theorem finiteDifferentDegree_le_powerBasisDiscriminantDegree
    (x : RatFuncFiniteIntegralClosure K L)
    (hx : Algebra.adjoin (RatFunc K)
      {algebraMap (RatFuncFiniteIntegralClosure K L) L x} = ⊤) :
    (differentMultiplicityDivisor K[X] (RatFuncFiniteIntegralClosure K L)
          (differentIdeal_ne_bot_of_primitiveElement
            (A := K[X]) (K := RatFunc K) (L := L)
            (B := RatFuncFiniteIntegralClosure K L) x hx)).sum
        (fun q e => (e : ℤ) * q.asIdeal.inertiaDeg K[X] *
          ratFuncFinitePlaceDegree (HeightOneSpectrum.under K[X] q)) ≤
      (Algebra.discr (RatFunc K)
        (PowerBasis.ofAdjoinEqTop'
          (Algebra.IsIntegral.isIntegral
            (algebraMap (RatFuncFiniteIntegralClosure K L) L x)) hx).basis).intDegree := by
  classical
  calc
    _ ≤ finiteExtensionFiniteDirectDegreeSum K L
        (algebraMap (RatFuncFiniteIntegralClosure K L) L
          (Polynomial.aeval x (Polynomial.derivative (minpoly K[X] x)))) :=
      finiteDifferentDegree_le_minpolyDerivativeDegree K L x hx
    _ = _ :=
      finiteExtensionMinpolyDerivativeDegree_eq_powerBasisDiscriminantDegree K L x hx

/-! ## The local-parameter Wronskian divisor -/

section WronskianDivisor

variable {C : Type*} [Field C] [Algebra C L]

/-- The global ordinary Wronskian attached to one derivation. -/
def finiteExtensionGlobalWronskian {n : ℕ}
    (D : Derivation C L L) (g : Fin n → L) : L :=
  (BGS.Algebra.derivationWronskian D g).det

section LocalChangeParameter

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  [Algebra R L] [IsFractionRing R L]

private theorem finitePlaceOrder_mul_of_ne_zero
    (v : HeightOneSpectrum R) (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    finitePlaceOrder v (x * y) = finitePlaceOrder v x + finitePlaceOrder v y := by
  have h := finitePlaceOrderTop_mul v x y
  rw [finitePlaceOrderTop_eq_coe v (x * y) (mul_ne_zero hx hy),
    finitePlaceOrderTop_eq_coe v x hx,
    finitePlaceOrderTop_eq_coe v y hy] at h
  exact_mod_cast h

private theorem finitePlaceOrder_pow_of_ne_zero
    (v : HeightOneSpectrum R) (x : L) (hx : x ≠ 0) (m : ℕ) :
    finitePlaceOrder v (x ^ m) = m • finitePlaceOrder v x := by
  have h := finitePlaceOrderTop_pow v x m
  rw [finitePlaceOrderTop_eq_coe v (x ^ m) (pow_ne_zero m hx),
    finitePlaceOrderTop_eq_coe v x hx] at h
  exact_mod_cast h

/-- Exact order change from a global derivation to a local-parameter
derivation.  If `D = a E`, then the local `E`-Wronskian has the global
`D`-Wronskian order minus `choose(n,2)` times the order of `a`. -/
theorem finitePlaceOrder_globalWronskian_changeParameter
    (v : HeightOneSpectrum R) {n : ℕ}
    (D E : Derivation C L L) (a : L) (hD : D = a • E)
    (g : Fin n → L) (ha : a ≠ 0)
    (hE : finiteExtensionGlobalWronskian L E g ≠ 0) :
    finitePlaceOrder v (finiteExtensionGlobalWronskian L E g) =
      finitePlaceOrder v (finiteExtensionGlobalWronskian L D g) -
        (n.choose 2 : ℤ) * finitePlaceOrder v a := by
  have hchange := derivationWronskian_det_changeParameter D E a hD g
  change finiteExtensionGlobalWronskian L D g =
    a ^ n.choose 2 * finiteExtensionGlobalWronskian L E g at hchange
  have hpow : a ^ n.choose 2 ≠ 0 := pow_ne_zero _ ha
  have hord := finitePlaceOrder_mul_of_ne_zero L v
    (a ^ n.choose 2) (finiteExtensionGlobalWronskian L E g) hpow hE
  rw [← hchange, finitePlaceOrder_pow_of_ne_zero L v a ha] at hord
  simp only [nsmul_eq_mul] at hord
  omega

end LocalChangeParameter

/-- Degree of a finitely supported divisor on the exhaustive places of the
finite extension. -/
def finiteExtensionDivisorDegree
    (D : FiniteExtensionPlace K L →₀ ℤ) : ℤ :=
  D.sum (fun v e => e * (finiteExtensionPlaceDegree K L v : ℤ))

/-- The divisor represented by local-parameter Wronskians: the principal
divisor of the global Wronskian plus the triangular multiple of a supplied
canonical correction divisor. -/
def finiteExtensionLocalWronskianDivisor {n : ℕ}
    (D : Derivation C L L) (g : Fin n → L)
    (canonicalDivisor : FiniteExtensionPlace K L →₀ ℤ) :
    FiniteExtensionPlace K L →₀ ℤ :=
  (n.choose 2 : ℤ) • canonicalDivisor +
    finiteExtensionPrincipalDivisor K L
      (finiteExtensionGlobalWronskian L D g)

omit [DecidableEq K] in
@[simp] theorem finiteExtensionLocalWronskianDivisor_apply {n : ℕ}
    (D : Derivation C L L) (g : Fin n → L)
    (canonicalDivisor : FiniteExtensionPlace K L →₀ ℤ)
    (v : FiniteExtensionPlace K L) :
    finiteExtensionLocalWronskianDivisor K L D g canonicalDivisor v =
      (n.choose 2 : ℤ) * canonicalDivisor v +
        finiteExtensionPrincipalDivisor K L
          (finiteExtensionGlobalWronskian L D g) v := by
  simp [finiteExtensionLocalWronskianDivisor]

/-- The product formula kills the principal global Wronskian contribution.
Thus the local Wronskian divisor has exactly the triangular multiple of the
canonical degree. -/
theorem finiteExtensionLocalWronskianDivisor_degree
    {n : ℕ} (D : Derivation C L L) (g : Fin n → L)
    (canonicalDivisor : FiniteExtensionPlace K L →₀ ℤ)
    (hW : finiteExtensionGlobalWronskian L D g ≠ 0) :
    finiteExtensionDivisorDegree K L
        (finiteExtensionLocalWronskianDivisor K L D g canonicalDivisor) =
      (n.choose 2 : ℤ) *
        finiteExtensionDivisorDegree K L canonicalDivisor := by
  classical
  rw [finiteExtensionDivisorDegree, finiteExtensionLocalWronskianDivisor,
    Finsupp.sum_add_index (by simp) (by intros; ring),
    Finsupp.sum_smul_index (by simp)]
  have hprincipal :
      (finiteExtensionPrincipalDivisor K L
          (finiteExtensionGlobalWronskian L D g)).sum
          (fun v e => e * (finiteExtensionPlaceDegree K L v : ℤ)) = 0 := by
    exact finiteExtensionPrincipalDivisorDegreeSum_eq_zero K L
      (finiteExtensionGlobalWronskian L D g) hW
  rw [hprincipal]
  simp only [finiteExtensionDivisorDegree]
  rw [add_zero]
  unfold Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

omit [DecidableEq K] in
/-- Over algebraically closed constants every place has degree one, so the
global canonical identity becomes the ordinary unweighted sum of local
Wronskian orders used by Corvaja--Zannier. -/
theorem finiteExtensionLocalWronskianDivisor_sum
    [IsAlgClosed K]
    {n : ℕ} (D : Derivation C L L) (g : Fin n → L)
    (canonicalDivisor : FiniteExtensionPlace K L →₀ ℤ)
    (hW : finiteExtensionGlobalWronskian L D g ≠ 0) :
    (finiteExtensionLocalWronskianDivisor K L D g canonicalDivisor).sum
        (fun _ e => e) =
      (n.choose 2 : ℤ) * canonicalDivisor.sum (fun _ e => e) := by
  classical
  have hdegree := finiteExtensionLocalWronskianDivisor_degree
    K L D g canonicalDivisor hW
  simpa only [finiteExtensionDivisorDegree,
    finiteExtensionPlaceDegree_eq_one K L,
    Int.ofNat_eq_natCast, Nat.cast_one, mul_one] using hdegree

end WronskianDivisor

/-! ## Final log-canonical arithmetic -/

/-- Once geometry bounds the canonical degree with the coarse boundary
allowance `2(a+b)`, and the actual exceptional set has at most that many
points, the exact Corvaja--Zannier choice `chi = 2ab` follows. -/
theorem canonicalDegree_add_boundaryCard_le_twice_bidegree
    {I : Type*} (S : Finset I) (canonicalDegree : ℤ)
    (firstDegree secondDegree : ℕ)
    (hCanonical :
      canonicalDegree + (2 * (firstDegree + secondDegree) : ℕ) ≤
        (2 * firstDegree * secondDegree : ℕ))
    (hBoundary : S.card ≤ 2 * (firstDegree + secondDegree)) :
    canonicalDegree + S.card ≤
      (2 * firstDegree * secondDegree : ℕ) := by
  have hBoundaryInt : (S.card : ℤ) ≤
      (2 * (firstDegree + secondDegree) : ℕ) := by
    exact_mod_cast hBoundary
  omega

/-- The usual genus and toric-boundary estimates imply the exact
log-canonical allowance used by Corvaja--Zannier.  This theorem is purely the
numerical assembly: constructing a normalization and proving the two supplied
geometric estimates remain separate obligations. -/
theorem canonicalDegree_add_boundaryCard_le_twice_bidegree_of_genus_bound
    {I : Type*} (S : Finset I) (canonicalDegree : ℤ)
    (genus firstDegree secondDegree : ℕ)
    (hFirst : 0 < firstDegree) (hSecond : 0 < secondDegree)
    (hCanonical : canonicalDegree ≤ 2 * (genus : ℤ) - 2)
    (hGenus : genus ≤ (firstDegree - 1) * (secondDegree - 1))
    (hBoundary : S.card ≤ 2 * (firstDegree + secondDegree)) :
    canonicalDegree + S.card ≤
      (2 * firstDegree * secondDegree : ℕ) := by
  have hGenusInt : (genus : ℤ) ≤
      ((firstDegree - 1 : ℕ) : ℤ) * ((secondDegree - 1 : ℕ) : ℤ) := by
    exact_mod_cast hGenus
  have hFirstOne : 1 ≤ firstDegree := hFirst
  have hSecondOne : 1 ≤ secondDegree := hSecond
  rw [Nat.cast_sub hFirstOne, Nat.cast_sub hSecondOne] at hGenusInt
  have hBoundaryInt : (S.card : ℤ) ≤
      2 * ((firstDegree : ℤ) + secondDegree) := by
    exact_mod_cast hBoundary
  norm_num at hGenusInt hBoundaryInt ⊢
  nlinarith

/-- The divisor-theoretic replacement for the genus-bound assembly.  If the
canonical correction is bounded by the total different minus twice the
projection degree, the sharp bivariate discriminant budget and the toric
boundary budget give the same log-canonical bound `2 * a * b` directly. -/
theorem canonicalDegree_add_boundaryCard_le_twice_bidegree_of_different_bound
    {I : Type*} (S : Finset I) (canonicalDegree : ℤ)
    (totalDifferent firstDegree secondDegree : ℕ)
    (hSecond : 0 < secondDegree)
    (hCanonical :
      canonicalDegree ≤ (totalDifferent : ℤ) - 2 * (secondDegree : ℤ))
    (hDifferent :
      totalDifferent ≤ (2 * secondDegree - 2) * firstDegree)
    (hBoundary : S.card ≤ 2 * (firstDegree + secondDegree)) :
    canonicalDegree + S.card ≤
      (2 * firstDegree * secondDegree : ℕ) := by
  have hDifferentInt : (totalDifferent : ℤ) ≤
      ((2 * secondDegree - 2) * firstDegree : ℕ) := by
    exact_mod_cast hDifferent
  have hBoundaryInt : (S.card : ℤ) ≤
      (2 * (firstDegree + secondDegree) : ℕ) := by
    exact_mod_cast hBoundary
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ 2 * secondDegree),
    Nat.cast_mul, Nat.cast_ofNat] at hDifferentInt
  norm_num at hDifferentInt hBoundaryInt ⊢
  nlinarith

end

end BGS.CorvajaZannier
