/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.FiniteProjection.PreparedQuotient
import LeanPool.LocalComplexGeometry.Germs.Ring
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The generic fibre of a prepared prime quotient

This file isolates the commutative-algebra layer used in the prime case of
the local analytic Nullstellensatz.  A prime ideal of the ambient germ ring
which contains a prepared monic equation gives a finite integral extension
of its contracted quotient.  Passing to fraction fields therefore gives a
finite extension, in which the last-coordinate class has a nonzero separable
minimal polynomial.  The last section clears all coefficients of that
minimal polynomial back to the contracted quotient.
-/


namespace LocalComplexGeometry

open scoped nonZeroDivisors

noncomputable section

/-! ## Contraction and quotient rings -/

/-- Contraction of an ambient ideal along the lower-dimensional germ inclusion. -/
abbrev lowerDimensionalContraction {n : ℕ}
    (P : Ideal (HolomorphicGerm (n + 1))) : Ideal (HolomorphicGerm n) :=
  P.under (HolomorphicGerm n)

/-- The quotient of the lower-dimensional germ ring by the contraction of `P`. -/
abbrev ContractedGermQuotient {n : ℕ}
    (P : Ideal (HolomorphicGerm (n + 1))) :=
  HolomorphicGerm n ⧸ lowerDimensionalContraction P

/-- The ambient germ quotient by `P`. -/
abbrev AmbientGermQuotient {n : ℕ}
    (P : Ideal (HolomorphicGerm (n + 1))) :=
  HolomorphicGerm (n + 1) ⧸ P

/-- The canonical quotient-base map induced by `lowerDimensionalInclusion`. -/
def contractedQuotientMap {n : ℕ}
    (P : Ideal (HolomorphicGerm (n + 1))) :
    ContractedGermQuotient P →+* AmbientGermQuotient P :=
  algebraMap _ _

@[simp]
theorem contractedQuotientMap_mk {n : ℕ}
    (P : Ideal (HolomorphicGerm (n + 1))) (f : HolomorphicGerm n) :
    contractedQuotientMap P
        (Ideal.Quotient.mk (lowerDimensionalContraction P) f) =
      Ideal.Quotient.mk P (lowerDimensionalInclusion n f) :=
  rfl

/-- Contraction of a prime ideal is prime. -/
theorem lowerDimensionalContraction_isPrime {n : ℕ}
    {P : Ideal (HolomorphicGerm (n + 1))} (hP : P.IsPrime) :
    (lowerDimensionalContraction P).IsPrime := by
  let : P.IsPrime := hP
  infer_instance

/-- The canonical map from the contracted quotient is injective. -/
theorem contractedQuotientMap_injective {n : ℕ}
    (P : Ideal (HolomorphicGerm (n + 1))) :
    Function.Injective (contractedQuotientMap P) :=
  FaithfulSMul.algebraMap_injective _ _

/-! ## Finiteness from a prepared monic equation -/

/-- Membership of the prepared polynomial in `P` puts its principal ideal below `P`. -/
theorem preparedPolynomialIdeal_le_of_mem {n d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    {P : Ideal (HolomorphicGerm (n + 1))}
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    WPTBridge.preparedPolynomialIdeal a ha ≤ P := by
  rw [WPTBridge.preparedPolynomialIdeal, Ideal.span_le]
  simpa using hmem

/-- Before quotienting the base by the contraction, the ambient prime quotient
is already a finite module over the lower-dimensional germ ring. -/
theorem ambientQuotient_moduleFinite_over_germs {n d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (P : Ideal (HolomorphicGerm (n + 1)))
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    Module.Finite (HolomorphicGerm n) (AmbientGermQuotient P) := by
  let I := WPTBridge.preparedPolynomialIdeal a ha
  have hIP : I ≤ P := preparedPolynomialIdeal_le_of_mem a ha hmem
  let q : (HolomorphicGerm (n + 1) ⧸ I) →ₐ[HolomorphicGerm n]
      AmbientGermQuotient P :=
    Ideal.Quotient.factorₐ (HolomorphicGerm n) hIP
  let : Module.Finite (HolomorphicGerm n)
      (HolomorphicGerm (n + 1) ⧸ I) :=
    WPTBridge.preparedQuotient_moduleFinite a ha ha0
  exact Module.Finite.of_surjective q.toLinearMap
    (Ideal.Quotient.factor_surjective hIP)

/-- The ambient prime quotient is finite over the quotient by the contracted
prime.  This is the module-finite generic-projection statement over the local
base, before passing to fraction fields. -/
theorem ambientQuotient_moduleFinite {n d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (P : Ideal (HolomorphicGerm (n + 1)))
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    Module.Finite (ContractedGermQuotient P) (AmbientGermQuotient P) := by
  let : Module.Finite (HolomorphicGerm n) (AmbientGermQuotient P) :=
    ambientQuotient_moduleFinite_over_germs a ha ha0 P hmem
  exact Module.Finite.of_restrictScalars_finite
    (HolomorphicGerm n) (ContractedGermQuotient P) (AmbientGermQuotient P)

/-- Module-finiteness makes every class in the ambient quotient integral over
the contracted quotient. -/
theorem ambientQuotient_isIntegral {n d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (P : Ideal (HolomorphicGerm (n + 1)))
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    Algebra.IsIntegral (ContractedGermQuotient P) (AmbientGermQuotient P) := by
  let : Module.Finite (ContractedGermQuotient P) (AmbientGermQuotient P) :=
    ambientQuotient_moduleFinite a ha ha0 P hmem
  exact Algebra.IsIntegral.of_finite
    (ContractedGermQuotient P) (AmbientGermQuotient P)

/-! ## Clearing coefficients in a fraction field -/

/-- A nonzero polynomial over a fraction field has a nonzero common
denominator and a nonzero polynomial lift after multiplication by it. -/
theorem clearFractionPolynomialDenominators
    {A : Type*} [CommRing A] [IsDomain A]
    (p : Polynomial (FractionRing A)) (hp : p ≠ 0) :
    ∃ d : A, d ≠ 0 ∧ ∃ q : Polynomial A, q ≠ 0 ∧
      q.map (algebraMap A (FractionRing A)) =
        Polynomial.C (algebraMap A (FractionRing A) d) * p := by
  classical
  let M := nonZeroDivisors A
  let den : M := IsLocalization.commonDenom M p.support p.coeff
  have hlift :
      Polynomial.C (algebraMap A (FractionRing A) (den : A)) * p ∈
        Polynomial.lifts (algebraMap A (FractionRing A)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [Polynomial.coeff_C_mul]
    by_cases hk : k ∈ p.support
    · refine ⟨IsLocalization.integerMultiple M p.support p.coeff ⟨k, hk⟩, ?_⟩
      rw [IsLocalization.map_integerMultiple]
      simp only [Submonoid.smul_def, Algebra.smul_def, den]
    · have hpzero : p.coeff k = 0 := by simpa using hk
      simp [hpzero]
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).mp hlift
  have hden : (den : A) ≠ 0 := nonZeroDivisors.ne_zero den.property
  have hdenK : algebraMap A (FractionRing A) (den : A) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hden
  have hq0 : q ≠ 0 := by
    intro hzero
    have hz : Polynomial.C (algebraMap A (FractionRing A) (den : A)) * p = 0 := by
      rw [← hq, hzero, Polynomial.map_zero]
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hdenK) hp) hz
  exact ⟨den, hden, q, hq0, hq⟩

/-- Common-denominator clearance without a nonzero hypothesis.  This version
also covers the zero quotient polynomial arising from a generator whose WPT
remainder vanishes identically on the generic fibre. -/
theorem clearFractionPolynomialDenominators_allowZero
    {A : Type*} [CommRing A] [IsDomain A]
    (p : Polynomial (FractionRing A)) :
    ∃ d : A, d ≠ 0 ∧ ∃ q : Polynomial A,
      q.map (algebraMap A (FractionRing A)) =
        Polynomial.C (algebraMap A (FractionRing A) d) * p := by
  by_cases hp : p = 0
  · exact ⟨1, one_ne_zero, 0, by simp [hp]⟩
  · obtain ⟨d, hd, q, _, hq⟩ := clearFractionPolynomialDenominators p hp
    exact ⟨d, hd, q, hq⟩

/-! ## The fraction-field generic fibre -/

/-- Fraction field of the contracted prime quotient. -/
abbrev ContractedFractionField {n : ℕ}
    (P : Ideal (HolomorphicGerm (n + 1))) :=
  FractionRing (ContractedGermQuotient P)

/-- Fraction field of the ambient prime quotient. -/
abbrev AmbientFractionField {n : ℕ}
    (P : Ideal (HolomorphicGerm (n + 1))) :=
  FractionRing (AmbientGermQuotient P)

/-- The last-coordinate germ viewed in the ambient prime quotient. -/
def lastCoordinateQuotientClass {n : ℕ}
    (P : Ideal (HolomorphicGerm (n + 1))) : AmbientGermQuotient P :=
  Ideal.Quotient.mk P (lastCoordinateGerm n)

/-! The explicit polynomials represented by prepared and remainder germs. -/

/-- The analytic coefficient `a i`, regarded as a lower-dimensional germ. -/
def preparedCoefficientGerm {n d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) (i : Fin d) : HolomorphicGerm n :=
  HolomorphicGerm.ofFunction (a i) (ha i)

/-- The prepared monic polynomial with coefficients in the base germ ring. -/
def preparedGermPolynomial {n d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) : Polynomial (HolomorphicGerm n) :=
  Polynomial.X ^ d + ∑ i : Fin d,
    Polynomial.C (preparedCoefficientGerm a ha i) * Polynomial.X ^ (i : ℕ)

/-- A WPT coefficient vector, assembled as a polynomial over the base germ ring. -/
def remainderGermPolynomial {n d : ℕ}
    (r : Fin d → HolomorphicGerm n) : Polynomial (HolomorphicGerm n) :=
  ∑ i : Fin d, Polynomial.C (r i) * Polynomial.X ^ (i : ℕ)

@[simp]
theorem aeval_remainderGermPolynomial {n d : ℕ}
    (r : Fin d → HolomorphicGerm n) :
    Polynomial.aeval (lastCoordinateGerm n) (remainderGermPolynomial r) =
      WPTBridge.remainderPolynomialGerm r := by
  simp [remainderGermPolynomial, WPTBridge.remainderPolynomialGerm]

@[simp]
theorem aeval_preparedGermPolynomial {n d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    Polynomial.aeval (lastCoordinateGerm n) (preparedGermPolynomial a ha) =
      WPTBridge.preparedPolynomialGerm a ha := by
  rw [preparedGermPolynomial]
  simp only [map_add, map_pow, Polynomial.aeval_X, map_sum,
    Polynomial.aeval_mul, Polynomial.aeval_C]
  change lastCoordinateGerm n ^ d +
      WPTBridge.remainderPolynomialGerm
        (fun i ↦ preparedCoefficientGerm a ha i) =
    WPTBridge.preparedPolynomialGerm a ha
  apply Subtype.ext
  simp only [Subring.coe_add, Subring.coe_pow]
  simp only [preparedCoefficientGerm]
  rw [WPTBridge.coe_remainderPolynomialGerm_ofFunction a ha]
  rw [show (lastCoordinateGerm n : FunctionGerm (n + 1)) =
    lastCoordinateCLM n from rfl]
  rw [show (WPTBridge.preparedPolynomialGerm a ha : FunctionGerm (n + 1)) =
    WPTBridge.preparedPolynomialFunction a from rfl]
  rw [← Filter.Germ.coe_pow, ← Filter.Germ.coe_add]
  apply congrArg Filter.Germ.ofFun
  rfl

section Prime

variable {n : ℕ} (P : Ideal (HolomorphicGerm (n + 1))) [P.IsPrime]

/-- The injective map from the complex constants into the contracted quotient. -/
def complexToContractedQuotient : ℂ →+* ContractedGermQuotient P :=
  (Ideal.Quotient.mk (lowerDimensionalContraction P)).comp (constantGermHom n)

theorem complexToContractedQuotient_injective :
    Function.Injective (complexToContractedQuotient P) :=
  (complexToContractedQuotient P).injective

/-- Contracted prime quotients of complex germ rings have characteristic zero. -/
instance contractedGermQuotient_charZero : CharZero (ContractedGermQuotient P) :=
  charZero_of_injective_ringHom (complexToContractedQuotient_injective P)

/-- The ambient fraction field is canonically an algebra over the contracted
fraction field, extending the contracted quotient map. -/
noncomputable instance contractedFractionFieldAlgebra :
    Algebra (ContractedFractionField P) (AmbientFractionField P) :=
  FractionRing.liftAlgebra (ContractedGermQuotient P) (AmbientFractionField P)

/-- The fraction field of the contracted quotient also has characteristic zero. -/
instance contractedFractionField_charZero : CharZero (ContractedFractionField P) :=
  charZero_of_injective_algebraMap
    (IsFractionRing.injective (ContractedGermQuotient P) (ContractedFractionField P))

/-- The last-coordinate class in the fraction-field generic fibre. -/
def genericLastCoordinate : AmbientFractionField P :=
  algebraMap (AmbientGermQuotient P) (AmbientFractionField P)
    (lastCoordinateQuotientClass P)

/-- The minimal polynomial of the generic last-coordinate class over the
contracted fraction field. -/
def genericLastCoordinateMinpoly : Polynomial (ContractedFractionField P) :=
  minpoly (ContractedFractionField P) (genericLastCoordinate P)

/-- The prepared polynomial after reducing its coefficients modulo the
contracted prime. -/
def contractedPreparedPolynomial {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    Polynomial (ContractedGermQuotient P) :=
  (preparedGermPolynomial a ha).map
    (Ideal.Quotient.mk (lowerDimensionalContraction P))

/-- The prepared polynomial over the contracted fraction field. -/
def genericPreparedPolynomial {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    Polynomial (ContractedFractionField P) :=
  (contractedPreparedPolynomial P a ha).map
    (algebraMap (ContractedGermQuotient P) (ContractedFractionField P))

/-- A WPT remainder polynomial after reducing its coefficients modulo the
contracted prime. -/
def contractedRemainderPolynomial {d : ℕ}
    (r : Fin d → HolomorphicGerm n) :
    Polynomial (ContractedGermQuotient P) :=
  (remainderGermPolynomial r).map
    (Ideal.Quotient.mk (lowerDimensionalContraction P))

/-- A WPT remainder polynomial over the contracted fraction field. -/
def genericRemainderPolynomial {d : ℕ}
    (r : Fin d → HolomorphicGerm n) :
    Polynomial (ContractedFractionField P) :=
  (contractedRemainderPolynomial P r).map
    (algebraMap (ContractedGermQuotient P) (ContractedFractionField P))

omit [P.IsPrime] in
@[simp]
theorem aeval_contractedRemainderPolynomial {d : ℕ}
    (r : Fin d → HolomorphicGerm n) :
    Polynomial.aeval (lastCoordinateQuotientClass P)
        (contractedRemainderPolynomial P r) =
      Ideal.Quotient.mk P (WPTBridge.remainderPolynomialGerm r) := by
  change Polynomial.aeval (lastCoordinateQuotientClass P)
      ((remainderGermPolynomial r).map
        (algebraMap (HolomorphicGerm n) (ContractedGermQuotient P))) = _
  rw [Polynomial.aeval_map_algebraMap]
  change Polynomial.aeval
      ((Ideal.Quotient.mkₐ (HolomorphicGerm n) P) (lastCoordinateGerm n))
        (remainderGermPolynomial r) = _
  rw [Polynomial.aeval_algHom_apply,
    aeval_remainderGermPolynomial]
  simp only [Ideal.Quotient.mkₐ_eq_mk]

omit [P.IsPrime] in
@[simp]
theorem aeval_contractedPreparedPolynomial {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    Polynomial.aeval (lastCoordinateQuotientClass P)
        (contractedPreparedPolynomial P a ha) =
      Ideal.Quotient.mk P (WPTBridge.preparedPolynomialGerm a ha) := by
  change Polynomial.aeval (lastCoordinateQuotientClass P)
      ((preparedGermPolynomial a ha).map
        (algebraMap (HolomorphicGerm n) (ContractedGermQuotient P))) = _
  rw [Polynomial.aeval_map_algebraMap]
  change Polynomial.aeval
      ((Ideal.Quotient.mkₐ (HolomorphicGerm n) P) (lastCoordinateGerm n))
        (preparedGermPolynomial a ha) = _
  rw [Polynomial.aeval_algHom_apply,
    aeval_preparedGermPolynomial]
  simp only [Ideal.Quotient.mkₐ_eq_mk]

@[simp]
theorem aeval_genericRemainderPolynomial {d : ℕ}
    (r : Fin d → HolomorphicGerm n) :
    Polynomial.aeval (genericLastCoordinate P)
        (genericRemainderPolynomial P r) =
      algebraMap (AmbientGermQuotient P) (AmbientFractionField P)
        (Ideal.Quotient.mk P (WPTBridge.remainderPolynomialGerm r)) := by
  rw [genericRemainderPolynomial, Polynomial.aeval_map_algebraMap]
  change Polynomial.aeval
      (algebraMap (AmbientGermQuotient P) (AmbientFractionField P)
        (lastCoordinateQuotientClass P))
      (contractedRemainderPolynomial P r) = _
  rw [Polynomial.aeval_algebraMap_apply,
    aeval_contractedRemainderPolynomial]

@[simp]
theorem aeval_genericPreparedPolynomial {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    Polynomial.aeval (genericLastCoordinate P)
        (genericPreparedPolynomial P a ha) =
      algebraMap (AmbientGermQuotient P) (AmbientFractionField P)
        (Ideal.Quotient.mk P (WPTBridge.preparedPolynomialGerm a ha)) := by
  rw [genericPreparedPolynomial, Polynomial.aeval_map_algebraMap]
  change Polynomial.aeval
      (algebraMap (AmbientGermQuotient P) (AmbientFractionField P)
        (lastCoordinateQuotientClass P))
      (contractedPreparedPolynomial P a ha) = _
  rw [Polynomial.aeval_algebraMap_apply,
    aeval_contractedPreparedPolynomial]

/-- The prepared polynomial annihilates the generic last-coordinate class. -/
theorem genericPreparedPolynomial_aeval_eq_zero {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    Polynomial.aeval (genericLastCoordinate P)
      (genericPreparedPolynomial P a ha) = 0 := by
  rw [aeval_genericPreparedPolynomial]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]

/-- WPT division represents every ambient germ class by its degree-`< d`
remainder polynomial on the generic fibre. -/
theorem genericRemainderPolynomial_aeval_eq_ambientClass {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P)
    (h : HolomorphicGerm (n + 1)) :
    Polynomial.aeval (genericLastCoordinate P)
        (genericRemainderPolynomial P
          (WPTBridge.preparedGermDivisionRemainder a ha ha0 h)) =
      algebraMap (AmbientGermQuotient P) (AmbientFractionField P)
        (Ideal.Quotient.mk P h) := by
  rw [aeval_genericRemainderPolynomial]
  have hspec := WPTBridge.preparedGermDivision_spec a ha ha0 h
  unfold WPTBridge.IsPreparedGermDivision at hspec
  have hquot := congrArg (Ideal.Quotient.mk P) hspec
  simp only [map_add, map_mul] at hquot
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at hquot
  simp only [mul_zero, zero_add] at hquot
  exact congrArg
    (algebraMap (AmbientGermQuotient P) (AmbientFractionField P)) hquot.symm

/-- An ambient germ belongs to `P` exactly when the WPT remainder polynomial
vanishes at the generic last-coordinate class. -/
theorem mem_prime_iff_genericRemainder_aeval_eq_zero {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P)
    (h : HolomorphicGerm (n + 1)) :
    h ∈ P ↔
      Polynomial.aeval (genericLastCoordinate P)
        (genericRemainderPolynomial P
          (WPTBridge.preparedGermDivisionRemainder a ha ha0 h)) = 0 := by
  rw [genericRemainderPolynomial_aeval_eq_ambientClass P a ha ha0 hmem h]
  constructor
  · intro hh
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hh, map_zero]
  · intro hh
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (AmbientGermQuotient P)
      (AmbientFractionField P)
    simpa using hh

/-- The two fraction fields form a finite-dimensional extension whenever `P`
contains the prepared monic equation. -/
theorem genericFractionField_finiteDimensional {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    FiniteDimensional (ContractedFractionField P) (AmbientFractionField P) := by
  let : Module.Finite (ContractedGermQuotient P) (AmbientGermQuotient P) :=
    ambientQuotient_moduleFinite a ha ha0 P hmem
  infer_instance

/-- In particular, the generic last-coordinate class is algebraic (integral,
because the base is a field). -/
theorem genericLastCoordinate_isIntegral {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    IsIntegral (ContractedFractionField P) (genericLastCoordinate P) := by
  let : FiniteDimensional (ContractedFractionField P) (AmbientFractionField P) :=
    genericFractionField_finiteDimensional P a ha ha0 hmem
  exact IsIntegral.of_finite (ContractedFractionField P) (genericLastCoordinate P)

/-- The generic last-coordinate minimal polynomial divides the prepared monic
polynomial which produced the finite extension. -/
theorem genericLastCoordinateMinpoly_dvd_genericPreparedPolynomial {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    genericLastCoordinateMinpoly P ∣ genericPreparedPolynomial P a ha := by
  rw [genericLastCoordinateMinpoly, minpoly.dvd_iff]
  exact genericPreparedPolynomial_aeval_eq_zero P a ha hmem

/-- Prime membership is exactly divisibility of the generic WPT remainder by
the generic last-coordinate minimal polynomial. -/
theorem mem_prime_iff_minpoly_dvd_genericRemainderPolynomial {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P)
    (h : HolomorphicGerm (n + 1)) :
    h ∈ P ↔
      genericLastCoordinateMinpoly P ∣
        genericRemainderPolynomial P
          (WPTBridge.preparedGermDivisionRemainder a ha ha0 h) := by
  rw [genericLastCoordinateMinpoly, minpoly.dvd_iff]
  exact mem_prime_iff_genericRemainder_aeval_eq_zero P a ha ha0 hmem h

/-- The generic last-coordinate minimal polynomial is monic. -/
theorem genericLastCoordinateMinpoly_monic {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    (genericLastCoordinateMinpoly P).Monic :=
  minpoly.monic (genericLastCoordinate_isIntegral P a ha ha0 hmem)

/-- The generic last-coordinate minimal polynomial is nonzero. -/
theorem genericLastCoordinateMinpoly_ne_zero {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    genericLastCoordinateMinpoly P ≠ 0 :=
  minpoly.ne_zero (genericLastCoordinate_isIntegral P a ha ha0 hmem)

/-- Characteristic zero makes the generic last-coordinate minimal polynomial
separable. -/
theorem genericLastCoordinateMinpoly_separable {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    (genericLastCoordinateMinpoly P).Separable :=
  (minpoly.irreducible
    (genericLastCoordinate_isIntegral P a ha ha0 hmem)).separable

/-- A single base denominator and same-degree polynomial lift of the generic
last-coordinate minimal polynomial.  The denominator remains nonzero modulo
the contraction, and the displayed identity is an identity over the
contracted fraction field. -/
structure GenericMinpolyLiftCertificate where
  /-- The common denominator in the base germ ring. -/
  denominator : HolomorphicGerm n
  /-- A polynomial lift of the generic minimal polynomial. -/
  polynomial : Polynomial (HolomorphicGerm n)
  denominator_not_mem : denominator ∉ lowerDimensionalContraction P
  polynomial_mod_contraction_ne_zero :
    polynomial.map (Ideal.Quotient.mk (lowerDimensionalContraction P)) ≠ 0
  map_polynomial :
    (polynomial.map (Ideal.Quotient.mk (lowerDimensionalContraction P))).map
        (algebraMap (ContractedGermQuotient P) (ContractedFractionField P)) =
      Polynomial.C
          (algebraMap (ContractedGermQuotient P) (ContractedFractionField P)
            (Ideal.Quotient.mk (lowerDimensionalContraction P) denominator)) *
        genericLastCoordinateMinpoly P
  natDegree_eq : polynomial.natDegree = (genericLastCoordinateMinpoly P).natDegree
  natDegree_pos : 0 < polynomial.natDegree

/-- Canonical choice of the cleared, same-degree minimal-polynomial lift. -/
def genericMinpolyLiftCertificate {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    GenericMinpolyLiftCertificate P := by
  let π : HolomorphicGerm n →+* ContractedGermQuotient P :=
    Ideal.Quotient.mk (lowerDimensionalContraction P)
  let ι : ContractedGermQuotient P →+* ContractedFractionField P :=
    algebraMap (ContractedGermQuotient P) (ContractedFractionField P)
  let p := genericLastCoordinateMinpoly P
  have hp : p ≠ 0 := genericLastCoordinateMinpoly_ne_zero P a ha ha0 hmem
  have hclear := clearFractionPolynomialDenominators p hp
  let δ := Classical.choose hclear
  have hδspec := Classical.choose_spec hclear
  have hδ : δ ≠ 0 := hδspec.1
  let q := Classical.choose hδspec.2
  have hqspec := Classical.choose_spec hδspec.2
  have hq : q ≠ 0 := hqspec.1
  have hqmap : q.map ι = Polynomial.C (ι δ) * p := hqspec.2
  let D := Classical.choose (Ideal.Quotient.mk_surjective δ)
  have hD : π D = δ := Classical.choose_spec (Ideal.Quotient.mk_surjective δ)
  have hq_lifts : q ∈ Polynomial.lifts π :=
    Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective q
  have hQexists := Polynomial.exists_natDegree_eq_of_mem_lifts hq_lifts
  let Q := Classical.choose hQexists
  have hQspec := Classical.choose_spec hQexists
  have hQ : Q.map π = q := hQspec.1
  have hQdeg : Q.natDegree = q.natDegree := hQspec.2
  have hD_not : D ∉ lowerDimensionalContraction P := by
    intro hDin
    apply hδ
    rw [← hD]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hDin
  have hQ_ne : Q.map π ≠ 0 := by
    rw [hQ]
    exact hq
  have hι : Function.Injective ι :=
    IsFractionRing.injective (ContractedGermQuotient P) (ContractedFractionField P)
  have hδK : ι δ ≠ 0 := (map_ne_zero_iff ι hι).mpr hδ
  have hqdeg : q.natDegree = p.natDegree := by
    calc
      q.natDegree = (q.map ι).natDegree :=
        (Polynomial.natDegree_map_eq_of_injective hι q).symm
      _ = (Polynomial.C (ι δ) * p).natDegree := congrArg Polynomial.natDegree hqmap
      _ = p.natDegree := Polynomial.natDegree_C_mul hδK
  have hQdeg' : Q.natDegree = p.natDegree := hQdeg.trans hqdeg
  have hQpos : 0 < Q.natDegree := by
    rw [hQdeg']
    exact minpoly.natDegree_pos
      (genericLastCoordinate_isIntegral P a ha ha0 hmem)
  refine
    { denominator := D
      polynomial := Q
      denominator_not_mem := hD_not
      polynomial_mod_contraction_ne_zero := hQ_ne
      map_polynomial := ?_
      natDegree_eq := hQdeg'
      natDegree_pos := hQpos }
  change (Q.map π).map ι = Polynomial.C (ι (π D)) * p
  rw [hQ, hD, hqmap]

/-- The top coefficient of the cleared lift agrees with its common
denominator modulo the contraction.  This is the coefficient-level form of
the fact that the target minimal polynomial is monic. -/
theorem genericMinpolyLiftCertificate_leadingCoeff_sub_denominator_mem {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    let c := genericMinpolyLiftCertificate P a ha ha0 hmem
    c.polynomial.leadingCoeff - c.denominator ∈
      lowerDimensionalContraction P := by
  let c := genericMinpolyLiftCertificate P a ha ha0 hmem
  let π : HolomorphicGerm n →+* ContractedGermQuotient P :=
    Ideal.Quotient.mk (lowerDimensionalContraction P)
  let ι : ContractedGermQuotient P →+* ContractedFractionField P :=
    algebraMap (ContractedGermQuotient P) (ContractedFractionField P)
  let p := genericLastCoordinateMinpoly P
  have hpmonic : p.Monic :=
    genericLastCoordinateMinpoly_monic P a ha ha0 hmem
  have hcoeff := congrArg (fun q : Polynomial (ContractedFractionField P) ↦
      q.coeff c.polynomial.natDegree) c.map_polynomial
  have hcoeffK :
      ι (π c.polynomial.leadingCoeff) = ι (π c.denominator) := by
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at hcoeff
    rw [Polynomial.coeff_natDegree, c.natDegree_eq,
      hpmonic.coeff_natDegree, mul_one] at hcoeff
    exact hcoeff
  have hcoeffQ : π c.polynomial.leadingCoeff = π c.denominator :=
    (IsFractionRing.injective (ContractedGermQuotient P)
      (ContractedFractionField P)) hcoeffK
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, hcoeffQ, sub_self]

/-- The top coefficient of the cleared minimal-polynomial lift is a concrete
nonzero base germ modulo the contraction. -/
theorem genericMinpolyLiftCertificate_leadingCoeff_not_mem {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    let c := genericMinpolyLiftCertificate P a ha ha0 hmem
    c.polynomial.leadingCoeff ∉ lowerDimensionalContraction P := by
  dsimp only
  let c := genericMinpolyLiftCertificate P a ha ha0 hmem
  intro hlead
  change c.polynomial.leadingCoeff ∈ lowerDimensionalContraction P at hlead
  apply c.denominator_not_mem
  have hdiff : c.polynomial.leadingCoeff - c.denominator ∈
      lowerDimensionalContraction P :=
    genericMinpolyLiftCertificate_leadingCoeff_sub_denominator_mem
      P a ha ha0 hmem
  simpa only [sub_sub_cancel] using
    (lowerDimensionalContraction P).sub_mem hlead hdiff

/-- The fixed-size derivative resultant of the lifted minimal polynomial is
a second concrete base germ outside the contraction.  The matrix sizes are
the exact degree `e` and `e - 1`, so this is directly usable by fixed-degree
polynomial-specialization results. -/
theorem genericMinpolyLiftCertificate_resultant_not_mem {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    let c := genericMinpolyLiftCertificate P a ha ha0 hmem
    Polynomial.resultant c.polynomial c.polynomial.derivative
        c.polynomial.natDegree (c.polynomial.natDegree - 1) ∉
      lowerDimensionalContraction P := by
  dsimp only
  let c := genericMinpolyLiftCertificate P a ha ha0 hmem
  let π : HolomorphicGerm n →+* ContractedGermQuotient P :=
    Ideal.Quotient.mk (lowerDimensionalContraction P)
  let ι : ContractedGermQuotient P →+* ContractedFractionField P :=
    algebraMap (ContractedGermQuotient P) (ContractedFractionField P)
  let φ : HolomorphicGerm n →+* ContractedFractionField P := ι.comp π
  let p := genericLastCoordinateMinpoly P
  have hι : Function.Injective ι :=
    IsFractionRing.injective (ContractedGermQuotient P) (ContractedFractionField P)
  have hπden : π c.denominator ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact c.denominator_not_mem
  have hδ : ι (π c.denominator) ≠ 0 := (map_ne_zero_iff ι hι).mpr hπden
  have hQmap :
      c.polynomial.map φ = Polynomial.C (ι (π c.denominator)) * p := by
    simpa only [φ, RingHom.coe_comp, Function.comp_apply, Polynomial.map_map,
      p, π, ι] using c.map_polynomial
  have hQseparable : (c.polynomial.map φ).Separable := by
    rw [hQmap]
    exact Polynomial.Separable.unit_mul
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hδ))
      (genericLastCoordinateMinpoly_separable P a ha ha0 hmem)
  have hlead : c.polynomial.leadingCoeff ∉ lowerDimensionalContraction P :=
    genericMinpolyLiftCertificate_leadingCoeff_not_mem P a ha ha0 hmem
  have hπlead : π c.polynomial.leadingCoeff ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hlead
  have hφlead : φ c.polynomial.leadingCoeff ≠ 0 :=
    (map_ne_zero_iff ι hι).mpr hπlead
  have hdegree :
      (c.polynomial.map φ).natDegree = c.polynomial.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ hφlead
  have hresultant :
      Polynomial.resultant (c.polynomial.map φ)
          (c.polynomial.map φ).derivative c.polynomial.natDegree
          (c.polynomial.natDegree - 1) ≠ 0 := by
    have h := Polynomial.resultant_ne_zero (c.polynomial.map φ)
      (c.polynomial.map φ).derivative hQseparable
    simpa only [hdegree, Polynomial.natDegree_derivative] using h
  intro hresultant_mem
  apply hresultant
  have hmapzero :
      φ (Polynomial.resultant c.polynomial c.polynomial.derivative
        c.polynomial.natDegree (c.polynomial.natDegree - 1)) = 0 := by
    change ι (π _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hresultant_mem, map_zero]
  calc
    Polynomial.resultant (c.polynomial.map φ)
          (c.polynomial.map φ).derivative c.polynomial.natDegree
          (c.polynomial.natDegree - 1) =
        Polynomial.resultant (c.polynomial.map φ)
          (c.polynomial.derivative.map φ) c.polynomial.natDegree
          (c.polynomial.natDegree - 1) := by rw [Polynomial.derivative_map]
    _ = φ (Polynomial.resultant c.polynomial c.polynomial.derivative
          c.polynomial.natDegree (c.polynomial.natDegree - 1)) :=
      Polynomial.resultant_map_map c.polynomial c.polynomial.derivative
        c.polynomial.natDegree (c.polynomial.natDegree - 1) φ
    _ = 0 := hmapzero

/-! ## Denominator-cleared divisibility identities -/

/-- A polynomial identity modulo the contracted prime, with one explicit
common denominator outside that prime.  The `error` field is kept as an
honest polynomial over the base germ ring; every one of its coefficients is
certified to lie in the contraction. -/
structure GenericMinpolyDivisibilityLiftCertificate
    (Q R : Polynomial (HolomorphicGerm n)) where
  /-- The denominator clearing the generic divisibility identity. -/
  denominator : HolomorphicGerm n
  /-- The lifted quotient polynomial. -/
  quotient : Polynomial (HolomorphicGerm n)
  /-- The coefficientwise contraction error. -/
  error : Polynomial (HolomorphicGerm n)
  denominator_not_mem : denominator ∉ lowerDimensionalContraction P
  identity : Polynomial.C denominator * R = Q * quotient + error
  error_coeff_mem : ∀ k : ℕ, error.coeff k ∈ lowerDimensionalContraction P

/-- A polynomial of degree strictly below `e` is recovered from its first
`e` coefficients in the same format used by WPT remainders. -/
theorem remainderGermPolynomial_coefficients_eq {e : ℕ}
    (B : Polynomial (HolomorphicGerm n)) (hB : B.natDegree < e) :
    remainderGermPolynomial (fun i : Fin e ↦ B.coeff (i : ℕ)) = B := by
  unfold remainderGermPolynomial
  calc
    (∑ i : Fin e, Polynomial.C (B.coeff (i : ℕ)) *
        Polynomial.X ^ (i : ℕ)) =
      ∑ i ∈ Finset.range e,
        Polynomial.C (B.coeff i) * Polynomial.X ^ i :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ Polynomial.C (B.coeff i) * Polynomial.X ^ i) e
    _ = B := (B.as_sum_range_C_mul_X_pow' hB).symm

/-- A denominator-cleared Euclidean remainder of `R` modulo the generic
minimal polynomial.  Its displayed coefficient vector has length exactly
`Q.natDegree`, the identity holds over the base germ ring up to a
coefficientwise contraction error, and vanishing of all displayed
coefficients modulo the contraction forces generic divisibility. -/
structure GenericRemainderModMinpolyLiftCertificate
    (Q R : Polynomial (HolomorphicGerm n)) where
  positiveDegree : 0 < Q.natDegree
  /-- Coefficients of the strict remainder. -/
  coefficients : Fin Q.natDegree → HolomorphicGerm n
  /-- The denominator clearing the lifted Euclidean-division identity. -/
  denominator : HolomorphicGerm n
  /-- The quotient in the lifted Euclidean-division identity. -/
  quotient : Polynomial (HolomorphicGerm n)
  /-- The coefficientwise contraction error. -/
  error : Polynomial (HolomorphicGerm n)
  denominator_not_mem : denominator ∉ lowerDimensionalContraction P
  identity :
    Polynomial.C denominator * R =
      Q * quotient + remainderGermPolynomial coefficients + error
  error_coeff_mem : ∀ k : ℕ, error.coeff k ∈ lowerDimensionalContraction P
  divisible_of_coeff_mem :
    (∀ i, coefficients i ∈ lowerDimensionalContraction P) →
      genericLastCoordinateMinpoly P ∣
        (R.map (Ideal.Quotient.mk (lowerDimensionalContraction P))).map
          (algebraMap (ContractedGermQuotient P) (ContractedFractionField P))

/-- Clear the quotient in a generic-fibre divisibility statement.  The
result is a specialization-friendly identity over the original base germ
ring, with a single denominator and coefficientwise contraction error. -/
def genericMinpolyDivisibilityLiftCertificate {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P)
    (R : Polynomial (HolomorphicGerm n))
    (hdiv : genericLastCoordinateMinpoly P ∣
      (R.map (Ideal.Quotient.mk (lowerDimensionalContraction P))).map
        (algebraMap (ContractedGermQuotient P) (ContractedFractionField P))) :
    let c := genericMinpolyLiftCertificate P a ha ha0 hmem
    GenericMinpolyDivisibilityLiftCertificate P c.polynomial R := by
  let c := genericMinpolyLiftCertificate P a ha ha0 hmem
  let π : HolomorphicGerm n →+* ContractedGermQuotient P :=
    Ideal.Quotient.mk (lowerDimensionalContraction P)
  let ι : ContractedGermQuotient P →+* ContractedFractionField P :=
    algebraMap (ContractedGermQuotient P) (ContractedFractionField P)
  let p := genericLastCoordinateMinpoly P
  let Rbar := R.map π
  let t := Classical.choose hdiv
  have ht : Rbar.map ι = p * t := Classical.choose_spec hdiv
  have hclear := clearFractionPolynomialDenominators_allowZero t
  let μ := Classical.choose hclear
  have hμspec := Classical.choose_spec hclear
  have hμ : μ ≠ 0 := hμspec.1
  let Sbar := Classical.choose hμspec.2
  have hSbar : Sbar.map ι = Polynomial.C (ι μ) * t :=
    Classical.choose_spec hμspec.2
  have hSlifts : Sbar ∈ Polynomial.lifts π :=
    Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective Sbar
  have hSexists := Polynomial.exists_natDegree_eq_of_mem_lifts hSlifts
  let S := Classical.choose hSexists
  have hSspec := Classical.choose_spec hSexists
  have hS : S.map π = Sbar := hSspec.1
  let δ := π c.denominator
  have hδ : δ ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact c.denominator_not_mem
  have hδμ : δ * μ ≠ 0 := mul_ne_zero hδ hμ
  let D := Classical.choose (Ideal.Quotient.mk_surjective (δ * μ))
  have hD : π D = δ * μ :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective (δ * μ))
  have hD_not : D ∉ lowerDimensionalContraction P := by
    intro hDin
    apply hδμ
    rw [← hD]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hDin
  have hι : Function.Injective ι :=
    IsFractionRing.injective (ContractedGermQuotient P) (ContractedFractionField P)
  have hbaseIdentity :
      Polynomial.C (π D) * Rbar = (c.polynomial.map π) * Sbar := by
    apply Polynomial.map_injective ι hι
    simp only [Polynomial.map_mul, Polynomial.map_C]
    rw [hD, map_mul, c.map_polynomial, hSbar, ht]
    change Polynomial.C (ι δ * ι μ) * (p * t) =
      Polynomial.C (ι δ) * p * (Polynomial.C (ι μ) * t)
    rw [map_mul]
    ring
  let E := Polynomial.C D * R - c.polynomial * S
  have hEmap : E.map π = 0 := by
    simp only [E, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, hS]
    rw [hbaseIdentity, sub_self]
  refine
    { denominator := D
      quotient := S
      error := E
      denominator_not_mem := hD_not
      identity := ?_
      error_coeff_mem := ?_ }
  · dsimp only [E]
    ring
  · intro k
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← Polynomial.coeff_map, hEmap, Polynomial.coeff_zero]

omit [P.IsPrime] in
private lemma genericDivisibilityCertificateDenominatorNotMem
    {Q R : Polynomial (HolomorphicGerm n)}
    (C : GenericMinpolyDivisibilityLiftCertificate P Q R) :
    C.denominator ∉ lowerDimensionalContraction P :=
  C.denominator_not_mem

/-- A finite family of lifted divisibility identities sharing exactly one
base denominator outside the contraction. -/
structure CommonGenericMinpolyDivisibilityLiftCertificate
    {ι : Type*} [Fintype ι] (Q : Polynomial (HolomorphicGerm n))
    (R : ι → Polynomial (HolomorphicGerm n)) where
  /-- A denominator shared by the finite family of identities. -/
  denominator : HolomorphicGerm n
  /-- The family of lifted quotient polynomials. -/
  quotient : ι → Polynomial (HolomorphicGerm n)
  /-- The family of coefficientwise contraction errors. -/
  error : ι → Polynomial (HolomorphicGerm n)
  denominator_not_mem : denominator ∉ lowerDimensionalContraction P
  identity : ∀ i,
    Polynomial.C denominator * R i = Q * quotient i + error i
  error_coeff_mem : ∀ i k,
    (error i).coeff k ∈ lowerDimensionalContraction P

/-- Replace finitely many individual denominator-cleared identities by
identities with their product as a single common denominator. -/
def commonGenericMinpolyDivisibilityLiftCertificate
    {ι : Type*} [Fintype ι]
    (Q : Polynomial (HolomorphicGerm n))
    (R : ι → Polynomial (HolomorphicGerm n))
    (C : ∀ i, GenericMinpolyDivisibilityLiftCertificate P Q (R i)) :
    CommonGenericMinpolyDivisibilityLiftCertificate P Q R := by
  classical
  let D : HolomorphicGerm n := ∏ i, (C i).denominator
  let M : ι → HolomorphicGerm n := fun i ↦
    ∏ j ∈ Finset.univ.erase i, (C j).denominator
  have hfactor (i : ι) : (C i).denominator * M i = D := by
    exact Finset.mul_prod_erase Finset.univ (fun j ↦ (C j).denominator)
      (Finset.mem_univ i)
  have hDnot : D ∉ lowerDimensionalContraction P := by
    let π : HolomorphicGerm n →+* ContractedGermQuotient P :=
      Ideal.Quotient.mk (lowerDimensionalContraction P)
    have hi (i : ι) : π (C i).denominator ≠ 0 := by
      rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact (C i).denominator_not_mem
    have hprod : (∏ i, π (C i).denominator) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact hi i
    intro hDin
    apply hprod
    rw [← map_prod, show (∏ i, (C i).denominator) = D from rfl]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hDin
  refine
    { denominator := D
      quotient := fun i ↦ Polynomial.C (M i) * (C i).quotient
      error := fun i ↦ Polynomial.C (M i) * (C i).error
      denominator_not_mem := hDnot
      identity := ?_
      error_coeff_mem := ?_ }
  · intro i
    calc
      Polynomial.C D * R i =
          Polynomial.C ((C i).denominator * M i) * R i := by rw [hfactor]
      _ = Polynomial.C (M i) *
          (Polynomial.C (C i).denominator * R i) := by
        rw [map_mul]
        ring
      _ = Polynomial.C (M i) *
          (Q * (C i).quotient + (C i).error) := by rw [(C i).identity]
      _ = Q * (Polynomial.C (M i) * (C i).quotient) +
          Polynomial.C (M i) * (C i).error := by ring
  · intro i k
    rw [Polynomial.coeff_C_mul]
    exact (lowerDimensionalContraction P).mul_mem_left
      (M i) ((C i).error_coeff_mem k)

omit [P.IsPrime] in
private lemma commonDivisibilityCertificateDenominatorNotMem
    {ι : Type*} [Fintype ι]
    {Q : Polynomial (HolomorphicGerm n)}
    {R : ι → Polynomial (HolomorphicGerm n)}
    (C : CommonGenericMinpolyDivisibilityLiftCertificate P Q R) :
    C.denominator ∉ lowerDimensionalContraction P :=
  C.denominator_not_mem

/-- Divide an arbitrary base polynomial by the generic minimal polynomial,
then clear the quotient and the strict-lower-degree remainder with one common
denominator.  The lifted remainder is returned as a fixed-size coefficient
vector, and coefficientwise membership in the contraction recovers the
original generic divisibility statement. -/
def genericRemainderModMinpolyLiftCertificate {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P)
    (R : Polynomial (HolomorphicGerm n)) :
    let c := genericMinpolyLiftCertificate P a ha ha0 hmem
    GenericRemainderModMinpolyLiftCertificate P c.polynomial R := by
  let c := genericMinpolyLiftCertificate P a ha ha0 hmem
  let π : HolomorphicGerm n →+* ContractedGermQuotient P :=
    Ideal.Quotient.mk (lowerDimensionalContraction P)
  let ι : ContractedGermQuotient P →+* ContractedFractionField P :=
    algebraMap (ContractedGermQuotient P) (ContractedFractionField P)
  let p := genericLastCoordinateMinpoly P
  let Rbar := R.map π
  let RK := Rbar.map ι
  let tK := RK /ₘ p
  let bK := RK %ₘ p
  have hpmonic : p.Monic :=
    genericLastCoordinateMinpoly_monic P a ha ha0 hmem
  have hepos : 0 < c.polynomial.natDegree := c.natDegree_pos
  have hpdeg : p.natDegree = c.polynomial.natDegree := c.natDegree_eq.symm
  have hpneone : p ≠ 1 := by
    intro hpone
    have hdegree := congrArg Polynomial.natDegree hpone
    rw [Polynomial.natDegree_one, hpdeg] at hdegree
    exact (Nat.ne_of_gt hepos) hdegree
  have hbKdegree : bK.natDegree < c.polynomial.natDegree := by
    rw [← hpdeg]
    exact Polynomial.natDegree_modByMonic_lt RK hpmonic hpneone
  have hdivision : bK + p * tK = RK :=
    Polynomial.modByMonic_add_div RK p
  have htclear := clearFractionPolynomialDenominators_allowZero tK
  let μt := Classical.choose htclear
  have hμtspec := Classical.choose_spec htclear
  have hμt : μt ≠ 0 := hμtspec.1
  let St := Classical.choose hμtspec.2
  have hSt : St.map ι = Polynomial.C (ι μt) * tK :=
    Classical.choose_spec hμtspec.2
  have hbclear := clearFractionPolynomialDenominators_allowZero bK
  let μb := Classical.choose hbclear
  have hμbspec := Classical.choose_spec hbclear
  have hμb : μb ≠ 0 := hμbspec.1
  let Bb := Classical.choose hμbspec.2
  have hBb : Bb.map ι = Polynomial.C (ι μb) * bK :=
    Classical.choose_spec hμbspec.2
  let δ := π c.denominator
  have hδ : δ ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact c.denominator_not_mem
  let μ := μt * μb
  have hμ : μ ≠ 0 := mul_ne_zero hμt hμb
  have hδμ : δ * μ ≠ 0 := mul_ne_zero hδ hμ
  let Sbar := Polynomial.C μb * St
  let Bbar := Polynomial.C δ * (Polynomial.C μt * Bb)
  have hSbar : Sbar.map ι =
      Polynomial.C (ι μb) * (Polynomial.C (ι μt) * tK) := by
    simp only [Sbar, Polynomial.map_mul, Polynomial.map_C, hSt]
  have hBbar : Bbar.map ι =
      Polynomial.C (ι δ) *
        (Polynomial.C (ι μt) * (Polynomial.C (ι μb) * bK)) := by
    simp only [Bbar, Polynomial.map_mul, Polynomial.map_C, hBb]
  have hSlifts : Sbar ∈ Polynomial.lifts π :=
    Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective Sbar
  have hSexists := Polynomial.exists_natDegree_eq_of_mem_lifts hSlifts
  let S := Classical.choose hSexists
  have hSspec := Classical.choose_spec hSexists
  have hS : S.map π = Sbar := hSspec.1
  have hBlifts : Bbar ∈ Polynomial.lifts π :=
    Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective Bbar
  have hBexists := Polynomial.exists_natDegree_eq_of_mem_lifts hBlifts
  let B := Classical.choose hBexists
  have hBspec := Classical.choose_spec hBexists
  have hB : B.map π = Bbar := hBspec.1
  have hι : Function.Injective ι :=
    IsFractionRing.injective (ContractedGermQuotient P) (ContractedFractionField P)
  have hδK : ι δ ≠ 0 := (map_ne_zero_iff ι hι).mpr hδ
  have hμtK : ι μt ≠ 0 := (map_ne_zero_iff ι hι).mpr hμt
  have hμbK : ι μb ≠ 0 := (map_ne_zero_iff ι hι).mpr hμb
  have hBbarDegree : Bbar.natDegree = bK.natDegree := by
    calc
      Bbar.natDegree = (Bbar.map ι).natDegree :=
        (Polynomial.natDegree_map_eq_of_injective hι Bbar).symm
      _ = (Polynomial.C (ι δ) *
          (Polynomial.C (ι μt) * (Polynomial.C (ι μb) * bK))).natDegree :=
        congrArg Polynomial.natDegree hBbar
      _ = bK.natDegree := by
        rw [Polynomial.natDegree_C_mul hδK,
          Polynomial.natDegree_C_mul hμtK,
          Polynomial.natDegree_C_mul hμbK]
  have hBdegree : B.natDegree < c.polynomial.natDegree := by
    rw [hBspec.2, hBbarDegree]
    exact hbKdegree
  let b : Fin c.polynomial.natDegree → HolomorphicGerm n :=
    fun i ↦ B.coeff (i : ℕ)
  have hBreconstruct : remainderGermPolynomial b = B :=
    remainderGermPolynomial_coefficients_eq B hBdegree
  let D := Classical.choose (Ideal.Quotient.mk_surjective (δ * μ))
  have hD : π D = δ * μ :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective (δ * μ))
  have hD_not : D ∉ lowerDimensionalContraction P := by
    intro hDin
    apply hδμ
    rw [← hD]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hDin
  have hbaseIdentity :
      Polynomial.C (π D) * Rbar =
        (c.polynomial.map π) * Sbar + Bbar := by
    apply Polynomial.map_injective ι hι
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
    rw [hD, map_mul, map_mul, c.map_polynomial, hSbar, hBbar]
    change Polynomial.C (ι δ) * Polynomial.C (ι μ) * RK =
      (Polynomial.C (ι δ) * p) *
          (Polynomial.C (ι μb) * (Polynomial.C (ι μt) * tK)) +
        Polynomial.C (ι δ) *
          (Polynomial.C (ι μt) * (Polynomial.C (ι μb) * bK))
    rw [show ι μ = ι μt * ι μb by simp only [μ, map_mul], map_mul,
      ← hdivision]
    ring
  let E := Polynomial.C D * R -
    (c.polynomial * S + remainderGermPolynomial b)
  have hEmap : E.map π = 0 := by
    simp only [E, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, hS, hBreconstruct, hB]
    rw [hbaseIdentity, sub_self]
  refine
    { positiveDegree := hepos
      coefficients := b
      denominator := D
      quotient := S
      error := E
      denominator_not_mem := hD_not
      identity := ?_
      error_coeff_mem := ?_
      divisible_of_coeff_mem := ?_ }
  · dsimp only [E]
    ring
  · intro k
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← Polynomial.coeff_map, hEmap, Polynomial.coeff_zero]
  · intro hbmem
    have hBmap : B.map π = 0 := by
      apply Polynomial.ext
      intro k
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      by_cases hk : k < c.polynomial.natDegree
      · simpa only [b] using hbmem ⟨k, hk⟩
      · have hk' : B.natDegree < k := hBdegree.trans_le (Nat.le_of_not_gt hk)
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk']
        exact (lowerDimensionalContraction P).zero_mem
    have hBbarzero : Bbar = 0 := by rw [← hB, hBmap]
    have hbKzero : bK = 0 := by
      have hzero : Polynomial.C (ι δ) *
          (Polynomial.C (ι μt) * (Polynomial.C (ι μb) * bK)) = 0 := by
        rw [← hBbar, hBbarzero, Polynomial.map_zero]
      rcases mul_eq_zero.mp hzero with hscalar | hrest
      · exact False.elim ((Polynomial.C_ne_zero.mpr hδK) hscalar)
      rcases mul_eq_zero.mp hrest with hscalar | hrest
      · exact False.elim ((Polynomial.C_ne_zero.mpr hμtK) hscalar)
      rcases mul_eq_zero.mp hrest with hscalar | hbzero
      · exact False.elim ((Polynomial.C_ne_zero.mpr hμbK) hscalar)
      exact hbzero
    exact (Polynomial.modByMonic_eq_zero_iff_dvd hpmonic).mp hbKzero

private lemma genericRemainderCertificateDenominatorNotMem
    {Q R : Polynomial (HolomorphicGerm n)}
    (C : GenericRemainderModMinpolyLiftCertificate P Q R) :
    C.denominator ∉ lowerDimensionalContraction P :=
  C.denominator_not_mem

/-- The prepared monic polynomial itself has a cleared multiple identity by
the lifted generic minimal polynomial. -/
def preparedPolynomialMinpolyDivisibilityLiftCertificate {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    let c := genericMinpolyLiftCertificate P a ha ha0 hmem
    GenericMinpolyDivisibilityLiftCertificate P c.polynomial
      (preparedGermPolynomial a ha) :=
  genericMinpolyDivisibilityLiftCertificate P a ha ha0 hmem
    (preparedGermPolynomial a ha)
    (genericLastCoordinateMinpoly_dvd_genericPreparedPolynomial P a ha hmem)

/-- Every member of the prime has a denominator-cleared identity for its WPT
remainder. -/
def primeMemberRemainderMinpolyDivisibilityLiftCertificate {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P)
    (h : HolomorphicGerm (n + 1)) (hh : h ∈ P) :
    let c := genericMinpolyLiftCertificate P a ha ha0 hmem
    GenericMinpolyDivisibilityLiftCertificate P c.polynomial
      (remainderGermPolynomial
        (WPTBridge.preparedGermDivisionRemainder a ha ha0 h)) :=
  genericMinpolyDivisibilityLiftCertificate P a ha ha0 hmem
    (remainderGermPolynomial
      (WPTBridge.preparedGermDivisionRemainder a ha ha0 h))
    ((mem_prime_iff_minpoly_dvd_genericRemainderPolynomial
      P a ha ha0 hmem h).mp hh)

/-- The Euclidean-remainder certificate for the WPT remainder of an
arbitrary ambient germ. -/
def ambientGermRemainderModMinpolyLiftCertificate {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P)
    (g : HolomorphicGerm (n + 1)) :
    let c := genericMinpolyLiftCertificate P a ha ha0 hmem
    GenericRemainderModMinpolyLiftCertificate P c.polynomial
      (remainderGermPolynomial
        (WPTBridge.preparedGermDivisionRemainder a ha ha0 g)) :=
  genericRemainderModMinpolyLiftCertificate P a ha ha0 hmem
    (remainderGermPolynomial
      (WPTBridge.preparedGermDivisionRemainder a ha ha0 g))

/-- If every coefficient of the cleared strict remainder of an ambient germ
lies in the contraction, then the ambient germ lies in the original prime. -/
theorem ambientGermRemainderModMinpolyLiftCertificate_mem_of_coeff_mem
    {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P)
    (g : HolomorphicGerm (n + 1)) :
    let C := ambientGermRemainderModMinpolyLiftCertificate
      P a ha ha0 hmem g
    (∀ i, C.coefficients i ∈ lowerDimensionalContraction P) → g ∈ P := by
  dsimp only
  let C := ambientGermRemainderModMinpolyLiftCertificate
    P a ha ha0 hmem g
  intro hcoeff
  change ∀ i, C.coefficients i ∈ lowerDimensionalContraction P at hcoeff
  apply (mem_prime_iff_minpoly_dvd_genericRemainderPolynomial
    P a ha ha0 hmem g).mpr
  exact C.divisible_of_coeff_mem hcoeff

/-- The product of the leading coefficient and the fixed-size derivative
resultant is one common specialization bad factor outside the contraction. -/
def genericMinpolyLiftSpecializationBadFactor {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) : HolomorphicGerm n :=
  let c := genericMinpolyLiftCertificate P a ha ha0 hmem
  c.polynomial.leadingCoeff *
    Polynomial.resultant c.polynomial c.polynomial.derivative
      c.polynomial.natDegree (c.polynomial.natDegree - 1)

/-- The common specialization bad factor is not in the contracted prime. -/
theorem genericMinpolyLiftSpecializationBadFactor_not_mem {d : ℕ}
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P) :
    genericMinpolyLiftSpecializationBadFactor P a ha ha0 hmem ∉
      lowerDimensionalContraction P := by
  let c := genericMinpolyLiftCertificate P a ha ha0 hmem
  have hlead : c.polynomial.leadingCoeff ∉ lowerDimensionalContraction P :=
    genericMinpolyLiftCertificate_leadingCoeff_not_mem P a ha ha0 hmem
  have hres : Polynomial.resultant c.polynomial c.polynomial.derivative
      c.polynomial.natDegree (c.polynomial.natDegree - 1) ∉
        lowerDimensionalContraction P :=
    genericMinpolyLiftCertificate_resultant_not_mem P a ha ha0 hmem
  intro hprod
  have hor := (lowerDimensionalContraction_isPrime
    (P := P) (inferInstance : P.IsPrime)).mul_mem_iff_mem_or_mem.mp hprod
  exact hor.elim hlead hres

/-- The minimal polynomial annihilates the generic last-coordinate class. -/
theorem genericLastCoordinateMinpoly_aeval :
    Polynomial.aeval (genericLastCoordinate P)
      (genericLastCoordinateMinpoly P) = 0 := by
  exact minpoly.aeval (ContractedFractionField P) (genericLastCoordinate P)

end Prime

end

end LocalComplexGeometry
