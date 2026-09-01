/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Nullstellensatz.PreparedPrimeCore

/-!
# Construction of the prepared-prime certificate

This file constructs the finite pointwise certificate from generic-fibre data
and closes the prepared-prime induction step.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

/-- Construct the prepared-prime fiber certificate from the generic minimal polynomial. -/
def preparedPrimeFiberCertificateOfGenericMinpoly {n d : ℕ}
    (hd : 0 < d)
    (a : Fin d → ClassicalComplexWPT.Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (P : Ideal (HolomorphicGerm (n + 1))) (hP : P.IsPrime)
    (hmem : WPTBridge.preparedPolynomialGerm a ha ∈ P)
    (g : HolomorphicGerm (n + 1)) :
    PreparedPrimeFiberCertificate a P g := by
  classical
  letI : P.IsPrime := hP
  let c := genericMinpolyLiftCertificate P a ha ha0 hmem
  let Q : Polynomial (HolomorphicGerm n) := c.polynomial
  let e : ℕ := Q.natDegree
  let S := IdealGeneratorIndex P
  have hgenerator (f : S) : (f : HolomorphicGerm (n + 1)) ∈ P :=
    idealGenerator_mem P f
  let R : Option S → Polynomial (HolomorphicGerm n)
    | none => preparedGermPolynomial a ha
    | some f => remainderGermPolynomial
        (WPTBridge.preparedGermDivisionRemainder a ha ha0
          (f : HolomorphicGerm (n + 1)))
  let Cdiv : ∀ i : Option S,
      GenericMinpolyDivisibilityLiftCertificate P Q (R i) := fun i ↦ by
    cases i with
    | none =>
        simpa only [Q, c, R] using
          preparedPolynomialMinpolyDivisibilityLiftCertificate
            P a ha ha0 hmem
    | some f =>
        simpa only [Q, c, R] using
          primeMemberRemainderMinpolyDivisibilityLiftCertificate
            P a ha ha0 hmem (f : HolomorphicGerm (n + 1)) (hgenerator f)
  let Ccommon :=
    commonGenericMinpolyDivisibilityLiftCertificate P Q R Cdiv
  let Cspec (i : Option S) :
      GenericMinpolyDivisibilityLiftCertificate P Q (R i) :=
    { denominator := Ccommon.denominator
      quotient := Ccommon.quotient i
      error := Ccommon.error i
      denominator_not_mem := Ccommon.denominator_not_mem
      identity := Ccommon.identity i
      error_coeff_mem := Ccommon.error_coeff_mem i }
  let Ctarget := ambientGermRemainderModMinpolyLiftCertificate
    P a ha ha0 hmem g
  let baseBad := genericMinpolyLiftSpecializationBadFactor
    P a ha ha0 hmem
  let bad : HolomorphicGerm n := baseBad * Ccommon.denominator
  let Δ : HolomorphicGerm n :=
    Polynomial.resultant Q Q.derivative e (e - 1)
  have hQdegree : Q.natDegree ≤ e := by exact le_rfl
  have hpreparedDegree : (preparedGermPolynomial a ha).natDegree ≤ d := by
    rw [preparedGermPolynomial_natDegree]
  have hremainderDegree (h : HolomorphicGerm (n + 1)) :
      (remainderGermPolynomial
        (WPTBridge.preparedGermDivisionRemainder a ha ha0 h)).natDegree ≤ d :=
    remainderGermPolynomial_natDegree_le _
  have hbadRepresentative := eventually_representative_mul
    baseBad Ccommon.denominator
  have hbaseBadRepresentative :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n),
        HolomorphicGerm.representative baseBad z =
          HolomorphicGerm.representative Q.leadingCoeff z *
            HolomorphicGerm.representative Δ z := by
    simpa only [baseBad, genericMinpolyLiftSpecializationBadFactor,
      c, Q, e, Δ] using eventually_representative_mul Q.leadingCoeff Δ
  have hdegreeSeparable :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n),
        HolomorphicGerm.representative Q.leadingCoeff z ≠ 0 →
        HolomorphicGerm.representative Δ z ≠ 0 →
          (germPolynomialRepresentativeAt e Q z).natDegree = e ∧
            (germPolynomialRepresentativeAt e Q z).Separable := by
    simpa only [c, Q, e, Δ] using
      eventually_genericMinpolyLift_natDegree_eq_and_separable
        P a ha ha0 hmem
  have hpreparedDivides :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n),
        idealGeneratorZeroPredicate (lowerDimensionalContraction P) z →
        HolomorphicGerm.representative Ccommon.denominator z ≠ 0 →
        ∀ w : ℂ, (germPolynomialRepresentativeAt e Q z).eval w = 0 →
          (germPolynomialRepresentativeAt d
            (preparedGermPolynomial a ha) z).eval w = 0 := by
    simpa only [Cspec, R] using
      eventually_eval_eq_zero_of_genericMinpolyDivisibilityLiftCertificate
        P (Cspec none) hQdegree hpreparedDegree
  have hpreparedRepresentative :=
    eventually_germPolynomialRepresentativeAt_preparedGermPolynomial a ha
  have hgeneratorDivides :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n), ∀ f : S,
        idealGeneratorZeroPredicate (lowerDimensionalContraction P) z →
        HolomorphicGerm.representative Ccommon.denominator z ≠ 0 →
        ∀ w : ℂ, (germPolynomialRepresentativeAt e Q z).eval w = 0 →
          (germPolynomialRepresentativeAt d
            (remainderGermPolynomial
              (WPTBridge.preparedGermDivisionRemainder a ha ha0
                (f : HolomorphicGerm (n + 1)))) z).eval w = 0 := by
    apply Filter.eventually_all.mpr
    intro f
    simpa only [Cspec, R] using
      eventually_eval_eq_zero_of_genericMinpolyDivisibilityLiftCertificate
        P (Cspec (some f)) hQdegree
          (hremainderDegree (f : HolomorphicGerm (n + 1)))
  have hgeneratorPolynomialRepresentative :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n), ∀ f : S,
        germPolynomialRepresentativeAt d
            (remainderGermPolynomial
              (WPTBridge.preparedGermDivisionRemainder a ha ha0
                (f : HolomorphicGerm (n + 1)))) z =
          remainderPolynomialAt
            (HolomorphicGerm.coefficientRepresentatives
              (WPTBridge.preparedGermDivisionRemainder a ha ha0
                (f : HolomorphicGerm (n + 1)))) z := by
    apply Filter.eventually_all.mpr
    intro f
    exact eventually_germPolynomialRepresentativeAt_remainderGermPolynomial _
  have hgeneratorAmbientRepresentative :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n), ∀ f : S, ∀ w : ℂ,
        preparedValue a z w = 0 →
          HolomorphicGerm.representative
              (f : HolomorphicGerm (n + 1)) (appendLastCLE n (z, w)) =
            ∑ i : Fin d,
              HolomorphicGerm.representative
                  (WPTBridge.preparedGermDivisionRemainder a ha ha0
                    (f : HolomorphicGerm (n + 1)) i) z *
                w ^ (i : ℕ) := by
    apply Filter.eventually_all.mpr
    intro f
    exact eventually_representative_eq_remainder_on_preparedRoots
      hd a ha ha0 (f : HolomorphicGerm (n + 1))
  have htargetRemainderIdentity :
      ∀ᶠ z in nhds (0 : ComplexEuclidean n),
        idealGeneratorZeroPredicate (lowerDimensionalContraction P) z →
        ∀ w : ℂ, (germPolynomialRepresentativeAt e Q z).eval w = 0 →
          (remainderPolynomialAt
              (HolomorphicGerm.coefficientRepresentatives
                Ctarget.coefficients) z).eval w =
            HolomorphicGerm.representative Ctarget.denominator z *
              (germPolynomialRepresentativeAt d
                (remainderGermPolynomial
                  (WPTBridge.preparedGermDivisionRemainder
                    a ha ha0 g)) z).eval w := by
    simpa only [Ctarget, c, Q] using
      eventually_remainder_eval_eq_denominator_mul_of_genericRemainderModMinpolyLiftCertificate
        P Ctarget hQdegree (hremainderDegree g)
  have htargetPolynomialRepresentative :=
    eventually_germPolynomialRepresentativeAt_remainderGermPolynomial
      (WPTBridge.preparedGermDivisionRemainder a ha ha0 g)
  have htargetAmbientRepresentative :=
    eventually_representative_eq_remainder_on_preparedRoots
      hd a ha ha0 g
  refine
    { e := e
      positiveDegree := ?_
      q := fun i ↦ Q.coeff (i : ℕ)
      b := Ctarget.coefficients
      bad := bad
      bad_not_mem := ?_
      eventually_specializes := ?_
      mem_of_coeff_mem := ?_ }
  · simpa only [e, Q, c] using c.natDegree_pos
  · have hbase : baseBad ∉ lowerDimensionalContraction P := by
      simpa only [baseBad] using
        genericMinpolyLiftSpecializationBadFactor_not_mem P a ha ha0 hmem
    have hcommon : Ccommon.denominator ∉ lowerDimensionalContraction P :=
      Ccommon.denominator_not_mem
    intro hbad
    exact (lowerDimensionalContraction_isPrime hP).mul_mem_iff_mem_or_mem.mp hbad
      |>.elim hbase hcommon
  · filter_upwards [hbadRepresentative, hbaseBadRepresentative,
      hdegreeSeparable, hpreparedDivides, hpreparedRepresentative,
      hgeneratorDivides, hgeneratorPolynomialRepresentative,
      hgeneratorAmbientRepresentative, htargetRemainderIdentity,
      htargetPolynomialRepresentative, htargetAmbientRepresentative]
      with z hbadz hbasez hsepz hpreparedz hpreparedRepz hgeneratorz
        hgeneratorRepz hgeneratorAmbientz htargetz htargetRepz
        htargetAmbientz
    intro hZ hbadNonzero
    change
      (germPolynomialRepresentativeAt e Q z).natDegree = e ∧
        (germPolynomialRepresentativeAt e Q z).Separable ∧
          ∀ w : ℂ, (germPolynomialRepresentativeAt e Q z).eval w = 0 →
            preparedValue a z w = 0 ∧
              (∀ f : idealGeneratorFinset P,
                HolomorphicGerm.representative
                    (f : HolomorphicGerm (n + 1))
                    (appendLastCLE n (z, w)) = 0) ∧
              (HolomorphicGerm.representative g
                    (appendLastCLE n (z, w)) = 0 →
                (remainderPolynomialAt
                  (HolomorphicGerm.coefficientRepresentatives
                    Ctarget.coefficients) z).eval w = 0)
    have hfactorNonzero :
        HolomorphicGerm.representative baseBad z ≠ 0 ∧
          HolomorphicGerm.representative Ccommon.denominator z ≠ 0 := by
      apply mul_ne_zero_iff.mp
      rw [← hbadz]
      exact hbadNonzero
    have hleadingNonzero :
        HolomorphicGerm.representative Q.leadingCoeff z ≠ 0 := by
      intro hzero
      apply hfactorNonzero.1
      rw [hbasez, hzero, zero_mul]
    have hresultantNonzero : HolomorphicGerm.representative Δ z ≠ 0 := by
      intro hzero
      apply hfactorNonzero.1
      rw [hbasez, hzero, mul_zero]
    obtain ⟨hdegree, hseparable⟩ := hsepz hleadingNonzero hresultantNonzero
    refine ⟨hdegree, hseparable, ?_⟩
    intro w hQroot
    have hZ' : idealGeneratorZeroPredicate
        (lowerDimensionalContraction P) z := by
      simpa only [idealGeneratorZeroPredicate, idealGeneratorRepresentatives]
        using hZ
    have hpreparedRepRoot := hpreparedz hZ' hfactorNonzero.2 w hQroot
    have hpreparedPolynomialRoot : (preparedPolynomialAt a z).eval w = 0 := by
      rw [← hpreparedRepz]
      exact hpreparedRepRoot
    have hpreparedRoot : preparedValue a z w = 0 := by
      rwa [preparedPolynomialAt_eval] at hpreparedPolynomialRoot
    refine ⟨hpreparedRoot, ?_, ?_⟩
    · intro f
      have hremainderRepRoot := hgeneratorz f hZ' hfactorNonzero.2 w hQroot
      have hremainderRoot :
          (remainderPolynomialAt
            (HolomorphicGerm.coefficientRepresentatives
              (WPTBridge.preparedGermDivisionRemainder a ha ha0
                (f : HolomorphicGerm (n + 1)))) z).eval w = 0 := by
        rw [← hgeneratorRepz f]
        exact hremainderRepRoot
      calc
        HolomorphicGerm.representative (f : HolomorphicGerm (n + 1))
            (appendLastCLE n (z, w)) =
            ∑ i : Fin d,
              HolomorphicGerm.representative
                  (WPTBridge.preparedGermDivisionRemainder a ha ha0
                    (f : HolomorphicGerm (n + 1)) i) z *
                w ^ (i : ℕ) := hgeneratorAmbientz f w hpreparedRoot
        _ = 0 := by
          simpa only [remainderPolynomialAt_eval,
            HolomorphicGerm.coefficientRepresentatives] using hremainderRoot
    · intro hgzero
      have htargetDisplayedRoot :
          (remainderPolynomialAt
            (HolomorphicGerm.coefficientRepresentatives
              (WPTBridge.preparedGermDivisionRemainder a ha ha0 g)) z).eval w =
              0 := by
        rw [remainderPolynomialAt_eval]
        calc
          ∑ i : Fin d,
              HolomorphicGerm.coefficientRepresentatives
                  (WPTBridge.preparedGermDivisionRemainder a ha ha0 g) i z *
                w ^ (i : ℕ) =
              HolomorphicGerm.representative g
                (appendLastCLE n (z, w)) := by
                  simpa only [HolomorphicGerm.coefficientRepresentatives] using
                    (htargetAmbientz w hpreparedRoot).symm
          _ = 0 := hgzero
      have htargetGermRoot :
          (germPolynomialRepresentativeAt d
            (remainderGermPolynomial
              (WPTBridge.preparedGermDivisionRemainder a ha ha0 g)) z).eval w =
              0 := by
        rw [htargetRepz]
        exact htargetDisplayedRoot
      rw [htargetz hZ' w hQroot, htargetGermRoot, mul_zero]
  · simpa only [Ctarget] using
      ambientGermRemainderModMinpolyLiftCertificate_mem_of_coeff_mem
        P a ha ha0 hmem g

/-- The lower-dimensional prime theorem supplies the geometric cancellation
step needed to close the prepared successor case. -/
theorem preparedPrimeZeroSetStep_of_primeZeroSetProperty {n : ℕ}
    (hprime : PrimeZeroSetProperty n) : PreparedPrimeZeroSetStep n := by
  intro d hd a ha ha0 P hP hmem
  apply le_antisymm
  · intro g hg
    exact mem_prime_of_preparedPrimeFiberCertificate
      hprime hd a ha ha0 P hP g hg
        (preparedPrimeFiberCertificateOfGenericMinpoly
          hd a ha ha0 P hP hmem g)
  · intro g hg
    exact idealZeroSetGerm_le_germZeroLocus_of_mem P hg

/-- The prepared-prime construction closes the prime zero-set theorem in
every dimension by induction. -/
theorem primeZeroSetProperty_all : ∀ n : ℕ, PrimeZeroSetProperty n
  | 0 => primeZeroSetProperty_zero
  | n + 1 =>
      primeZeroSetProperty_succ_of_preparedPrimeZeroSetStep
        (preparedPrimeZeroSetStep_of_primeZeroSetProperty
          (primeZeroSetProperty_all n))

end

end LocalComplexGeometry
