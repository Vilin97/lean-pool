/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic

/-!
# Weak approximation at finite places

This file proves the finite-place weak-approximation theorem needed for
function-field Riemann--Roch constructions.  For finitely many distinct
height-one prime ideals, one may prescribe an element of the fraction field
to arbitrary positive order.  The resulting global fraction is integral at
every other height-one prime.

The proof is elementary Dedekind-domain algebra.  First clear all prescribed
fractions by one denominator.  The numerator is then chosen by the Chinese
remainder theorem.  At a selected prime the modulus contains both the desired
precision and the multiplicity of the common denominator.  At every other
prime dividing the denominator, a zero residue cancels the complete
denominator multiplicity.

Mathlib's multiplicative adic valuation is `exp (-order)`.  Thus
`v.valuation L (z - x) ≤ exp (-n)` means that `z - x` has additive order at
least `n`, while `v.valuation L z ≤ 1` means that `z` is regular at `v`.
-/

namespace BGS.HasseWeil

open IsDedekindDomain UniqueFactorizationMonoid
open scoped nonZeroDivisors

noncomputable section

/-- If the numerator contains every occurrence of a height-one prime in the
denominator, the resulting fraction is integral at that prime. -/
theorem valuation_div_algebraMap_le_one_of_mem_denominatorPower
    {R L : Type*} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (v : HeightOneSpectrum R) (numerator denominator : R)
    (hdenominator : denominator ≠ 0)
    (hnumerator : numerator ∈
      v.asIdeal ^
        (normalizedFactors (Ideal.span ({denominator} : Set R))).count v.asIdeal) :
    v.valuation L
        (algebraMap R L numerator / algebraMap R L denominator) ≤ 1 := by
  classical
  let m : ℕ :=
    (normalizedFactors (Ideal.span ({denominator} : Set R))).count v.asIdeal
  have hspan : Ideal.span ({denominator} : Set R) ≠ (⊥ : Ideal R) := by
    exact Ideal.span_singleton_eq_bot.not.mpr hdenominator
  have hdenominatorValuation :
      v.intValuation denominator = WithZero.exp (-(m : ℤ)) := by
    rw [v.intValuation_eq_exp_neg_multiplicity hdenominator,
      multiplicity_eq_count_normalizedFactors v.irreducible hspan]
    simp [m]
  have hnumeratorValuation :
      v.intValuation numerator ≤ WithZero.exp (-(m : ℤ)) := by
    exact (v.intValuation_le_pow_iff_mem numerator m).mpr hnumerator
  calc
    v.valuation L
        (algebraMap R L numerator / algebraMap R L denominator) =
        v.valuation L (algebraMap R L numerator) /
          v.valuation L (algebraMap R L denominator) :=
      (v.valuation L).map_div _ _
    _ = v.intValuation numerator / WithZero.exp (-(m : ℤ)) := by
      rw [v.valuation_of_algebraMap, v.valuation_of_algebraMap,
        hdenominatorValuation]
    _ ≤ 1 :=
      (div_le_one₀ (show 0 < WithZero.exp (-(m : ℤ)) from
        WithZero.exp_pos)).mpr hnumeratorValuation

/-- A congruence modulo the desired prime power plus the denominator
multiplicity gives the corresponding adic approximation bound after division
by the denominator. -/
theorem valuation_sub_div_algebraMap_le_of_mem_denominatorPrecisionPower
    {R L : Type*} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (v : HeightOneSpectrum R) (numerator target denominator : R)
    (precision : ℕ) (hdenominator : denominator ≠ 0)
    (hnumerator : numerator - target ∈
      v.asIdeal ^
        (precision +
          (normalizedFactors (Ideal.span ({denominator} : Set R))).count v.asIdeal)) :
    v.valuation L
        (algebraMap R L numerator / algebraMap R L denominator -
          algebraMap R L target / algebraMap R L denominator) ≤
      WithZero.exp (-(precision : ℤ)) := by
  classical
  let m : ℕ :=
    (normalizedFactors (Ideal.span ({denominator} : Set R))).count v.asIdeal
  have hspan : Ideal.span ({denominator} : Set R) ≠ (⊥ : Ideal R) := by
    exact Ideal.span_singleton_eq_bot.not.mpr hdenominator
  have hdenominatorValuation :
      v.intValuation denominator = WithZero.exp (-(m : ℤ)) := by
    rw [v.intValuation_eq_exp_neg_multiplicity hdenominator,
      multiplicity_eq_count_normalizedFactors v.irreducible hspan]
    simp [m]
  have hnumeratorValuation :
      v.intValuation (numerator - target) ≤
        WithZero.exp (-((precision + m : ℕ) : ℤ)) := by
    exact (v.intValuation_le_pow_iff_mem (numerator - target)
      (precision + m)).mpr hnumerator
  have hfractionIdentity :
      algebraMap R L numerator / algebraMap R L denominator -
          algebraMap R L target / algebraMap R L denominator =
        algebraMap R L (numerator - target) / algebraMap R L denominator := by
    rw [map_sub]
    ring
  rw [hfractionIdentity]
  calc
    v.valuation L
        (algebraMap R L (numerator - target) /
          algebraMap R L denominator) =
        v.intValuation (numerator - target) /
          WithZero.exp (-(m : ℤ)) := by
      rw [(v.valuation L).map_div, v.valuation_of_algebraMap,
        v.valuation_of_algebraMap, hdenominatorValuation]
    _ ≤ WithZero.exp (-((precision + m : ℕ) : ℤ)) /
          WithZero.exp (-(m : ℤ)) :=
      (div_le_div_iff_of_pos_right
        (show 0 < WithZero.exp (-(m : ℤ)) from WithZero.exp_pos)).mpr
          hnumeratorValuation
    _ = WithZero.exp (-(precision : ℤ)) := by
      rw [← WithZero.exp_sub]
      congr 1
      push_cast
      omega

/-- Chinese-remainder numerator selection with simultaneous denominator
cancellation.  At selected primes the congruence precision is increased by
the denominator multiplicity.  Every unselected prime factor of the
denominator divides the chosen numerator to its full multiplicity. -/
theorem exists_numerator_prescribedPrimePower_and_denominatorSupport
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (selected : Finset (Ideal R)) (denominatorIdeal : Ideal R)
    (hselectedPrime : ∀ P ∈ selected, Prime P)
    (target : selected → R) (precision : selected → ℕ) :
    ∃ numerator : R,
      (∀ P : selected,
        numerator - target P ∈
          (P : Ideal R) ^
            (precision P +
              (normalizedFactors denominatorIdeal).count (P : Ideal R))) ∧
      (∀ Q ∈ (normalizedFactors denominatorIdeal).toFinset,
        Q ∉ selected →
          numerator ∈ Q ^ (normalizedFactors denominatorIdeal).count Q) := by
  classical
  let support : Finset (Ideal R) :=
    selected ∪ (normalizedFactors denominatorIdeal).toFinset
  let exponent : Ideal R → ℕ := fun Q =>
    if hQ : Q ∈ selected then
      precision ⟨Q, hQ⟩ + (normalizedFactors denominatorIdeal).count Q
    else
      (normalizedFactors denominatorIdeal).count Q
  let residue : support → R := fun Q =>
    if hQ : (Q : Ideal R) ∈ selected then target ⟨Q, hQ⟩ else 0
  have hsupportPrime : ∀ Q ∈ support, Prime Q := by
    intro Q hQ
    rcases Finset.mem_union.mp hQ with hQselected | hQdenominator
    · exact hselectedPrime Q hQselected
    · exact prime_of_normalized_factor Q
        (Multiset.mem_toFinset.mp hQdenominator)
  obtain ⟨numerator, hnumerator⟩ :=
    IsDedekindDomain.exists_forall_sub_mem_ideal
      (s := support) (P := id) exponent hsupportPrime
      (by
        intro i hi j hj hij
        simpa using hij)
      residue
  refine ⟨numerator, ?_, ?_⟩
  · intro P
    have hPsupport : (P : Ideal R) ∈ support :=
      Finset.mem_union_left _ P.property
    have h := hnumerator (P : Ideal R) hPsupport
    simpa [residue, exponent, P.property] using h
  · intro Q hQdenominator hQselected
    have hQsupport : Q ∈ support :=
      Finset.mem_union_right _ hQdenominator
    have h := hnumerator Q hQsupport
    simpa [residue, exponent, hQselected] using h

/-- Finite-place weak approximation in a Dedekind fraction field.

The selected ideals must be prime.  The function `target` prescribes a local
fraction at each selected ideal, and `precision` prescribes its approximation
order.  The returned global fraction has that approximation order at every
selected height-one place and is integral at every unselected height-one
place. -/
theorem exists_fraction_approximating_at_finitePlaces_regular_elsewhere
    {R L : Type*} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (selected : Finset (Ideal R))
    (hselectedPrime : ∀ P ∈ selected, Prime P)
    (target : Ideal R → L) (precision : Ideal R → ℕ) :
    ∃ z : L,
      (∀ v : HeightOneSpectrum R, v.asIdeal ∈ selected →
        v.valuation L (z - target v.asIdeal) ≤
          WithZero.exp (-(precision v.asIdeal : ℤ))) ∧
      (∀ v : HeightOneSpectrum R, v.asIdeal ∉ selected →
        v.valuation L z ≤ 1) := by
  classical
  let denominator : nonZeroDivisors R :=
    IsLocalization.commonDenom (nonZeroDivisors R) selected target
  let localNumerator : selected → R :=
    IsLocalization.integerMultiple (nonZeroDivisors R) selected target
  obtain ⟨numerator, hselected, hdenominatorSupport⟩ :=
    exists_numerator_prescribedPrimePower_and_denominatorSupport
      selected (Ideal.span ({(denominator : R)} : Set R))
      hselectedPrime localNumerator (fun P => precision (P : Ideal R))
  let z : L :=
    algebraMap R L numerator / algebraMap R L (denominator : R)
  refine ⟨z, ?_, ?_⟩
  · intro v hv
    let P : selected := ⟨v.asIdeal, hv⟩
    have hlocal :=
      valuation_sub_div_algebraMap_le_of_mem_denominatorPrecisionPower
        (L := L) v numerator (localNumerator P) (denominator : R)
        (precision v.asIdeal)
        (nonZeroDivisors.ne_zero denominator.property)
        (by simpa [P] using hselected P)
    have hmap' :
        algebraMap R L (localNumerator P) =
          algebraMap R L (denominator : R) * target v.asIdeal := by
      change algebraMap R L
          (IsLocalization.integerMultiple (nonZeroDivisors R) selected target P) =
        algebraMap R L
            ((IsLocalization.commonDenom
              (nonZeroDivisors R) selected target : nonZeroDivisors R) : R) *
          target v.asIdeal
      rw [IsLocalization.map_integerMultiple]
      simp only [Submonoid.smul_def, Algebra.smul_def]
      rfl
    have hdenominatorMap : algebraMap R L (denominator : R) ≠ 0 := by
      intro hzero
      apply nonZeroDivisors.ne_zero denominator.property
      apply IsFractionRing.injective R L
      rw [map_zero]
      exact hzero
    have htarget :
        algebraMap R L (localNumerator P) /
            algebraMap R L (denominator : R) =
          target v.asIdeal := by
      rw [hmap']
      field_simp
    change v.valuation L
      (algebraMap R L numerator / algebraMap R L (denominator : R) -
        target v.asIdeal) ≤ WithZero.exp (-(precision v.asIdeal : ℤ))
    rw [← htarget]
    exact hlocal
  · intro v hv
    have hnumeratorPower : numerator ∈
        v.asIdeal ^
          (normalizedFactors
            (Ideal.span ({(denominator : R)} : Set R))).count v.asIdeal := by
      by_cases hfactor : v.asIdeal ∈
          (normalizedFactors
            (Ideal.span ({(denominator : R)} : Set R))).toFinset
      · exact hdenominatorSupport v.asIdeal hfactor hv
      · have hcount :
            (normalizedFactors
              (Ideal.span ({(denominator : R)} : Set R))).count v.asIdeal = 0 := by
          exact Multiset.count_eq_zero.mpr (by simpa only [Multiset.mem_toFinset] using hfactor)
        simp [hcount]
    simpa [z] using
      valuation_div_algebraMap_le_one_of_mem_denominatorPower
        (L := L) v numerator (denominator : R)
          (nonZeroDivisors.ne_zero denominator.property) hnumeratorPower

end

end BGS.HasseWeil
