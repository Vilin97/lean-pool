/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements

/-! # Prime Choice -/

@[expose] public section
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction: choosing prime elements

Surjectivity of the normalized valuation supplies a prime element in every
finite abstract field.  Any two choices differ by a unit (additively, their
difference has value zero).
-/

noncomputable
section

namespace ValuationData

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- A chosen prime element of a finite abstract field.  Later independence
lemmas show that the reciprocity class does not depend on this choice. -/
def chosenPrimeElement (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field :=
  Classical.choose (v.normalizedValuation_surjective K v.oneValue)

/-- Establishes the identity `v.valuationAt K (v.chosenPrimeElement K) = v.oneValue`. -/
@[simp]
theorem valuationAt_chosenPrimeElement (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    v.valuationAt K (v.chosenPrimeElement K) = v.oneValue :=
  Classical.choose_spec (v.normalizedValuation_surjective K v.oneValue)

/-- The chosen prime element has valuation equal to the distinguished degree-one value. -/
theorem chosenPrimeElement_isPrime (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    v.IsPrimeElement K (v.chosenPrimeElement K) :=
  v.valuationAt_chosenPrimeElement K

/-- In additive notation, two prime elements differ by a unit. -/
theorem sub_mem_unitAddSubgroup_of_prime
    (v : ValuationData D A) (K : FiniteAbstractField G)
    {π π' : ambientFixedAddSubgroup A K.field}
    (hπ : v.IsPrimeElement K π) (hπ' : v.IsPrimeElement K π') :
    π' - π ∈ v.unitAddSubgroup K := by
  rw [v.mem_unitAddSubgroup_iff, map_sub, hπ, hπ']
  exact sub_self _

/-- Establishes the membership statement `π - v.chosenPrimeElement K ∈ v.unitAddSubgroup K`. -/
theorem sub_chosenPrimeElement_mem_unitAddSubgroup
    (v : ValuationData D A) (K : FiniteAbstractField G)
    {π : ambientFixedAddSubgroup A K.field}
    (hπ : v.IsPrimeElement K π) :
    π - v.chosenPrimeElement K ∈ v.unitAddSubgroup K :=
  v.sub_mem_unitAddSubgroup_of_prime
    K (v.chosenPrimeElement_isPrime K) hπ

end ValuationData

end
end ClassFormation
