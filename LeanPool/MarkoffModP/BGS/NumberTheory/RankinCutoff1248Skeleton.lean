/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.NumberTheory.RankinCutoff1248Data

/-!
# Finite exponent skeletons below `2^1248`

After side erasure and positional prime caps, the only varying arithmetic data
are two two-adic exponents and a list of positive odd exponents.  This module
records an executable admissibility predicate.  Every actual prime below the
target cutoff satisfies it, including the strong global product budget
`jointLowerNeighborProduct < 2^2496`.
-/

@[expose] public section

namespace BGS.NumberTheory

structure RankinExponentSkeleton where
  minusTwoExponent : ℕ
  plusTwoExponent : ℕ
  oddExponents : List ℕ
  deriving DecidableEq, Repr

namespace RankinExponentSkeleton

def toProfile (skeleton : RankinExponentSkeleton)
    (table : RankinPositionalCapTable) (rootCap : ℕ) :
    RankinNeighborProfile :=
  positionalRankinSkeletonProfile table.twoCap table.oddCapAt
    skeleton.minusTwoExponent skeleton.plusTwoExponent
    skeleton.oddExponents rootCap

def TwoFactorizationShape (skeleton : RankinExponentSkeleton) : Prop :=
  (skeleton.minusTwoExponent = 1 ∧
      2 ≤ skeleton.plusTwoExponent) ∨
    (skeleton.plusTwoExponent = 1 ∧
      2 ≤ skeleton.minusTwoExponent)

def twoFactorizationShapeCheck
    (skeleton : RankinExponentSkeleton) : Bool :=
  (decide (skeleton.minusTwoExponent = 1) &&
      decide (2 ≤ skeleton.plusTwoExponent)) ||
    (decide (skeleton.plusTwoExponent = 1) &&
      decide (2 ≤ skeleton.minusTwoExponent))

@[simp] theorem twoFactorizationShapeCheck_eq_true_iff
    (skeleton : RankinExponentSkeleton) :
    skeleton.twoFactorizationShapeCheck = true ↔
      skeleton.TwoFactorizationShape := by
  simp [twoFactorizationShapeCheck, TwoFactorizationShape]

def OddExponentsPositive (skeleton : RankinExponentSkeleton) : Prop :=
  ∀ exponent ∈ skeleton.oddExponents, 0 < exponent

def oddExponentsPositiveCheck (skeleton : RankinExponentSkeleton) : Bool :=
  skeleton.oddExponents.all fun exponent => decide (0 < exponent)

@[simp] theorem oddExponentsPositiveCheck_eq_true_iff
    (skeleton : RankinExponentSkeleton) :
    skeleton.oddExponentsPositiveCheck = true ↔
      skeleton.OddExponentsPositive := by
  simp [oddExponentsPositiveCheck, OddExponentsPositive]

def Admissible (skeleton : RankinExponentSkeleton)
    (table : RankinPositionalCapTable)
    (slotBound productBound : ℕ) : Prop :=
  skeleton.TwoFactorizationShape ∧
    skeleton.OddExponentsPositive ∧
    skeleton.oddExponents.length < slotBound ∧
    (skeleton.toProfile table 1).jointLowerNeighborProduct < productBound

def admissibleCheck (skeleton : RankinExponentSkeleton)
    (table : RankinPositionalCapTable)
    (slotBound productBound : ℕ) : Bool :=
  skeleton.twoFactorizationShapeCheck &&
    skeleton.oddExponentsPositiveCheck &&
    decide (skeleton.oddExponents.length < slotBound) &&
    decide
      ((skeleton.toProfile table 1).jointLowerNeighborProduct < productBound)

@[simp] theorem admissibleCheck_eq_true_iff
    (skeleton : RankinExponentSkeleton)
    (table : RankinPositionalCapTable)
    (slotBound productBound : ℕ) :
    skeleton.admissibleCheck table slotBound productBound = true ↔
      skeleton.Admissible table slotBound productBound := by
  simp [admissibleCheck, Admissible, and_assoc]

end RankinExponentSkeleton

def actualRankinExponentSkeleton (p : ℕ) : RankinExponentSkeleton where
  minusTwoExponent := (p - 1).factorization 2
  plusTwoExponent := (p + 1).factorization 2
  oddExponents := actualOddExponentSkeleton p

@[simp] theorem actualRankinExponentSkeleton_toProfile
    (p : ℕ) (table : RankinPositionalCapTable) (rootCap : ℕ) :
    (actualRankinExponentSkeleton p).toProfile table rootCap =
      positionalRankinSkeletonProfile table.twoCap table.oddCapAt
        ((p - 1).factorization 2) ((p + 1).factorization 2)
        (actualOddExponentSkeleton p) rootCap := by
  rfl

theorem actualRankinExponentSkeleton_oddExponentsPositive
    {p : ℕ} (hpOne : 1 < p) :
    (actualRankinExponentSkeleton p).OddExponentsPositive := by
  intro exponent hexponent
  simp only [actualRankinExponentSkeleton] at hexponent ⊢
  rw [actualOddExponentSkeleton] at hexponent
  obtain ⟨prime, hprime, rfl⟩ := List.mem_map.mp hexponent
  exact actualNeighborExponent_pos hpOne hprime

theorem actualRankinExponentSkeleton_productBudget_1248
    {p : ℕ} (hpPrime : p.Prime) (hpTwo : 2 < p)
    (hp : p < 2 ^ 1248) :
    ((actualRankinExponentSkeleton p).toProfile
      rankinCutoff1248CapTable 1).jointLowerNeighborProduct <
        2 ^ (2 * 1248) := by
  have hlength : (jointOddPrimeList p).length ≤
      rankinCutoff1248CapTable.oddPrimeFloors.length := by
    apply jointOddPrimeList_length_le_rankinCutoff1248CapTable
    · omega
    · exact hp
  let actualProfile := positionalCanonicalRankinNeighborProfile p
    rankinCutoff1248CapTable.twoCap
    rankinCutoff1248CapTable.oddCapAt 1
  have hmatch : actualProfile.Matches p := by
    exact positionalCanonicalRankinNeighborProfile_matches_of_capTable
      rankinCutoff1248CapTable_valid hlength 1
  have hlower := actualProfile.lowerNeighborProducts_le
    hpPrime hpTwo hmatch
  have hjointLower : actualProfile.jointLowerNeighborProduct ≤
      (p - 1) * (p + 1) := by
    rw [RankinNeighborProfile.jointLowerNeighborProduct_eq_mul]
    exact Nat.mul_le_mul hlower.1 hlower.2
  have hneighbors := neighbors_mul_lt_two_pow_two_mul (by omega) hp
  have herase := eraseSides_positionalCanonicalRankinNeighborProfile p
    rankinCutoff1248CapTable.twoCap
    rankinCutoff1248CapTable.oddCapAt 1
  calc
    ((actualRankinExponentSkeleton p).toProfile
        rankinCutoff1248CapTable 1).jointLowerNeighborProduct =
      actualProfile.eraseSides.jointLowerNeighborProduct := by
        rw [herase]
        rfl
    _ = actualProfile.jointLowerNeighborProduct := by
      exact RankinNeighborProfile.eraseSides_jointLowerNeighborProduct
        actualProfile
    _ ≤ (p - 1) * (p + 1) := hjointLower
    _ < 2 ^ (2 * 1248) := hneighbors

/-- Every actual prime below the target lies in the executable finite search
domain.  This theorem is coverage, not yet the terminal leaf check. -/
theorem actualRankinExponentSkeleton_admissible_1248
    {p : ℕ} (hpPrime : p.Prime) (hpTwo : 2 < p)
    (hp : p < 2 ^ 1248) :
    (actualRankinExponentSkeleton p).Admissible
      rankinCutoff1248CapTable 275 (2 ^ (2 * 1248)) := by
  refine ⟨neighboring_twoFactorization_shape hpPrime hpTwo,
    actualRankinExponentSkeleton_oddExponentsPositive (by omega), ?_, ?_⟩
  · simpa [actualRankinExponentSkeleton, actualOddExponentSkeleton] using
      jointOddPrimeList_length_lt_275_of_lt_two_pow_1248
        (by omega) hp
  · exact actualRankinExponentSkeleton_productBudget_1248 hpPrime hpTwo hp

end BGS.NumberTheory
