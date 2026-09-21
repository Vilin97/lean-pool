/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.RankinCutoff1248Skeleton
import LeanPool.MarkoffModP.BGS.NumberTheory.RankinJointEnvelopeSummaryCoverage

/-!
# Certified actual Rankin profiles below `2^1248`

The finite exponent skeleton by itself does not choose the auxiliary twelfth
root used by the Rankin inequality.  This module chooses one canonically from
the side-erased witness cap.  It then proves that the actual positional
profile is structurally valid, matches `p`, and is dominated by the exact
scalar summary of its skeleton representative.
-/

namespace BGS.NumberTheory

namespace RankinExponentSkeleton

/-- One more than the integral twelfth root of the joint witness cap. -/
def jointEnvelopeRootCap (skeleton : RankinExponentSkeleton)
    (table : RankinPositionalCapTable) : Nat :=
  Nat.nthRoot 12
      ((skeleton.toProfile table 1).jointEnvelopeWitnessCap) + 1

/-- The side-erased profile with its canonical twelfth-root cap installed. -/
def certifiedProfile (skeleton : RankinExponentSkeleton)
    (table : RankinPositionalCapTable) : RankinNeighborProfile :=
  skeleton.toProfile table (skeleton.jointEnvelopeRootCap table)

@[simp] theorem certifiedProfile_jointEnvelopeWitnessCap
    (skeleton : RankinExponentSkeleton)
    (table : RankinPositionalCapTable) :
    (skeleton.certifiedProfile table).jointEnvelopeWitnessCap =
      (skeleton.toProfile table 1).jointEnvelopeWitnessCap := by
  rfl

theorem jointEnvelopeRootCap_pos
    (skeleton : RankinExponentSkeleton)
    (table : RankinPositionalCapTable) :
    0 < skeleton.jointEnvelopeRootCap table := by
  exact Nat.zero_lt_succ _

theorem certifiedProfile_jointEnvelopeValid
    (skeleton : RankinExponentSkeleton)
    (table : RankinPositionalCapTable) :
    (skeleton.certifiedProfile table).JointEnvelopeValid := by
  rw [RankinNeighborProfile.JointEnvelopeValid,
    certifiedProfile_jointEnvelopeWitnessCap]
  exact (Nat.lt_pow_nthRoot_add_one (by norm_num : Ne 12 0)
    ((skeleton.toProfile table 1).jointEnvelopeWitnessCap)).le

end RankinExponentSkeleton

/-- The canonical matched profile of `p`, using the cap determined by its
side-erased exponent skeleton. -/
def actualRankinProfile1248 (p : Nat) : RankinNeighborProfile :=
  positionalCanonicalRankinNeighborProfile p
    rankinCutoff1248CapTable.twoCap
    rankinCutoff1248CapTable.oddCapAt
    ((actualRankinExponentSkeleton p).jointEnvelopeRootCap
      rankinCutoff1248CapTable)

/-- The corresponding exact scalar summary, computed without side labels. -/
def actualRankinSkeletonSummary1248 (p : Nat) :
    RankinJointEnvelopeSummary :=
  RankinJointEnvelopeSummary.ofProfile
    ((actualRankinExponentSkeleton p).certifiedProfile
      rankinCutoff1248CapTable)

theorem actualRankinProfile1248_matches
    {p : Nat} (hp : p < 2 ^ 1248) (hpOne : 1 < p) :
    (actualRankinProfile1248 p).Matches p := by
  apply positionalCanonicalRankinNeighborProfile_matches_of_capTable
    rankinCutoff1248CapTable_valid
  · exact jointOddPrimeList_length_le_rankinCutoff1248CapTable hpOne hp

theorem eraseSides_actualRankinProfile1248
    (p : Nat) :
    (actualRankinProfile1248 p).eraseSides =
      (actualRankinExponentSkeleton p).certifiedProfile
        rankinCutoff1248CapTable := by
  exact eraseSides_positionalCanonicalRankinNeighborProfile p
    rankinCutoff1248CapTable.twoCap
    rankinCutoff1248CapTable.oddCapAt
    ((actualRankinExponentSkeleton p).jointEnvelopeRootCap
      rankinCutoff1248CapTable)

theorem actualRankinProfile1248_valid
    {p : Nat} (hpPrime : p.Prime) (hpTwo : 2 < p)
    (hp : p < 2 ^ 1248) :
    (actualRankinProfile1248 p).Valid := by
  apply positionalCanonicalRankinNeighborProfile_valid_of_capTable
    hpPrime hpTwo rankinCutoff1248CapTable_valid
    (jointOddPrimeList_length_le_rankinCutoff1248CapTable (by omega) hp)
  · exact (actualRankinExponentSkeleton p).jointEnvelopeRootCap_pos
      rankinCutoff1248CapTable
  · exact (actualRankinExponentSkeleton p).certifiedProfile_jointEnvelopeValid
      rankinCutoff1248CapTable

/-- The exact skeleton summary dominates the actual side-assigned profile.
This is the semantic handoff from actual primes to scalar search rows. -/
theorem actualRankinSkeletonSummary1248_dominates
    (p : Nat) :
    (actualRankinSkeletonSummary1248 p).Dominates
      (actualRankinProfile1248 p) := by
  rw [actualRankinSkeletonSummary1248,
    RankinJointEnvelopeSummary.Dominates]
  rw [← eraseSides_actualRankinProfile1248 p]
  simp [RankinJointEnvelopeSummary.ofProfile]

end BGS.NumberTheory
