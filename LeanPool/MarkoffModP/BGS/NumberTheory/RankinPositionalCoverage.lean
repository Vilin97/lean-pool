/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.RankinPositionalProfile
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.PrimeFin

/-!
# Finite positional cap ladders

A finite certificate can store the first `k` odd primes as literal data.  The
checker verifies each entry by primality and `primeCounting'`, so no
noncomputable prime enumeration occurs in the payload.  Every increasing list
of odd primes of length at most `k` is then pointwise bounded below by this
ladder.  Consequently the positional canonical profile really matches the
actual neighboring factorization.

The remaining global coverage obligation is deliberately visible: one must
prove that the actual joint odd support has length at most the stored ladder.
-/

namespace BGS.NumberTheory

open scoped Nat.Prime

/-- A strictly increasing list of odd primes has its entry in position `i` at
least the `(i + 1)`-st prime.  The initial prime `2` supplies the shift. -/
theorem nthPrime_succ_idxOf_le_of_pairwise
    (values : List ℕ) (hnodup : values.Nodup)
    (hpair : values.Pairwise (· < ·))
    (hprime : ∀ q ∈ values, q.Prime)
    (htwo : 2 ∉ values) {q : ℕ} (hq : q ∈ values) :
    Nat.nth Nat.Prime (values.idxOf q + 1) ≤ q := by
  have hqPrime : q.Prime := hprime q hq
  have hqThree : 3 ≤ q := by
    have hqTwo := hqPrime.two_le
    have hqNeTwo : q ≠ 2 := by
      intro heq
      subst q
      exact htwo hq
    omega
  let earlier := values.take (values.idxOf q)
  have hearlierNodup : earlier.Nodup := hnodup.take
  have htwoEarlier : 2 ∉ earlier := by
    intro hmem
    exact htwo (List.mem_of_mem_take hmem)
  have hsubset : insert 2 earlier.toFinset ⊆ q.primesBelow := by
    intro r hr
    rw [Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · exact Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
    · have hrEarlier : r ∈ earlier := by simpa using hr
      have hrValues : r ∈ values := List.mem_of_mem_take hrEarlier
      have hrIndex : values.idxOf r < values.idxOf q := by
        exact (List.mem_take_iff_idxOf_lt hrValues).mp hrEarlier
      have hrlt : r < q := by
        have hrel := hpair.rel_get_of_lt
          (a := ⟨values.idxOf r, List.idxOf_lt_length_of_mem hrValues⟩)
          (b := ⟨values.idxOf q, List.idxOf_lt_length_of_mem hq⟩)
          hrIndex
        simpa [List.getElem_idxOf
            (List.idxOf_lt_length_of_mem hrValues),
          List.getElem_idxOf (List.idxOf_lt_length_of_mem hq)] using hrel
      exact Nat.mem_primesBelow.mpr ⟨hrlt, hprime r hrValues⟩
  have hcard := Finset.card_le_card hsubset
  have hindexCard : values.idxOf q + 1 ≤ q.primeCounting' := by
    simpa [earlier, Finset.card_insert_of_notMem,
      htwoEarlier, List.toFinset_card_of_nodup hearlierNodup,
      List.length_take, Nat.min_eq_left
        (List.idxOf_lt_length_of_mem hq).le,
      Nat.primesBelow_card_eq_primeCounting'] using hcard
  calc
    Nat.nth Nat.Prime (values.idxOf q + 1) ≤
        Nat.nth Nat.Prime q.primeCounting' :=
      Nat.nth_monotone Nat.infinite_setOf_prime hindexCard
    _ = q := by
      simpa [Nat.primeCounting'] using Nat.nth_count hqPrime

/-- The universal positional prime bound specialized to the canonical joint
odd support of `p`. -/
theorem nthPrime_succ_idxOf_le_jointOddPrimeList
    (p : ℕ) {q : ℕ} (hq : q ∈ jointOddPrimeList p) :
    Nat.nth Nat.Prime ((jointOddPrimeList p).idxOf q + 1) ≤ q := by
  apply nthPrime_succ_idxOf_le_of_pairwise
    (jointOddPrimeList p)
    (Finset.sort_nodup (jointOddPrimeSupport p) (· ≤ ·))
    (jointOddPrimeList_pairwise_lt p)
  · intro prime hprime
    rcases (mem_jointOddPrimeList.mp hprime).2 with hminus | hplus
    · exact Nat.prime_of_mem_primeFactors hminus
    · exact Nat.prime_of_mem_primeFactors hplus
  · intro htwo
    exact (mem_jointOddPrimeList.mp htwo).1 rfl
  · exact hq

/-- Proof predicate for a literal prime-floor ladder, starting at prime index
`start`. -/
def primeFloorLadderValidFrom : ℕ → List ℕ → Prop
  | _, [] => True
  | start, floor :: floors =>
      floor.Prime ∧ floor.primeCounting' = start + 1 ∧
        primeFloorLadderValidFrom (start + 1) floors

/-- Executable checker corresponding to `primeFloorLadderValidFrom`. -/
def primeFloorLadderCheckFrom : ℕ → List ℕ → Bool
  | _, [] => true
  | start, floor :: floors =>
      decide floor.Prime && decide (floor.primeCounting' = start + 1) &&
        primeFloorLadderCheckFrom (start + 1) floors

@[simp] theorem primeFloorLadderCheckFrom_eq_true_iff
    (start : ℕ) (floors : List ℕ) :
    primeFloorLadderCheckFrom start floors = true ↔
      primeFloorLadderValidFrom start floors := by
  induction floors generalizing start with
  | nil => simp [primeFloorLadderCheckFrom, primeFloorLadderValidFrom]
  | cons floor floors ih =>
      simp [primeFloorLadderCheckFrom, primeFloorLadderValidFrom, ih,
        and_assoc]

private theorem primeFloorLadderValidFrom_getD
    {start : ℕ} {floors : List ℕ}
    (hvalid : primeFloorLadderValidFrom start floors)
    {index : ℕ} (hindex : index < floors.length) :
    (floors.getD index 0).Prime ∧
      (floors.getD index 0).primeCounting' = start + index + 1 := by
  induction floors generalizing start index with
  | nil => simp at hindex
  | cons floor floors ih =>
      cases index with
      | zero =>
          simpa [primeFloorLadderValidFrom] using
            And.intro hvalid.1 hvalid.2.1
      | succ index =>
          have htail : primeFloorLadderValidFrom (start + 1) floors := by
            simpa [primeFloorLadderValidFrom] using hvalid.2.2
          have hindexTail : index < floors.length := by
            simpa using hindex
          have hdata := ih htail hindexTail
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdata

/-- Literal data used to generate all rational prime-weight caps in a
positional search. -/
structure RankinPositionalCapTable where
  precision : ℕ
  oddPrimeFloors : List ℕ
  deriving DecidableEq, Repr

namespace RankinPositionalCapTable

def Valid (table : RankinPositionalCapTable) : Prop :=
  0 < table.precision ∧
    primeFloorLadderValidFrom 0 table.oddPrimeFloors

def check (table : RankinPositionalCapTable) : Bool :=
  decide (0 < table.precision) &&
    primeFloorLadderCheckFrom 0 table.oddPrimeFloors

@[simp] theorem check_eq_true_iff (table : RankinPositionalCapTable) :
    table.check = true ↔ table.Valid := by
  simp [check, Valid]

def twoCap (table : RankinPositionalCapTable) : RationalPrimeWeightCap :=
  rationalPrimeWeightCapForFloor table.precision 2

def oddCapAt (table : RankinPositionalCapTable)
    (index : ℕ) : RationalPrimeWeightCap :=
  rationalPrimeWeightCapForFloor table.precision
    (table.oddPrimeFloors.getD index 0)

theorem oddFloor_data_of_valid
    {table : RankinPositionalCapTable} (hvalid : table.Valid)
    {index : ℕ} (hindex : index < table.oddPrimeFloors.length) :
    (table.oddPrimeFloors.getD index 0).Prime ∧
      (table.oddPrimeFloors.getD index 0).primeCounting' = index + 1 := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    primeFloorLadderValidFrom_getD hvalid.2 hindex

theorem oddCapAt_lowerPrime_eq_nthPrime
    {table : RankinPositionalCapTable} (hvalid : table.Valid)
    {index : ℕ} (hindex : index < table.oddPrimeFloors.length) :
    (table.oddCapAt index).lowerPrime =
      Nat.nth Nat.Prime (index + 1) := by
  have hdata := table.oddFloor_data_of_valid hvalid hindex
  change table.oddPrimeFloors.getD index 0 =
    Nat.nth Nat.Prime (index + 1)
  calc
    table.oddPrimeFloors.getD index 0 =
        Nat.nth Nat.Prime
          (table.oddPrimeFloors.getD index 0).primeCounting' := by
      simpa [Nat.primeCounting'] using (Nat.nth_count hdata.1).symm
    _ = Nat.nth Nat.Prime (index + 1) := by rw [hdata.2]

end RankinPositionalCapTable

/-- A checked literal prime prefix covers every actual odd support whose
length fits in the table. -/
theorem positionalCanonicalRankinNeighborProfile_matches_of_capTable
    {p : ℕ} {table : RankinPositionalCapTable}
    (hvalid : table.Valid)
    (hlength : (jointOddPrimeList p).length ≤
      table.oddPrimeFloors.length)
    (rootCap : ℕ) :
    (positionalCanonicalRankinNeighborProfile p table.twoCap
      table.oddCapAt rootCap).Matches p := by
  apply canonicalRankinNeighborProfile_matches
  intro prime hprime
  have hindexActual : (jointOddPrimeList p).idxOf prime <
      (jointOddPrimeList p).length :=
    List.idxOf_lt_length_of_mem hprime
  have hindexTable : (jointOddPrimeList p).idxOf prime <
      table.oddPrimeFloors.length := hindexActual.trans_le hlength
  change (table.oddCapAt ((jointOddPrimeList p).idxOf prime)).lowerPrime ≤ prime
  rw [table.oddCapAt_lowerPrime_eq_nthPrime hvalid hindexTable]
  exact nthPrime_succ_idxOf_le_jointOddPrimeList p hprime

private theorem idxOf_lt_idxOf_of_pairwise_lt
    (values : List ℕ) (hpair : values.Pairwise (· < ·))
    {left right : ℕ} (hleft : left ∈ values) (hright : right ∈ values)
    (hlr : left < right) :
    values.idxOf left < values.idxOf right := by
  have hindexNe : values.idxOf left ≠ values.idxOf right := by
    intro heq
    have hvalueEq : left = right := (List.idxOf_inj hleft).mp heq
    exact hvalueEq.not_lt hlr
  have hnotReverse : ¬values.idxOf right < values.idxOf left := by
    intro hreverse
    have hrel := hpair.rel_get_of_lt
      (a := ⟨values.idxOf right, List.idxOf_lt_length_of_mem hright⟩)
      (b := ⟨values.idxOf left, List.idxOf_lt_length_of_mem hleft⟩)
      hreverse
    have hrightLeft : right < left := by
      simpa [List.getElem_idxOf
          (List.idxOf_lt_length_of_mem hright),
        List.getElem_idxOf (List.idxOf_lt_length_of_mem hleft)] using hrel
    exact hlr.asymm hrightLeft
  omega

theorem jointOddPrimeList_pairwise_positionalCapFloor_lt
    {p : ℕ} {table : RankinPositionalCapTable}
    (hvalid : table.Valid)
    (hlength : (jointOddPrimeList p).length ≤
      table.oddPrimeFloors.length) :
    (jointOddPrimeList p).Pairwise fun left right =>
      (table.oddCapAt ((jointOddPrimeList p).idxOf left)).lowerPrime <
        (table.oddCapAt ((jointOddPrimeList p).idxOf right)).lowerPrime := by
  apply (jointOddPrimeList_pairwise_lt p).imp_of_mem
  intro left right hleft hright hlr
  have hleftIndex : (jointOddPrimeList p).idxOf left <
      table.oddPrimeFloors.length :=
    (List.idxOf_lt_length_of_mem hleft).trans_le hlength
  have hrightIndex : (jointOddPrimeList p).idxOf right <
      table.oddPrimeFloors.length :=
    (List.idxOf_lt_length_of_mem hright).trans_le hlength
  rw [table.oddCapAt_lowerPrime_eq_nthPrime hvalid hleftIndex,
    table.oddCapAt_lowerPrime_eq_nthPrime hvalid hrightIndex]
  apply Nat.nth_strictMono Nat.infinite_setOf_prime
  exact Nat.add_lt_add_right
    (idxOf_lt_idxOf_of_pairwise_lt (jointOddPrimeList p)
      (jointOddPrimeList_pairwise_lt p) hleft hright hlr) 1

/-- The table also supplies every structural validity condition for the
actual positional profile.  The only profile-dependent root obligation is
stated on the side-erased exponent skeleton that the finite search checks. -/
theorem positionalCanonicalRankinNeighborProfile_valid_of_capTable
    {p rootCap : ℕ} {table : RankinPositionalCapTable}
    (hpPrime : p.Prime) (hpTwo : 2 < p)
    (hvalid : table.Valid)
    (hlength : (jointOddPrimeList p).length ≤
      table.oddPrimeFloors.length)
    (hrootPos : 0 < rootCap)
    (hjointRoot :
      RankinNeighborProfile.JointEnvelopeValid
        (positionalRankinSkeletonProfile table.twoCap table.oddCapAt
          ((p - 1).factorization 2) ((p + 1).factorization 2)
          (actualOddExponentSkeleton p) rootCap)) :
    (positionalCanonicalRankinNeighborProfile p table.twoCap
      table.oddCapAt rootCap).Valid := by
  apply canonicalRankinNeighborProfile_valid_of_jointEnvelope
    hpPrime hpTwo
  · exact rationalPrimeWeightCapForFloor_valid hvalid.1 (by norm_num)
  · rfl
  · intro prime hprime
    have hindexActual : (jointOddPrimeList p).idxOf prime <
        (jointOddPrimeList p).length :=
      List.idxOf_lt_length_of_mem hprime
    have hindexTable : (jointOddPrimeList p).idxOf prime <
        table.oddPrimeFloors.length := hindexActual.trans_le hlength
    have hdata := table.oddFloor_data_of_valid hvalid hindexTable
    change (table.oddCapAt ((jointOddPrimeList p).idxOf prime)).Valid ∧
      (table.oddCapAt
        ((jointOddPrimeList p).idxOf prime)).lowerPrime.Prime ∧
      3 ≤ (table.oddCapAt
        ((jointOddPrimeList p).idxOf prime)).lowerPrime
    refine ⟨?_, ?_, ?_⟩
    · exact rationalPrimeWeightCapForFloor_valid hvalid.1 hdata.1.pos
    · exact hdata.1
    · rw [table.oddCapAt_lowerPrime_eq_nthPrime hvalid hindexTable]
      have hbound := Nat.add_two_le_nth_prime
        ((jointOddPrimeList p).idxOf prime + 1)
      omega
  · exact jointOddPrimeList_pairwise_positionalCapFloor_lt hvalid hlength
  · exact hrootPos
  · apply (RankinNeighborProfile.eraseSides_jointEnvelopeValid_iff _).mp
    change (positionalCanonicalRankinNeighborProfile p table.twoCap
      table.oddCapAt rootCap).eraseSides.JointEnvelopeValid
    rw [eraseSides_positionalCanonicalRankinNeighborProfile]
    exact hjointRoot

end BGS.NumberTheory
