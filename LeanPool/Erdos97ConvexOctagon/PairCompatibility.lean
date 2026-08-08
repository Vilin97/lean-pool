/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.FiniteModel

/-! # Pair-sparsity guard for direct incidence-table search -/

namespace Erdos97Octagon.RawIncidence

/-- Number of processed row masks containing both vertices. -/
def pairCount
    (assignments : List (Vertex × UInt64)) (a b : Vertex) : ℕ :=
  (assignments.filter fun previous =>
    bitSetB previous.2 a.val && bitSetB previous.2 b.val).length

/-- Boolean guard that prevents a new row from making any pair occur three times. -/
def pairCompatibleB
    (assignments : List (Vertex × UInt64)) (row : UInt64) : Bool :=
  (((List.finRange 8).sublistsLen 2).reverse).all fun pair =>
    match pair with
    | [a, b] => !(bitSetB row a.val && bitSetB row b.val) ||
        decide (pairCount assignments a b < 2)
    | _ => false

/-- The processed-row count of a pair is bounded by its full incidence multiplicity. -/
theorem pairCount_le_pairMultiplicity
    (Q : OctagonIncidence) (assignments : List (Vertex × UInt64))
    (a b : Vertex)
    (hcentres : (assignments.map Prod.fst).Nodup)
    (hrows : ∀ centre row, (centre, row) ∈ assignments →
      Q.targets centre = packedRow row) :
    pairCount assignments a b ≤ Q.pairMultiplicity a b := by
  let matchingCentres :=
    (assignments.filter fun previous =>
      bitSetB previous.2 a.val && bitSetB previous.2 b.val).map Prod.fst
  have hmatchingSublist : matchingCentres.Sublist (assignments.map Prod.fst) := by
    exact List.filter_sublist.map _
  have hmatchingNodup : matchingCentres.Nodup :=
    hcentres.sublist hmatchingSublist
  have hcard : matchingCentres.toFinset.card ≤ Q.pairMultiplicity a b := by
    rw [OctagonIncidence.pairMultiplicity, Finset.sum_boole]
    apply Finset.card_le_card
    intro centre hcentre
    simp only [matchingCentres, List.mem_toFinset, List.mem_map] at hcentre
    obtain ⟨assignment, hassignment, hcentre⟩ := hcentre
    subst centre
    have hparts := List.mem_filter.mp hassignment
    have hbits :
        bitSetB assignment.2 a.val = true ∧
          bitSetB assignment.2 b.val = true := by
      simpa only [Bool.and_eq_true] using hparts.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rw [hrows assignment.1 assignment.2 hparts.1, mem_packedRow]
      exact hbits.1
    · rw [hrows assignment.1 assignment.2 hparts.1, mem_packedRow]
      exact hbits.2
  rw [List.toFinset_card_of_nodup hmatchingNodup] at hcard
  simpa only [matchingCentres, List.length_map, pairCount] using hcard

private theorem vertexPairs_shape {pair : List Vertex}
    (hpair : pair ∈ ((List.finRange 8).sublistsLen 2).reverse) :
    ∃ a b, pair = [a, b] ∧ a ≠ b := by
  revert pair
  decide

/-- Pair sparsity makes the direct-search pair guard accept the actual next row. -/
theorem pairCompatibleB_of_pairSparse
    (Q : OctagonIncidence) (hSparse : Q.PairSparse)
    (assignments : List (Vertex × UInt64))
    (nextCentre : Vertex) (nextMask : UInt64)
    (hcentres : (nextCentre :: assignments.map Prod.fst).Nodup)
    (hrows : ∀ centre row, (centre, row) ∈ assignments →
      Q.targets centre = packedRow row)
    (hnext : Q.targets nextCentre = packedRow nextMask) :
    pairCompatibleB assignments nextMask = true := by
  rw [pairCompatibleB, List.all_eq_true]
  intro pair hpair
  obtain ⟨a, b, rfl, hab⟩ := vertexPairs_shape hpair
  by_cases hselected :
      (bitSetB nextMask a.val && bitSetB nextMask b.val) = true
  · have hextendedRows : ∀ centre row,
        (centre, row) ∈ (nextCentre, nextMask) :: assignments →
          Q.targets centre = packedRow row := by
      intro centre row hmember
      simp only [List.mem_cons, Prod.mk.injEq] at hmember
      rcases hmember with hnew | hprevious
      · rcases hnew with ⟨rfl, rfl⟩
        exact hnext
      · exact hrows centre row hprevious
    have hextendedCentres :
        (((nextCentre, nextMask) :: assignments).map Prod.fst).Nodup := by
      simpa using hcentres
    have hcount := pairCount_le_pairMultiplicity Q
      ((nextCentre, nextMask) :: assignments) a b
      hextendedCentres hextendedRows
    have hmultiplicity := hSparse hab
    have hcountEq :
        pairCount ((nextCentre, nextMask) :: assignments) a b =
          pairCount assignments a b + 1 := by
      simp [pairCount, hselected, Nat.add_comm]
    rw [hcountEq] at hcount
    have hlt : pairCount assignments a b < 2 := by
      omega
    simp [hselected, hlt]
  · have hfalse :
        (bitSetB nextMask a.val && bitSetB nextMask b.val) = false :=
      Bool.eq_false_of_not_eq_true hselected
    simp [hfalse]

/-- The pair guard accepts the next row of a prefix partitioning all eight centres. -/
theorem pairCompatibleB_of_pairSparse_prefix
    (Q : OctagonIncidence) (hSparse : Q.PairSparse)
    (assignments : List (Vertex × UInt64))
    (nextCentre : Vertex) (remaining : List Vertex) (nextMask : UInt64)
    (hcentres : assignments.map Prod.fst ++ nextCentre :: remaining =
      List.finRange 8)
    (hrows : ∀ centre row, (centre, row) ∈ assignments →
      Q.targets centre = packedRow row)
    (hnext : Q.targets nextCentre = packedRow nextMask) :
    pairCompatibleB assignments nextMask = true := by
  have hallCentres :
      (assignments.map Prod.fst ++ nextCentre :: remaining).Nodup := by
    rw [hcentres]
    exact List.nodup_finRange 8
  have hprocessed : (assignments.map Prod.fst).Nodup :=
    hallCentres.of_append_left
  have hnextFresh : nextCentre ∉ assignments.map Prod.fst := by
    intro hmember
    exact hallCentres.disjoint hmember (by simp)
  apply pairCompatibleB_of_pairSparse Q hSparse assignments nextCentre nextMask
  · exact List.nodup_cons.mpr ⟨hnextFresh, hprocessed⟩
  · exact hrows
  · exact hnext

end Erdos97Octagon.RawIncidence
