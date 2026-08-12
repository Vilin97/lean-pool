/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CodeStateExactness
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateLookup
import LeanPool.Erdos97ConvexOctagon.CoverageCertificateSupportSoundness

/-! # Semantic consequences of compact coverage certificates -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Every stored assignment agrees with the corresponding mathematical row. -/
def AssignmentsMatch
    (Q : OctagonIncidence) (assignments : List RowAssignment) : Prop :=
  ∀ centre row, (centre, row) ∈ assignments →
    Q.targets centre = packedRow row

/-- Prepending a matching row preserves semantic assignment agreement. -/
theorem AssignmentsMatch.cons
    {Q : OctagonIncidence} {assignments : List RowAssignment}
    (hmatch : AssignmentsMatch Q assignments)
    (centre : Vertex) (row : UInt64)
    (hrow : Q.targets centre = packedRow row) :
    AssignmentsMatch Q ((centre, row) :: assignments) := by
  intro centre' row' hassignment
  rcases List.mem_cons.mp hassignment with hnew | hprevious
  · simp only [Prod.mk.injEq] at hnew
    rcases hnew with ⟨rfl, rfl⟩
    exact hrow
  · exact hmatch centre' row' hprevious

/-- A selected bit in matching assignments is a mathematical incidence. -/
theorem selectedByAssignmentsB_sound
    {Q : OctagonIncidence} {assignments : List RowAssignment}
    (hassignments : AssignmentsMatch Q assignments)
    {centre target : Vertex}
    (hselected : selectedByAssignmentsB assignments centre target = true) :
    target ∈ Q.targets centre := by
  simp only [selectedByAssignmentsB, List.any_eq_true] at hselected
  obtain ⟨assignment, hassignment, hselected⟩ := hselected
  have hparts : assignment.1 = centre ∧
      bitSetB assignment.2 target.val = true := by
    simpa only [Bool.and_eq_true, beq_iff_eq] using hselected
  rcases assignment with ⟨centre', row⟩
  simp only at hparts
  rw [← hparts.1, hassignments centre' row hassignment, mem_packedRow]
  exact hparts.2

/-- A mathematical incidence is selected when its centre occurs in matching assignments. -/
theorem selectedByAssignmentsB_complete_of_mem
    {Q : OctagonIncidence} {assignments : List RowAssignment}
    (hassignments : AssignmentsMatch Q assignments)
    {centre target : Vertex} (hcentre : centre ∈ assignments.map Prod.fst)
    (hselected : target ∈ Q.targets centre) :
    selectedByAssignmentsB assignments centre target = true := by
  rw [List.mem_map] at hcentre
  obtain ⟨assignment, hassignment, hcentre⟩ := hcentre
  rcases assignment with ⟨centre', row⟩
  simp only at hcentre
  subst centre'
  have hbit : bitSetB row target.val = true := by
    rw [← mem_packedRow, ← hassignments centre row hassignment]
    exact hselected
  simp only [selectedByAssignmentsB, List.any_eq_true]
  exact ⟨(centre, row), hassignment, by simp [hbit]⟩

private theorem assignmentColumnCount_eq_filter_length
    {Q : OctagonIncidence} {assignments : List RowAssignment}
    (hassignments : AssignmentsMatch Q assignments) (target : Vertex) :
    assignmentColumnCount assignments target =
      ((assignments.map Prod.fst).filter fun centre =>
        target ∈ Q.targets centre).length := by
  induction assignments with
  | nil => rfl
  | cons assignment assignments induction =>
      rcases assignment with ⟨centre, row⟩
      have hrow := hassignments centre row (by simp)
      have htail : AssignmentsMatch Q assignments := by
        intro centre' row' hmember
        exact hassignments centre' row' (by simp [hmember])
      have hinduction := induction htail
      by_cases hbit : bitSetB row target.val = true
      · have htarget : target ∈ Q.targets centre := by
          rw [hrow, mem_packedRow]
          exact hbit
        simpa [assignmentColumnCount, hbit, htarget] using
          congrArg Nat.succ hinduction
      · have htarget : target ∉ Q.targets centre := by
          intro htarget
          apply hbit
          rw [← mem_packedRow, ← hrow]
          exact htarget
        simpa [assignmentColumnCount, hbit, htarget] using hinduction

private theorem finRange_filter_length_eq_indegree
    (Q : OctagonIncidence) (target : Vertex) :
    ((List.finRange 8).filter fun centre =>
      target ∈ Q.targets centre).length = Q.indegree target := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 8).filter _)]
  simp only [List.toFinset_filter, List.toFinset_finRange]
  unfold OctagonIncidence.indegree
  rw [Finset.sum_boole]
  norm_num

private theorem remaining_selected_le_capacity
    (Q : OctagonIncidence) (remaining : List Vertex) (target : Vertex) :
    ((remaining.filter fun centre => target ∈ Q.targets centre).length ≤
      (remaining.filter (· ≠ target)).length) := by
  induction remaining with
  | nil => simp
  | cons centre remaining induction =>
      by_cases hselected : target ∈ Q.targets centre
      · have hne : centre ≠ target := by
          intro hequal
          subst centre
          exact Q.centre_not_mem target hselected
        have hselectedB := decide_eq_true hselected
        have hneB := decide_eq_true hne
        simp only [List.filter_cons, hselectedB, hneB, ite_true,
          List.length_cons]
        exact Nat.succ_le_succ induction
      · by_cases hne : centre ≠ target
        · have hselectedB := decide_eq_false hselected
          have hneB := decide_eq_true hne
          simp only [List.filter_cons, hselectedB, hneB, ite_true,
            List.length_cons]
          exact Nat.le_succ_of_le induction
        · have hselectedB := decide_eq_false hselected
          have hneB := decide_eq_false hne
          simp only [List.filter_cons, hselectedB, hneB]
          exact induction

/-- Balanced incidence tables satisfy both semantic column bounds on a prefix. -/
theorem assignmentColumnBounds
    (Q : OctagonIncidence) (hBalanced : Q.Balanced)
    {assignments : List RowAssignment} {remaining : List Vertex}
    (hcentres : (assignments.map Prod.fst ++ remaining).Perm
      (List.finRange 8))
    (hassignments : AssignmentsMatch Q assignments) (target : Vertex) :
    assignmentColumnCount assignments target ≤ 4 ∧
      4 ≤ assignmentColumnCount assignments target +
        remainingColumnCapacity remaining target := by
  have hfiltered := hcentres.filter (fun centre => target ∈ Q.targets centre)
  have hdecomposition :
      ((assignments.map Prod.fst).filter fun centre =>
          target ∈ Q.targets centre).length +
        (remaining.filter fun centre => target ∈ Q.targets centre).length =
        ((List.finRange 8).filter fun centre =>
          target ∈ Q.targets centre).length := by
    simpa only [List.filter_append, List.length_append] using hfiltered.length_eq
  have hsum : assignmentColumnCount assignments target +
      (remaining.filter fun centre => target ∈ Q.targets centre).length = 4 := by
    rw [assignmentColumnCount_eq_filter_length hassignments]
    calc
      _ = ((List.finRange 8).filter fun centre =>
          target ∈ Q.targets centre).length := hdecomposition
      _ = Q.indegree target := finRange_filter_length_eq_indegree Q target
      _ = 4 := hBalanced target
  have hremaining := remaining_selected_le_capacity Q remaining target
  constructor
  · omega
  · unfold remainingColumnCapacity
    omega

/-- Pair sparsity accepts the actual next row of any permuted prefix. -/
theorem pairCompatibleB_of_pairSparse_perm
    (Q : OctagonIncidence) (hSparse : Q.PairSparse)
    {assignments : List RowAssignment} {centre : Vertex}
    {remaining : List Vertex} {row : UInt64}
    (hcentres : (assignments.map Prod.fst ++ centre :: remaining).Perm
      (List.finRange 8))
    (hassignments : AssignmentsMatch Q assignments)
    (hrow : Q.targets centre = packedRow row) :
    pairCompatibleB assignments row = true := by
  have hallCentres : (assignments.map Prod.fst ++ centre :: remaining).Nodup :=
    (List.Perm.nodup_iff hcentres).mpr (List.nodup_finRange 8)
  have hprocessed : (assignments.map Prod.fst).Nodup :=
    hallCentres.of_append_left
  have hcentreFresh : centre ∉ assignments.map Prod.fst := by
    intro hmember
    exact hallCentres.disjoint hmember (by simp)
  exact pairCompatibleB_of_pairSparse Q hSparse assignments centre row
    (List.nodup_cons.mpr ⟨hcentreFresh, hprocessed⟩) hassignments hrow

/-- A valid monotone summary contradicts the realised convex configuration. -/
theorem impossible_of_patternSummary
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    {code : UInt64} {assignments : List RowAssignment}
    {summary : PatternSummary}
    (hassignments : AssignmentsMatch Q assignments)
    (hcodeExact : CodeMatches code assignments)
    (hsummary : summary.Valid)
    (hmatch : ((summary.mask &&& code) == summary.mask) = true) : False := by
  obtain ⟨entry, _horigin, hmask, hvalidB⟩ := hsummary
  have hextendsSummary := hcodeExact.extends_of_subset
    (fun centre target hselected =>
      selectedByAssignmentsB_sound hassignments hselected) hmatch
  have hextends : Extends (packedIncidence entry.mask) Q.targets := by
    simpa only [hmask] using hextendsSummary
  have hvalid := PatternEntry.valid_of_validB hvalidB
  exact Certificate.not_convex_realises entry.certificate.toCertificate
    (entry.certificate.valid_mono hextends hvalid) hC hR

/-- A valid exact summary contradicts the realised convex configuration. -/
theorem impossible_of_hardSummary
    {p : Vertex → Plane} {Q : OctagonIncidence}
    (hC : ConvexIndependent ℝ p) (hR : Realises p Q)
    {code : UInt64} {assignments : List RowAssignment}
    {summary : HardSummary}
    (hcentres : (assignments.map Prod.fst).Perm (List.finRange 8))
    (hassignments : AssignmentsMatch Q assignments)
    (hcodeExact : CodeMatches code assignments)
    (hsummary : summary.Valid)
    (hmatch : (summary.code == code) = true) : False := by
  obtain ⟨entry, _horigin, hcode, hvalidB⟩ := hsummary
  have htargetsSummary : Q.targets = packedIncidence summary.code :=
    hcodeExact.table_eq_of_code_eq
      (fun centre target hselected =>
        selectedByAssignmentsB_sound hassignments hselected)
      (fun centre target htarget =>
        selectedByAssignmentsB_complete_of_mem hassignments
          (hcentres.mem_iff.mpr (List.mem_finRange centre)) htarget)
      hmatch
  have htargets : Q.targets = packedIncidence entry.code := by
    simpa only [hcode] using htargetsSummary
  have hcertificate : entry.certificate.Valid Q.targets := by
    rw [htargets]
    exact HardEntry.valid_of_validB hvalidB
  exact Certificate.not_convex_realises entry.certificate hcertificate hC hR

private theorem bitSetB_eq_getLsbD (code : UInt64) (index : Fin 64) :
    bitSetB code index.val = code.toBitVec.getLsbD index.val := by
  unfold bitSetB
  have hmasked :
      ((code >>> UInt64.ofNat index.val) &&& 1).toBitVec =
        (BitVec.ofBool (code.toBitVec.getLsbD index.val)).setWidth 64 := by
    rw [UInt64.toBitVec_and, UInt64.toBitVec_shiftRight,
      UInt64.toBitVec_one, BitVec.and_one_eq_setWidth_ofBool_getLsbD]
    change (BitVec.ofBool ((code.toBitVec >>>
      ((UInt64.ofNat index.val).toBitVec % 64).toNat).getLsbD 0)).setWidth 64 =
      (BitVec.ofBool (code.toBitVec.getLsbD index.val)).setWidth 64
    rw [BitVec.getLsbD_ushiftRight]
    congr 3
    simp [index.isLt]
  cases hbit : code.toBitVec.getLsbD index.val with
  | false =>
      have hzero : (code >>> UInt64.ofNat index.val) &&& 1 = 0 := by
        apply UInt64.toBitVec_inj.mp
        rw [hmasked, hbit]
        decide
      simp [hzero]
  | true =>
      have hone : (code >>> UInt64.ofNat index.val) &&& 1 = 1 := by
        apply UInt64.toBitVec_inj.mp
        rw [hmasked, hbit]
        decide
      simp [hone]

/-- Reading a packed row preserves every one of its eight incidence bits. -/
theorem rowFromCode_bit (code : UInt64) (centre target : Vertex) :
    bitSetB (rowFromCode code centre) target.val =
      bitSetB code (varIndex centre target) := by
  let rowIndex : Fin 64 := ⟨target.val, by omega⟩
  let codeIndex : Fin 64 := ⟨varIndex centre target, by
    unfold varIndex
    omega⟩
  rw [show target.val = rowIndex.val by rfl,
    bitSetB_eq_getLsbD (rowFromCode code centre) rowIndex]
  rw [show varIndex centre target = codeIndex.val by rfl,
    bitSetB_eq_getLsbD code codeIndex]
  unfold rowFromCode
  simp only [UInt64.toBitVec_and, BitVec.getLsbD_and,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat,
    BitVec.getLsbD_ofNat]
  have hshift : ((UInt64.ofNat (8 * centre.val)).toBitVec % 64).toNat =
      8 * centre.val := by
    simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : 8 * centre.val < 64)]
  change ((code.toBitVec >>>
      ((UInt64.ofNat (8 * centre.val)).toBitVec % 64).toNat).getLsbD
        rowIndex.val &&
      (decide (rowIndex.val < 64) && Nat.testBit 255 rowIndex.val)) =
    code.toBitVec.getLsbD codeIndex.val
  rw [BitVec.getLsbD_ushiftRight, hshift]
  have hmask :
      (decide (rowIndex.val < 64) && Nat.testBit 255 rowIndex.val) = true := by
    change (decide (target.val < 64) && Nat.testBit (2 ^ 8 - 1) target.val) = true
    rw [Nat.testBit_two_pow_sub_one]
    simp [target.isLt, show target.val < 64 by omega]
  rw [hmask, Bool.and_true]
  congr 2

/-- Exact packed code semantics reconstructs rows matching every assigned centre. -/
theorem assignmentsFromCode_match
    {Q : OctagonIncidence} {code : UInt64}
    {assignments : List RowAssignment} {depth : Nat}
    (hcentres : (assignments.map Prod.fst).Perm (assignedCentres depth))
    (hassignments : AssignmentsMatch Q assignments)
    (hcode : CodeMatches code assignments) :
    AssignmentsMatch Q (assignmentsFromCode code depth) := by
  intro centre row hmember
  simp only [assignmentsFromCode, List.mem_map] at hmember
  obtain ⟨sourceCentre, hsource, hassignment⟩ := hmember
  simp only [Prod.mk.injEq] at hassignment
  rcases hassignment with ⟨rfl, rfl⟩
  have hcentre : sourceCentre ∈ assignments.map Prod.fst :=
    hcentres.mem_iff.mpr hsource
  ext target
  rw [mem_packedRow, rowFromCode_bit, hcode]
  constructor
  · exact selectedByAssignmentsB_complete_of_mem hassignments hcentre
  · exact selectedByAssignmentsB_sound hassignments

/-- Search-centre suffixes expose the current centre followed by the next suffix. -/
theorem searchCentres_drop_eq_cons
    (depth : Nat) (hdepth : depth < searchCentres.length) :
    searchCentres.drop depth =
      searchCentres.getD depth 0 :: searchCentres.drop (depth + 1) := by
  change depth < 5 at hdepth
  interval_cases depth <;> rfl

/-- Assigned centres followed by the search suffix enumerate all eight centres. -/
theorem assignedCentres_remaining_perm
    (depth : Nat) (hdepth : depth ≤ searchCentres.length) :
    (assignedCentres depth ++ searchCentres.drop depth).Perm
      (List.finRange 8) := by
  change depth ≤ 5 at hdepth
  interval_cases depth <;> decide

/-- Prepending the current search centre advances the assigned-centre prefix. -/
theorem nextAssignedCentres_perm
    (depth : Nat) (hdepth : depth < searchCentres.length) :
    (searchCentres.getD depth 0 :: assignedCentres depth).Perm
      (assignedCentres (depth + 1)) := by
  change depth < 5 at hdepth
  interval_cases depth <;> decide

/-- Reconstructed prefixes and the remaining search suffix cover all centres. -/
theorem reconstructedCentres_perm
    (code row : UInt64) (depth : Nat)
    (hdepth : depth < searchCentres.length) :
    (((searchCentres.getD depth 0, row) ::
        assignmentsFromCode code depth).map Prod.fst ++
      searchCentres.drop (depth + 1)).Perm (List.finRange 8) := by
  change depth < 5 at hdepth
  simp only [assignmentsFromCode, List.map_cons, List.map_map,
    Function.comp_def]
  interval_cases depth <;> decide

private theorem standardTargets_eq_packedRow :
    standardTargets = packedRow 30 := by
  ext target
  fin_cases target <;> decide

/-- The normalized zeroth row and a canonical first row match the initial prefix. -/
theorem initialAssignmentsMatch
    {Q : OctagonIncidence} (hN : Q.Normalized) (orbit : Fin 7)
    (hrowOne : Q.targets 1 = packedRow (canonicalRowMask orbit)) :
    AssignmentsMatch Q [(1, canonicalRowMask orbit), (0, 30)] := by
  have hempty : AssignmentsMatch Q [] := by
    intro centre row hmember
    simp at hmember
  have hrowZero : Q.targets 0 = packedRow 30 :=
    hN.trans standardTargets_eq_packedRow
  exact (hempty.cons 0 30 hrowZero).cons
    1 (canonicalRowMask orbit) hrowOne

/-- The packed two-row code exactly denotes the normalized canonical prefix. -/
theorem initialCodeMatches (orbit : Fin 7) :
    CodeMatches
      (addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1)
      [(1, canonicalRowMask orbit), (0, 30)] := by
  exact (CodeMatches.empty.add 0 30).add 1 (canonicalRowMask orbit)

/-- Adding the indexed second row preserves semantic agreement with the prefix. -/
theorem initialAssignmentsMatchThree
    {Q : OctagonIncidence} (hN : Q.Normalized) (orbit : Fin 7)
    (hrowOne : Q.targets 1 = packedRow (canonicalRowMask orbit))
    (rowTwo : Fin 35)
    (hrowTwo : Q.targets 2 = packedRow (rowTwoMask rowTwo)) :
    AssignmentsMatch Q
      [(2, rowTwoMask rowTwo), (1, canonicalRowMask orbit), (0, 30)] := by
  exact (initialAssignmentsMatch hN orbit hrowOne).cons
    2 (rowTwoMask rowTwo) hrowTwo

/-- The packed three-row root code exactly denotes the fixed branch prefix. -/
theorem initialCodeMatchesThree (orbit : Fin 7) (rowTwo : Fin 35) :
    CodeMatches
      (addRowCode
        (addRowCode (addRowCode 0 30 0) (canonicalRowMask orbit) 1)
        (rowTwoMask rowTwo) 2)
      [(2, rowTwoMask rowTwo), (1, canonicalRowMask orbit), (0, 30)] := by
  exact (initialCodeMatches orbit).add 2 (rowTwoMask rowTwo)

/-- The packed three-row pair state exactly denotes the fixed branch prefix. -/
theorem initialPairStateExactThree (orbit : Fin 7) (rowTwo : Fin 35) :
    let choice0 := searchChoiceForRow 0 30
    let choice1 := searchChoiceForRow 1 (canonicalRowMask orbit)
    let choice2 := searchChoiceForRow 2 (rowTwoMask rowTwo)
    (((PairState.empty.add choice0.pairMask).add choice1.pairMask).add
      choice2.pairMask).Exact
        [(2, rowTwoMask rowTwo), (1, canonicalRowMask orbit), (0, 30)] := by
  let choice0 := searchChoiceForRow 0 30
  let choice1 := searchChoiceForRow 1 (canonicalRowMask orbit)
  let choice2 := searchChoiceForRow 2 (rowTwoMask rowTwo)
  have hexact0 := PairState.empty_exact.add 0 30 choice0.pairMask
    (by simpa only [choice0] using searchChoiceForRow_zero_pairMask)
  have hexact1 := hexact0.add 1 (canonicalRowMask orbit) choice1.pairMask
    (by simpa only [choice1] using searchChoiceForRow_canonical_pairMask orbit)
  exact hexact1.add 2 (rowTwoMask rowTwo) choice2.pairMask
    (by simpa only [choice2] using searchChoiceForRow_two_pairMask rowTwo)

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
