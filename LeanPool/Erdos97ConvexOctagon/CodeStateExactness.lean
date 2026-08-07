/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.Certificates
import LeanPool.Erdos97ConvexOctagon.CoverageSearchCore

/-! # Exactness of packed incidence-table prefixes -/

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

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

private theorem varIndex_lt (centre target : Vertex) :
    varIndex centre target < 64 := by
  unfold varIndex
  omega

@[simp] private theorem bitSetB_or
    (left right : UInt64) (index : Fin 64) :
    bitSetB (left ||| right) index.val =
      (bitSetB left index.val || bitSetB right index.val) := by
  simp only [bitSetB_eq_getLsbD]
  simp

@[simp] private theorem bitSetB_and
    (left right : UInt64) (index : Fin 64) :
    bitSetB (left &&& right) index.val =
      (bitSetB left index.val && bitSetB right index.val) := by
  simp only [bitSetB_eq_getLsbD]
  simp

@[simp] private theorem bitSetB_or_at
    (left right : UInt64) (centre target : Vertex) :
    bitSetB (left ||| right) (varIndex centre target) =
      (bitSetB left (varIndex centre target) ||
        bitSetB right (varIndex centre target)) := by
  let index : Fin 64 := ⟨varIndex centre target, varIndex_lt centre target⟩
  simpa only [index] using bitSetB_or left right index

private theorem maskedRow_getLsbD (row : UInt64) (index : Nat) :
    (row &&& 255).toBitVec.getLsbD index =
      (row.toBitVec.getLsbD index && decide (index < 8)) := by
  rw [UInt64.toBitVec_and, BitVec.getLsbD_and, UInt64.toBitVec_ofNat,
    BitVec.getLsbD_ofNat]
  change (row.toBitVec.getLsbD index &&
      (decide (index < 64) && Nat.testBit (2 ^ 8 - 1) index)) = _
  rw [Nat.testBit_two_pow_sub_one]
  by_cases hindex : index < 8
  · have hwide : index < 64 := by omega
    simp [hindex, hwide]
  · simp [hindex]

private theorem shiftAmount (shift : Fin 64) :
    ((UInt64.ofNat shift.val).toBitVec % 64).toNat = shift.val := by
  simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt shift.isLt]

private theorem bitSetB_shiftLeft
    (value : UInt64) (shift index : Fin 64) :
    bitSetB (value <<< UInt64.ofNat shift.val) index.val =
      (!decide (index.val < shift.val) &&
        bitSetB value (index.val - shift.val)) := by
  let difference : Fin 64 :=
    ⟨index.val - shift.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) index.isLt⟩
  rw [bitSetB_eq_getLsbD, UInt64.toBitVec_shiftLeft,
    BitVec.getLsbD_shiftLeft', shiftAmount]
  simp only [index.isLt, decide_true, Bool.true_and]
  rw [← bitSetB_eq_getLsbD value difference]

private theorem bitSetB_mask255 (row : UInt64) (index : Fin 64) :
    bitSetB (row &&& 255) index.val =
      (bitSetB row index.val && decide (index.val < 8)) := by
  simp only [bitSetB_eq_getLsbD, maskedRow_getLsbD]

private theorem shiftedRow_bit
    (row : UInt64) (rowCentre centre target : Vertex) :
    bitSetB ((row &&& 255) <<< UInt64.ofNat (8 * rowCentre.val))
        (varIndex centre target) =
      (decide (rowCentre = centre) && bitSetB row target.val) := by
  let shift : Fin 64 := ⟨8 * rowCentre.val, by omega⟩
  let index : Fin 64 :=
    ⟨varIndex centre target, varIndex_lt centre target⟩
  let difference : Fin 64 :=
    ⟨index.val - shift.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) index.isLt⟩
  rw [show UInt64.ofNat (8 * rowCentre.val) = UInt64.ofNat shift.val by rfl]
  change bitSetB ((row &&& 255) <<< UInt64.ofNat shift.val) index.val = _
  rw [bitSetB_shiftLeft]
  change (!decide (index.val < shift.val) &&
    bitSetB (row &&& 255) difference.val) = _
  rw [bitSetB_mask255]
  by_cases hequal : rowCentre = centre
  · subst centre
    simp only [decide_true, Bool.true_and]
    have hnotLess : ¬index.val < shift.val := by
      simp only [index, shift, varIndex]
      omega
    have hdifference : difference.val = target.val := by
      simp only [difference, index, shift, varIndex]
      omega
    simp [hnotLess, hdifference, target.isLt]
  · have hvalues : rowCentre.val ≠ centre.val := by
      intro hvalues
      exact hequal (Fin.ext hvalues)
    rcases lt_or_gt_of_ne hvalues with hless | hgreater
    · have hfar : 8 ≤ difference.val := by
        simp only [difference, index, shift, varIndex]
        omega
      simp [hequal, show ¬difference.val < 8 by omega]
    · have hbefore : index.val < shift.val := by
        simp only [index, shift, varIndex]
        omega
      simp [hequal, hbefore]

/-- A packed table code exactly records all selected bits in its assignment list. -/
def CodeMatches (code : UInt64) (assignments : List RowAssignment) : Prop :=
  ∀ centre target,
    bitSetB code (varIndex centre target) =
      selectedByAssignmentsB assignments centre target

/-- The zero code exactly represents the empty assignment list. -/
theorem CodeMatches.empty : CodeMatches 0 [] := by
  intro centre target
  let index : Fin 64 :=
    ⟨varIndex centre target, varIndex_lt centre target⟩
  change bitSetB 0 index.val = false
  rw [bitSetB_eq_getLsbD]
  simp

/-- Adding a masked row preserves exact packed-code semantics. -/
theorem CodeMatches.add
    {code : UInt64} {assignments : List RowAssignment}
    (hexact : CodeMatches code assignments) (rowCentre : Vertex) (row : UInt64) :
    CodeMatches (addRowCode code row rowCentre)
      ((rowCentre, row) :: assignments) := by
  intro centre target
  rw [addRowCode, bitSetB_or_at, shiftedRow_bit, hexact]
  simp only [selectedByAssignmentsB, List.any_cons]
  rw [Bool.or_comm]
  have hequal : decide (rowCentre = centre) = (rowCentre == centre) := by
    apply Bool.eq_iff_iff.mpr
    simp
  rw [hequal]

/-- Exact code semantics are invariant under reordering the assignment list. -/
theorem CodeMatches.perm
    {code : UInt64} {assignments assignments' : List RowAssignment}
    (hexact : CodeMatches code assignments) (hperm : assignments.Perm assignments') :
    CodeMatches code assignments' := by
  intro centre target
  rw [hexact centre target]
  exact hperm.any_eq

/-- A subset mask selects only bits selected by an exact prefix code. -/
theorem CodeMatches.selected_of_subset
    {code mask : UInt64} {assignments : List RowAssignment}
    (hexact : CodeMatches code assignments)
    (hsubset : ((mask &&& code) == mask) = true)
    {centre target : Vertex}
    (hselected : bitSetB mask (varIndex centre target) = true) :
    selectedByAssignmentsB assignments centre target = true := by
  have hequal : mask &&& code = mask := beq_iff_eq.mp hsubset
  let index : Fin 64 :=
    ⟨varIndex centre target, varIndex_lt centre target⟩
  have hbits := congrArg (fun value => bitSetB value index.val) hequal
  rw [bitSetB_and] at hbits
  rw [hselected] at hbits
  simp only [Bool.true_and] at hbits
  rw [← hexact centre target]
  exact hbits

/-- A subset of an exact prefix code extends any table matched by its assignments. -/
theorem CodeMatches.extends_of_subset
    {code mask : UInt64} {assignments : List RowAssignment}
    {table : Vertex → Finset Vertex}
    (hexact : CodeMatches code assignments)
    (hsound : ∀ centre target,
      selectedByAssignmentsB assignments centre target = true →
        target ∈ table centre)
    (hsubset : ((mask &&& code) == mask) = true) :
    Extends (packedIncidence mask) table := by
  intro centre target htarget
  apply hsound centre target
  apply hexact.selected_of_subset hsubset
  rw [mem_packedIncidence] at htarget
  simpa only [packedSelectsB] using htarget

/-- Equality with a complete exact prefix code identifies the entire incidence table. -/
theorem CodeMatches.table_eq_of_code_eq
    {code exactCode : UInt64} {assignments : List RowAssignment}
    {table : Vertex → Finset Vertex}
    (hexact : CodeMatches code assignments)
    (hsound : ∀ centre target,
      selectedByAssignmentsB assignments centre target = true →
        target ∈ table centre)
    (hcomplete : ∀ centre target, target ∈ table centre →
      selectedByAssignmentsB assignments centre target = true)
    (hequal : (exactCode == code) = true) :
    table = packedIncidence exactCode := by
  have hcode : exactCode = code := beq_iff_eq.mp hequal
  funext centre
  ext target
  rw [mem_packedIncidence]
  change (target ∈ table centre) ↔
    bitSetB exactCode (varIndex centre target) = true
  have hbit : bitSetB exactCode (varIndex centre target) =
      selectedByAssignmentsB assignments centre target := by
    rw [hcode]
    exact hexact centre target
  constructor
  · intro htarget
    rw [hbit]
    exact hcomplete centre target htarget
  · intro htarget
    apply hsound centre target
    rw [← hbit]
    exact htarget

/-- Packed subset validation implies the full semantic prefix extension check. -/
theorem CodeMatches.patternExtendsAssignmentsB
    {code : UInt64} {assignments : List RowAssignment}
    (hexact : CodeMatches code assignments) (summary : PatternSummary)
    (hsubset : ((summary.mask &&& code) == summary.mask) = true) :
    patternExtendsAssignmentsB assignments summary = true := by
  apply List.all_eq_true.mpr
  intro centre _hcentre
  apply List.all_eq_true.mpr
  intro target _htarget
  by_cases hselected : bitSetB summary.mask (varIndex centre target) = true
  · simp only [hselected, Bool.not_true, Bool.false_or]
    exact hexact.selected_of_subset hsubset hselected
  · have hselectedFalse := Bool.eq_false_of_not_eq_true hselected
    simp [hselectedFalse]

/-- Equality with an exact prefix code implies the full semantic table-code check. -/
theorem CodeMatches.hardEqualsAssignmentsB
    {code : UInt64} {assignments : List RowAssignment}
    (hexact : CodeMatches code assignments) (summary : HardSummary)
    (hequal : (summary.code == code) = true) :
    hardEqualsAssignmentsB assignments summary = true := by
  have hcode : summary.code = code := beq_iff_eq.mp hequal
  apply List.all_eq_true.mpr
  intro centre _hcentre
  apply List.all_eq_true.mpr
  intro target _htarget
  simp only [hcode, beq_iff_eq]
  exact hexact centre target

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
