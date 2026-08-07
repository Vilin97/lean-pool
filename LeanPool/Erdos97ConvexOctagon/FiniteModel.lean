/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.Relabelling
import Mathlib.Data.List.Sort

/-! # Erdős 97 convex-octagon formalization: Finite Model -/

namespace Erdos97Octagon

/-- An unbundled eight-row incidence table used by the finite certificate. -/
abbrev RawIncidence := Vertex → Finset Vertex

namespace RawIncidence

/-- A four-entry row used by the finite certificate. -/
abbrev SearchRow := Finset Vertex

/-- All four-element rows available at a specified centre. -/
def rowOptions (v : Vertex) : List SearchRow :=
  (((List.finRange 8).filter (· ≠ v)).sublistsLen 4).map List.toFinset

/-- Every row of an octagon incidence system occurs in the finite row list. -/
theorem target_row_mem_rowOptions (Q : OctagonIncidence) (v : Vertex) :
    Q.targets v ∈ rowOptions v := by
  let row := (Q.targets v).sort (· ≤ ·)
  have hnodup : row.Nodup := Finset.sort_nodup _ _
  have hsubset : row ⊆ (List.finRange 8).filter (· ≠ v) := by
    intro x hx
    rw [List.mem_filter]
    have hxQ : x ∈ Q.targets v := by
      simpa [row] using hx
    exact ⟨List.mem_finRange x,
      decide_eq_true (fun h => Q.centre_not_mem v (h ▸ hxQ))⟩
  have hsubperm : row.Subperm ((List.finRange 8).filter (· ≠ v)) :=
    hnodup.subperm hsubset
  have hsortedRow : row.SortedLE :=
    (Finset.pairwise_sort (Q.targets v) (· ≤ ·)).sortedLE
  have hsortedAll : ((List.finRange 8).filter (· ≠ v)).SortedLE :=
    ((List.sortedLT_finRange 8).sortedLE.pairwise.filter _).sortedLE
  have hsublist : row.Sublist ((List.finRange 8).filter (· ≠ v)) :=
    List.sublist_of_subperm_of_sortedLE hsubperm hsortedRow hsortedAll
  have hlength : row.length = 4 := by
    rw [← List.toFinset_card_of_nodup hnodup, Finset.sort_toFinset, Q.card_targets]
  rw [rowOptions, List.mem_map]
  exact ⟨row, List.mem_sublistsLen.mpr ⟨hsublist, hlength⟩,
    Finset.sort_toFinset _ _⟩

/-- The zero-based SAT variable representing one directed incidence. -/
def varIndex (centre target : Vertex) : ℕ :=
  8 * centre.val + target.val

/-- Test one bit of a packed 64-bit incidence table. -/
def bitSetB (code : UInt64) (index : ℕ) : Bool :=
  ((code >>> UInt64.ofNat index) &&& 1) != 0

/-- Decode one three-bit entry of a packed permutation. -/
def decodeMap (code : UInt64) (vertex : Vertex) : Vertex :=
  Fin.ofNat 8 (((code >>> UInt64.ofNat (3 * vertex.val)) &&& 7).toNat)

/-- Decode an eight-bit row mask as a set of octagon vertices. -/
def packedRow (mask : UInt64) : Finset Vertex :=
  Finset.univ.filter fun target => bitSetB mask target.val

@[simp] theorem mem_packedRow (mask : UInt64) (target : Vertex) :
    target ∈ packedRow mask ↔ bitSetB mask target.val = true := by
  simp [packedRow]

/-- Read one directed incidence from a packed table. -/
def packedSelectsB (code : UInt64) (centre target : Vertex) : Bool :=
  bitSetB code (varIndex centre target)

/-- Decode a packed table to the mathematical finite-set model. -/
def packedIncidence (code : UInt64) : RawIncidence := fun centre =>
  Finset.univ.filter fun target => packedSelectsB code centre target

@[simp] theorem mem_packedIncidence (code : UInt64) (centre target : Vertex) :
    target ∈ packedIncidence code centre ↔ packedSelectsB code centre target = true := by
  simp [packedIncidence]

/-- Pack one finite row into its eight-bit position. -/
def rowMask (row : SearchRow) : UInt64 :=
  (List.finRange 8).foldl (fun mask target =>
    if target ∈ row then mask ||| (1 <<< UInt64.ofNat target.val) else mask) 0

/-- Pack all eight rows into one 64-bit key. -/
def systemCode (R : RawIncidence) : UInt64 :=
  (List.finRange 8).foldl (fun packed centre =>
    packed ||| (rowMask (R centre) <<< UInt64.ofNat (8 * centre.val))) 0

end RawIncidence

end Erdos97Octagon
