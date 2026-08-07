/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSearchRowChoices
import LeanPool.Erdos97ConvexOctagon.RowMasks

/-! # Soundness and completeness of lightweight legal-row search data -/

namespace Erdos97Octagon.RawIncidence

/-- The lightweight choice at one legal-row index. -/
def searchRowChoiceAt (centre : Vertex) (index : Fin 35) : SearchRowChoice :=
  (searchRowChoices.getD centre.val #[]).getD index.val ⟨0, 0⟩

/-- Each centre has exactly the expected 35 legal rows. -/
theorem searchRowChoices_size (centre : Vertex) :
    (searchRowChoices.getD centre.val #[]).size = 35 := by
  fin_cases centre <;> rfl

/-- Indexed lookup returns a member of the corresponding centre's row table. -/
theorem searchRowChoiceAt_mem (centre : Vertex) (index : Fin 35) :
    searchRowChoiceAt centre index ∈
      searchRowChoices.getD centre.val #[] := by
  have hindex : index.val < (searchRowChoices.getD centre.val #[]).size := by
    rw [searchRowChoices_size]
    exact index.isLt
  have hequal : searchRowChoiceAt centre index =
      (searchRowChoices.getD centre.val #[])[index.val] := by
    unfold searchRowChoiceAt
    change (if h : index.val < (searchRowChoices.getD centre.val #[]).size then
      (searchRowChoices.getD centre.val #[])[index.val] else ⟨0, 0⟩) = _
    rw [dif_pos hindex]
  rw [hequal]
  exact Array.getElem_mem hindex

/-- The generated table is the complete legal-row enumeration, in search order. -/
theorem searchRowChoices_complete (centre : Vertex) :
    (rowOptions centre).reverse =
      List.ofFn (fun index : Fin 35 =>
        packedRow (searchRowChoiceAt centre index).rowMask) := by
  fin_cases centre <;> decide

/-- Every mathematical incidence row occurs at one lightweight search index. -/
theorem exists_searchRowChoiceIndex (Q : OctagonIncidence) (centre : Vertex) :
    ∃ index : Fin 35,
      Q.targets centre =
        packedRow (searchRowChoiceAt centre index).rowMask := by
  have hrow : Q.targets centre ∈ (rowOptions centre).reverse := by
    simpa using target_row_mem_rowOptions Q centre
  rw [searchRowChoices_complete, List.mem_ofFn] at hrow
  obtain ⟨index, hrow⟩ := hrow
  exact ⟨index, hrow.symm⟩

/-- Every stored unordered-pair mask is exactly computed from its row mask. -/
theorem searchRowChoiceAt_pairMask (centre : Vertex) (index : Fin 35) :
    (searchRowChoiceAt centre index).pairMask =
      rowPairMask (searchRowChoiceAt centre index).rowMask := by
  fin_cases centre <;> fin_cases index <;> rfl

/-- The centre-two row table uses exactly the public fixed-branch ordering. -/
theorem searchRowChoiceAt_two_mask (index : Fin 35) :
    (searchRowChoiceAt 2 index).rowMask = rowTwoMask index := by
  fin_cases index <;> rfl

/-- Every member of a centre's row table carries the exact computed pair mask. -/
theorem searchRowChoice_pairMask_of_mem
    (centre : Vertex) {choice : SearchRowChoice}
    (hchoice : choice ∈ searchRowChoices.getD centre.val #[]) :
    choice.pairMask = rowPairMask choice.rowMask := by
  rw [Array.mem_iff_getElem] at hchoice
  obtain ⟨index, hindex, rfl⟩ := hchoice
  have hindex35 : index < 35 := by
    rw [← searchRowChoices_size centre]
    exact hindex
  let boundedIndex : Fin 35 := ⟨index, hindex35⟩
  have hat : searchRowChoiceAt centre boundedIndex =
      (searchRowChoices.getD centre.val #[])[index] := by
    unfold searchRowChoiceAt
    change (if h : index < (searchRowChoices.getD centre.val #[]).size then
      (searchRowChoices.getD centre.val #[])[index] else ⟨0, 0⟩) = _
    rw [dif_pos hindex]
  rw [← hat]
  exact searchRowChoiceAt_pairMask centre boundedIndex

/-- Natural-number indexed lookup has the same audited pair-mask guarantee. -/
theorem searchRowChoice_pairMask
    (centre : Vertex) (index : Nat) (hindex : index < 35) :
    let choice := (searchRowChoices.getD centre.val #[]).getD index ⟨0, 0⟩
    choice.pairMask = rowPairMask choice.rowMask := by
  let boundedIndex : Fin 35 := ⟨index, hindex⟩
  simpa only [searchRowChoiceAt, boundedIndex] using
    searchRowChoiceAt_pairMask centre boundedIndex

private theorem findSearchChoice_spec
    (choices : Array SearchRowChoice) (row : UInt64)
    (hexists : ∃ choice ∈ choices, choice.rowMask = row) :
    let choice := (choices.find? (fun candidate => candidate.rowMask == row)).getD
      ⟨0, 0⟩
    choice ∈ choices ∧ choice.rowMask = row := by
  generalize hfind : choices.find?
      (fun candidate => candidate.rowMask == row) = found
  cases found with
  | none =>
      obtain ⟨choice, hchoice, hrow⟩ := hexists
      have hnone := (Array.find?_eq_none.mp hfind) choice hchoice
      simp [hrow] at hnone
  | some choice =>
      have hchoice := Array.mem_of_find?_eq_some hfind
      have hrow : choice.rowMask = row := by
        simpa only [beq_iff_eq] using Array.find?_some hfind
      simpa only [Option.getD_some] using And.intro hchoice hrow

/-- Lookup by row mask returns the matching audited table entry when it exists. -/
theorem searchChoiceForRow_spec
    (centre : Vertex) (row : UInt64)
    (hexists : ∃ choice ∈ searchRowChoices.getD centre.val #[],
      choice.rowMask = row) :
    searchChoiceForRow centre row ∈
        searchRowChoices.getD centre.val #[] ∧
      (searchChoiceForRow centre row).rowMask = row := by
  exact findSearchChoice_spec _ _ hexists

/-- Successful row-mask lookup also returns its exactly computed pair mask. -/
theorem searchChoiceForRow_pairMask
    (centre : Vertex) (row : UInt64)
    (hexists : ∃ choice ∈ searchRowChoices.getD centre.val #[],
      choice.rowMask = row) :
    (searchChoiceForRow centre row).pairMask = rowPairMask row := by
  have hspec := searchChoiceForRow_spec centre row hexists
  calc
    _ = rowPairMask (searchChoiceForRow centre row).rowMask :=
      searchRowChoice_pairMask_of_mem centre hspec.1
    _ = rowPairMask row := congrArg rowPairMask hspec.2

/-- Lookup finds the normalized zeroth row. -/
theorem searchChoiceForRow_zero_spec :
    (searchChoiceForRow 0 30).rowMask = 30 := by
  exact (searchChoiceForRow_spec 0 30
    ⟨searchRowChoiceAt 0 0, searchRowChoiceAt_mem 0 0, rfl⟩).2

/-- The normalized zeroth-row lookup carries its exact pair mask. -/
theorem searchChoiceForRow_zero_pairMask :
    (searchChoiceForRow 0 30).pairMask = rowPairMask 30 := by
  exact searchChoiceForRow_pairMask 0 30
    ⟨searchRowChoiceAt 0 0, searchRowChoiceAt_mem 0 0, rfl⟩

private def canonicalSearchChoiceIndex : Fin 7 → Fin 35 :=
  ![0, 1, 7, 19, 20, 23, 29]

/-- Lookup finds every public canonical first-row mask. -/
theorem searchChoiceForRow_canonical_spec (orbit : Fin 7) :
    (searchChoiceForRow 1 (canonicalRowMask orbit)).rowMask =
      canonicalRowMask orbit := by
  let index := canonicalSearchChoiceIndex orbit
  apply (searchChoiceForRow_spec 1 (canonicalRowMask orbit)
    ⟨searchRowChoiceAt 1 index, searchRowChoiceAt_mem 1 index, ?_⟩).2
  fin_cases orbit <;> rfl

/-- Every canonical first-row lookup carries its exact pair mask. -/
theorem searchChoiceForRow_canonical_pairMask (orbit : Fin 7) :
    (searchChoiceForRow 1 (canonicalRowMask orbit)).pairMask =
      rowPairMask (canonicalRowMask orbit) := by
  let index := canonicalSearchChoiceIndex orbit
  apply searchChoiceForRow_pairMask 1 (canonicalRowMask orbit)
  refine ⟨searchRowChoiceAt 1 index, searchRowChoiceAt_mem 1 index, ?_⟩
  fin_cases orbit <;> rfl

/-- Lookup finds every public second-row mask in the same indexed order. -/
theorem searchChoiceForRow_two_spec (index : Fin 35) :
    (searchChoiceForRow 2 (rowTwoMask index)).rowMask = rowTwoMask index := by
  exact (searchChoiceForRow_spec 2 (rowTwoMask index)
    ⟨searchRowChoiceAt 2 index, searchRowChoiceAt_mem 2 index,
      searchRowChoiceAt_two_mask index⟩).2

/-- Every indexed second-row lookup carries its exact pair mask. -/
theorem searchChoiceForRow_two_pairMask (index : Fin 35) :
    (searchChoiceForRow 2 (rowTwoMask index)).pairMask =
      rowPairMask (rowTwoMask index) := by
  exact searchChoiceForRow_pairMask 2 (rowTwoMask index)
    ⟨searchRowChoiceAt 2 index, searchRowChoiceAt_mem 2 index,
      searchRowChoiceAt_two_mask index⟩

end Erdos97Octagon.RawIncidence
