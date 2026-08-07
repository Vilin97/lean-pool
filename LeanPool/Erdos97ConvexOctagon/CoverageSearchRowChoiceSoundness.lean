/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CoverageSearchRowChoices

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

end Erdos97Octagon.RawIncidence
