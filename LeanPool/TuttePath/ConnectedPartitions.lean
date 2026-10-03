/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.SeparationRank
public import LeanPool.TuttePath.ContractionFlats

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-! Connectivity background in additive-partition form. This verifies the
needed conclusions without claiming to audit the source's cocircuit proof. -/
public section

namespace TutteFormalization
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite]

theorem connected_iff_no_natRank_partition : Connected M ↔
    ¬ ∃ A B : Set α, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      A ∪ B = M.E ∧ natRank M A + natRank M B = natRank M M.E := by
  unfold Connected
  have heq (A B : Set α) : M.eRk A + M.eRk B = M.eRk M.E ↔
      natRank M A + natRank M B = natRank M M.E := by
    rw [← cast_natRank M A, ← cast_natRank M B, ← cast_natRank M M.E]
    exact_mod_cast Iff.rfl
  simp only [heq]

theorem connected_contract_partition_side {A B F : Set α}
    (hd : Disjoint A B) (hu : A ∪ B = M.E)
    (hr : natRank M A + natRank M B = natRank M M.E)
    (hF : F ⊆ M.E) (hc : Connected (M ／ F)) : A ⊆ F ∨ B ⊆ F := by
  by_contra hn
  have hn := not_or.mp hn
  have hA : (A \ F).Nonempty := Set.not_subset.mp hn.1
  have hB : (B \ F).Nonempty := Set.not_subset.mp hn.2
  apply connected_iff_no_natRank_partition.mp hc
  refine ⟨A \ F, B \ F, hA, hB, hd.mono Set.sdiff_subset Set.sdiff_subset, ?_, ?_⟩
  · change (A \ F) ∪ (B \ F) = M.E \ F
    rw [← Set.union_sdiff_distrib, hu]
  · exact natRank_contract_partition hd hu hr F hF

/-- `prop:connected-intersection`, via the same direct-sum obstruction in rank form.
The source's particular common-cocircuit argument is not claimed audited. -/
theorem indecomposable_inter {F₁ F₂ : Set α} (h₁ : Indecomposable M F₁)
    (h₂ : Indecomposable M F₂) (hu : F₁ ∪ F₂ ≠ M.E) :
    Indecomposable M (F₁ ∩ F₂) := by
  let F := F₁ ∩ F₂
  have hF : M.IsFlat F := flat_inter h₁.1 h₂.1
  refine ⟨hF, connected_iff_no_natRank_partition.mpr ?_⟩
  rintro ⟨A, B, hA, hB, hd, hAB, hr⟩
  have hAE : A ⊆ M.E \ F := Set.subset_union_left.trans_eq hAB
  have hBE : B ⊆ M.E \ F := Set.subset_union_right.trans_eq hAB
  have hC₁ := (indecomposable_sdiff_contract_iff (F := F) h₁.1 Set.inter_subset_left).mpr h₁
  have hC₂ := (indecomposable_sdiff_contract_iff (F := F) h₂.1 Set.inter_subset_right).mpr h₂
  have hs₁ := connected_contract_partition_side hd hAB hr
    (Set.sdiff_subset_sdiff_left h₁.1.subset_ground) hC₁.2
  have hs₂ := connected_contract_partition_side hd hAB hr
    (Set.sdiff_subset_sdiff_left h₂.1.subset_ground) hC₂.2
  have hsame (C : Set α) (hne : C.Nonempty) (hc₁ : C ⊆ F₁ \ F)
      (hc₂ : C ⊆ F₂ \ F) : False := by
    obtain ⟨e, he⟩ := hne
    exact (hc₁ he).2 ⟨(hc₁ he).1, (hc₂ he).1⟩
  have hop (hAF : A ⊆ F₁ ∪ F₂) (hBF : B ⊆ F₁ ∪ F₂) : False := by
    apply hu
    apply Set.Subset.antisymm (Set.union_subset h₁.1.subset_ground h₂.1.subset_ground)
    intro e he
    by_cases heF : e ∈ F
    · exact Or.inl heF.1
    · have heAB : e ∈ A ∪ B := hAB.symm ▸ (show e ∈ M.E \ F from ⟨he, heF⟩)
      exact heAB.elim (fun h => hAF h) (fun h => hBF h)
  rcases hs₁ with ha₁ | hb₁ <;> rcases hs₂ with ha₂ | hb₂
  · exact hsame A hA ha₁ ha₂
  · exact hop (ha₁.trans (Set.sdiff_subset.trans Set.subset_union_left))
      (hb₂.trans (Set.sdiff_subset.trans Set.subset_union_right))
  · exact hop (ha₂.trans (Set.sdiff_subset.trans Set.subset_union_right))
      (hb₁.trans (Set.sdiff_subset.trans Set.subset_union_left))
  · exact hsame B hB hb₁ hb₂
end TutteFormalization
