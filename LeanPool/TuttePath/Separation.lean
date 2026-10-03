/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.ConnectedPartitions

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-! `lem:separation` in its literal set-theoretic form. Direct-sum background
is expanded using rank partitions; the source cocircuit criterion is not audited. -/
public section

namespace TutteFormalization
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite] {F : Set α}

theorem decomposable_iff_separation (hF : M.IsFlat F) :
    ¬ Indecomposable M F ↔ ∃ X₁ X₂ : Set α,
      F = X₁ ∩ X₂ ∧ X₁ ∪ X₂ = M.E ∧ X₁ ≠ F ∧ X₂ ≠ F ∧
      ∀ H, IsHyperplane M H → F ⊆ H → X₁ ⊆ H ∨ X₂ ⊆ H := by
  constructor
  · intro hn
    have hnC : ¬ Connected (M ／ F) := fun hc => hn ⟨hF, hc⟩
    rw [connected_iff_no_natRank_partition, not_not] at hnC
    obtain ⟨A, B, hA, hB, hd, hu, hr⟩ := hnC
    have hAE : A ⊆ M.E \ F := Set.subset_union_left.trans_eq hu
    have hBE : B ⊆ M.E \ F := Set.subset_union_right.trans_eq hu
    refine ⟨A ∪ F, B ∪ F, ?_, ?_, ?_, ?_, ?_⟩
    · ext e
      constructor
      · intro he; exact ⟨Or.inr he, Or.inr he⟩
      · rintro ⟨ha | hf, hb | hf'⟩
        · exact False.elim (Set.disjoint_left.mp hd ha hb)
        · exact hf'
        · exact hf
        · exact hf
    · calc
        (A ∪ F) ∪ (B ∪ F) = (A ∪ B) ∪ F := by ext e; simp only [Set.mem_union]; tauto
        _ = (M.E \ F) ∪ F := congrArg (fun S => S ∪ F) hu
        _ = M.E := Set.sdiff_union_of_subset hF.subset_ground
    · intro heq
      obtain ⟨e, he⟩ := hA
      exact (hAE he).2 (heq ▸ (show e ∈ A ∪ F from Or.inl he))
    · intro heq
      obtain ⟨e, he⟩ := hB
      exact (hBE he).2 (heq ▸ (show e ∈ B ∪ F from Or.inl he))
    · intro H hH hFH
      rcases hyperplane_contains_partition_side hd hu hr
        (hyperplane_sdiff_contract hF hH hFH) with hAH | hBH
      · exact Or.inl (Set.union_subset (hAH.trans Set.sdiff_subset) hFH)
      · exact Or.inr (Set.union_subset (hBH.trans Set.sdiff_subset) hFH)
  · rintro ⟨X₁, X₂, hi, hu, hn₁, hn₂, hh⟩ hI
    have hFX₁ : F ⊆ X₁ := hi ▸ Set.inter_subset_left
    have hFX₂ : F ⊆ X₂ := hi ▸ Set.inter_subset_right
    have hXE₁ : X₁ ⊆ M.E := Set.subset_union_left.trans_eq hu
    have hXE₂ : X₂ ⊆ M.E := Set.subset_union_right.trans_eq hu
    have hA : (X₁ \ F).Nonempty := Set.not_subset.mp
      (fun hs => hn₁ (Set.Subset.antisymm hs hFX₁))
    have hB : (X₂ \ F).Nonempty := Set.not_subset.mp
      (fun hs => hn₂ (Set.Subset.antisymm hs hFX₂))
    have hd : Disjoint (X₁ \ F) (X₂ \ F) := by
      apply Set.disjoint_left.mpr
      intro e he₁ he₂
      exact he₁.2 (hi.symm ▸ (show e ∈ X₁ ∩ X₂ from ⟨he₁.1, he₂.1⟩))
    have hu' : (X₁ \ F) ∪ (X₂ \ F) = (M ／ F).E := by
      change (X₁ \ F) ∪ (X₂ \ F) = M.E \ F
      rw [← Set.union_sdiff_distrib, hu]
    apply connected_iff_no_natRank_partition.mp hI.2
    refine ⟨X₁ \ F, X₂ \ F, hA, hB, hd, hu', ?_⟩
    apply natRank_add_of_hyperplane_sides hd hu'
    intro G hG
    rcases hh (G ∪ F) (hyperplane_union_of_contract hF hG) Set.subset_union_right with h₁ | h₂
    · left; intro e he
      exact (h₁ he.1).resolve_right he.2
    · right; intro e he
      exact (h₂ he.1).resolve_right he.2
end TutteFormalization
