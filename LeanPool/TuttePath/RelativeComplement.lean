/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.FlatRank

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-!
ST-05: the relative complement construction in `lem:flat-complement`.
The recursion is the paper's simultaneous adjoining of an element to S and T;
it terminates because the corank of S decreases strictly at each step.
-/

public section

namespace TutteFormalization

variable {α : Type*} {M : Matroid α} [M.Finite]

theorem natRank_closure_insert {S : Set α} (hS : M.IsFlat S) {e : α}
    (he : e ∈ M.E) (heS : e ∉ S) :
    natRank M (M.closure (insert e S)) = natRank M S + 1 := by
  rw [natRank_closure]
  have hr : M.eRk (insert e S) = M.eRk S + 1 :=
    M.eRk_insert_eq_add_one ⟨he, by simpa only [hS.closure] using heS⟩
  rw [← cast_natRank M (insert e S), ← cast_natRank M S] at hr
  exact_mod_cast hr

/-- ST-05: recursive construction before the final intersection calculation.
The additive rank equation avoids truncated subtraction in the invariant. -/
theorem exists_relative_complement_data (S T : Set α)
    (hS : M.IsFlat S) (hT : M.IsFlat T) (hTS : T ⊆ S) :
    ∃ U : Set α, M.IsFlat U ∧ T ⊆ U ∧ M.closure (U ∪ S) = M.E ∧
      natRank M U + natRank M S = natRank M T + natRank M M.E := by
  generalize hn : natRank M M.E - natRank M S = n
  induction n using Nat.strong_induction_on generalizing S T with
  | h n ih =>
    by_cases hSE : S = M.E
    · subst S
      exact ⟨T, hT, Set.Subset.rfl, by simp [Set.union_eq_right.mpr hT.subset_ground], rfl⟩
    have hnsub : ¬ M.E ⊆ S := fun h => hSE (Set.Subset.antisymm hS.subset_ground h)
    obtain ⟨e, heE, heS⟩ := Set.not_subset.mp hnsub
    let S' := M.closure (insert e S)
    let T' := M.closure (insert e T)
    have hS' : M.IsFlat S' := M.isFlat_closure _
    have hT' : M.IsFlat T' := M.isFlat_closure _
    have hT'S' : T' ⊆ S' := M.closure_mono (Set.insert_subset_insert hTS)
    have hSr : natRank M S' = natRank M S + 1 := natRank_closure_insert hS heE heS
    have hTr : natRank M T' = natRank M T + 1 :=
      natRank_closure_insert hT heE (fun heT => heS (hTS heT))
    have hSbound : natRank M S' ≤ natRank M M.E := natRank_mono hS'.subset_ground
    have hdec : natRank M M.E - natRank M S' < n := by omega
    obtain ⟨U, hU, hT'U, hjoin, hr⟩ :=
      ih (natRank M M.E - natRank M S') hdec S' T' hS' hT' hT'S' rfl
    have hTT' : T ⊆ T' := (Set.subset_insert e T).trans
      (M.subset_closure _ (Set.insert_subset heE hT.subset_ground))
    have heU : e ∈ U := hT'U (M.subset_closure _
      (Set.insert_subset heE hT.subset_ground) (Set.mem_insert e T))
    have hjoin' : M.closure (U ∪ S) = M.E := by
      have heq : U ∪ insert e S = U ∪ S := by
        rw [Set.union_insert, Set.insert_eq_of_mem (show e ∈ U ∪ S from Or.inl heU)]
      simpa only [S', M.closure_union_closure_right_eq, heq] using hjoin
    exact ⟨U, hU, hTT'.trans hT'U, hjoin', by omega⟩

/-- ST-05: full relative complement, with the source corank formula. -/
theorem exists_relative_complement (S T : Set α)
    (hS : M.IsFlat S) (hT : M.IsFlat T) (hTS : T ⊆ S) :
    ∃ U : Set α, M.IsFlat U ∧ T ⊆ U ∧ U ∩ S = T ∧ M.closure (U ∪ S) = M.E ∧
      natRank M M.E - natRank M U = natRank M S - natRank M T := by
  obtain ⟨U, hU, hTU, hjoin, hr⟩ := exists_relative_complement_data S T hS hT hTS
  have hsub : natRank M (U ∩ S) + natRank M M.E ≤ natRank M U + natRank M S := by
    simpa only [hjoin] using natRank_submodular M U S
  have hinter : U ∩ S = T := (flat_eq_of_subset_of_natRank_le hT (flat_inter hU hS)
    (Set.subset_inter hTU hTS) (by omega)).symm
  exact ⟨U, hU, hTU, hinter, hjoin, by omega⟩

end TutteFormalization
