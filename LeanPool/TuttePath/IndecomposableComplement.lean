/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.Diamond

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-! `prop:indecomposable-complement`: minimal-rank crossing cover and corank induction. -/
public section

namespace TutteFormalization
variable {α : Type*} {M : Matroid α} [M.Finite] {S T U : Set α}

/-- The minimal-rank argument in the source complement proof. -/
theorem exists_indecomposable_cover_not_subset (hS : Indecomposable M S)
    (hT : Indecomposable M T) (hU : M.IsFlat U) (hTS : T ⊆ S) (hTU : T ⊆ U) (hnSU : ¬ S ⊆ U) :
    ∃ W, Indecomposable M W ∧ T ⊆ W ∧ W ⊆ S ∧ ¬ W ⊆ U ∧
      natRank M W = natRank M T + 1 := by
  let P : Set (Set α) := {W | Indecomposable M W ∧ T ⊆ W ∧ W ⊆ S ∧ ¬ W ⊆ U}
  have hPfin : P.Finite := M.ground_finite.powerset.subset
    (fun _ h => h.1.1.subset_ground)
  obtain ⟨W, hW, hmin⟩ := Set.exists_min_image P (natRank M) hPfin
    ⟨S, hS, hTS, Set.Subset.rfl, hnSU⟩
  have hTW : T ⊂ W := Set.ssubset_iff_subset_ne.mpr ⟨hW.2.1, by
    intro heq; exact hW.2.2.2 (heq.symm ▸ hTU)⟩
  have hlt := natRank_lt_of_flat_ssubset hT.1 hW.1.1 hTW
  refine ⟨W, hW.1, hW.2.1, hW.2.2.1, hW.2.2.2, ?_⟩
  by_contra hneq
  have hgap : natRank M T + 2 ≤ natRank M W := by omega
  obtain ⟨V, hV, hTV, hVW, hVr⟩ := exists_indecomposable_of_rank hW.1 hT hW.2.1
    (natRank M W - 2) (by omega) (by omega)
  obtain ⟨A, B, hA, hB, hVA, hVB, hAW, hBW, hAB, hAr, hBr⟩ :=
    exists_indecomposable_diamond hW.1 hV hVW (by omega)
  have hj : M.closure (A ∪ B) = W :=
    cover_flats_join_eq hW.1.1 hA.1 hB.1 hAW hBW hAr hBr (by omega) hAB
  have hcross : ¬ A ⊆ U ∨ ¬ B ⊆ U := by
    by_contra hn
    have hs := not_or.mp hn
    have hAU : A ⊆ U := not_not.mp hs.1
    have hBU : B ⊆ U := not_not.mp hs.2
    apply hW.2.2.2
    rw [← hj]
    exact (M.closure_mono (Set.union_subset hAU hBU)).trans_eq hU.closure
  rcases hcross with hAU | hBU
  · have hbound := hmin A ⟨hA, hTV.trans hVA, hAW.trans hW.2.2.1, hAU⟩
    omega
  · have hbound := hmin B ⟨hB, hTV.trans hVB, hBW.trans hW.2.2.1, hBU⟩
    omega

/-- Source indecomposable complement, with the literal corank equation. -/
theorem exists_indecomposable_complement (hS : Indecomposable M S)
    (hT : Indecomposable M T) (hU : M.IsFlat U) (hTS : T ⊆ S) (hTU : T ⊆ U)
    (hjoin : M.closure (S ∪ U) = M.E) :
    ∃ R, Indecomposable M R ∧ T ⊆ R ∧ R ⊆ S ∧ M.closure (R ∪ U) = M.E ∧
      natRank M M.E - natRank M R = natRank M U - natRank M T := by
  generalize hn : natRank M M.E - natRank M U = n
  induction n using Nat.strong_induction_on generalizing T U with
  | h n ih =>
    by_cases hUE : U = M.E
    · subst U
      exact ⟨T, hT, Set.Subset.rfl, hTS,
        by simp [Set.union_eq_right.mpr hT.1.subset_ground], rfl⟩
    have hnSU : ¬ S ⊆ U := by
      intro hs
      rw [Set.union_eq_right.mpr hs, hU.closure] at hjoin
      exact hUE hjoin
    obtain ⟨W, hW, hTW, hWS, hnWU, hWr⟩ :=
      exists_indecomposable_cover_not_subset hS hT hU hTS hTU hnSU
    let U' := M.closure (U ∪ W)
    have hU' : M.IsFlat U' := M.isFlat_closure _
    have hUU' : U ⊆ U' := M.subset_closure_of_subset' Set.subset_union_left hU.subset_ground
    have hWU' : W ⊆ U' := M.subset_closure_of_subset' Set.subset_union_right hW.1.subset_ground
    have hstrict : U ⊂ U' := ⟨hUU', fun hs => hnWU (hWU'.trans hs)⟩
    have hlt := natRank_lt_of_flat_ssubset hU hU' hstrict
    have hsub := natRank_submodular M U W
    have hTr := natRank_mono (M := M) (Set.subset_inter hTU hTW)
    have hU'r : natRank M U' = natRank M U + 1 := by
      change natRank M (U ∩ W) + natRank M U' ≤ natRank M U + natRank M W at hsub
      omega
    have hU'E := natRank_mono (M := M) hU'.subset_ground
    have hdec : natRank M M.E - natRank M U' < n := by omega
    have hj' : M.closure (S ∪ U') = M.E := by
      apply Set.Subset.antisymm (M.closure_subset_ground _)
      rw [← hjoin]
      exact M.closure_mono (Set.union_subset_union_right S hUU')
    obtain ⟨R, hR, hWR, hRS, hRj, hRr⟩ :=
      ih (natRank M M.E - natRank M U') hdec hW hU' hWS hWU' hj' rfl
    have hRUj : M.closure (R ∪ U) = M.E := by
      have heq : R ∪ (U ∪ W) = R ∪ U := by
        ext e
        constructor
        · rintro (heR | heU | heW)
          · exact Or.inl heR
          · exact Or.inr heU
          · exact Or.inl (hWR heW)
        · rintro (heR | heU)
          · exact Or.inl heR
          · exact Or.inr (Or.inl heU)
      simpa only [U', M.closure_union_closure_right_eq, heq] using hRj
    exact ⟨R, hR, hTW.trans hWR, hRS, hRUj, by omega⟩
end TutteFormalization
