/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.IndecomposableComplement
public import LeanPool.TuttePath.PathOperations

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-! The corank induction of `thm:path-theorem`. This file does not import the
public target, so none of its dependencies can rely on that target. -/
public section

namespace TutteFormalization

theorem path_theorem_induction {α : Type*} (M : Matroid α) [M.Finite]
    (Γ : Set (Set α)) (hΓ : ModularCut M Γ)
    (F : Set α) (hF : Indecomposable M F)
    (X Y : Set α) (hX : IsHyperplane M X) (hY : IsHyperplane M Y)
    (hFX : F ⊆ X) (hFY : F ⊆ Y) (hXoff : X ∉ Γ) (hYoff : Y ∉ Γ) :
    ∃ p : TuttePath M, p.origin = X ∧ p.terminus = Y ∧ p.On F ∧ p.Off Γ := by
  generalize hn : natRank M M.E - natRank M F = n
  induction n using Nat.strong_induction_on generalizing F X Y with
  | h n ih =>
    by_cases hXY : X = Y
    · subst Y; exact exists_singleton_path hX hFX hXoff
    have hXr := hyperplane_natRank hX
    have hFE := natRank_mono (M := M) hF.1.subset_ground
    have hFXne : F ≠ X := by
      intro heq
      have hXYsub : X ⊆ Y := heq ▸ hFY
      exact hXY (flat_eq_of_subset_of_natRank_le hX.1 hY.1 hXYsub (by
        have hYr := hyperplane_natRank hY; omega))
    have hFXlt := natRank_lt_of_flat_ssubset hF.1 hX.1
      (Set.ssubset_iff_subset_ne.mpr ⟨hFX, hFXne⟩)
    by_cases hn2 : n ≤ 2
    · exact exists_path_of_corankTwo hF ((corankTwo_iff_natRank hF.1).mpr (by omega))
        hX hY hFX hFY hXoff hYoff
    have hn3 : 3 ≤ n := by omega
    obtain ⟨U, hU, hFU, hUX, hUr⟩ := exists_indecomposable_of_rank
      (hyperplane_indecomposable hX) hF hFX (natRank M F + 2) (by omega) (by omega)
    obtain ⟨V, W, hV, hW, hFV, hFW, hVU, hWU, hVW, hVr, hWr⟩ :=
      exists_indecomposable_diamond hU hF hFU hUr
    have hFV' : F ⊂ V := Set.ssubset_iff_subset_ne.mpr ⟨hFV, by
      intro heq; have := congrArg (natRank M) heq; omega⟩
    have hFW' : F ⊂ W := Set.ssubset_iff_subset_ne.mpr ⟨hFW, by
      intro heq; have := congrArg (natRank M) heq; omega⟩
    have hVX : V ⊆ X := hVU.trans hUX
    have hWX : W ⊆ X := hWU.trans hUX
    have recurse (P Z : Set α) (hP : Indecomposable M P) (hFP : F ⊂ P)
        (hPX : P ⊆ X) (hZ : IsHyperplane M Z) (hPZ : P ⊆ Z) (hZoff : Z ∉ Γ) :
        ∃ p : TuttePath M, p.origin = X ∧ p.terminus = Z ∧ p.On F ∧ p.Off Γ := by
      have hPr := natRank_lt_of_flat_ssubset hF.1 hP.1 hFP
      have hPE := natRank_mono (M := M) hP.1.subset_ground
      have hdec : natRank M M.E - natRank M P < n := by omega
      obtain ⟨p, hpX, hpZ, hpOn, hpOff⟩ := ih (natRank M M.E - natRank M P) hdec
        P hP X Z hX hZ hPX hPZ hXoff hZoff rfl
      exact ⟨p, hpX, hpZ, hpOn.mono hFP.subset, hpOff⟩
    by_cases hVY : V ⊆ Y
    · exact recurse V Y hV hFV' hVX hY hVY hYoff
    by_cases hWY : W ⊆ Y
    · exact recurse W Y hW hFW' hWX hY hWY hYoff
    have hUY : ¬ U ⊆ Y := fun hs => hVY (hVU.trans hs)
    have hjUY : M.closure (Y ∪ U) = M.E := by
      have hYC : Y ⊆ M.closure (Y ∪ U) :=
        M.subset_closure_of_subset' Set.subset_union_left hY.1.subset_ground
      rcases hY.2.2 _ (M.isFlat_closure _) hYC with heq | heq
      · exact False.elim (hUY ((M.subset_closure_of_subset'
          Set.subset_union_right hU.1.subset_ground).trans_eq heq))
      · exact heq
    obtain ⟨L, hL, hFL, hLY, hjLU, hLcor⟩ := exists_indecomposable_complement
      (hyperplane_indecomposable hY) hF hU.1 hFY hFU hjUY
    have hLE := natRank_mono (M := M) hL.1.subset_ground
    have hcL : CorankTwo M L := (corankTwo_iff_natRank hL.1).mpr (by omega)
    have hLU : L ∩ U = F := corankTwo_inter_eq_of_join_eq_ground hF.1 hcL hU.1
      hFL hFU hUr hjLU
    let H₁ := M.closure (L ∪ V)
    let H₂ := M.closure (L ∪ W)
    have hH₁ : IsHyperplane M H₁ := path_join_isHyperplane hcL hV.1 hLU hFV' hVU hVr
    have hH₂ : IsHyperplane M H₂ := path_join_isHyperplane hcL hW.1 hLU hFW' hWU hWr
    have hLH₁ : L ⊆ H₁ := M.subset_closure_of_subset' Set.subset_union_left hL.1.subset_ground
    have hLH₂ : L ⊆ H₂ := M.subset_closure_of_subset' Set.subset_union_left hL.1.subset_ground
    have hVH₁ : V ⊆ H₁ := M.subset_closure_of_subset' Set.subset_union_right hV.1.subset_ground
    have hWH₂ : W ⊆ H₂ := M.subset_closure_of_subset' Set.subset_union_right hW.1.subset_ground
    have hH₁Y : H₁ ≠ Y := fun heq => hVY (hVH₁.trans_eq heq)
    have hH₂Y : H₂ ≠ Y := fun heq => hWY (hWH₂.trans_eq heq)
    have hH₁H₂ : H₁ ≠ H₂ := by
      intro heq
      have hjVW : M.closure (V ∪ W) = U :=
        cover_flats_join_eq hU.1 hV.1 hW.1 hVU hWU hVr hWr hUr hVW
      have hUH₁ : U ⊆ H₁ := by
        rw [← hjVW]
        exact (M.closure_mono
          (Set.union_subset hVH₁ (hWH₂.trans_eq heq.symm))).trans_eq hH₁.1.closure
      have hEH₁ : M.E ⊆ H₁ := by
        rw [← hjLU]
        exact (M.closure_mono (Set.union_subset hLH₁ hUH₁)).trans_eq hH₁.1.closure
      exact hH₁.2.1 (Set.Subset.antisymm hH₁.1.subset_ground hEH₁)
    have hi₁₂ : H₁ ∩ H₂ = L :=
      hyperplane_inter_eq_of_corankTwo hcL hH₁ hH₂ hH₁H₂ hLH₁ hLH₂
    have hoff : H₁ ∉ Γ ∨ H₂ ∉ Γ := by
      by_contra hnOff
      have hs := not_or.mp hnOff
      have hLΓ : L ∈ Γ := hi₁₂ ▸ hΓ.hyperplane_inter_mem hH₁ hH₂ hH₁H₂
        (hi₁₂ ▸ hcL) (not_not.mp hs.1) (not_not.mp hs.2)
      exact hYoff (hΓ.upward L Y hLΓ hY.1 hLY)
    have finish (P H : Set α) (hP : Indecomposable M P) (hFP : F ⊂ P)
        (hPX : P ⊆ X) (hH : IsHyperplane M H) (hPH : P ⊆ H)
        (hLH : L ⊆ H) (hHY : H ≠ Y) (hHoff : H ∉ Γ) :
        ∃ p : TuttePath M, p.origin = X ∧ p.terminus = Y ∧ p.On F ∧ p.Off Γ := by
      obtain ⟨p, hpX, hpH, hpOn, hpOff⟩ := recurse P H hP hFP hPX hH hPH hHoff
      have hedge : TutteAdjacent M p.terminus Y := by
        rw [hpH]
        exact tutteAdjacent_of_corankTwo hL hcL hH hY hHY hLH hLY
      exact ⟨p.snoc Y hY hedge, by simpa using hpX, by simp,
        hpOn.snoc hY hedge hFY, hpOff.snoc hY hedge hYoff⟩
    rcases hoff with h₁ | h₂
    · exact finish V H₁ hV hFV' hVX hH₁ hVH₁ hLH₁ hH₁Y h₁
    · exact finish W H₂ hW hFW' hWX hH₂ hWH₂ hLH₂ hH₂Y h₂
end TutteFormalization
