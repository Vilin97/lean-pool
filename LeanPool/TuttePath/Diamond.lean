/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.DiamondRanks

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-! The source `prop:indecomposable-diamond` construction. -/
public section

namespace TutteFormalization
variable {α : Type*} {M : Matroid α} [M.Finite] {S T : Set α}

theorem exists_indecomposable_diamond (hS : Indecomposable M S)
    (hT : Indecomposable M T) (hTS : T ⊆ S)
    (hSr : natRank M S = natRank M T + 2) :
    ∃ U V, Indecomposable M U ∧ Indecomposable M V ∧ T ⊆ U ∧ T ⊆ V ∧
      U ⊆ S ∧ V ⊆ S ∧ U ≠ V ∧
      natRank M U = natRank M T + 1 ∧ natRank M V = natRank M T + 1 := by
  have hTS' : T ⊂ S := Set.ssubset_iff_subset_ne.mpr ⟨hTS, by
    intro heq; have := congrArg (natRank M) heq; omega⟩
  obtain ⟨U, hU, hTU, hUS, hUr'⟩ := exists_indecomposable_step hS hT hTS'
  have hUr : natRank M U = natRank M T + 1 := by omega
  obtain ⟨a, haS, haU⟩ := Set.not_subset.mp hUS.not_superset
  let W := M.closure (insert a T)
  have hW : M.IsFlat W := M.isFlat_closure _
  have hWin : insert a T ⊆ W := M.subset_closure _
    (Set.insert_subset (hS.1.subset_ground haS) hT.1.subset_ground)
  have hTW : T ⊆ W := (Set.subset_insert a T).trans hWin
  have haW : a ∈ W := hWin (Set.mem_insert a T)
  have hWS : W ⊆ S := (M.closure_mono (Set.insert_subset haS hTS)).trans_eq hS.1.closure
  have hWr : natRank M W = natRank M T + 1 :=
    natRank_closure_insert hT.1 (hS.1.subset_ground haS) (fun ha => haU (hTU ha))
  have hUW : U ≠ W := fun heq => haU (heq.symm ▸ haW)
  by_cases hWi : Indecomposable M W
  · exact ⟨U, W, hU, hWi, hTU, hTW, hUS.subset, hWS, hUW, hUr, hWr⟩
  have hSE : S ≠ M.E := by
    intro heq
    have hWh : IsHyperplane M W := isHyperplane_of_natRank hW (by
      rw [← heq]; omega)
    exact hWi (hyperplane_indecomposable hWh)
  have hSlt : natRank M S < natRank M M.E := natRank_lt_of_flat_ssubset hS.1 M.ground_isFlat
    (Set.ssubset_iff_subset_ne.mpr ⟨hS.1.subset_ground, hSE⟩)
  obtain ⟨L, hL, hTL, hLS, hj, hLr⟩ := exists_relative_complement S T hS.1 hT.1 hTS
  have hLE := natRank_mono (M := M) hL.subset_ground
  have hcL : CorankTwo M L := (corankTwo_iff_natRank hL).mpr (by omega)
  have hTU' : T ⊂ U := Set.ssubset_iff_subset_ne.mpr ⟨hTU, by
    intro heq; have := congrArg (natRank M) heq; omega⟩
  have hTW' : T ⊂ W := Set.ssubset_iff_subset_ne.mpr ⟨hTW, by
    intro heq; have := congrArg (natRank M) heq; omega⟩
  let H₁ := M.closure (L ∪ U)
  let H₂ := M.closure (L ∪ W)
  obtain ⟨hH₁, hi₁⟩ := diamond_join_inter hS.1 hcL hU.1 hLS hTU' hUS.subset hSr hUr hj
  obtain ⟨hH₂, hi₂⟩ := diamond_join_inter hS.1 hcL hW hLS hTW' hWS hSr hWr hj
  have hSH₂ : S ∪ H₂ = M.E := by
    by_contra hn
    exact hWi (hi₂ ▸ indecomposable_inter hS (hyperplane_indecomposable hH₂) hn)
  have hUH₂ : U ∩ H₂ = T := by
    have heq : U ∩ H₂ = U ∩ W := by
      rw [← hi₂, ← Set.inter_assoc, Set.inter_eq_left.mpr hUS.subset]
    rw [heq]
    exact cover_flats_inter_eq hT.1 hU.1 hW hTU hTW hUr hWr hUW
  have hH₁r := hyperplane_natRank hH₁
  have hH₂r := hyperplane_natRank hH₂
  have hnUH₂ : U ∪ H₂ ≠ M.E := union_ne_ground_of_indecomposable_inter hT hU.1 hH₂.1
    hUH₂ (by intro heq; have := congrArg (natRank M) heq; omega)
    (by intro heq; have := congrArg (natRank M) heq; change natRank M H₂ + 1 = _ at hH₂r; omega)
    (by change natRank M H₂ + 1 = _ at hH₂r; omega)
  have hnSH₁ : S ∪ H₁ ≠ M.E := union_ne_ground_of_indecomposable_inter hU hS.1 hH₁.1
    hi₁ (by intro heq; have := congrArg (natRank M) heq; omega)
    (by intro heq; have := congrArg (natRank M) heq; change natRank M H₁ + 1 = _ at hH₁r; omega)
    (by change natRank M H₁ + 1 = _ at hH₁r; omega)
  obtain ⟨b, hbE, hbUnion⟩ := Set.not_subset.mp (show ¬ M.E ⊆ U ∪ H₂ from fun hs =>
    hnUH₂ (Set.Subset.antisymm (Set.union_subset hU.1.subset_ground hH₂.1.subset_ground) hs))
  have hbU : b ∉ U := fun h => hbUnion (Or.inl h)
  have hbH₂ : b ∉ H₂ := fun h => hbUnion (Or.inr h)
  have hbS : b ∈ S := (show b ∈ S ∪ H₂ from hSH₂.symm ▸ hbE).resolve_right hbH₂
  obtain ⟨c, hcE, hcUnion⟩ := Set.not_subset.mp (show ¬ M.E ⊆ S ∪ H₁ from fun hs =>
    hnSH₁ (Set.Subset.antisymm (Set.union_subset hS.1.subset_ground hH₁.1.subset_ground) hs))
  have hcS : c ∉ S := fun h => hcUnion (Or.inl h)
  have hcH₁ : c ∉ H₁ := fun h => hcUnion (Or.inr h)
  let V := M.closure (insert b T)
  have hV : M.IsFlat V := M.isFlat_closure _
  have hVin : insert b T ⊆ V := M.subset_closure _ (Set.insert_subset hbE hT.1.subset_ground)
  have hTV : T ⊆ V := (Set.subset_insert b T).trans hVin
  have hbV : b ∈ V := hVin (Set.mem_insert b T)
  have hVS : V ⊆ S := (M.closure_mono (Set.insert_subset hbS hTS)).trans_eq hS.1.closure
  have hVr : natRank M V = natRank M T + 1 :=
    natRank_closure_insert hT.1 hbE (fun hb => hbU (hTU hb))
  have hTV' : T ⊂ V := Set.ssubset_iff_subset_ne.mpr ⟨hTV, by
    intro heq; have := congrArg (natRank M) heq; omega⟩
  have hUV : U ≠ V := fun heq => hbU (heq.symm ▸ hbV)
  let H := M.closure (L ∪ V)
  obtain ⟨hH, hi⟩ := diamond_join_inter hS.1 hcL hV hLS hTV' hVS hSr hVr hj
  have hLH : L ⊆ H := M.subset_closure_of_subset' Set.subset_union_left hL.subset_ground
  have hLH₁ : L ⊆ H₁ := M.subset_closure_of_subset' Set.subset_union_left hL.subset_ground
  have hLH₂ : L ⊆ H₂ := M.subset_closure_of_subset' Set.subset_union_left hL.subset_ground
  have hHH₂ : H ≠ H₂ := by
    intro heq
    have hbH : b ∈ H := M.subset_closure_of_subset' Set.subset_union_right hV.subset_ground hbV
    exact hbH₂ (heq ▸ hbH)
  have hIH₂ : H ∩ H₂ = L := hyperplane_inter_eq_of_corankTwo hcL hH hH₂ hHH₂ hLH hLH₂
  have hnSH : S ∪ H ≠ M.E := by
    intro heq
    have hcH : c ∈ H := (show c ∈ S ∪ H from heq.symm ▸ hcE).resolve_left hcS
    have hcH₂ : c ∈ H₂ := (show c ∈ S ∪ H₂ from hSH₂.symm ▸ hcE).resolve_left hcS
    exact hcH₁ (hLH₁ (hIH₂ ▸ (show c ∈ H ∩ H₂ from ⟨hcH, hcH₂⟩)))
  have hVi : Indecomposable M V := hi ▸ indecomposable_inter hS (hyperplane_indecomposable hH) hnSH
  exact ⟨U, V, hU, hVi, hTU, hTV, hUS.subset, hVS, hUV, hUr, hVr⟩
end TutteFormalization
