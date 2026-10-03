/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.Chain
public import LeanPool.TuttePath.PathRanks

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-! Explicit rank calculations used in the source Diamond construction. -/
public section

namespace TutteFormalization
open scoped Matroid
variable {α : Type*} {M : Matroid α} [M.Finite] {S T L P X Y : Set α}

theorem corankTwo_iff_natRank (hF : M.IsFlat T) :
    CorankTwo M T ↔ natRank M T + 2 = natRank M M.E := by
  unfold CorankTwo
  rw [and_iff_right hF, ← cast_natRank M T, ← cast_natRank M M.E]
  exact_mod_cast Iff.rfl

theorem union_ne_ground_of_indecomposable_inter (hT : Indecomposable M T)
    (hX : M.IsFlat X) (hY : M.IsFlat Y) (hi : X ∩ Y = T)
    (hnX : X ≠ T) (hnY : Y ≠ T)
    (hr : natRank M X + natRank M Y = natRank M T + natRank M M.E) :
    X ∪ Y ≠ M.E := by
  intro hu
  have hTX : T ⊆ X := hi ▸ Set.inter_subset_left
  have hTY : T ⊆ Y := hi ▸ Set.inter_subset_right
  have hA : (X \ T).Nonempty := Set.not_subset.mp
    (fun hs => hnX (Set.Subset.antisymm hs hTX))
  have hB : (Y \ T).Nonempty := Set.not_subset.mp
    (fun hs => hnY (Set.Subset.antisymm hs hTY))
  have hd : Disjoint (X \ T) (Y \ T) := by
    apply Set.disjoint_left.mpr
    intro e heX heY
    exact heX.2 (hi ▸ (show e ∈ X ∩ Y from ⟨heX.1, heY.1⟩))
  apply connected_iff_no_natRank_partition.mp hT.2
  refine ⟨X \ T, Y \ T, hA, hB, hd, ?_, ?_⟩
  · change (X \ T) ∪ (Y \ T) = M.E \ T
    rw [← Set.union_sdiff_distrib, hu]
  · have hXr := natRank_contract_add T (X \ T) hT.1.subset_ground
      (Set.sdiff_subset_sdiff_left hX.subset_ground)
    have hYr := natRank_contract_add T (Y \ T) hT.1.subset_ground
      (Set.sdiff_subset_sdiff_left hY.subset_ground)
    have hEr := natRank_contract_add T (M.E \ T) hT.1.subset_ground Set.Subset.rfl
    rw [Set.sdiff_union_of_subset hTX] at hXr
    rw [Set.sdiff_union_of_subset hTY] at hYr
    rw [Set.sdiff_union_of_subset hT.1.subset_ground] at hEr
    change natRank (M ／ T) (X \ T) + natRank (M ／ T) (Y \ T) =
      natRank (M ／ T) (M.E \ T)
    omega

theorem diamond_join_inter (hS : M.IsFlat S) (hL : CorankTwo M L)
    (hP : M.IsFlat P) (hi : L ∩ S = T) (hTP : T ⊂ P) (hPS : P ⊆ S)
    (hSr : natRank M S = natRank M T + 2)
    (hPr : natRank M P = natRank M T + 1) (hj : M.closure (L ∪ S) = M.E) :
    IsHyperplane M (M.closure (L ∪ P)) ∧ S ∩ M.closure (L ∪ P) = P := by
  have hH := path_join_isHyperplane hL hP hi hTP hPS hPr
  refine ⟨hH, ?_⟩
  have hPH : P ⊆ M.closure (L ∪ P) := M.subset_closure_of_subset'
    Set.subset_union_right hP.subset_ground
  have hjoin : M.closure (S ∪ M.closure (L ∪ P)) = M.E := by
    apply Set.Subset.antisymm (M.closure_subset_ground _)
    rw [← hj]
    apply M.closure_mono
    exact Set.union_subset
      ((M.subset_closure_of_subset' Set.subset_union_left hL.1.subset_ground).trans
        Set.subset_union_right)
      Set.subset_union_left
  have hsub := natRank_submodular M S (M.closure (L ∪ P))
  rw [hjoin] at hsub
  have hHr := hyperplane_natRank hH
  exact (flat_eq_of_subset_of_natRank_le hP (flat_inter hS hH.1)
    (Set.subset_inter hPS hPH) (by omega)).symm

theorem cover_flats_inter_eq {F P Q : Set α} (hF : M.IsFlat F)
    (hP : M.IsFlat P) (hQ : M.IsFlat Q) (hFP : F ⊆ P) (hFQ : F ⊆ Q)
    (hrP : natRank M P = natRank M F + 1)
    (hrQ : natRank M Q = natRank M F + 1) (hne : P ≠ Q) : P ∩ Q = F := by
  have hn : P ∩ Q ≠ P := by
    intro heq
    have hPQ : P ⊆ Q := heq ▸ Set.inter_subset_right
    exact hne (flat_eq_of_subset_of_natRank_le hP hQ hPQ (by omega))
  have hlt := natRank_lt_of_flat_ssubset (flat_inter hP hQ) hP
    (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_left, hn⟩)
  exact (flat_eq_of_subset_of_natRank_le hF (flat_inter hP hQ)
    (Set.subset_inter hFP hFQ) (by omega)).symm

theorem cover_flats_join_eq {F P Q S : Set α} (hS : M.IsFlat S)
    (hP : M.IsFlat P) (hQ : M.IsFlat Q) (hPS : P ⊆ S) (hQS : Q ⊆ S)
    (hrP : natRank M P = natRank M F + 1)
    (hrQ : natRank M Q = natRank M F + 1)
    (hrS : natRank M S = natRank M F + 2) (hne : P ≠ Q) :
    M.closure (P ∪ Q) = S := by
  have hPJ : P ⊆ M.closure (P ∪ Q) :=
    M.subset_closure_of_subset' Set.subset_union_left hP.subset_ground
  have hQJ : Q ⊆ M.closure (P ∪ Q) :=
    M.subset_closure_of_subset' Set.subset_union_right hQ.subset_ground
  have hn : P ≠ M.closure (P ∪ Q) := by
    intro heq
    have hQP : Q ⊆ P := hQJ.trans_eq heq.symm
    exact hne (flat_eq_of_subset_of_natRank_le hQ hP hQP (by omega)).symm
  have hlt := natRank_lt_of_flat_ssubset hP (M.isFlat_closure _)
    (Set.ssubset_iff_subset_ne.mpr ⟨hPJ, hn⟩)
  exact flat_eq_of_subset_of_natRank_le (M.isFlat_closure _) hS
    ((M.closure_mono (Set.union_subset hPS hQS)).trans_eq hS.closure) (by omega)
end TutteFormalization
