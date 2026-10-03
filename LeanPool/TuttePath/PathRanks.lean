/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.FlatRank

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-!
Local rank arguments for adjacency and hyperplane intersections in the path proof.
All contextual hypotheses are explicit. No structural existence theorem is
assumed globally, and none of these results depends on the path theorem.
-/

public section

namespace TutteFormalization

variable {α : Type*} {M : Matroid α} [M.Finite] {F L U P X Y : Set α}

/-- After the nested-flat equality, indecomposability gives the Tutte edge. -/
theorem tutteAdjacent_of_corankTwo (hF : Indecomposable M F) (hc : CorankTwo M F)
    (hX : IsHyperplane M X) (hY : IsHyperplane M Y) (hXY : X ≠ Y)
    (hFX : F ⊆ X) (hFY : F ⊆ Y) : TutteAdjacent M X Y := by
  have hI : X ∩ Y = F := hyperplane_inter_eq_of_corankTwo hc hX hY hXY hFX hFY
  exact ⟨hXY, hI ▸ hF, hI ▸ hc⟩

/-- The source's submodularity argument for the complementary intersection.
The rank equation for U and the join condition are explicit premises supplied by
the structural constructions in the other project modules. -/
theorem corankTwo_inter_eq_of_join_eq_ground (hF : M.IsFlat F)
    (hL : CorankTwo M L) (hU : M.IsFlat U) (hFL : F ⊆ L) (hFU : F ⊆ U)
    (hUr : natRank M U = natRank M F + 2)
    (hjoin : M.closure (L ∪ U) = M.E) : L ∩ U = F := by
  have hLr : natRank M L + 2 = natRank M M.E := by
    have hr := hL.2
    rw [← cast_natRank M L, ← cast_natRank M M.E] at hr
    exact_mod_cast hr
  have hsub : natRank M (L ∩ U) + natRank M M.E ≤ natRank M L + natRank M U := by
    simpa only [hjoin] using natRank_submodular M L U
  have hupper : natRank M (L ∩ U) ≤ natRank M F := by omega
  exact (flat_eq_of_subset_of_natRank_le hF (flat_inter hL.1 hU)
    (Set.subset_inter hFL hFU) hupper).symm

/-- Apply with P=V or P=W. Derives the intersection and strict
containment before proving both rank bounds. No corank hypothesis is needed here. -/
theorem path_join_rank_bounds (hL : M.IsFlat L) (hP : M.IsFlat P)
    (hLU : L ∩ U = F) (hFP : F ⊂ P) (hPU : P ⊆ U)
    (hPr : natRank M P = natRank M F + 1) :
    L ∩ P = F ∧ L ⊂ M.closure (L ∪ P) ∧
      natRank M L + 1 ≤ natRank M (M.closure (L ∪ P)) ∧
      natRank M (M.closure (L ∪ P)) ≤ natRank M L + 1 := by
  have hFL : F ⊆ L := hLU ▸ Set.inter_subset_left
  have hLP : L ∩ P = F := Set.Subset.antisymm
    ((show L ∩ P ⊆ L ∩ U from fun _ hx => ⟨hx.1, hPU hx.2⟩).trans_eq hLU)
    (Set.subset_inter hFL hFP.1)
  have hnot : ¬ P ⊆ L := by
    intro hPL
    apply hFP.2
    exact (Set.subset_inter hPL Set.Subset.rfl).trans_eq hLP
  have hLE : L ∪ P ⊆ M.E := Set.union_subset hL.subset_ground hP.subset_ground
  have hLC : L ⊆ M.closure (L ∪ P) :=
    Set.subset_union_left.trans (M.subset_closure _ hLE)
  have hPC : P ⊆ M.closure (L ∪ P) :=
    Set.subset_union_right.trans (M.subset_closure _ hLE)
  have hstrict : L ⊂ M.closure (L ∪ P) :=
    ⟨hLC, fun hCL => hnot (hPC.trans hCL)⟩
  have hlower : natRank M L + 1 ≤ natRank M (M.closure (L ∪ P)) :=
    natRank_lt_of_flat_ssubset hL (M.isFlat_closure _) hstrict
  have hsub : natRank M F + natRank M (M.closure (L ∪ P)) ≤
      natRank M L + (natRank M F + 1) := by
    simpa only [hLP, hPr] using natRank_submodular M L P
  have hupper : natRank M (M.closure (L ∪ P)) ≤ natRank M L + 1 := by omega
  exact ⟨hLP, hstrict, hlower, hupper⟩

/-- With L of corank two, the two bounds give the constructed hyperplane's rank. -/
theorem path_join_isHyperplane (hL : CorankTwo M L) (hP : M.IsFlat P)
    (hLU : L ∩ U = F) (hFP : F ⊂ P) (hPU : P ⊆ U)
    (hPr : natRank M P = natRank M F + 1) : IsHyperplane M (M.closure (L ∪ P)) := by
  obtain ⟨_, _, hlo, hhi⟩ := path_join_rank_bounds hL.1 hP hLU hFP hPU hPr
  have hLr : natRank M L + 2 = natRank M M.E := by
    have hr := hL.2
    rw [← cast_natRank M L, ← cast_natRank M M.E] at hr
    exact_mod_cast hr
  apply isHyperplane_of_natRank (M.isFlat_closure _)
  omega

end TutteFormalization
