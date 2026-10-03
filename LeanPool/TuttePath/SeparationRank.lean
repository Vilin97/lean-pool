/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.HyperplaneTools

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-!
Additive-rank partitions and their restrictions, the elementary direct-sum
background used in `lem:separation`. These lemmas use the actual partition and
rank equations rather than assuming a decomposition theorem.
-/

public section

namespace TutteFormalization

variable {α : Type*} {M : Matroid α} [M.Finite] {A B X H : Set α}

theorem natRank_submodular_sets (M : Matroid α) [M.Finite] (X Y : Set α) :
    natRank M (X ∩ Y) + natRank M (X ∪ Y) ≤ natRank M X + natRank M Y := by
  simpa only [natRank_closure] using natRank_submodular M X Y

/-- BG-01/BG-02: ranks in an additive ground partition add on every subset. -/
theorem natRank_partition (hd : Disjoint A B) (hu : A ∪ B = M.E)
    (hr : natRank M A + natRank M B = natRank M M.E) (hX : X ⊆ M.E) :
    natRank M X = natRank M (X ∩ A) + natRank M (X ∩ B) := by
  have h1 := natRank_submodular_sets M X A
  have h2 := natRank_submodular_sets M (X ∪ A) B
  have h3 := natRank_submodular_sets M (X ∩ A) (X ∩ B)
  have heq1 : (X ∪ A) ∩ B = X ∩ B := by
    rw [Set.union_inter_distrib_right, Set.disjoint_iff_inter_eq_empty.mp hd, Set.union_empty]
  have heq2 : (X ∪ A) ∪ B = M.E := by
    rw [Set.union_assoc, hu, Set.union_eq_right.mpr hX]
  have heq3 : (X ∩ A) ∩ (X ∩ B) = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp (hd.mono Set.inter_subset_right Set.inter_subset_right)
  have heq4 : (X ∩ A) ∪ (X ∩ B) = X := by
    rw [← Set.inter_union_distrib_left, hu, Set.inter_eq_left.mpr hX]
  rw [heq1, heq2] at h2
  rw [heq3, heq4, natRank_empty] at h3
  omega

/-- A set losing an element outside a flat loses rank when intersected with it. -/
theorem natRank_inter_lt_of_not_subset_flat (hH : M.IsFlat H)
    (hXE : X ⊆ M.E) (hn : ¬ X ⊆ H) : natRank M (X ∩ H) < natRank M X := by
  by_contra h
  have hr : M.eRk X ≤ M.eRk (X ∩ H) := by
    rw [← cast_natRank M X, ← cast_natRank M (X ∩ H)]
    exact_mod_cast (not_lt.mp h)
  have hc : M.closure (X ∩ H) = M.closure X :=
    (M.isRkFinite_set (X ∩ H)).closure_eq_closure_of_subset_of_eRk_ge_eRk
      Set.inter_subset_left hr
  apply hn
  exact (M.subset_closure X hXE).trans
    (hc.symm.subset.trans ((M.closure_mono Set.inter_subset_right).trans_eq hH.closure))

/-- BG-01: a hyperplane in an additive ground partition contains one entire side. -/
theorem hyperplane_contains_partition_side (hd : Disjoint A B) (hu : A ∪ B = M.E)
    (hr : natRank M A + natRank M B = natRank M M.E) (hH : IsHyperplane M H) :
    A ⊆ H ∨ B ⊆ H := by
  by_contra hn
  have hn := not_or.mp hn
  have hAE : A ⊆ M.E := Set.subset_union_left.trans_eq hu
  have hBE : B ⊆ M.E := Set.subset_union_right.trans_eq hu
  have hA : natRank M (A ∩ H) < natRank M A := natRank_inter_lt_of_not_subset_flat hH.1 hAE hn.1
  have hB : natRank M (B ∩ H) < natRank M B := natRank_inter_lt_of_not_subset_flat hH.1 hBE hn.2
  have hsplit := natRank_partition hd hu hr hH.1.subset_ground
  rw [Set.inter_comm H A, Set.inter_comm H B] at hsplit
  have hHr := hyperplane_natRank hH
  omega

/-- BG-01: contraction preserves the additive rank of the two residual sides. -/
theorem natRank_contract_partition (hd : Disjoint A B) (hu : A ∪ B = M.E)
    (hr : natRank M A + natRank M B = natRank M M.E) (F : Set α) (hF : F ⊆ M.E) :
    natRank (M.contract F) (A \ F) + natRank (M.contract F) (B \ F) =
      natRank (M.contract F) (M.E \ F) := by
  have hAE : A ⊆ M.E := Set.subset_union_left.trans_eq hu
  have hBE : B ⊆ M.E := Set.subset_union_right.trans_eq hu
  have hA := natRank_contract_add F (A \ F) hF (Set.sdiff_subset_sdiff_left hAE)
  have hB := natRank_contract_add F (B \ F) hF (Set.sdiff_subset_sdiff_left hBE)
  have hE := natRank_contract_add F (M.E \ F) hF Set.Subset.rfl
  have hFA := natRank_partition hd hu hr (Set.union_subset hAE hF)
  have hFB := natRank_partition hd hu hr (Set.union_subset hBE hF)
  have hFF := natRank_partition hd hu hr hF
  have hAA : (A ∪ F) ∩ A = A := by simp
  have hAB : (A ∪ F) ∩ B = F ∩ B := by
    rw [Set.union_inter_distrib_right, Set.disjoint_iff_inter_eq_empty.mp hd, Set.empty_union]
  have hBA : (B ∪ F) ∩ A = F ∩ A := by
    rw [Set.union_inter_distrib_right, Set.disjoint_iff_inter_eq_empty.mp hd.symm, Set.empty_union]
  have hBB : (B ∪ F) ∩ B = B := by simp
  rw [hAA, hAB] at hFA
  rw [hBA, hBB] at hFB
  rw [Set.sdiff_union_self] at hA hB
  rw [Set.sdiff_union_of_subset hF] at hE
  omega

omit [M.Finite] in
/-- BG-01: a basis computes natural rank by its finite cardinality. -/
theorem natRank_eq_ncard_of_isBasis {I S : Set α} (hI : M.IsBasis I S) :
    natRank M S = I.ncard := by
  simp only [natRank, hI.eRk_eq_encard, Set.ncard_def]

/-- Direct-sum background: the hyperplane-side property implies rank additivity.
Extend a basis of A to a ground basis; the remaining basis elements span B,
since otherwise a hyperplane containing them would contain neither full side. -/
theorem natRank_add_of_hyperplane_sides (hd : Disjoint A B) (hu : A ∪ B = M.E)
    (hh : ∀ H : Set α, IsHyperplane M H → A ⊆ H ∨ B ⊆ H) :
    natRank M A + natRank M B = natRank M M.E := by
  have hAE : A ⊆ M.E := Set.subset_union_left.trans_eq hu
  have hBE : B ⊆ M.E := Set.subset_union_right.trans_eq hu
  obtain ⟨I, hI⟩ := M.exists_isBasis A hAE
  obtain ⟨J, hJ, hJA⟩ := hI.exists_isBasis_inter_eq_of_superset hAE Set.Subset.rfl
  let K := J ∩ B
  have hK : M.Indep K := hJ.indep.subset Set.inter_subset_left
  have hJK : J = I ∪ K := by
    rw [← hJA]
    change J = (J ∩ A) ∪ (J ∩ B)
    rw [← Set.inter_union_distrib_left, hu, Set.inter_eq_left.mpr hJ.subset]
  have hBcl : B ⊆ M.closure K := by
    intro e heB
    by_contra heC
    obtain ⟨H, hH, hCH, heH⟩ :=
      exists_hyperplane_superset_notMem (M.isFlat_closure K) (hBE heB) heC
    rcases hh H hH with hAH | hBH
    · have hJH : J ⊆ H := by
        rw [hJK]
        exact Set.union_subset (hI.subset.trans hAH)
          ((M.subset_closure K hK.subset_ground).trans hCH)
      have hEH : M.E ⊆ H := by
        rw [← (Matroid.isBasis_ground_iff.mp hJ).closure_eq]
        exact (M.closure_mono hJH).trans_eq hH.1.closure
      exact hH.2.1 (Set.Subset.antisymm hH.1.subset_ground hEH)
    · exact heH (hBH heB)
  have hBr : natRank M B = natRank M K := by
    apply Nat.le_antisymm
    · simpa only [natRank_closure] using natRank_mono (M := M) hBcl
    · exact natRank_mono Set.inter_subset_right
  have hIK : Disjoint I K := hd.mono hI.subset Set.inter_subset_right
  have hcard : J.ncard = I.ncard + K.ncard := by
    rw [hJK]
    exact Set.ncard_union_eq hIK hI.indep.finite hK.finite
  rw [natRank_eq_ncard_of_isBasis hI, hBr, natRank_eq_ncard_of_isBasis hK.isBasis_self,
    natRank_eq_ncard_of_isBasis hJ]
  exact hcard.symm

end TutteFormalization
