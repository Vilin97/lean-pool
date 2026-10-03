/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.FlatRank

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-!
Finite rank compatibility for contraction. The pinned API defines contraction by
dual deletion; its dual and restriction rank formulas therefore suffice
to derive the paper's contraction rank formula without adding an assumption.
-/

public section

namespace TutteFormalization

open scoped Matroid

variable {α : Type*} {M : Matroid α} [M.Finite]

theorem natRank_dual_add (M : Matroid α) [M.Finite] (X : Set α) (hX : X ⊆ M.E) :
    natRank M✶ X + natRank M M.E = natRank M (M.E \ X) + X.ncard := by
  have h := M.eRk_dual_add_eRank X hX
  rw [M.eRank_def, ← cast_natRank M✶ X, ← cast_natRank M M.E,
    ← cast_natRank M (M.E \ X), ← (M.ground_finite.subset hX).cast_ncard_eq] at h
  exact_mod_cast h

theorem natRank_delete (M : Matroid α) (C X : Set α) (hX : X ⊆ M.E \ C) :
    natRank (M ＼ C) X = natRank M X := by
  unfold natRank
  rw [M.delete_eq_restrict, M.restrict_eRk_eq hX]

/-- BG-01: the exact additive form of the contraction rank formula on its ground set. -/
theorem natRank_contract_add (F X : Set α) (hF : F ⊆ M.E) (hX : X ⊆ M.E \ F) :
    natRank (M ／ F) X + natRank M F = natRank M (X ∪ F) := by
  let N := M✶ ＼ F
  have h1 : natRank (M ／ F) X + natRank M✶ (M.E \ F) =
      natRank M✶ ((M.E \ F) \ X) + X.ncard := by
    have h := natRank_dual_add N X hX
    change natRank (M ／ F) X + natRank (M✶ ＼ F) (M.E \ F) =
      natRank (M✶ ＼ F) ((M.E \ F) \ X) + X.ncard at h
    have hd1 : natRank (M✶ ＼ F) (M.E \ F) = natRank M✶ (M.E \ F) :=
      natRank_delete M✶ F (M.E \ F) Set.Subset.rfl
    have hd2 : natRank (M✶ ＼ F) ((M.E \ F) \ X) = natRank M✶ ((M.E \ F) \ X) :=
      natRank_delete M✶ F ((M.E \ F) \ X) Set.sdiff_subset
    simpa only [hd1, hd2] using h
  have h2 := natRank_dual_add M (M.E \ F) Set.sdiff_subset
  have h3 := natRank_dual_add M ((M.E \ F) \ X) (Set.sdiff_subset.trans Set.sdiff_subset)
  have heq2 : M.E \ (M.E \ F) = F := Set.sdiff_sdiff_cancel_left hF
  have heq3 : M.E \ ((M.E \ F) \ X) = X ∪ F := by
    rw [Set.sdiff_sdiff_right, Set.union_comm,
      Set.inter_eq_right.mpr (hX.trans Set.sdiff_subset), heq2]
  rw [heq2] at h2
  rw [heq3] at h3
  have hc : ((M.E \ F) \ X).ncard + X.ncard = (M.E \ F).ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hX (M.ground_finite.sdiff)
  omega

omit [M.Finite] in
/-- BG-01: contracting a flat makes the empty set a flat (the quotient is loopless). -/
theorem contract_empty_isFlat {F : Set α} (hF : M.IsFlat F) :
    (M ／ F).IsFlat ∅ := by
  apply (M ／ F).isFlat_iff_closure_eq.mpr
  simp [M.contract_closure_eq, hF.closure]

theorem natRank_empty (M : Matroid α) : natRank M ∅ = 0 := by
  simp [natRank]

/-- A nonempty ground subset of a loopless matroid has positive rank. -/
theorem natRank_pos_of_empty_isFlat (h0 : M.IsFlat ∅) {A : Set α}
    (hAE : A ⊆ M.E) (hA : A.Nonempty) : 0 < natRank M A := by
  obtain ⟨e, heA⟩ := hA
  have hr : M.eRk {e} = 1 := by
    simpa [h0.closure] using
      (M.eRk_insert_eq_add_one (X := ∅) ⟨hAE heA, by simp [h0.closure]⟩)
  have hnr : natRank M {e} = 1 := by simp [natRank, hr]
  have hmono : natRank M {e} ≤ natRank M A := natRank_mono (Set.singleton_subset_iff.mpr heA)
  omega

/-- Source connectedness for loopless matroids of rank at most one, including rank zero. -/
theorem connected_of_empty_isFlat_of_rank_le_one (h0 : M.IsFlat ∅)
    (hr : natRank M M.E ≤ 1) : Connected M := by
  rintro ⟨A, B, hA, hB, _, hAB, hsep⟩
  have hAE : A ⊆ M.E := Set.subset_union_left.trans_eq hAB
  have hBE : B ⊆ M.E := Set.subset_union_right.trans_eq hAB
  have hposA : 0 < natRank M A := natRank_pos_of_empty_isFlat h0 hAE hA
  have hposB : 0 < natRank M B := natRank_pos_of_empty_isFlat h0 hBE hB
  have hsum : natRank M A + natRank M B = natRank M M.E := by
    rw [← cast_natRank M A, ← cast_natRank M B, ← cast_natRank M M.E] at hsep
    exact_mod_cast hsep
  omega

/-- `def:indecomposable`: every hyperplane is indecomposable. -/
theorem hyperplane_indecomposable {H : Set α} (hH : IsHyperplane M H) :
    Indecomposable M H := by
  refine ⟨hH.1, connected_of_empty_isFlat_of_rank_le_one (contract_empty_isFlat hH.1) ?_⟩
  have h := natRank_contract_add H (M.E \ H) hH.1.subset_ground Set.Subset.rfl
  have heq : (M.E \ H) ∪ H = M.E := Set.sdiff_union_of_subset hH.1.subset_ground
  rw [heq] at h
  have hr : natRank M H + 1 = natRank M M.E := hyperplane_natRank hH
  change natRank (M ／ H) (M.E \ H) ≤ 1
  omega

end TutteFormalization
