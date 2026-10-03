/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.Definitions
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Elab.Tactic.NormCast

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-!
Finite-flat rank tools using Mathlib's rank and closure API.
Natural ranks are an internal arithmetic interface to finite `eRk`.
The structural lemmas do not depend on the path theorem.
-/

public section

namespace TutteFormalization

variable {α : Type*} {M : Matroid α} [M.Finite] {F G H : Set α}

/-- Mathlib infers finiteness after arbitrary contraction. -/
theorem contraction_finite (M : Matroid α) [M.Finite] (F : Set α) :
    (M.contract F).Finite := inferInstance

/-- Engineering interface; only used with a finite-ground-set matroid below. -/
@[expose] noncomputable def natRank (M : Matroid α) (F : Set α) : ℕ := (M.eRk F).toNat

theorem cast_natRank (M : Matroid α) [M.Finite] (F : Set α) :
    (natRank M F : ℕ∞) = M.eRk F :=
  ENat.natCast_toNat (M.isRkFinite_set F).eRk_lt_top.ne

theorem natRank_mono (hFG : F ⊆ G) : natRank M F ≤ natRank M G := by
  exact ENat.toNat_le_toNat (M.eRk_mono hFG) (M.isRkFinite_set G).eRk_lt_top.ne

theorem natRank_closure (M : Matroid α) (F : Set α) :
    natRank M (M.closure F) = natRank M F := by
  simp only [natRank, M.eRk_closure_eq]

/-- Convert Mathlib's submodular rank inequality to finite natural ranks. -/
theorem natRank_submodular (M : Matroid α) [M.Finite] (F G : Set α) :
    natRank M (F ∩ G) + natRank M (M.closure (F ∪ G)) ≤
      natRank M F + natRank M G := by
  have h := M.eRk_inter_add_eRk_union_le F G
  rw [← cast_natRank M (F ∩ G), ← cast_natRank M (F ∪ G),
    ← cast_natRank M F, ← cast_natRank M G] at h
  rw [natRank_closure]
  exact_mod_cast h

/-- BG-01: nested flats cannot have nonincreasing rank unless they are equal. -/
theorem flat_eq_of_subset_of_natRank_le (hF : M.IsFlat F) (hG : M.IsFlat G)
    (hFG : F ⊆ G) (hr : natRank M G ≤ natRank M F) : F = G := by
  have her : M.eRk G ≤ M.eRk F := by
    rw [← cast_natRank M G, ← cast_natRank M F]
    exact_mod_cast hr
  have hc : M.closure F = M.closure G :=
    (M.isRkFinite_set F).closure_eq_closure_of_subset_of_eRk_ge_eRk hFG her
  simpa only [hF.closure, hG.closure] using hc

theorem natRank_lt_of_flat_ssubset (hF : M.IsFlat F) (hG : M.IsFlat G)
    (hFG : F ⊂ G) : natRank M F < natRank M G := by
  by_contra hn
  have heq : F = G := flat_eq_of_subset_of_natRank_le hF hG hFG.1 (not_lt.mp hn)
  exact hFG.2 heq.symm.subset

omit [M.Finite] in
/-- BG-01: intersection of flats, via closure monotonicity and extensivity. -/
theorem flat_inter (hF : M.IsFlat F) (hG : M.IsFlat G) : M.IsFlat (F ∩ G) := by
  apply M.isFlat_iff_closure_eq.mpr
  apply Set.Subset.antisymm
  · exact Set.subset_inter
      ((M.closure_mono Set.inter_subset_left).trans_eq hF.closure)
      ((M.closure_mono Set.inter_subset_right).trans_eq hG.closure)
  · exact M.subset_closure _ (Set.inter_subset_left.trans hF.subset_ground)

/-- BG-01: adjoining one element outside a hyperplane spans the ground set. -/
theorem hyperplane_natRank (hH : IsHyperplane M H) :
    natRank M H + 1 = natRank M M.E := by
  have hn : ¬ M.E ⊆ H := fun h => hH.2.1 (Set.Subset.antisymm hH.1.subset_ground h)
  obtain ⟨e, heE, heH⟩ := Set.not_subset.mp hn
  have hins : insert e H ⊆ M.E := Set.insert_subset heE hH.1.subset_ground
  have hHC : H ⊆ M.closure (insert e H) :=
    (Set.subset_insert e H).trans (M.subset_closure _ hins)
  have heC : e ∈ M.closure (insert e H) :=
    M.subset_closure _ hins (Set.mem_insert e H)
  have hCE : M.closure (insert e H) = M.E := by
    rcases hH.2.2 _ (M.isFlat_closure _) hHC with heq | heq
    · exact False.elim (heH (heq ▸ heC))
    · exact heq
  have hr : M.eRk (insert e H) = M.eRk H + 1 :=
    M.eRk_insert_eq_add_one ⟨heE, by simpa only [hH.1.closure] using heH⟩
  have hground : M.eRk (insert e H) = M.eRk M.E := by
    rw [← M.eRk_closure_eq (insert e H), hCE]
  rw [hground, ← cast_natRank M M.E, ← cast_natRank M H] at hr
  exact_mod_cast hr.symm

theorem isHyperplane_of_natRank (hH : M.IsFlat H)
    (hr : natRank M H + 1 = natRank M M.E) : IsHyperplane M H := by
  refine ⟨hH, ?_, ?_⟩
  · intro heq
    rw [heq] at hr
    omega
  · intro G hG hHG
    by_cases heq : G = H
    · exact Or.inl heq
    right
    have hlt : natRank M H < natRank M G :=
      natRank_lt_of_flat_ssubset hH hG (hHG.ssubset_of_ne (Ne.symm heq))
    exact flat_eq_of_subset_of_natRank_le hG M.ground_isFlat hG.subset_ground (by omega)

/-- Strict containment below a hyperplane gives the upper rank bound. -/
theorem hyperplane_inter_eq_of_corankTwo (hF : CorankTwo M F)
    {X Y : Set α} (hX : IsHyperplane M X) (hY : IsHyperplane M Y)
    (hXY : X ≠ Y) (hFX : F ⊆ X) (hFY : F ⊆ Y) : X ∩ Y = F := by
  have hn : ¬ X ⊆ Y := by
    intro h
    rcases hX.2.2 Y hY.1 h with heq | heq
    · exact hXY heq.symm
    · exact hY.2.1 heq
  have hI : M.IsFlat (X ∩ Y) := flat_inter hX.1 hY.1
  have hstrict : X ∩ Y ⊂ X :=
    ⟨Set.inter_subset_left, fun h => hn (h.trans Set.inter_subset_right)⟩
  have hlt : natRank M (X ∩ Y) < natRank M X :=
    natRank_lt_of_flat_ssubset hI hX.1 hstrict
  have hXrank : natRank M X + 1 = natRank M M.E := hyperplane_natRank hX
  have hFrank : natRank M F + 2 = natRank M M.E := by
    have hr := hF.2
    rw [← cast_natRank M F, ← cast_natRank M M.E] at hr
    exact_mod_cast hr
  exact (flat_eq_of_subset_of_natRank_le hF.1 hI (Set.subset_inter hFX hFY)
    (by omega)).symm

end TutteFormalization
