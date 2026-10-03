/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.Separation
public import LeanPool.TuttePath.RelativeComplement
public import Mathlib.Data.Set.Finite.Lemmas

-- Modified for Lean Pool: module integration, public visibility, and import paths.

/-! `prop:indecomposable-step`: the source maximal-intersection construction. -/
public section

namespace TutteFormalization
variable {α : Type*} {M : Matroid α} [M.Finite] {S T : Set α}

theorem exists_crossing_hyperplane (hS : M.IsFlat S) (hT : Indecomposable M T)
    (hTS : T ⊂ S) (hSE : S ≠ M.E) :
    ∃ H, IsHyperplane M H ∧ T ⊆ H ∧ ¬ S ⊆ H ∧ S ∪ H ≠ M.E := by
  by_contra hn
  apply (decomposable_iff_separation hT.1).mpr ?_ hT
  refine ⟨S, T ∪ (M.E \ S), ?_, ?_, ne_of_gt hTS, ?_, ?_⟩
  · ext e
    constructor
    · intro he; exact ⟨hTS.subset he, Or.inl he⟩
    · rintro ⟨heS, heT | heD⟩
      · exact heT
      · exact False.elim (heD.2 heS)
  · ext e
    constructor
    · rintro (heS | heT | heD)
      · exact hS.subset_ground heS
      · exact hT.1.subset_ground heT
      · exact heD.1
    · intro he; by_cases hs : e ∈ S
      · exact Or.inl hs
      · exact Or.inr (Or.inr ⟨he, hs⟩)
  · intro heq
    apply hSE
    apply Set.Subset.antisymm hS.subset_ground
    intro e he
    by_cases hs : e ∈ S
    · exact hs
    · exact hTS.subset (heq ▸ (show e ∈ T ∪ (M.E \ S) from Or.inr ⟨he, hs⟩))
  · intro H hH hTH
    by_cases hSH : S ⊆ H
    · exact Or.inl hSH
    right
    have hUnion : S ∪ H = M.E := by
      by_contra hne
      exact hn ⟨H, hH, hTH, hSH, hne⟩
    apply Set.union_subset hTH
    intro e he
    exact (show e ∈ S ∪ H from hUnion.symm ▸ he.1).resolve_left he.2

/-- Source rank-one downward step; the maximized quantity is literally |H ∩ S|. -/
theorem exists_indecomposable_step (hS : Indecomposable M S) (hT : Indecomposable M T)
    (hTS : T ⊂ S) : ∃ U, Indecomposable M U ∧ T ⊆ U ∧ U ⊂ S ∧
      natRank M U + 1 = natRank M S := by
  by_cases hSE : S = M.E
  · obtain ⟨e, heS, heT⟩ := Set.not_subset.mp hTS.not_superset
    obtain ⟨H, hH, hTH, heH⟩ := exists_hyperplane_superset_notMem hT.1
      (hS.1.subset_ground heS) heT
    refine ⟨H, hyperplane_indecomposable hH, hTH, ?_, ?_⟩
    · rw [hSE]; exact Set.ssubset_iff_subset_ne.mpr ⟨hH.1.subset_ground, hH.2.1⟩
    · rw [hSE]; exact hyperplane_natRank hH
  let P : Set (Set α) := {H | IsHyperplane M H ∧ T ⊆ H ∧ ¬ S ⊆ H ∧ S ∪ H ≠ M.E}
  have hPfin : P.Finite := M.ground_finite.powerset.subset
    (fun _ h => h.1.1.subset_ground)
  obtain ⟨H, hH, hmax⟩ := Set.exists_max_image P (fun H => (H ∩ S).ncard) hPfin
    (exists_crossing_hyperplane hS.1 hT hTS hSE)
  obtain ⟨s, hsS, hsH⟩ := Set.not_subset.mp hH.2.2.1
  let U := H ∩ S
  have hU : Indecomposable M U := indecomposable_inter (hyperplane_indecomposable hH.1)
    hS (by simpa only [Set.union_comm] using hH.2.2.2)
  have hTU : T ⊆ U := Set.subset_inter hH.2.1 hTS.subset
  have hUS : U ⊂ S := Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_right, by
    intro heq; exact hsH ((heq.symm ▸ hsS : s ∈ U).1)⟩
  have hlt := natRank_lt_of_flat_ssubset hU.1 hS.1 hUS
  refine ⟨U, hU, hTU, hUS, ?_⟩
  by_contra hneq
  have hgap : natRank M U + 1 < natRank M S := by omega
  let U' := M.closure (insert s U)
  have hU' : M.IsFlat U' := M.isFlat_closure _
  have hU'r : natRank M U' = natRank M U + 1 :=
    natRank_closure_insert hU.1 (hS.1.subset_ground hsS) (fun hs => hsH hs.1)
  have hin : insert s U ⊆ U' := M.subset_closure _
    (Set.insert_subset (hS.1.subset_ground hsS) hU.1.subset_ground)
  have hU'S : U' ⊆ S := (M.closure_mono (Set.insert_subset hsS hUS.subset)).trans_eq hS.1.closure
  have hnSU' : ¬ S ⊆ U' := by
    intro hsub; have := natRank_mono (M := M) hsub; omega
  obtain ⟨s', hs'S, hs'U'⟩ := Set.not_subset.mp hnSU'
  obtain ⟨C, hC, hU'C, hCS, _hjoin, _hr⟩ := exists_relative_complement S U' hS.1 hU' hU'S
  have hs'C : s' ∉ C := fun he => hs'U' (hCS ▸ (show s' ∈ C ∩ S from ⟨he, hs'S⟩))
  obtain ⟨H', hH', hCH', hs'H'⟩ := exists_hyperplane_superset_notMem hC
    (hS.1.subset_ground hs'S) hs'C
  have hU'H' : U' ⊆ H' := hU'C.trans hCH'
  have hHH' : U ⊆ H' := (Set.subset_insert s U).trans (hin.trans hU'H')
  have hsH' : s ∈ H' := hU'H' (hin (Set.mem_insert s U))
  have hPH' : H' ∈ P := by
    refine ⟨hH', hTU.trans hHH', (fun h => hs'H' (h hs'S)), ?_⟩
    intro hUnion
    have hsub : H ⊆ H' := by
      intro e heH
      by_cases heS : e ∈ S
      · exact hHH' ⟨heH, heS⟩
      · exact (show e ∈ S ∪ H' from hUnion.symm ▸ hH.1.1.subset_ground heH).resolve_left heS
    rcases hH.1.2.2 H' hH'.1 hsub with heq | heq
    · exact hsH (heq ▸ hsH')
    · exact hH'.2.1 heq
  have hstrict : U ⊂ H' ∩ S := Set.ssubset_iff_subset_ne.mpr
    ⟨Set.subset_inter hHH' hUS.subset, by
      intro heq; exact hsH ((heq.symm ▸ (show s ∈ H' ∩ S from ⟨hsH', hsS⟩) : s ∈ U).1)⟩
  have hcard := Set.ncard_lt_ncard hstrict
    (M.ground_finite.subset (Set.inter_subset_right.trans hS.1.subset_ground))
  have hbound := hmax H' hPH'
  change (H' ∩ S).ncard ≤ U.ncard at hbound
  omega
end TutteFormalization
