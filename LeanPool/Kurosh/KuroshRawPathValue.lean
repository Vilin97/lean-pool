/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.Kurosh.KuroshCoverLocal

/-!
# Kurosh Raw Path Value

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshRawPathValueDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v

namespace GraphCoveringTheory.Kurosh

theorem test_coverPathValue_rawTree {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) (rawBassSerreOrbitRoot G H) a) :
    coverPathValue G H (rawTreePathMap G H p) = 1 := by
  induction p with
  | nil =>
      simpa [rawTreePathMap] using
        (coverPathValue_nil G H
          (a := rawBassSerreOrbitRoot G H))
  | @cons b c p e ih =>
      rw [rawTreePathMap_cons_raw]
      cases e using Subtype.casesOn with
      | mk e he =>
          cases e using Sum.casesOn with
          | inl f =>
              rw [coverPathValue_pos G H (rawTreePathMap G H p) f]
              rw [ih]
              have hloop := quotientEdgeLoop_tree_pos G H f he
              have hloop' :
                  quotientEdgeLoop G H (coverBaseEdge G H f).2.2 = 𝟙 _ := by
                change quotientEdgeLoop G H f = 𝟙 _
                exact hloop
              simp only [coverEdgeLetter]
              rw [hloop']
              simpa using (treeKuroshFreeInclusion G H).map_one
          | inr f =>
              rw [coverPathValue_neg G H (rawTreePathMap G H p) f]
              rw [ih]
              have hloop := quotientEdgeLoop_tree_neg G H f he
              have hloop' :
                  quotientEdgeLoop G H (coverBaseEdge G H f).2.2 = 𝟙 _ := by
                change quotientEdgeLoop G H f = 𝟙 _
                exact hloop
              simp only [coverEdgeLetter]
              rw [hloop']
              simpa using (treeKuroshFreeInclusion G H).map_one

end GraphCoveringTheory.Kurosh
