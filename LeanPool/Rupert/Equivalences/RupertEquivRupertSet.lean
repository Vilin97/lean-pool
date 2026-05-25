/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import LeanPool.Rupert.Equivalences.Util
open Matrix

theorem rupert_imp_rupert_set {ι : Type} [Finite ι] (v : ι → ℝ³) :
    IsRupert v → IsRupertSet (convexHull ℝ (Set.range v)) := by
  intro ⟨ inner_rot, inner_so3, inner_offset, outer_rot, outer_so3, rupert⟩
  use inner_rot, inner_so3, inner_offset, outer_rot, outer_so3
  intro inner_shadow outer_shadow
  let tx := full_transform_affine inner_offset ⟨inner_rot, inner_so3⟩
  have inner_shadow_closed : IsClosed inner_shadow := by
    have inner_shadow_is_txed_convex_hull :
        tx '' (convexHull ℝ (Set.range v)) = convexHull ℝ (tx '' Set.range v) := by
      apply AffineMap.image_convexHull
    change inner_shadow = convexHull ℝ (tx '' Set.range v) at inner_shadow_is_txed_convex_hull
    rw [inner_shadow_is_txed_convex_hull, ← Set.range_comp]
    exact Set.Finite.isClosed_convexHull ℝ (Set.finite_range (tx ∘ v))
  rw [closure_eq_iff_isClosed.mpr inner_shadow_closed]
  exact rupert

theorem rupert_set_imp_rupert {ι : Type} [Finite ι] (v : ι → ℝ³) :
    IsRupertSet (convexHull ℝ (Set.range v)) → IsRupert v := by
  intro ⟨ inner_rot, inner_so3, inner_offset, outer_rot, outer_so3, rupert⟩
  use inner_rot, inner_so3, inner_offset, outer_rot, outer_so3
  intro _ _ _ _ ha
  exact rupert (subset_closure ha)

theorem rupert_iff_rupert_set {ι : Type} [Finite ι] (v : ι → ℝ³) :
    IsRupert v ↔ IsRupertSet (convexHull ℝ (Set.range v)) :=
  ⟨rupert_imp_rupert_set v, rupert_set_imp_rupert v⟩
