/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import LeanPool.Rupert.Equivalences.Util
open Matrix

theorem rupert'_imp_rupert {ι : Type} (v : ι → ℝ³) : IsRupert' v → IsRupert v := by
 intro ⟨ inner_rot, inner_so3, offset, outer_rot,  outer_so3, rupert⟩
 use inner_rot, inner_so3, offset, outer_rot, outer_so3
 let raw_outer_shadow := Set.range fun i ↦ proj_xy (outer_rot.toEuclideanLin (v i))
 let raw_inner_shadow := Set.range fun i ↦ offset + proj_xy (inner_rot.toEuclideanLin (v i))
 let hull := convexHull ℝ (Set.range v)
 let outer_shadow := (fun p ↦ proj_xy (outer_rot.toEuclideanLin p)) '' hull
 let inner_shadow := (fun p ↦ offset + proj_xy (inner_rot.toEuclideanLin p)) '' hull
 have inner_lemma : convexHull ℝ raw_inner_shadow = inner_shadow := by
   dsimp only [raw_inner_shadow, inner_shadow, hull]
   symm; rw [Set.range_comp' (fun p ↦ offset + proj_xy (inner_rot.toEuclideanLin p)) v]
   apply (AffineMap.image_convexHull (full_transform_affine offset ⟨inner_rot, inner_so3⟩))
 have outer_lemma : convexHull ℝ raw_outer_shadow = outer_shadow := by
    dsimp only [raw_outer_shadow, outer_shadow, hull]
    symm; rw [Set.range_comp' (fun p ↦ proj_xy (outer_rot.toEuclideanLin p)) v]
    apply (AffineMap.image_convexHull (proj_xy_rotation_is_affine ⟨outer_rot, outer_so3⟩))
 change raw_inner_shadow ⊆ interior (convexHull ℝ raw_outer_shadow) at rupert
 change inner_shadow ⊆ interior outer_shadow
 rw [← inner_lemma, ← outer_lemma]
 let interior_convex : Convex ℝ (interior (convexHull ℝ raw_outer_shadow)) :=
    Convex.interior (convex_convexHull ℝ raw_outer_shadow)
 exact convexHull_min rupert interior_convex

theorem rupert_imp_rupert' {ι : Type} (v : ι → ℝ³) : IsRupert v → IsRupert' v := by
 intro ⟨ inner_rot, inner_so3, offset, outer_rot,  outer_so3, rupert⟩
 use inner_rot, inner_so3, offset, outer_rot, outer_so3
 let raw_outer_shadow := Set.range fun i ↦ proj_xy (outer_rot.toEuclideanLin (v i))
 let raw_inner_shadow := Set.range fun i ↦ offset + proj_xy (inner_rot.toEuclideanLin (v i))
 let hull := convexHull ℝ (Set.range v)
 let outer_shadow := (fun p ↦ proj_xy (outer_rot.toEuclideanLin p)) '' hull
 let inner_shadow := (fun p ↦ offset + proj_xy (inner_rot.toEuclideanLin p)) '' hull
 have inner_lemma : convexHull ℝ raw_inner_shadow = inner_shadow := by
   dsimp only [raw_inner_shadow, inner_shadow, hull]
   symm; rw [Set.range_comp' (fun p ↦ offset + proj_xy (inner_rot.toEuclideanLin p)) v]
   apply (AffineMap.image_convexHull (full_transform_affine offset ⟨inner_rot, inner_so3⟩))
 have outer_lemma : convexHull ℝ raw_outer_shadow = outer_shadow := by
    dsimp only [raw_outer_shadow, outer_shadow, hull]
    symm; rw [Set.range_comp' (fun p ↦ proj_xy (outer_rot.toEuclideanLin p)) v]
    apply (AffineMap.image_convexHull (proj_xy_rotation_is_affine ⟨outer_rot, outer_so3⟩))
 change raw_inner_shadow ⊆ interior (convexHull ℝ raw_outer_shadow)
 change inner_shadow ⊆ interior outer_shadow at rupert
 rw [outer_lemma]
 rw [← inner_lemma] at rupert
 intro x hx
 exact rupert (subset_convexHull ℝ raw_inner_shadow hx)

theorem rupert_iff_rupert' {ι : Type} (v : ι → ℝ³) : IsRupert v ↔ IsRupert' v :=
  ⟨rupert_imp_rupert' v, rupert'_imp_rupert v⟩
