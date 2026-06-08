/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import LeanPool.Rupert.Equivalences.Util

/-!
# LeanPool.Rupert.Equivalences.RupertEquivRupertPrime

Imported Lean Pool material for `LeanPool.Rupert.Equivalences.RupertEquivRupertPrime`.
-/
open Matrix

theorem rupert'_imp_rupert {ι : Type} (v : ι → ℝ³) : IsRupert' v → IsRupert v := by
 intro ⟨ innerRot, inner_so3, offset, outerRot,  outer_so3, rupert⟩
 use innerRot, inner_so3, offset, outerRot, outer_so3
 let raw_outerShadow := Set.range fun i ↦ projXy (outerRot.toEuclideanLin (v i))
 let raw_inner_shadow := Set.range fun i ↦ offset + projXy (innerRot.toEuclideanLin (v i))
 let hull := convexHull ℝ (Set.range v)
 let outerShadow := (fun p ↦ projXy (outerRot.toEuclideanLin p)) '' hull
 let inner_shadow := (fun p ↦ offset + projXy (innerRot.toEuclideanLin p)) '' hull
 have inner_lemma : convexHull ℝ raw_inner_shadow = inner_shadow := by
   dsimp only [raw_inner_shadow, inner_shadow, hull]
   symm; rw [Set.range_comp' (fun p ↦ offset + projXy (innerRot.toEuclideanLin p)) v]
   apply (AffineMap.image_convexHull (fullTransformAffine offset ⟨innerRot, inner_so3⟩))
 have outer_lemma : convexHull ℝ raw_outerShadow = outerShadow := by
    dsimp only [raw_outerShadow, outerShadow, hull]
    symm; rw [Set.range_comp' (fun p ↦ projXy (outerRot.toEuclideanLin p)) v]
    apply (AffineMap.image_convexHull (projXyRotationIsAffine ⟨outerRot, outer_so3⟩))
 change raw_inner_shadow ⊆ interior (convexHull ℝ raw_outerShadow) at rupert
 change inner_shadow ⊆ interior outerShadow
 rw [← inner_lemma, ← outer_lemma]
 let interior_convex : Convex ℝ (interior (convexHull ℝ raw_outerShadow)) :=
    Convex.interior (convex_convexHull ℝ raw_outerShadow)
 exact convexHull_min rupert interior_convex

theorem rupert_imp_rupert' {ι : Type} (v : ι → ℝ³) : IsRupert v → IsRupert' v := by
 intro ⟨ innerRot, inner_so3, offset, outerRot,  outer_so3, rupert⟩
 use innerRot, inner_so3, offset, outerRot, outer_so3
 let raw_outerShadow := Set.range fun i ↦ projXy (outerRot.toEuclideanLin (v i))
 let raw_inner_shadow := Set.range fun i ↦ offset + projXy (innerRot.toEuclideanLin (v i))
 let hull := convexHull ℝ (Set.range v)
 let outerShadow := (fun p ↦ projXy (outerRot.toEuclideanLin p)) '' hull
 let inner_shadow := (fun p ↦ offset + projXy (innerRot.toEuclideanLin p)) '' hull
 have inner_lemma : convexHull ℝ raw_inner_shadow = inner_shadow := by
   dsimp only [raw_inner_shadow, inner_shadow, hull]
   symm; rw [Set.range_comp' (fun p ↦ offset + projXy (innerRot.toEuclideanLin p)) v]
   apply (AffineMap.image_convexHull (fullTransformAffine offset ⟨innerRot, inner_so3⟩))
 have outer_lemma : convexHull ℝ raw_outerShadow = outerShadow := by
    dsimp only [raw_outerShadow, outerShadow, hull]
    symm; rw [Set.range_comp' (fun p ↦ projXy (outerRot.toEuclideanLin p)) v]
    apply (AffineMap.image_convexHull (projXyRotationIsAffine ⟨outerRot, outer_so3⟩))
 change raw_inner_shadow ⊆ interior (convexHull ℝ raw_outerShadow)
 change inner_shadow ⊆ interior outerShadow at rupert
 rw [outer_lemma]
 rw [← inner_lemma] at rupert
 intro x hx
 exact rupert (subset_convexHull ℝ raw_inner_shadow hx)

theorem rupert_iff_rupert' {ι : Type} (v : ι → ℝ³) : IsRupert v ↔ IsRupert' v :=
  ⟨rupert_imp_rupert' v, rupert'_imp_rupert v⟩
