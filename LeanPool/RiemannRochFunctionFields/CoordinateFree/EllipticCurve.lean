/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.CoordinateFree.RiemannRoch
public import LeanPool.RiemannRochFunctionFields.EllipticCurve.PicTorsorCore

/-!
# Coordinate-free elliptic-curve dictionary

This file restates the elliptic function-field place dictionary and degree-one Picard torsor over
intrinsic places.  The former two-chart implementation remains in
`WeierstrassCurve.Affine.Chart`.
-/

@[expose] public section

open FunctionField
open FunctionField.Chart
open scoped Polynomial RatFunc nonZeroDivisors

namespace WeierstrassCurve.Affine

noncomputable section

variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K]

/-- The intrinsic infinity place of an elliptic function field. -/
noncomputable def infinityPlace : Place k K :=
  chartToPlace k K (Chart.infinityPlace K)

/-- The intrinsic place associated to a Weierstrass point. -/
noncomputable def placeOfPoint (P : W.Point) : Place k K :=
  chartToPlace k K (Chart.placeOfPoint W K P)

omit [IsFullConstantField k K] in
include W in
/-- Every Weierstrass point gives a degree-one intrinsic place. -/
theorem placeOfPoint_deg_one (P : W.Point) :
    (placeOfPoint W K P).degree = 1 := by
  rw [placeOfPoint, ← placeDegree_eq]
  exact Chart.placeOfPoint_deg_one W K P

include W in
omit [WeierstrassCurve.IsElliptic W] in
omit [IsFullConstantField k K] in
/-- The intrinsic infinity place has degree one. -/
theorem infinityPlace_deg_one : (infinityPlace (k := k) K).degree = 1 := by
  rw [infinityPlace, ← placeDegree_eq]
  exact Chart.infinityPlace_deg_one (k := k) W K

/-- Degree-one intrinsic places are equivalent to degree-one coordinate places. -/
noncomputable def degreeOnePlaceEquivChart :
    {v : Place k K // v.degree = 1} ≃ {w : PlaceA k K // placeDegree k K w = 1} where
  toFun v := ⟨(chartToPlace k K).symm v.1, by
    rw [placeDegree_eq]
    simpa using v.2⟩
  invFun w := ⟨chartToPlace k K w.1, by
    rw [← placeDegree_eq]
    exact w.2⟩
  left_inv v := Subtype.ext ((chartToPlace k K).apply_symm_apply v.1)
  right_inv w := Subtype.ext ((chartToPlace k K).symm_apply_apply w.1)

omit [IsFullConstantField k K] in
include W in
/-- Every degree-one intrinsic place comes from a Weierstrass point. -/
theorem exists_point_of_place_degree_one (v : Place k K) (hv : v.degree = 1) :
    ∃ P : W.Point, v = placeOfPoint W K P := by
  let w := (chartToPlace k K).symm v
  have hw : placeDegree k K w = 1 := by
    rw [placeDegree_eq]
    simpa [w] using hv
  obtain ⟨P, hP⟩ := Chart.exists_point_of_place_degree_one W K w hw
  refine ⟨P, ?_⟩
  rw [placeOfPoint, ← hP]
  simp [w]

include W in
/-- The genus of an elliptic function field is one, in the intrinsic API. -/
theorem genus_eq_one : FunctionField.genus k K = 1 :=
  (FunctionField.genus_eq_genusChart k K).trans (Chart.genus_eq_one W K)

/-- The degree-one intrinsic places form the Picard torsor of the elliptic coordinate ring. -/
noncomputable def picTorsor :
    {v : Place k K // v.degree = 1} ≃ ClassGroup W.CoordinateRing :=
  (degreeOnePlaceEquivChart (k := k) K).trans (Chart.Internal.picTorsor' W K)

/-- Compatibility with Angdinata's group law in the intrinsic place API. -/
theorem picTorsor_compat_groupLaw {x y : k} (h : W.Nonsingular x y) :
    picTorsor W K ⟨placeOfPoint W K (Point.some x y h),
        placeOfPoint_deg_one W K (Point.some x y h)⟩ =
      ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' h) := by
  rw [picTorsor]
  change Chart.Internal.picTorsor' W K
      (degreeOnePlaceEquivChart (k := k) K
        ⟨placeOfPoint W K (Point.some x y h),
          placeOfPoint_deg_one W K (Point.some x y h)⟩) = _
  have hz : degreeOnePlaceEquivChart (k := k) K
      ⟨placeOfPoint W K (Point.some x y h),
        placeOfPoint_deg_one W K (Point.some x y h)⟩ =
      ⟨Chart.placeOfPoint W K (Point.some x y h),
        Chart.placeOfPoint_deg_one W K (Point.some x y h)⟩ := by
    apply Subtype.ext
    exact (chartToPlace k K).symm_apply_apply _
  rw [hz]
  exact Chart.Internal.picTorsor'_compat_groupLaw W K h

end

end WeierstrassCurve.Affine
