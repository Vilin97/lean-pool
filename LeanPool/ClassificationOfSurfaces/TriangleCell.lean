/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.ConeExtension
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceModel
import LeanPool.ClassificationOfSurfaces.PolygonCellRadial
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# A side-parameter-compatible polygon cell model for a triangle

This file identifies the three-sided `PolygonCell` with the standard closed triangle.  The
boundary calibration is exact: circular side `i` at parameter `t` is sent to the affine point at
parameter `t` on standard triangle edge `i`.
-/

open Set Topology

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open Moise

namespace TriangleCell

local instance : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩

/-- The closed standard triangle, viewed as a topological subspace. -/
abbrev StandardTriangle :=
  Moise.standardTrianglePlaneComplex.support

/-- The frontier of the standard triangle. -/
abbrev StandardTriangleBoundary :=
  frontier Moise.standardTrianglePlaneComplex.support

/-- Traverse the three affine sides of the standard triangle during the interval `[0, 3]`. -/
noncomputable def boundaryParam (x : ℝ) : Moise.Plane :=
  if x ≤ 1 then
    AffineMap.lineMap (k := ℝ)
      (Moise.standardTriangleVertex 0) (Moise.standardTriangleVertex 1) x
  else if x ≤ 2 then
    AffineMap.lineMap (k := ℝ)
      (Moise.standardTriangleVertex 1) (Moise.standardTriangleVertex 2) (x - 1)
  else
    AffineMap.lineMap (k := ℝ)
      (Moise.standardTriangleVertex 2) (Moise.standardTriangleVertex 0) (x - 2)

theorem continuous_boundaryParam : Continuous boundaryParam := by
  unfold boundaryParam
  apply Continuous.if_le
    (by fun_prop)
    (by
      apply Continuous.if_le (by fun_prop) (by fun_prop)
        continuous_id continuous_const
      intro x hx
      change x = 2 at hx
      subst x
      norm_num [AffineMap.lineMap_apply_module])
    continuous_id continuous_const
  intro x hx
  change x = 1 at hx
  subst x
  norm_num [AffineMap.lineMap_apply_module]

@[simp]
theorem boundaryParam_zero :
    boundaryParam 0 = Moise.standardTriangleVertex 0 := by
  simp [boundaryParam]

@[simp]
theorem boundaryParam_one :
    boundaryParam 1 = Moise.standardTriangleVertex 1 := by
  simp [boundaryParam]

@[simp]
theorem boundaryParam_two :
    boundaryParam 2 = Moise.standardTriangleVertex 2 := by
  norm_num [boundaryParam]

@[simp]
theorem boundaryParam_three :
    boundaryParam 3 = Moise.standardTriangleVertex 0 := by
  norm_num [boundaryParam]

theorem boundaryParam_mem_frontier {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 3) :
    boundaryParam x ∈ StandardTriangleBoundary := by
  change boundaryParam x ∈
    frontier Moise.standardTrianglePlaneComplex.support
  rw [Moise.standardTrianglePlaneComplex_support,
    ← Moise.standardTriangleCircle_carrier]
  by_cases hx1 : x ≤ 1
  · apply Set.mem_iUnion.mpr
    refine ⟨(0 : ZMod 3), ?_⟩
    unfold Moise.PolygonalCircle.edgeSegment
    rw [segment_eq_image_lineMap]
    refine ⟨x, ⟨hx.1, hx1⟩, ?_⟩
    change
      AffineMap.lineMap (k := ℝ)
          (Moise.standardTriangleVertex 0)
          (Moise.standardTriangleVertex 1) x =
        boundaryParam x
    rw [boundaryParam, ite_eq_left hx1]
  · have hx1' : 1 < x := lt_of_not_ge hx1
    by_cases hx2 : x ≤ 2
    · apply Set.mem_iUnion.mpr
      refine ⟨(1 : ZMod 3), ?_⟩
      unfold Moise.PolygonalCircle.edgeSegment
      rw [segment_eq_image_lineMap]
      refine ⟨x - 1, ⟨by linarith, by linarith⟩, ?_⟩
      change
        AffineMap.lineMap (k := ℝ)
            (Moise.standardTriangleVertex 1)
            (Moise.standardTriangleVertex 2) (x - 1) =
          boundaryParam x
      rw [boundaryParam, ite_eq_right hx1, ite_eq_left hx2]
    · have hx2' : 2 < x := lt_of_not_ge hx2
      apply Set.mem_iUnion.mpr
      refine ⟨(2 : ZMod 3), ?_⟩
      unfold Moise.PolygonalCircle.edgeSegment
      rw [segment_eq_image_lineMap]
      refine ⟨x - 2, ⟨by linarith, by linarith [hx.2]⟩, ?_⟩
      change
        AffineMap.lineMap (k := ℝ)
            (Moise.standardTriangleVertex 2)
            (Moise.standardTriangleVertex 0) (x - 2) =
          boundaryParam x
      rw [boundaryParam, ite_eq_right hx1, ite_eq_right hx2]

/-- The affine boundary traversal, with its frontier-membership proof. -/
noncomputable def boundaryParamIcc (x : Set.Icc (0 : ℝ) (0 + 3)) :
    StandardTriangleBoundary :=
  ⟨boundaryParam x, boundaryParam_mem_frontier (by simpa only [zero_add] using x.2)⟩

theorem continuous_boundaryParamIcc : Continuous boundaryParamIcc := by
  apply Continuous.subtype_mk
  exact continuous_boundaryParam.comp continuous_subtype_val

theorem boundaryParamIcc_zero_eq_three :
    boundaryParamIcc ⟨0, by norm_num⟩ =
      boundaryParamIcc ⟨3, by norm_num⟩ := by
  apply Subtype.ext
  exact boundaryParam_zero.trans boundaryParam_three.symm

private theorem boundaryParam_eq_iff
    (x y : Set.Icc (0 : ℝ) (0 + 3))
    (h : boundaryParam x = boundaryParam y) :
    x = y ∨
      (x = ⟨0, by norm_num⟩ ∧ y = ⟨3, by norm_num⟩) ∨
      (x = ⟨3, by norm_num⟩ ∧ y = ⟨0, by norm_num⟩) := by
  have hx0 : 0 ≤ (x : ℝ) := x.2.1
  have hx3 : (x : ℝ) ≤ 3 := by simpa only [zero_add] using x.2.2
  have hy0 : 0 ≤ (y : ℝ) := y.2.1
  have hy3 : (y : ℝ) ≤ 3 := by simpa only [zero_add] using y.2.2
  have h0 := congrArg (fun p : Moise.Plane => p 0) h
  have h1 := congrArg (fun p : Moise.Plane => p 1) h
  by_cases hx1 : (x : ℝ) ≤ 1
  · by_cases hy1 : (y : ℝ) ≤ 1
    · left
      apply Subtype.ext
      simp only [Fin.isValue, boundaryParam, hx1, ↓reduceIte, Moise.standardTriangleVertex,
        Matrix.cons_val_zero, Matrix.cons_val_one, AffineMap.lineMap_apply_module,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_zero, mul_one, zero_add,
        hy1] at h0
      exact h0
    · have hy1' : 1 < (y : ℝ) := lt_of_not_ge hy1
      by_cases hy2 : (y : ℝ) ≤ 2
      · simp [boundaryParam, hx1, hy1, hy2, Moise.standardTriangleVertex,
          AffineMap.lineMap_apply_module] at h0 h1
        exfalso
        linarith
      · right
        left
        have hy2' : 2 < (y : ℝ) := lt_of_not_ge hy2
        simp [boundaryParam, hx1, hy1, hy2, Moise.standardTriangleVertex,
          AffineMap.lineMap_apply_module] at h0 h1
        constructor <;> apply Subtype.ext <;> simp_all ; linarith
  · have hx1' : 1 < (x : ℝ) := lt_of_not_ge hx1
    by_cases hx2 : (x : ℝ) ≤ 2
    · by_cases hy1 : (y : ℝ) ≤ 1
      · simp [boundaryParam, hx1, hx2, hy1, Moise.standardTriangleVertex,
          AffineMap.lineMap_apply_module] at h0 h1
        exfalso
        linarith
      · have hy1' : 1 < (y : ℝ) := lt_of_not_ge hy1
        by_cases hy2 : (y : ℝ) ≤ 2
        · left
          apply Subtype.ext
          simp [boundaryParam, hx1, hx2, hy1, hy2,
            Moise.standardTriangleVertex,
            AffineMap.lineMap_apply_module] at h0 h1
          linarith
        · have hy2' : 2 < (y : ℝ) := lt_of_not_ge hy2
          simp [boundaryParam, hx1, hx2, hy1, hy2,
            Moise.standardTriangleVertex,
            AffineMap.lineMap_apply_module] at h0 h1
          exfalso
          linarith
    · have hx2' : 2 < (x : ℝ) := lt_of_not_ge hx2
      by_cases hy1 : (y : ℝ) ≤ 1
      · right
        right
        simp [boundaryParam, hx1, hx2, hy1, Moise.standardTriangleVertex,
          AffineMap.lineMap_apply_module] at h0 h1
        constructor <;> apply Subtype.ext <;> simp_all ; linarith
      · have hy1' : 1 < (y : ℝ) := lt_of_not_ge hy1
        by_cases hy2 : (y : ℝ) ≤ 2
        · simp [boundaryParam, hx1, hx2, hy1, hy2,
            Moise.standardTriangleVertex,
            AffineMap.lineMap_apply_module] at h0 h1
          exfalso
          linarith
        · left
          apply Subtype.ext
          simp [boundaryParam, hx1, hx2, hy1, hy2,
            Moise.standardTriangleVertex,
            AffineMap.lineMap_apply_module] at h0 h1
          linarith

/-- The quotient of `[0,3]` with its endpoints identified maps around the standard frontier. -/
noncomputable def boundaryQuotMap :
    Quot (AddCircle.EndpointIdent (3 : ℝ) 0) → StandardTriangleBoundary :=
  Quot.lift boundaryParamIcc (by
    rintro _ _ ⟨_⟩
    simpa only [zero_add] using boundaryParamIcc_zero_eq_three)

theorem continuous_boundaryQuotMap : Continuous boundaryQuotMap := by
  exact continuous_quot_lift _ continuous_boundaryParamIcc

theorem injective_boundaryQuotMap : Function.Injective boundaryQuotMap := by
  intro q r
  induction q using Quot.inductionOn with
  | _ x =>
      induction r using Quot.inductionOn with
      | _ y =>
          intro h
          change boundaryParamIcc x = boundaryParamIcc y at h
          have hval : boundaryParam x = boundaryParam y :=
            congrArg Subtype.val h
          rcases boundaryParam_eq_iff x y hval with hxy | hends | hends
          · subst y
            rfl
          · rcases hends with ⟨rfl, rfl⟩
            have hend :
                AddCircle.EndpointIdent (3 : ℝ) 0
                  ⟨0, by norm_num⟩ ⟨0 + 3, by norm_num⟩ :=
              AddCircle.EndpointIdent.mk
            simpa only [zero_add] using Quot.sound hend
          · rcases hends with ⟨rfl, rfl⟩
            have hend :
                AddCircle.EndpointIdent (3 : ℝ) 0
                  ⟨0, by norm_num⟩ ⟨0 + 3, by norm_num⟩ :=
              AddCircle.EndpointIdent.mk
            simpa only [zero_add] using (Quot.sound hend).symm

theorem surjective_boundaryQuotMap : Function.Surjective boundaryQuotMap := by
  intro p
  have hpCarrier : p.1 ∈ Moise.standardTriangleCircle.carrier := by
    rw [Moise.standardTriangleCircle_carrier,
      ← Moise.standardTrianglePlaneComplex_support]
    exact p.2
  change p.1 ∈
    ⋃ i : ZMod 3, Moise.standardTriangleCircle.edgeSegment i at hpCarrier
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpCarrier
  fin_cases i
  · change p.1 ∈ segment ℝ
      (Moise.standardTriangleVertex 0) (Moise.standardTriangleVertex 1) at hi
    rw [segment_eq_image_lineMap] at hi
    obtain ⟨t, ht, htp⟩ := hi
    let x : Set.Icc (0 : ℝ) (0 + 3) :=
      ⟨t, ht.1, by norm_num; linarith [ht.2]⟩
    refine ⟨Quot.mk _ x, ?_⟩
    change boundaryParamIcc x = p
    apply Subtype.ext
    change boundaryParam t = p.1
    rw [boundaryParam, ite_eq_left ht.2]
    exact htp
  · change p.1 ∈ segment ℝ
      (Moise.standardTriangleVertex 1) (Moise.standardTriangleVertex 2) at hi
    rw [segment_eq_image_lineMap] at hi
    obtain ⟨t, ht, htp⟩ := hi
    let x : Set.Icc (0 : ℝ) (0 + 3) :=
      ⟨1 + t, by linarith [ht.1], by norm_num; linarith [ht.2]⟩
    refine ⟨Quot.mk _ x, ?_⟩
    change boundaryParamIcc x = p
    apply Subtype.ext
    change boundaryParam (1 + t) = p.1
    by_cases ht0 : t = 0
    · subst t
      simpa [Moise.standardTriangleVertex] using htp
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      rw [boundaryParam, ite_eq_right (by linarith), ite_eq_left (by linarith [ht.2])]
      convert htp using 1; ring
  · change p.1 ∈ segment ℝ
      (Moise.standardTriangleVertex 2) (Moise.standardTriangleVertex 0) at hi
    rw [segment_eq_image_lineMap] at hi
    obtain ⟨t, ht, htp⟩ := hi
    let x : Set.Icc (0 : ℝ) (0 + 3) :=
      ⟨2 + t, by linarith [ht.1], by norm_num; linarith [ht.2]⟩
    refine ⟨Quot.mk _ x, ?_⟩
    change boundaryParamIcc x = p
    apply Subtype.ext
    change boundaryParam (2 + t) = p.1
    by_cases ht0 : t = 0
    · subst t
      simpa [Moise.standardTriangleVertex] using htp
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      rw [boundaryParam, ite_eq_right (by linarith), ite_eq_right (by linarith)]
      convert htp using 1; ring

/-- The additive circle of circumference three is the standard triangular frontier. -/
noncomputable def addCircleBoundaryHomeomorph :
    AddCircle (3 : ℝ) ≃ₜ StandardTriangleBoundary :=
  let e : AddCircle (3 : ℝ) ≃ StandardTriangleBoundary :=
    (AddCircle.equivIccQuot 3 0).trans
      (Equiv.ofBijective boundaryQuotMap
        ⟨injective_boundaryQuotMap, surjective_boundaryQuotMap⟩)
  Continuous.homeoOfEquivCompactToT2 (f := e) (by
    exact continuous_boundaryQuotMap.comp
      (AddCircle.homeoIccQuot 3 0).continuous)

/-- The complex unit circle is the standard triangular frontier. -/
noncomputable def circleBoundaryHomeomorph :
    Circle ≃ₜ StandardTriangleBoundary :=
  (AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)).symm.trans
    addCircleBoundaryHomeomorph

private theorem addCircleBoundaryHomeomorph_coe_Icc
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 3) :
    addCircleBoundaryHomeomorph (x : AddCircle (3 : ℝ)) =
      boundaryParamIcc
        ⟨x, by simpa only [zero_add] using hx⟩ := by
  by_cases hx3 : x = 3
  · subst x
    rw [show (↑(3 : ℝ) : AddCircle (3 : ℝ)) = 0 by
      exact AddCircle.coe_period (3 : ℝ)]
    have hzero : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 3 := by norm_num
    have hzero' : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 3) := by
      simpa only [zero_add] using hzero
    change
      boundaryQuotMap
          (AddCircle.equivIccQuot 3 0 (0 : AddCircle (3 : ℝ))) =
        boundaryParamIcc ⟨3, by norm_num⟩
    have he :=
      (AddCircle.equivIco (3 : ℝ) 0).apply_symm_apply ⟨0, hzero'⟩
    change AddCircle.equivIco (3 : ℝ) 0 (0 : AddCircle (3 : ℝ)) =
      ⟨0, hzero'⟩ at he
    rw [show AddCircle.equivIccQuot 3 0 (0 : AddCircle (3 : ℝ)) =
        Quot.mk _ ⟨0, by norm_num⟩ by
      change Quot.mk _ (Set.inclusion Set.Ico_subset_Icc_self
        (AddCircle.equivIco 3 0 (0 : AddCircle (3 : ℝ)))) = _
      rw [he]]
    exact boundaryParamIcc_zero_eq_three
  · have hxIco : x ∈ Set.Ico (0 : ℝ) 3 :=
      ⟨hx.1, hx.2.lt_of_ne hx3⟩
    have hxIco' : x ∈ Set.Ico (0 : ℝ) (0 + 3) := by
      simpa only [zero_add] using hxIco
    change
      boundaryQuotMap
          (AddCircle.equivIccQuot 3 0 (x : AddCircle (3 : ℝ))) =
        boundaryParamIcc ⟨x, by simpa only [zero_add] using hx⟩
    have he :=
      (AddCircle.equivIco (3 : ℝ) 0).apply_symm_apply ⟨x, hxIco'⟩
    change AddCircle.equivIco (3 : ℝ) 0 (x : AddCircle (3 : ℝ)) =
      ⟨x, hxIco'⟩ at he
    rw [show AddCircle.equivIccQuot 3 0 (x : AddCircle (3 : ℝ)) =
        Quot.mk _ ⟨x, by simpa only [zero_add] using hx⟩ by
      change Quot.mk _ (Set.inclusion Set.Ico_subset_Icc_self
        (AddCircle.equivIco 3 0 (x : AddCircle (3 : ℝ)))) = _
      rw [he]]
    rfl

theorem circleBoundaryHomeomorph_side
    (i : Fin 3) (t : unitInterval) :
    circleBoundaryHomeomorph
        (Circle.exp (PolygonCell.sideAngle i t)) =
      ⟨AffineMap.lineMap (k := ℝ)
          (Moise.standardTriangleVertex i)
          (Moise.standardTriangleVertex (finRotate 3 i)) t,
        by
          change
            AffineMap.lineMap (k := ℝ)
                (Moise.standardTriangleVertex i)
                (Moise.standardTriangleVertex (finRotate 3 i)) t ∈
              frontier Moise.standardTrianglePlaneComplex.support
          rw [Moise.standardTrianglePlaneComplex_support,
            ← Moise.standardTriangleCircle_carrier]
          apply Set.mem_iUnion.mpr
          refine ⟨(i : ZMod 3), ?_⟩
          unfold Moise.PolygonalCircle.edgeSegment
          rw [segment_eq_image_lineMap]
          refine ⟨t, t.2, ?_⟩
          congr 2; fin_cases i <;> rfl⟩ := by
  let x : ℝ := i + t
  have hx : x ∈ Set.Icc (0 : ℝ) 3 := by
    have hi0 : (0 : ℝ) ≤ (i : ℕ) := by positivity
    have hi2 : (i : ℕ) ≤ 2 := Nat.le_of_lt_succ i.isLt
    have hi2' : ((i : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hi2
    constructor
    · dsimp [x]
      exact add_nonneg hi0 t.2.1
    · dsimp [x]
      linarith [t.2.2]
  have hcircle :
      AddCircle.homeomorphCircle (by norm_num : (3 : ℝ) ≠ 0)
          (x : AddCircle (3 : ℝ)) =
        Circle.exp (PolygonCell.sideAngle i t) := by
    rw [AddCircle.homeomorphCircle_apply]
    change Circle.exp (2 * Real.pi / 3 * x) =
      Circle.exp (PolygonCell.sideAngle i t)
    congr 1
    dsimp [x]
    unfold PolygonCell.sideAngle
    push_cast
    ring
  change
    addCircleBoundaryHomeomorph
        ((AddCircle.homeomorphCircle
          (by norm_num : (3 : ℝ) ≠ 0)).symm
            (Circle.exp (PolygonCell.sideAngle i t))) = _
  rw [← hcircle, Homeomorph.symm_apply_apply,
    addCircleBoundaryHomeomorph_coe_Icc hx]
  apply Subtype.ext
  change boundaryParam x =
    AffineMap.lineMap (k := ℝ)
      (Moise.standardTriangleVertex i)
      (Moise.standardTriangleVertex (finRotate 3 i)) t
  have hicases : i = 0 ∨ i = 1 ∨ i = 2 := by
    fin_cases i <;> simp
  rcases hicases with rfl | rfl | rfl
  · have hxval : x = (t : ℝ) := by simp [x]
    have hrot : finRotate 3 (0 : Fin 3) = 1 := rfl
    rw [hxval, hrot, boundaryParam, ite_eq_left t.2.2]
  · have hxval : x = 1 + (t : ℝ) := by norm_num [x]
    have hrot : finRotate 3 (1 : Fin 3) = 2 := rfl
    rw [hxval, hrot]
    by_cases ht0 : (t : ℝ) = 0
    · have ht : t = 0 := Subtype.ext ht0
      subst t
      norm_num [boundaryParam, AffineMap.lineMap_apply_module]
    · have htpos : 0 < (t : ℝ) :=
        lt_of_le_of_ne t.2.1 (Ne.symm ht0)
      rw [boundaryParam, ite_eq_right (by linarith),
        ite_eq_left (by linarith [t.2.2])]
      congr 2
      ring
  · have hxval : x = 2 + (t : ℝ) := by norm_num [x]
    have hrot : finRotate 3 (2 : Fin 3) = 0 := rfl
    rw [hxval, hrot]
    by_cases ht0 : (t : ℝ) = 0
    · have ht : t = 0 := Subtype.ext ht0
      subst t
      norm_num [boundaryParam, AffineMap.lineMap_apply_module]
    · have htpos : 0 < (t : ℝ) :=
        lt_of_le_of_ne t.2.1 (Ne.symm ht0)
      rw [boundaryParam, ite_eq_right (by linarith),
        ite_eq_right (by linarith)]
      congr 2
      ring

/-- An ambient straightening of the standard triangle to the Euclidean closed unit disk. -/
theorem exists_triangleAmbientHomeomorph :
    ∃ h : Moise.Plane ≃ₜ ℂ,
      h '' Moise.standardTrianglePlaneComplex.support = Metric.closedBall 0 1 ∧
      h '' frontier Moise.standardTrianglePlaneComplex.support = Metric.sphere 0 1 := by
  obtain ⟨g, _hinterior, hclosure, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      Moise.standardTrianglePlaneComplex_isTriangle.convex
      Moise.standardTrianglePlaneComplex_isTriangle.infinite_interior.nonempty
      Moise.standardTrianglePlaneComplex.isCompact_support.isBounded
  let h : Moise.Plane ≃ₜ ℂ :=
    g.trans Moise.PolygonalCircle.planeComplexEquiv.toHomeomorph
  have hball :
      Moise.PolygonalCircle.planeComplexEquiv ''
          Metric.closedBall (0 : Moise.Plane) 1 =
        Metric.closedBall (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [Metric.mem_closedBall,
        Moise.PolygonalCircle.norm_planeComplexEquiv] using hx
    · intro hz
      refine ⟨Moise.PolygonalCircle.planeComplexEquiv.symm z, ?_, by simp⟩
      simpa [Metric.mem_closedBall,
        Moise.PolygonalCircle.norm_planeComplexEquiv] using hz
  have hsphere :
      Moise.PolygonalCircle.planeComplexEquiv ''
          Metric.sphere (0 : Moise.Plane) 1 =
        Metric.sphere (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [Metric.mem_sphere,
        Moise.PolygonalCircle.norm_planeComplexEquiv] using hx
    · intro hz
      refine ⟨Moise.PolygonalCircle.planeComplexEquiv.symm z, ?_, by simp⟩
      simpa [Metric.mem_sphere,
        Moise.PolygonalCircle.norm_planeComplexEquiv] using hz
  refine ⟨h, ?_, ?_⟩
  · rw [show h '' Moise.standardTrianglePlaneComplex.support =
        Moise.PolygonalCircle.planeComplexEquiv ''
          (g '' Moise.standardTrianglePlaneComplex.support) by
      rw [Set.image_image]
      rfl]
    have hsupport :
        g '' Moise.standardTrianglePlaneComplex.support =
          Metric.closedBall (0 : Moise.Plane) 1 := by
      simpa only [
        Moise.standardTrianglePlaneComplex.isCompact_support.isClosed.closure_eq]
        using hclosure
    rw [hsupport, hball]
  · rw [show h '' frontier Moise.standardTrianglePlaneComplex.support =
        Moise.PolygonalCircle.planeComplexEquiv ''
          (g '' frontier Moise.standardTrianglePlaneComplex.support) by
      rw [Set.image_image]
      rfl]
    rw [hfrontier, hsphere]

/-- The `triangleAmbientHomeomorph` declaration. -/
noncomputable def triangleAmbientHomeomorph : Moise.Plane ≃ₜ ℂ :=
  Classical.choose exists_triangleAmbientHomeomorph

theorem triangleAmbientHomeomorph_image_triangle :
    triangleAmbientHomeomorph '' Moise.standardTrianglePlaneComplex.support =
      Metric.closedBall 0 1 :=
  (Classical.choose_spec exists_triangleAmbientHomeomorph).1

theorem triangleAmbientHomeomorph_image_boundary :
    triangleAmbientHomeomorph ''
        frontier Moise.standardTrianglePlaneComplex.support =
      Metric.sphere 0 1 :=
  (Classical.choose_spec exists_triangleAmbientHomeomorph).2

/-- Restrict the ambient straightening to the closed triangle. -/
noncomputable def triangleDiskHomeomorph :
    StandardTriangle ≃ₜ PolygonCell 3 where
  toFun z :=
    ⟨triangleAmbientHomeomorph z.1, by
      rw [← triangleAmbientHomeomorph_image_triangle]
      exact ⟨z.1, z.2, rfl⟩⟩
  invFun z :=
    ⟨triangleAmbientHomeomorph.symm z.val, by
      have hz :
          triangleAmbientHomeomorph
              (triangleAmbientHomeomorph.symm z.val) ∈
            triangleAmbientHomeomorph ''
              Moise.standardTrianglePlaneComplex.support := by
        rw [triangleAmbientHomeomorph_image_triangle]
        simpa using z.property
      rcases hz with ⟨w, hw, heq⟩
      exact triangleAmbientHomeomorph.injective heq.symm ▸ hw⟩
  left_inv := by
    intro z
    apply Subtype.ext
    exact triangleAmbientHomeomorph.symm_apply_apply z.1
  right_inv := by
    intro z
    apply PolygonCell.ext
    exact triangleAmbientHomeomorph.apply_symm_apply z.val
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact triangleAmbientHomeomorph.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.2
    exact triangleAmbientHomeomorph.symm.continuous.comp PolygonCell.continuous_val

/-- The ambient straightening restricted to the standard triangular frontier. -/
noncomputable def boundaryCircleHomeomorph :
    StandardTriangleBoundary ≃ₜ Circle where
  toFun z :=
    ⟨triangleAmbientHomeomorph z.1, by
      change triangleAmbientHomeomorph z.1 ∈ Metric.sphere 0 1
      rw [← triangleAmbientHomeomorph_image_boundary]
      exact ⟨z.1, z.2, rfl⟩⟩
  invFun z :=
    ⟨triangleAmbientHomeomorph.symm z, by
      have hz :
          triangleAmbientHomeomorph
              (triangleAmbientHomeomorph.symm z) ∈
            triangleAmbientHomeomorph ''
              frontier Moise.standardTrianglePlaneComplex.support := by
        rw [triangleAmbientHomeomorph_image_boundary]
        rw [triangleAmbientHomeomorph.apply_symm_apply]
        rw [Metric.mem_sphere, dist_zero_right]
        exact Circle.norm_coe z
      rcases hz with ⟨w, hw, heq⟩
      exact triangleAmbientHomeomorph.injective heq.symm ▸ hw⟩
  left_inv := by
    intro z
    apply Subtype.ext
    exact triangleAmbientHomeomorph.symm_apply_apply z.1
  right_inv := by
    intro z
    apply Circle.ext
    exact triangleAmbientHomeomorph.apply_symm_apply z
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact triangleAmbientHomeomorph.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.2
    exact triangleAmbientHomeomorph.symm.continuous.comp continuous_subtype_val

/-- Include the standard frontier in the closed standard triangle. -/
def boundaryInclusion : C(StandardTriangleBoundary, StandardTriangle) where
  toFun z :=
    ⟨z.1, Moise.standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset z.2⟩
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val

@[simp]
theorem triangleDiskHomeomorph_boundary (z : StandardTriangleBoundary) :
    triangleDiskHomeomorph (boundaryInclusion z) =
      PolygonCell.ofCircle 3 (boundaryCircleHomeomorph z) := by
  apply PolygonCell.ext
  rfl

/-- The calibrated homeomorphism from the three-sided cell to the standard triangle. -/
noncomputable def cellHomeomorph : PolygonCell 3 ≃ₜ StandardTriangle :=
  (PolygonCell.radialHomeomorph
      (circleBoundaryHomeomorph.trans boundaryCircleHomeomorph)).trans
    triangleDiskHomeomorph.symm

@[simp]
theorem cellHomeomorph_ofCircle (z : Circle) :
    cellHomeomorph (PolygonCell.ofCircle 3 z) =
      boundaryInclusion (circleBoundaryHomeomorph z) := by
  apply triangleDiskHomeomorph.injective
  rw [cellHomeomorph, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, PolygonCell.radialHomeomorph_ofCircle,
    triangleDiskHomeomorph_boundary]
  rfl

theorem cellHomeomorph_side (i : Fin 3) (t : unitInterval) :
    cellHomeomorph (PolygonCell.side i t) =
      ⟨AffineMap.lineMap (k := ℝ)
          (Moise.standardTriangleVertex i)
          (Moise.standardTriangleVertex (finRotate 3 i)) t,
        by
          have hfrontier :
              AffineMap.lineMap (k := ℝ)
                  (Moise.standardTriangleVertex i)
                  (Moise.standardTriangleVertex (finRotate 3 i)) t ∈
                frontier Moise.standardTrianglePlaneComplex.support := by
            have heq := congrArg Subtype.val
              (circleBoundaryHomeomorph_side i t)
            change
              (circleBoundaryHomeomorph
                  (Circle.exp (PolygonCell.sideAngle i t))).1 =
                AffineMap.lineMap (k := ℝ)
                  (Moise.standardTriangleVertex i)
                  (Moise.standardTriangleVertex (finRotate 3 i)) t at heq
            rw [← heq]
            exact (circleBoundaryHomeomorph
              (Circle.exp (PolygonCell.sideAngle i t))).2
          exact
            Moise.standardTrianglePlaneComplex.isCompact_support.isClosed.frontier_subset
              hfrontier⟩ := by
  rw [show PolygonCell.side i t =
      PolygonCell.ofCircle 3
        (Circle.exp (PolygonCell.sideAngle i t)) by rfl,
    cellHomeomorph_ofCircle]
  apply Subtype.ext
  change
    (circleBoundaryHomeomorph
        (Circle.exp (PolygonCell.sideAngle i t))).1 =
      AffineMap.lineMap (k := ℝ)
        (Moise.standardTriangleVertex i)
        (Moise.standardTriangleVertex (finRotate 3 i)) t
  exact congrArg Subtype.val (circleBoundaryHomeomorph_side i t)

end TriangleCell

end ClassificationOfSurfaces
end Topology
end LeanEval
