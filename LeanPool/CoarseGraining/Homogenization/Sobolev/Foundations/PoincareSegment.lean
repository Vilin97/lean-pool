/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
public import Mathlib.Data.Set.Function
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-! # Poincare Segment -/

@[expose] public section

namespace Homogenization

/-!
# Convex-domain segment geometry

This file isolates the algebraic and convexity lemmas for the segment
parametrization

`y ↦ y + t • (x - y)`,

which is the geometric core of the direct bounded-open-convex-domain Poincare
proof. The later analytic files should be able to import this one and work only
with segment identities, convex-membership statements, and `MapsTo` packaging,
without redoing the affine algebra each time.
-/

/-- The point on the segment from `y` to `x` with parameter `t`. -/
noncomputable def segmentBlend {d : ℕ} (x : Vec d) (t : ℝ) (y : Vec d) : Vec d :=
  AffineMap.lineMap y x t

@[simp] theorem segmentBlend_eq_lineMap {d : ℕ} (x y : Vec d) (t : ℝ) :
    segmentBlend x t y = AffineMap.lineMap y x t :=
  rfl

@[simp] theorem segmentBlend_zero {d : ℕ} (x y : Vec d) :
    segmentBlend x 0 y = y := by
  simp [segmentBlend]

@[simp] theorem segmentBlend_one {d : ℕ} (x y : Vec d) :
    segmentBlend x 1 y = x := by
  simp [segmentBlend]

@[simp] theorem segmentBlend_self {d : ℕ} (x : Vec d) (t : ℝ) :
    segmentBlend x t x = x := by
  simp [segmentBlend]

theorem segmentBlend_eq_add_smul_sub {d : ℕ} (x y : Vec d) (t : ℝ) :
    segmentBlend x t y = y + t • (x - y) := by
  simpa [segmentBlend, add_comm] using (AffineMap.lineMap_apply_module' y x t)

theorem segmentBlend_eq_smul_add {d : ℕ} (x y : Vec d) (t : ℝ) :
    segmentBlend x t y = (1 - t) • y + t • x := by
  simpa [segmentBlend] using (AffineMap.lineMap_apply_module y x t)

theorem add_smul_sub_eq_segmentBlend {d : ℕ} (x y : Vec d) (t : ℝ) :
    x + t • (y - x) = segmentBlend y t x := by
  simpa using (segmentBlend_eq_add_smul_sub y x t).symm

theorem segmentBlend_sub_right {d : ℕ} (x y : Vec d) (t : ℝ) :
    segmentBlend x t y - y = t • (x - y) := by
  ext i
  simp [segmentBlend, AffineMap.lineMap_apply_module']

theorem left_sub_segmentBlend {d : ℕ} (x y : Vec d) (t : ℝ) :
    x - segmentBlend x t y = (1 - t) • (x - y) := by
  ext i
  simp [segmentBlend, AffineMap.lineMap_apply_module]
  ring_nf

theorem norm_segmentBlend_sub_right {d : ℕ} (x y : Vec d) (t : ℝ) :
    ‖segmentBlend x t y - y‖ = |t| * ‖x - y‖ := by
  rw [segmentBlend_sub_right, norm_smul, Real.norm_eq_abs]

theorem norm_left_sub_segmentBlend {d : ℕ} (x y : Vec d) (t : ℝ) :
    ‖x - segmentBlend x t y‖ = |1 - t| * ‖x - y‖ := by
  rw [left_sub_segmentBlend, norm_smul, Real.norm_eq_abs]

theorem segmentBlend_mem {d : ℕ} {U : Set (Vec d)} (hU : Convex ℝ U)
    {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segmentBlend x t y ∈ U := by
  simpa [segmentBlend] using hU.lineMap_mem hy hx ⟨ht0, ht1⟩

theorem segmentBlend_mapsTo {d : ℕ} {U : Set (Vec d)} (hU : Convex ℝ U)
    {x : Vec d} (hx : x ∈ U) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Set.MapsTo (segmentBlend x t) U U := by
  intro y hy
  exact segmentBlend_mem hU hx hy ht0 ht1

theorem segmentBlend_mem_of_isOpenBoundedConvexDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {x y : Vec d}
    (hx : x ∈ U) (hy : y ∈ U) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segmentBlend x t y ∈ U :=
  segmentBlend_mem hU.convex hx hy ht0 ht1

theorem segmentBlend_mapsTo_of_isOpenBoundedConvexDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {x : Vec d} (hx : x ∈ U) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Set.MapsTo (segmentBlend x t) U U :=
  segmentBlend_mapsTo hU.convex hx ht0 ht1

theorem ray_mem_of_endpoint_mem_of_isOpenBoundedConvexDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {x ω : Vec d} {s t : ℝ}
    (hx : x ∈ U) (hs : x + s • ω ∈ U) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (hts : t ≤ s) :
    x + t • ω ∈ U := by
  by_cases hs_zero : s = 0
  · have ht_zero : t = 0 := by linarith
    simpa [ht_zero] using hx
  · have hs_pos : 0 < s := lt_of_le_of_ne hs0 (by simpa [eq_comm] using hs_zero)
    have hτ0 : 0 ≤ t / s := by positivity
    have hτ1 : t / s ≤ 1 := by
      have hs_inv_nonneg : 0 ≤ s⁻¹ := by positivity
      have hmul := mul_le_mul_of_nonneg_right hts hs_inv_nonneg
      simpa [div_eq_mul_inv, hs_pos.ne'] using hmul
    have hseg :
        segmentBlend (x + s • ω) (t / s) x ∈ U :=
      segmentBlend_mem_of_isOpenBoundedConvexDomain hU hs hx hτ0 hτ1
    have hEq : x + t • ω = segmentBlend (x + s • ω) (t / s) x := by
      calc
        x + t • ω = x + (((t / s) * s) • ω) := by
          congr 1
          field_simp [hs_pos.ne']
        _ = x + (t / s) • (s • ω) := by rw [← smul_smul]
        _ = x + (t / s) • ((x + s • ω) - x) := by
          congr 1
          abel_nf
        _ = segmentBlend (x + s • ω) (t / s) x := by
          rw [add_smul_sub_eq_segmentBlend]
    rw [hEq]
    exact hseg

end Homogenization
