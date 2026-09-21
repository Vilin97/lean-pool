/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.Geometry.ConvexBody.HalfspaceCut

/-!
# `NRR.HalfSpaceCutArea` — area of fixed-normal halfspace cuts

Defines lower and upper halfspace-cut areas for a planar convex body and proves their basic
monotonicity and endpoint properties. The compatibility name `cutArea` denotes the lower cut area.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace NRR.Geometry.ConvexBody

/-- **Lower cut area**: the real-valued Lebesgue measure of `K ∩ {x | ⟪u, x⟫ ≤ c}`. -/
noncomputable def cutAreaLower
    (K : ConvexBody Plane) (u : Plane) (c : ℝ) : ℝ :=
  (volume ((K : Set Plane) ∩ Geometry.lowerClosedHalfspace u c)).toReal

/-- **Upper cut area**: the real-valued Lebesgue measure of `K ∩ {x | c ≤ ⟪u, x⟫}`. -/
noncomputable def cutAreaUpper
    (K : ConvexBody Plane) (u : Plane) (c : ℝ) : ℝ :=
  (volume ((K : Set Plane) ∩ Geometry.upperClosedHalfspace u c)).toReal

/-- The compatibility name `cutArea` denotes the **lower** cut area. -/
noncomputable def cutArea := cutAreaLower

/-! ### Finiteness of the cut measures -/

theorem volume_inter_lowerClosedHalfspace_lt_top
    (K : ConvexBody Plane) (u : Plane) (c : ℝ) :
    volume ((K : Set Plane) ∩ Geometry.lowerClosedHalfspace u c) < ⊤ :=
  lt_of_le_of_lt (measure_mono Set.inter_subset_left) K.area_lt_top

theorem volume_inter_upperClosedHalfspace_lt_top
    (K : ConvexBody Plane) (u : Plane) (c : ℝ) :
    volume ((K : Set Plane) ∩ Geometry.upperClosedHalfspace u c) < ⊤ :=
  lt_of_le_of_lt (measure_mono Set.inter_subset_left) K.area_lt_top

/-! ### Nonnegativity -/

theorem cutAreaLower_nonneg
    (K : ConvexBody Plane) (u : Plane) (c : ℝ) :
    0 ≤ cutAreaLower K u c :=
  ENNReal.toReal_nonneg

theorem cutAreaUpper_nonneg
    (K : ConvexBody Plane) (u : Plane) (c : ℝ) :
    0 ≤ cutAreaUpper K u c :=
  ENNReal.toReal_nonneg

/-! ### Monotonicity in the threshold -/

theorem cutAreaLower_mono
    (K : ConvexBody Plane) (u : Plane) {a b : ℝ} (hab : a ≤ b) :
    cutAreaLower K u a ≤ cutAreaLower K u b := by
  apply ENNReal.toReal_mono (K.volume_inter_lowerClosedHalfspace_lt_top u b).ne
  apply measure_mono
  apply Set.inter_subset_inter_right
  intro x hx
  simp only [Geometry.mem_lowerClosedHalfspace] at *
  linarith

theorem cutAreaUpper_antitone
    (K : ConvexBody Plane) (u : Plane) {a b : ℝ} (hab : a ≤ b) :
    cutAreaUpper K u b ≤ cutAreaUpper K u a := by
  apply ENNReal.toReal_mono (K.volume_inter_upperClosedHalfspace_lt_top u a).ne
  apply measure_mono
  apply Set.inter_subset_inter_right
  intro x hx
  simp only [Geometry.mem_upperClosedHalfspace] at *
  linarith

/-! ### Bounds by the total area -/

theorem cutAreaLower_le_area
    (K : ConvexBody Plane) (u : Plane) (c : ℝ) :
    cutAreaLower K u c ≤ K.area := by
  apply ENNReal.toReal_mono K.area_lt_top.ne
  exact measure_mono Set.inter_subset_left

theorem cutAreaUpper_le_area
    (K : ConvexBody Plane) (u : Plane) (c : ℝ) :
    cutAreaUpper K u c ≤ K.area := by
  apply ENNReal.toReal_mono K.area_lt_top.ne
  exact measure_mono Set.inter_subset_left

end NRR.Geometry.ConvexBody
