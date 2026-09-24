/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Measure.RestrictedVolume
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Data.Set.Function
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Geometry for ball Poincare estimates

Adapted from CoarseGraining (LeanIntoHomogenization, 2026) with the author's
permission.  This file keeps the bounded convex-domain and affine-segment
interfaces needed by the ball estimate while using the established CKN carriers.
-/

@[expose] public section

namespace CKN

open MeasureTheory

/-- A coordinatewise bounded domain in the native finite-dimensional carrier. -/
def IsBoundedDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ∀ i, |x i| ≤ R

theorem IsBoundedDomain.isBounded {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) : Bornology.IsBounded U := by
  rcases hU with ⟨R, hR, hU⟩
  refine isBounded_iff_forall_norm_le.2 ⟨R, ?_⟩
  intro x hx
  refine (pi_norm_le_iff_of_nonneg hR.le).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using hU x hx i

theorem IsBoundedDomain.volume_lt_top {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) : MeasureTheory.volume U < ⊤ :=
  hU.isBounded.measure_lt_top

theorem IsBoundedDomain.isFiniteMeasure_restrict_volume
    {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) := by
  let _ : Fact (MeasureTheory.volume U < ⊤) := ⟨hU.volume_lt_top⟩
  infer_instance

/-- The average of a scalar function over a restricted volume measure. -/
noncomputable def integralAverage {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  MeasureTheory.average (MeasureTheory.volume.restrict U) u

def IsSobolevRegularDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  MeasurableSet U ∧ IsBoundedDomain U

namespace IsSobolevRegularDomain

theorem measurableSet {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    MeasurableSet U :=
  hU.1

theorem isBoundedDomain {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    IsBoundedDomain U :=
  hU.2

theorem volume_lt_top {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    MeasureTheory.volume U < ⊤ :=
  hU.isBoundedDomain.volume_lt_top

theorem isFiniteMeasure_restrict_volume {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) :=
  hU.isBoundedDomain.isFiniteMeasure_restrict_volume

end IsSobolevRegularDomain

/-- An open bounded convex domain in the native carrier. -/
def IsOpenBoundedConvexDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  IsOpen U ∧ IsBoundedDomain U ∧ Convex ℝ U

namespace IsOpenBoundedConvexDomain

theorem isOpen {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    IsOpen U :=
  hU.1

theorem isBoundedDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) : IsBoundedDomain U :=
  hU.2.1

theorem convex {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    Convex ℝ U :=
  hU.2.2

theorem measurableSet {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    MeasurableSet U :=
  hU.isOpen.measurableSet

theorem isFiniteMeasure_restrict_volume {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) :=
  hU.isBoundedDomain.isFiniteMeasure_restrict_volume

theorem isSobolevRegularDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    IsSobolevRegularDomain U :=
  ⟨hU.measurableSet, hU.isBoundedDomain⟩

end IsOpenBoundedConvexDomain

theorem IsBoundedDomain.norm_le_choose {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) {x : Vec d} (hx : x ∈ U) :
    ‖x‖ ≤ Classical.choose hU := by
  have hRpos : 0 < Classical.choose hU := (Classical.choose_spec hU).1
  have hR : ∀ z ∈ U, ∀ i, |z i| ≤ Classical.choose hU :=
    (Classical.choose_spec hU).2
  refine (pi_norm_le_iff_of_nonneg hRpos.le).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using hR x hx i

theorem IsBoundedDomain.norm_sub_le_two_mul_choose {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) :
    ‖x - y‖ ≤ 2 * Classical.choose hU := by
  calc
    ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    _ ≤ Classical.choose hU + Classical.choose hU :=
      add_le_add (hU.norm_le_choose hx) (hU.norm_le_choose hy)
    _ = 2 * Classical.choose hU := by ring

/-- Translate a set by a vector in the native finite-dimensional carrier. -/
def translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) : Set (Vec d) :=
  {x | ∃ y ∈ U, x = y + z}

theorem mem_translateSet_iff_sub_mem {d : ℕ} {z x : Vec d} {U : Set (Vec d)} :
    x ∈ translateSet z U ↔ x - z ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [sub_eq_add_neg, add_assoc]
  · intro hx
    refine ⟨x - z, hx, ?_⟩
    ext i
    simp [sub_eq_add_neg, add_assoc]

theorem preimage_addNeg_eq_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x + -z) ⁻¹' U = translateSet z U := by
  ext x
  simp [mem_translateSet_iff_sub_mem, sub_eq_add_neg]

theorem translateSet_translateSet {d : ℕ} (z w : Vec d) (U : Set (Vec d)) :
    translateSet w (translateSet z U) = translateSet (z + w) U := by
  ext x
  constructor
  · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by simp [add_assoc]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u + z, ⟨u, hu, rfl⟩, by simp [add_assoc]⟩

@[simp] theorem translateSet_zero {d : ℕ} (U : Set (Vec d)) :
    translateSet (0 : Vec d) U = U := by
  ext x
  simp [translateSet]

theorem measurePreserving_subRight_restrict_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x - z)
      (MeasureTheory.volume.restrict (translateSet z U))
      (MeasureTheory.volume.restrict U) := by
  let hμ : MeasurePreserving (fun x : Vec d => x + -z)
      (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) MeasureTheory.volume :=
    measurePreserving_add_right (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) (-z)
  simpa [preimage_addNeg_eq_translateSet (z := z) U, sub_eq_add_neg] using
    MeasurePreserving.restrict_preimage_emb hμ (Homeomorph.subRight z).measurableEmbedding U

theorem image_addRight_eq_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x + z) '' U = translateSet z U := by
  ext x
  constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, rfl⟩

theorem measurePreserving_addRight_restrict_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x + z)
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict (translateSet z U)) := by
  let hμ : MeasurePreserving (fun x : Vec d => x + z)
      (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) MeasureTheory.volume :=
    measurePreserving_add_right (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) z
  simpa [preimage_addNeg_eq_translateSet (z := z) U, image_addRight_eq_translateSet (z := z) U,
    sub_eq_add_neg] using
    MeasurePreserving.restrict_image_emb hμ (Homeomorph.addRight z).measurableEmbedding U

theorem setIntegral_comp_subRight_translateSet {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ x in translateSet z U, f (x - z) ∂MeasureTheory.volume =
      ∫ y in U, f y ∂MeasureTheory.volume := by
  simpa using
    (measurePreserving_subRight_restrict_translateSet (d := d) z U).integral_comp
      (Homeomorph.subRight z).measurableEmbedding f

theorem setIntegral_comp_addRight_translateSet {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ y in U, f (y + z) ∂MeasureTheory.volume =
      ∫ x in translateSet z U, f x ∂MeasureTheory.volume := by
  simpa using
    (measurePreserving_addRight_restrict_translateSet (d := d) z U).integral_comp
      (Homeomorph.addRight z).measurableEmbedding f

theorem isOpenBoundedConvexDomain_ball {d : ℕ} (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    IsOpenBoundedConvexDomain (Metric.ball x₀ r) := by
  refine ⟨Metric.isOpen_ball, ?_, convex_ball x₀ r⟩
  refine ⟨‖x₀‖ + r + 1, ?_, ?_⟩
  · positivity
  · intro x hx i
    have hx' : ‖x - x₀‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hxi : |x i| ≤ ‖x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
    have hnorm : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
      calc
        ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
    linarith only [hxi, hx', hnorm]

/-- The affine map which sends the unit ball to the ball of radius `r`. -/
def ballAffineMap {d : ℕ} (x₀ : Vec d) (r : ℝ) (x : Vec d) : Vec d :=
  x₀ + r • x

/-- The point on the segment from `y` to `x` with parameter `t`. -/
noncomputable def segmentBlend {d : ℕ} (x : Vec d) (t : ℝ) (y : Vec d) : Vec d :=
  AffineMap.lineMap y x t

@[simp] theorem segmentBlend_zero {d : ℕ} (x y : Vec d) :
    segmentBlend x 0 y = y := by
  simp [segmentBlend]

@[simp] theorem segmentBlend_one {d : ℕ} (x y : Vec d) :
    segmentBlend x 1 y = x := by
  simp [segmentBlend]

theorem segmentBlend_eq_add_smul_sub {d : ℕ} (x y : Vec d) (t : ℝ) :
    segmentBlend x t y = y + t • (x - y) := by
  simpa [segmentBlend, add_comm] using (AffineMap.lineMap_apply_module' y x t)

@[simp] theorem segmentBlend_self {d : ℕ} (x : Vec d) (t : ℝ) :
    segmentBlend x t x = x := by
  simp [segmentBlend]

theorem segmentBlend_mem {d : ℕ} {U : Set (Vec d)} (hU : Convex ℝ U)
    {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segmentBlend x t y ∈ U := by
  simpa [segmentBlend] using hU.lineMap_mem hy hx ⟨ht0, ht1⟩

theorem segmentBlend_mem_of_isOpenBoundedConvexDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {x y : Vec d}
    (hx : x ∈ U) (hy : y ∈ U) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segmentBlend x t y ∈ U :=
  segmentBlend_mem hU.convex hx hy ht0 ht1

end CKN
