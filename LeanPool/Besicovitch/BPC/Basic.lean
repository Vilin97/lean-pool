/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.BPC.Defs

/-!
# Basic facts about the Besicovitch pair condition

This file develops the elementary set-distance API needed by the six-point transfer.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LeanPool.Besicovitch

variable {X : Type*} [PseudoEMetricSpace X] {s t : Set X}

/-- The set distance is bounded by the distance between any selected pair of points. -/
theorem setEDist_le_edist_of_mem {x y : X} (hx : x ∈ s) (hy : y ∈ t) :
    setEDist s t ≤ edist x y := by
  exact iInf_le_of_le x <| iInf_le_of_le hx <| iInf_le_of_le y <| iInf_le_of_le hy le_rfl

/-- Extended set distance is symmetric. -/
theorem setEDist_comm (s t : Set X) : setEDist s t = setEDist t s := by
  apply le_antisymm
  · refine le_iInf fun y ↦ le_iInf fun hy ↦ le_iInf fun x ↦ le_iInf fun hx ↦ ?_
    simpa [edist_comm] using setEDist_le_edist_of_mem (s := s) (t := t) hx hy
  · refine le_iInf fun x ↦ le_iInf fun hx ↦ le_iInf fun y ↦ le_iInf fun hy ↦ ?_
    simpa [edist_comm] using setEDist_le_edist_of_mem (s := t) (t := s) hy hx

@[simp]
theorem setEDist_empty_left (t : Set X) : setEDist ∅ t = ∞ := by
  simp [setEDist]

/-- Two nonempty sets in a metric space have finite extended distance. -/
theorem setEDist_ne_top {Y : Type*} [PseudoMetricSpace Y] {u v : Set Y}
    (hu : u.Nonempty) (hv : v.Nonempty) : setEDist u v ≠ ∞ := by
  obtain ⟨x, hx⟩ := hu
  obtain ⟨y, hy⟩ := hv
  exact ne_top_of_le_ne_top (edist_ne_top x y) (setEDist_le_edist_of_mem hx hy)

/-- A positive finite set distance has a positive real value. -/
theorem setEDist_toReal_pos {Y : Type*} [PseudoMetricSpace Y] {u v : Set Y}
    (hu : u.Nonempty) (hv : v.Nonempty) (hpos : 0 < setEDist u v) :
    0 < (setEDist u v).toReal := by
  exact ENNReal.toReal_pos hpos.ne' (setEDist_ne_top hu hv)

/-- The real set distance is no larger than any distance between the two sets. -/
theorem setEDist_toReal_le_dist {Y : Type*} [PseudoMetricSpace Y] {u v : Set Y}
    (hu : u.Nonempty) (hv : v.Nonempty) {x y : Y} (hx : x ∈ u) (hy : y ∈ v) :
    (setEDist u v).toReal ≤ dist x y := by
  have h := setEDist_le_edist_of_mem hx hy
  have hfinite := setEDist_ne_top hu hv
  rw [← ENNReal.toReal_le_toReal hfinite (edist_ne_top x y)] at h
  simpa [edist_dist] using h

/-- A ball whose radius is at most the set distance misses the opposite set. -/
theorem ball_disjoint_of_le_setEDist_toReal {Y : Type*} [PseudoMetricSpace Y]
    {u v : Set Y} (hu : u.Nonempty) (hv : v.Nonempty) {x : Y} (hx : x ∈ u)
    {r : ℝ} (hr : r ≤ (setEDist u v).toReal) : Disjoint (Metric.ball x r) v := by
  rw [Set.disjoint_left]
  intro y hy hyMem
  have hlower := setEDist_toReal_le_dist hu hv hx hyMem
  rw [Metric.mem_ball'] at hy
  exact (not_lt_of_ge hlower) (hy.trans_le hr)

/-- A strict upper bound on set distance is witnessed by an actual pair of points. -/
theorem exists_edist_lt_of_setEDist_lt {r : ℝ≥0∞} (h : setEDist s t < r) :
    ∃ x ∈ s, ∃ y ∈ t, edist x y < r := by
  rw [setEDist, iInf_lt_iff] at h
  obtain ⟨x, hx⟩ := h
  rw [iInf_lt_iff] at hx
  obtain ⟨hxs, hx⟩ := hx
  rw [iInf_lt_iff] at hx
  obtain ⟨y, hy⟩ := hx
  rw [iInf_lt_iff] at hy
  obtain ⟨hyt, hy⟩ := hy
  exact ⟨x, hxs, y, hyt, hy⟩

/-- A real number above the finite set distance bounds some actual pair distance. -/
theorem exists_dist_lt_of_setEDist_toReal_lt {Y : Type*} [PseudoMetricSpace Y]
    {u v : Set Y} (hu : u.Nonempty) (hv : v.Nonempty) {r : ℝ}
    (h : (setEDist u v).toReal < r) : ∃ x ∈ u, ∃ y ∈ v, dist x y < r := by
  have hr : 0 < r := (ENNReal.toReal_nonneg.trans_lt h)
  have hfinite := setEDist_ne_top hu hv
  have hed : setEDist u v < ENNReal.ofReal r := by
    rw [← ENNReal.toReal_lt_toReal hfinite (by simp)]
    simpa [ENNReal.toReal_ofReal hr.le] using h
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_edist_lt_of_setEDist_lt hed
  refine ⟨x, hx, y, hy, ?_⟩
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr] at hxy
  exact hxy

/-- Raising the density parameter preserves the Besicovitch pair condition. -/
theorem BesicovitchPairCondition.mono {β γ : ℝ} (hβγ : β ≤ γ)
    (hβ : BesicovitchPairCondition β) : BesicovitchPairCondition γ := by
  intro μ hμ
  obtain ⟨τ, hτ, hβ⟩ := hβ μ hμ
  refine ⟨τ, hτ, fun scale hscale ↦ ?_⟩
  obtain ⟨δ, hδ, hβ⟩ := hβ scale hscale
  refine ⟨δ, hδ, fun e₁ e₂ he₁ he₂ he₁n he₂n hpos hlt hdensity ↦ ?_⟩
  apply hβ e₁ e₂ he₁ he₂ he₁n he₂n hpos hlt
  intro x hx r hr hrscale
  refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) (hdensity x hx r hr hrscale)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβγ (by norm_num)) hr.le

/-- A straight set whose mass exceeds `a` contains two points more than `a` apart. -/
theorem IsStraightMeasure.exists_dist_gt {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    (hμ : IsStraightMeasure μ) {s : Set (EuclideanSpace ℝ (Fin 2))}
    (hs : MeasurableSet s) {a : ℝ} (ha : ENNReal.ofReal a < μ s) :
    ∃ x ∈ s, ∃ y ∈ s, a < dist x y := by
  by_contra h
  have hall : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ a := by
    intro x hx y hy
    by_contra hxy
    exact h ⟨x, hx, y, hy, lt_of_not_ge hxy⟩
  have hed : Metric.ediam s ≤ ENNReal.ofReal a :=
    Metric.ediam_le_of_forall_dist_le hall
  exact (not_lt_of_ge hed) (ha.trans_le (hμ s hs))

end LeanPool.Besicovitch
