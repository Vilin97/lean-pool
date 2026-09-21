/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmallRadialLevels
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # Whole radial levels identified by a normal chart -/

@[expose] public noncomputable section
open Set

namespace LichnerowiczObata

/-- Restrict a chart to whole corresponding levels. The source and target
containment hypotheses ensure that no part of either level is omitted. -/
def chartLevelHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (Q : X → ℝ) (ρ : Y → ℝ) (r : ℝ)
    (hsource : ∀ v, Q v = r → v ∈ e.source)
    (htarget : ∀ x, ρ x = r → x ∈ e.target)
    (hlevel : ∀ v ∈ e.source, ρ (e v) = Q v) :
    {v : X // Q v = r} ≃ₜ {x : Y // ρ x = r} where
  toFun v := ⟨e v, (hlevel v (hsource v v.2)).trans v.2⟩
  invFun x := ⟨e.symm x, by
    rw [← hlevel (e.symm x) (e.map_target (htarget x x.2)), e.right_inv (htarget x x.2)]
    exact x.2⟩
  left_inv v := Subtype.ext (e.left_inv (hsource v v.2))
  right_inv x := Subtype.ext (e.right_inv (htarget x x.2))
  continuous_toFun := (e.continuousOn.comp_continuous continuous_subtype_val
    (fun v => hsource v v.2)).subtype_mk _
  continuous_invFun := (e.symm.continuousOn.comp_continuous continuous_subtype_val
    (fun x => htarget x x.2)).subtype_mk _

/-- When a normal chart sends vector norm to scaled radial distance, its
restriction identifies the full small radial level with an actual sphere. -/
def normalSphereLevelHomeomorph {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (e : OpenPartialHomeomorph E M) (ρ : M → ℝ)
    {t : ℝ} (ht : t ≠ 0) (r : ℝ)
    (hsource : ∀ v : E, ‖v‖ = r / t → v ∈ e.source)
    (htarget : ∀ x : M, ρ x = r → x ∈ e.target)
    (hlevel : ∀ v ∈ e.source, ρ (e v) = t * ‖v‖) :
    Metric.sphere (0 : E) (r / t) ≃ₜ {x : M // ρ x = r} where
  toFun v := ⟨e v, by
    have hv : ‖(v : E)‖ = r / t := by simpa only [Metric.mem_sphere, dist_zero_right] using v.2
    rw [hlevel v (hsource v hv), hv]
    field_simp⟩
  invFun x := ⟨e.symm x, by
    have he := hlevel (e.symm x) (e.map_target (htarget x x.2))
    rw [e.right_inv (htarget x x.2), x.2] at he
    have hn : ‖e.symm (x : M)‖ = r / t := by
      apply (eq_div_iff ht).mpr
      nlinarith [he]
    simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩
  left_inv v := Subtype.ext (e.left_inv (hsource v (by
    simpa only [Metric.mem_sphere, dist_zero_right] using v.2)))
  right_inv x := Subtype.ext (e.right_inv (htarget x x.2))
  continuous_toFun := (e.continuousOn.comp_continuous continuous_subtype_val
    (fun v => hsource v (by simpa only [Metric.mem_sphere, dist_zero_right] using v.2))).subtype_mk _
  continuous_invFun := (e.symm.continuousOn.comp_continuous continuous_subtype_val
    (fun x => htarget x x.2)).subtype_mk _

/-- Compactness and a genuine radial normal chart supply whole small sphere
levels. Both source-sphere and target-level containment are conclusions. -/
theorem exists_small_sphere_level_homeomorph_map {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] [CompactSpace M] (e : OpenPartialHomeomorph E M)
    (hzero : (0 : E) ∈ e.source) {ρ : M → ℝ} (hc : Continuous ρ)
    (hn : ∀ x, 0 ≤ ρ x) (hz : ∀ x, ρ x = 0 ↔ x = e 0)
    {t : ℝ} (ht : 0 < t) (hlevel : ∀ v ∈ e.source, ρ (e v) = t * ‖v‖) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0 : E) (ε / t) ⊆ e.source ∧ ∀ r ∈ Ioo 0 ε,
      ∃ H : Metric.sphere (0 : E) (r / t) ≃ₜ {x : M // ρ x = r},
        (∀ v : Metric.sphere (0 : E) (r / t), (v : E) ∈ e.source) ∧
        ∀ v, (H v : M) = e v := by
  obtain ⟨a, ha, htarget⟩ := exists_small_sublevel_subset_of_unique_zero hc hn hz
    e.open_target (e.map_source hzero)
  obtain ⟨b, hb, hsource⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hzero)
  refine ⟨min a (t * b), lt_min ha (mul_pos ht hb), ?_⟩
  refine ⟨?_, ?_⟩
  · apply Set.Subset.trans (Metric.ball_subset_ball ?_) hsource
    apply (div_le_iff₀ ht).mpr
    simpa [mul_comm] using min_le_right a (t * b)
  intro r hr
  have hsrc : ∀ v : E, ‖v‖ = r / t → v ∈ e.source := by
    intro v hv
    apply hsource
    have hrb : r / t < b := (div_lt_iff₀ ht).mpr (by
      have := lt_of_lt_of_le hr.2 (min_le_right a (t * b))
      nlinarith)
    simpa only [Metric.mem_ball, dist_zero_right, hv] using hrb
  have htgt : ∀ x : M, ρ x = r → x ∈ e.target := by
    intro x hx
    apply htarget x
    rw [hx]
    exact lt_of_lt_of_le hr.2 (min_le_left a (t * b))
  refine ⟨normalSphereLevelHomeomorph e ρ ht.ne' r hsrc htgt hlevel, ?_, ?_⟩
  · intro v
    exact hsrc v (by simpa only [Metric.mem_sphere, dist_zero_right] using v.2)
  · intro v
    rfl

/-- Existence-only form of the whole-level normal chart. -/
theorem exists_small_sphere_level_homeomorph {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] [CompactSpace M] (e : OpenPartialHomeomorph E M)
    (hzero : (0 : E) ∈ e.source) {ρ : M → ℝ} (hc : Continuous ρ)
    (hn : ∀ x, 0 ≤ ρ x) (hz : ∀ x, ρ x = 0 ↔ x = e 0)
    {t : ℝ} (ht : 0 < t) (hlevel : ∀ v ∈ e.source, ρ (e v) = t * ‖v‖) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Ioo 0 ε,
      Nonempty (Metric.sphere (0 : E) (r / t) ≃ₜ {x : M // ρ x = r}) := by
  obtain ⟨ε, hε, _, h⟩ := exists_small_sphere_level_homeomorph_map e hzero hc hn hz ht hlevel
  exact ⟨ε, hε, fun r hr => ⟨(h r hr).choose⟩⟩

end LichnerowiczObata
