/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataRadial

/-! # Small radial levels lie in every pole neighborhood -/

@[expose] public noncomputable section
open Set
open scoped Topology

namespace LichnerowiczObata

/-- On a compact space, a nonnegative continuous function with a unique zero
has all sufficiently small sublevels inside any neighborhood of that zero. -/
theorem exists_small_sublevel_subset_of_unique_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {ρ : X → ℝ}
    (hc : Continuous ρ) (hn : ∀ x, 0 ≤ ρ x) {p : X}
    (hz : ∀ x, ρ x = 0 ↔ x = p) {U : Set X} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, ρ x < ε → x ∈ U := by
  have hclosed : IsClosed (ρ '' Uᶜ) := (hU.isClosed_compl.isCompact.image hc).isClosed
  have hzero : (0 : ℝ) ∈ (ρ '' Uᶜ)ᶜ := by
    rintro ⟨x, hx, he⟩
    exact hx ((hz x).mp he ▸ hp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hzero)
  refine ⟨ε, hε, ?_⟩
  intro x hx
  have hd : ρ x ∈ Metric.ball 0 ε := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (hn x)] using hx
  classical
  by_contra hxu
  exact hball hd ⟨x, hxu, rfl⟩

/-- Every neighborhood of the unique maximum contains all sufficiently
small Obata radial levels. In particular this applies to a normal-chart image. -/
theorem exists_small_obata_radial_sublevel_subset
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {f : X → ℝ}
    (hf : Continuous f) {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hb : ∀ x, f x ≤ a) {p : X} (hmax : ∀ x, f x = a ↔ x = p)
    {U : Set X} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, obataRadial K a f x < ε → x ∈ U := by
  have hc : Continuous (obataRadial K a f) := by
    unfold obataRadial
    fun_prop
  have hn : ∀ x, 0 ≤ obataRadial K a f x :=
    fun x => div_nonneg (Real.arccos_nonneg _) (Real.sqrt_nonneg _)
  have hz : ∀ x, obataRadial K a f x = 0 ↔ x = p := by
    intro x
    constructor
    · intro he
      have hsqrt : Real.sqrt K ≠ 0 := (Real.sqrt_pos.mpr hK).ne'
      have hz := (div_eq_zero_iff.mp he).resolve_right hsqrt
      have hle := (le_div_iff₀ ha).mp (Real.arccos_eq_zero.mp hz)
      apply (hmax x).mp
      exact le_antisymm (hb x) (by simpa using hle)
    · intro he
      have hx : f x = a := (hmax x).mpr he
      simp [obataRadial, hx, ha.ne']
  exact exists_small_sublevel_subset_of_unique_zero hc hn hz hU hp

end LichnerowiczObata
