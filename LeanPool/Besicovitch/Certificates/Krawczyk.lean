/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Contraction certificates

This file gives the small fixed-point argument used by a Krawczyk certificate. A contraction
which preserves a complete nonempty set has a unique fixed point there. If the contraction is a
preconditioned Newton map, that fixed point is the unique zero in the set.
-/

@[expose] public section

open Function NNReal Set

namespace LeanPool.Besicovitch

section FixedPoint

variable {E : Type*} [MetricSpace E] {K : ℝ≥0} {T : E → E} {box : Set E}

/-- A contraction preserving a complete nonempty set has exactly one fixed point in that set. -/
theorem existsUnique_fixedPoint_mem (hbox : box.Nonempty) (hcomplete : IsComplete box)
    (hmaps : MapsTo T box box)
    (hcontract : ContractingWith K (hmaps.restrict T box box)) :
    ∃! x, x ∈ box ∧ IsFixedPt T x := by
  obtain ⟨x, hx⟩ := hbox
  obtain ⟨y, hy, hy_fixed, -, -⟩ :=
    hcontract.exists_fixedPoint' hcomplete hmaps hx (edist_ne_top x (T x))
  refine ⟨y, ⟨hy, hy_fixed⟩, ?_⟩
  intro z hz
  let y' : box := ⟨y, hy⟩
  let z' : box := ⟨z, hz.1⟩
  have hy' : IsFixedPt (hmaps.restrict T box box) y' := by
    apply Subtype.ext
    exact hy_fixed
  have hz' : IsFixedPt (hmaps.restrict T box box) z' := by
    apply Subtype.ext
    exact hz.2
  exact congrArg Subtype.val (hcontract.fixedPoint_unique' hz' hy')

end FixedPoint

section PreconditionedZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : ℝ≥0} {F T : E → E} {R : E →ₗ[ℝ] E} {box : Set E}

/-- A certified preconditioned contraction isolates a unique zero of `F` in `box`. -/
theorem existsUnique_zero_of_contracting_preconditioner (hbox : box.Nonempty)
    (hcomplete : IsComplete box) (hmaps : MapsTo T box box)
    (hcontract : ContractingWith K (hmaps.restrict T box box))
    (hupdate : ∀ x ∈ box, T x = x - R (F x)) (hR : Injective R) :
    ∃! x, x ∈ box ∧ F x = 0 := by
  obtain ⟨x, hx, hx_unique⟩ :=
    existsUnique_fixedPoint_mem hbox hcomplete hmaps hcontract
  have hzero : F x = 0 := by
    apply hR
    rw [map_zero]
    exact sub_eq_self.mp ((hupdate x hx.1).symm.trans hx.2)
  refine ⟨x, ⟨hx.1, hzero⟩, ?_⟩
  intro y hy
  apply hx_unique y
  refine ⟨hy.1, ?_⟩
  change T y = y
  rw [hupdate y hy.1, hy.2, map_zero, sub_zero]

end PreconditionedZero

end LeanPool.Besicovitch
