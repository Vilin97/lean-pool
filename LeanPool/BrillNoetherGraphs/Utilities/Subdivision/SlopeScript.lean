/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ExplicitPotentialRankOne
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.MovingPosition
import Mathlib.Tactic

/-!
# Laplacians of subdivision scripts described by their unit-step slopes

`ExplicitPotentialRankOne` computes `prin` for the *interpolated* script, whose
value along a slot is forced to be affine.  Several all-length constructions
need potentials that bend inside a slot, so this file records the same two
formulas for an arbitrary firing script, keyed only on its unit-step
differences.

A script is described here by a slope datum `slope : Fin p → ℕ → ℤ` together
with the hypothesis that the script rises by `slope edge k` across the `k`-th
unit step of slot `edge`.  Then

* at a core vertex the Laplacian is the sum, over all slots, of the outgoing
  slope at each incident endpoint; and
* at an interior vertex it is the difference of the two adjacent slopes.

Both statements are exact, and neither refers to the values of the script.
-/

namespace Utilities.Certificate

open Finset

namespace SubdivisionGraph.Spec

variable {n p : ℕ} (spec : SubdivisionGraph.Spec n p)

/-- A slope datum for a firing script: the script rises by `slope edge k`
across the `k`-th unit step of slot `edge`. -/
def IsStepSlope (script : firingScript spec.graph) (slope : Fin p → ℕ → ℤ) :
    Prop :=
  ∀ (edge : Fin p) (offset : Fin (spec.length edge)),
    script (spec.stepRight edge offset) - script (spec.stepLeft edge offset) =
      slope edge offset.val

theorem sum_over_first_step (edge : Fin p)
    (value : Fin (spec.length edge) → ℤ) :
    (∑ offset : Fin (spec.length edge),
      if offset.val = 0 then value offset else 0) =
      value ⟨0, spec.length_pos edge⟩ := by
  classical
  let first : Fin (spec.length edge) := ⟨0, spec.length_pos edge⟩
  calc
    (∑ offset : Fin (spec.length edge),
        if offset.val = 0 then value offset else 0) =
        (if first.val = 0 then value first else 0) := by
      apply Fintype.sum_eq_single first
      intro offset hne
      rw [if_neg]
      intro hzero
      apply hne
      apply Fin.ext
      simpa [first] using hzero
    _ = value ⟨0, spec.length_pos edge⟩ := by simp [first]

theorem sum_over_last_step (edge : Fin p)
    (value : Fin (spec.length edge) → ℤ) :
    (∑ offset : Fin (spec.length edge),
      if offset.val + 1 = spec.length edge then value offset else 0) =
      value ⟨spec.length edge - 1, by
        have := spec.length_pos edge
        omega⟩ := by
  classical
  let last : Fin (spec.length edge) :=
    ⟨spec.length edge - 1, by have := spec.length_pos edge; omega⟩
  have hlast : last.val + 1 = spec.length edge := by
    have := spec.length_pos edge
    dsimp [last]
    omega
  calc
    (∑ offset : Fin (spec.length edge),
        if offset.val + 1 = spec.length edge then value offset else 0) =
        (if last.val + 1 = spec.length edge then value last else 0) := by
      apply Fintype.sum_eq_single last
      intro offset hne
      rw [if_neg]
      intro hEq
      apply hne
      apply Fin.ext
      change offset.val = spec.length edge - 1
      omega
    _ = _ := by simp [last, hlast]

/-- The Laplacian of any script, written entirely in terms of its unit-step
slopes. -/
theorem prin_eq_sum_slopes {script : firingScript spec.graph}
    {slope : Fin p → ℕ → ℤ} (hslope : spec.IsStepSlope script slope)
    (vertex : spec.Vertex) :
    prin spec.graph script vertex =
      ∑ step : spec.Step,
        ((if spec.stepLeft step.1 step.2 = vertex then
            slope step.1 step.2.val else 0) +
          (if spec.stepRight step.1 step.2 = vertex then
            -slope step.1 step.2.val else 0)) := by
  classical
  rw [spec.prin_eq_sum_steps]
  apply Finset.sum_congr rfl
  intro step _hstep
  rcases step with ⟨edge, offset⟩
  have hDifference := hslope edge offset
  by_cases hleft : spec.stepLeft edge offset = vertex <;>
    by_cases hright : spec.stepRight edge offset = vertex
  · exact absurd (hleft.trans hright.symm) (spec.stepLeft_ne_stepRight edge offset)
  · subst vertex
    simp only [hright, if_false, if_true, add_zero]
    exact hDifference
  · subst vertex
    simp only [hleft, if_false, if_true, zero_add]
    omega
  · simp [hleft, hright]

/-- At a core vertex, the Laplacian is the sum over all slots of the outgoing
slope at each incident endpoint. -/
theorem prin_coreVertex_eq_endpointSum {script : firingScript spec.graph}
    {slope : Fin p → ℕ → ℤ} (hslope : spec.IsStepSlope script slope)
    (vertex : Fin n) :
    prin spec.graph script (spec.coreVertex vertex) =
      ∑ edge : Fin p,
        ((if spec.core.tail edge = vertex then slope edge 0 else 0) +
          (if spec.core.head edge = vertex then
            -slope edge (spec.length edge - 1) else 0)) := by
  classical
  rw [spec.prin_eq_sum_slopes hslope]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro edge _hedge
  rw [Finset.sum_add_distrib]
  have hLeft :
      (∑ offset : Fin (spec.length edge),
        if spec.stepLeft edge offset = spec.coreVertex vertex then
          slope edge offset.val else 0) =
        if spec.core.tail edge = vertex then slope edge 0 else 0 := by
    by_cases hTail : spec.core.tail edge = vertex
    · simp_rw [spec.stepLeft_eq_coreVertex_iff edge]
      simp only [hTail, and_true]
      simpa using spec.sum_over_first_step edge
        (fun offset => slope edge offset.val)
    · have hNever (offset : Fin (spec.length edge)) :
          spec.stepLeft edge offset ≠ spec.coreVertex vertex := by
        simp [spec.stepLeft_eq_coreVertex_iff edge, hTail]
      simp [hNever, hTail]
  have hRight :
      (∑ offset : Fin (spec.length edge),
        if spec.stepRight edge offset = spec.coreVertex vertex then
          -slope edge offset.val else 0) =
        if spec.core.head edge = vertex then
          -slope edge (spec.length edge - 1) else 0 := by
    by_cases hHead : spec.core.head edge = vertex
    · simp_rw [spec.stepRight_eq_coreVertex_iff edge]
      simp only [hHead, and_true]
      simpa using spec.sum_over_last_step edge
        (fun offset => -slope edge offset.val)
    · have hNever (offset : Fin (spec.length edge)) :
          spec.stepRight edge offset ≠ spec.coreVertex vertex := by
        simp [spec.stepRight_eq_coreVertex_iff edge, hHead]
      simp [hNever, hHead]
  rw [hLeft, hRight]

/-- At an interior vertex, the Laplacian is the difference of the two adjacent
slopes. -/
theorem prin_interiorVertex_eq_slopeDifference
    {script : firingScript spec.graph}
    {slope : Fin p → ℕ → ℤ} (hslope : spec.IsStepSlope script slope)
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    prin spec.graph script (spec.interiorVertex edge offset) =
      slope edge (offset.val + 1) - slope edge offset.val := by
  classical
  rw [spec.prin_eq_sum_slopes hslope]
  rw [Finset.sum_add_distrib]
  have hLeft :
      (∑ step : spec.Step,
        if spec.stepLeft step.1 step.2 = spec.interiorVertex edge offset then
          slope step.1 step.2.val else 0) =
        slope edge (offset.val + 1) := by
    let selected : spec.Step := ⟨edge, spec.nextStep edge offset⟩
    let value : spec.Step → ℤ := fun step =>
      if spec.stepLeft step.1 step.2 = spec.interiorVertex edge offset then
        slope step.1 step.2.val else 0
    change (∑ step : spec.Step, value step) = _
    calc
      (∑ step : spec.Step, value step) = value selected := by
        apply Fintype.sum_eq_single selected
        intro step hne
        by_cases hEqual :
            spec.stepLeft step.1 step.2 = spec.interiorVertex edge offset
        · exact (hne
            ((spec.stepLeft_eq_interiorVertex_iff step edge offset).mp
              hEqual)).elim
        · simp [value, hEqual]
      _ = _ := by simp [value, selected, nextStep]
  have hRight :
      (∑ step : spec.Step,
        if spec.stepRight step.1 step.2 = spec.interiorVertex edge offset then
          -slope step.1 step.2.val else 0) =
        -slope edge offset.val := by
    let selected : spec.Step := ⟨edge, spec.previousStep edge offset⟩
    let value : spec.Step → ℤ := fun step =>
      if spec.stepRight step.1 step.2 = spec.interiorVertex edge offset then
        -slope step.1 step.2.val else 0
    change (∑ step : spec.Step, value step) = _
    calc
      (∑ step : spec.Step, value step) = value selected := by
        apply Fintype.sum_eq_single selected
        intro step hne
        by_cases hEqual :
            spec.stepRight step.1 step.2 = spec.interiorVertex edge offset
        · exact (hne
            ((spec.stepRight_eq_interiorVertex_iff step edge offset).mp
              hEqual)).elim
        · simp [value, hEqual]
      _ = _ := by simp [value, selected, previousStep]
  rw [hLeft, hRight]
  ring

/-! ## Scripts assembled from per-slot path values -/

/-- The script whose value at path position `k` of slot `edge` is
`value edge k`, and `potential v` at the core vertex `v`. -/
def slotValueScript (potential : Fin n → ℤ) (value : Fin p → ℕ → ℤ) :
    firingScript spec.graph
  | Sum.inl vertex => potential vertex
  | Sum.inr interior => value interior.1 (interior.2.val + 1)

@[simp] theorem slotValueScript_core (potential : Fin n → ℤ)
    (value : Fin p → ℕ → ℤ) (vertex : Fin n) :
    spec.slotValueScript potential value (spec.coreVertex vertex) =
      potential vertex := rfl

@[simp] theorem slotValueScript_interior (potential : Fin n → ℤ)
    (value : Fin p → ℕ → ℤ) (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) :
    spec.slotValueScript potential value (spec.interiorVertex edge offset) =
      value edge (offset.val + 1) := rfl

/-- Compatibility of the per-slot values with the core potential. -/
structure SlotValueCompatible (potential : Fin n → ℤ) (value : Fin p → ℕ → ℤ) :
    Prop where
  tail : ∀ edge : Fin p, value edge 0 = potential (spec.core.tail edge)
  head : ∀ edge : Fin p,
    value edge (spec.length edge) = potential (spec.core.head edge)

theorem slotValueScript_stepLeft {potential : Fin n → ℤ}
    {value : Fin p → ℕ → ℤ}
    (hCompat : spec.SlotValueCompatible potential value)
    (edge : Fin p) (offset : Fin (spec.length edge)) :
    spec.slotValueScript potential value (spec.stepLeft edge offset) =
      value edge offset.val := by
  unfold SubdivisionGraph.Spec.stepLeft
  by_cases hzero : offset.val = 0
  · rw [dif_pos hzero, hzero]
    exact (hCompat.tail edge).symm
  · rw [dif_neg hzero]
    show value edge (offset.val - 1 + 1) = value edge offset.val
    congr 1
    omega

theorem slotValueScript_stepRight {potential : Fin n → ℤ}
    {value : Fin p → ℕ → ℤ}
    (hCompat : spec.SlotValueCompatible potential value)
    (edge : Fin p) (offset : Fin (spec.length edge)) :
    spec.slotValueScript potential value (spec.stepRight edge offset) =
      value edge (offset.val + 1) := by
  unfold SubdivisionGraph.Spec.stepRight
  by_cases hlast : offset.val + 1 = spec.length edge
  · rw [dif_pos hlast, hlast]
    exact (hCompat.head edge).symm
  · rw [dif_neg hlast]
    exact spec.slotValueScript_interior potential value edge
      ⟨offset.val, by have := offset.isLt; omega⟩

/-- The unit-step slopes of a compatible slot-value script are the forward
differences of its path values. -/
theorem isStepSlope_slotValueScript {potential : Fin n → ℤ}
    {value : Fin p → ℕ → ℤ}
    (hCompat : spec.SlotValueCompatible potential value) :
    spec.IsStepSlope (spec.slotValueScript potential value)
      (fun edge k => value edge (k + 1) - value edge k) := by
  intro edge offset
  rw [spec.slotValueScript_stepRight hCompat,
    spec.slotValueScript_stepLeft hCompat]

end SubdivisionGraph.Spec

end Utilities.Certificate
