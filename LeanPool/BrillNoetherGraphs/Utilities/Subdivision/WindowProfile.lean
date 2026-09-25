/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionSeparator
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.MovingPosition

/-!
# Signed window profiles on subdivision slots

Many compact Dhar calculations are specified by assigning an integral value
to each core vertex and, on every oriented subdivision slot, allowing one
interval of constant integral slope.  Outside that interval the script is
constant.  Endpoint compatibility is the only gluing condition.

This file turns that description into an actual firing script and computes
its principal divisor solely from the signed window endpoints.  The slope is
allowed to be any integer; the `-1`, `0`, and `1` profiles used in genus four
are special cases.
-/

open Finset

namespace Utilities.Certificate.WindowProfile
open Utilities.Certificate

open Utilities

open SubdivisionGraph

/-! ## One numerical window -/

/-- Value gained by offset `i` across a signed window `[start, stop]`.
The value is zero before `start`, changes with constant slope inside the
window, and is constant after `stop`. -/
def windowValue (start stop : ℕ) (slope : ℤ) (i : ℕ) : ℤ :=
  if i ≤ start then 0
  else if i ≤ stop then slope * (i - start : ℕ)
  else slope * (stop - start : ℕ)

/-- Slope across the unit step beginning at offset `i`. -/
def windowSlope (start stop : ℕ) (slope : ℤ) (i : ℕ) : ℤ :=
  if start ≤ i ∧ i < stop then slope else 0

@[simp] theorem windowValue_zero (start stop : ℕ) (slope : ℤ) :
    windowValue start stop slope 0 = 0 := by
  simp [windowValue]

theorem windowValue_of_stop_le {start stop i : ℕ} {slope : ℤ}
    (hStop : stop ≤ i) (hOrder : start ≤ stop) :
    windowValue start stop slope i = slope * (stop - start : ℕ) := by
  by_cases hIStart : i ≤ start
  · have hEqStartStop : start = stop := by omega
    have hEqI : i = start := by omega
    subst stop
    subst i
    simp [windowValue]
  · by_cases hIStop : i ≤ stop
    · have hEqI : i = stop := by omega
      subst i
      simp [windowValue, hIStart]
    · simp [windowValue, hIStart, hIStop]

/-- Consecutive window values have the advertised slope. -/
theorem windowValue_succ_sub_windowValue {start stop i : ℕ} {slope : ℤ}
    (hOrder : start ≤ stop) :
    windowValue start stop slope (i + 1) -
        windowValue start stop slope i =
      windowSlope start stop slope i := by
  by_cases hBefore : i < start
  · have hi : i ≤ start := by omega
    have hSucc : i + 1 ≤ start := by omega
    have hNotStart : ¬start ≤ i := by omega
    simp [windowValue, windowSlope, hi, hSucc, hNotStart]
  · by_cases hAfter : stop ≤ i
    · have hAfterSucc : stop ≤ i + 1 := by omega
      have hNotBeforeStop : ¬i < stop := by omega
      rw [windowValue_of_stop_le hAfterSucc hOrder,
        windowValue_of_stop_le hAfter hOrder]
      simp [windowSlope, hNotBeforeStop]
    · have hStart : start ≤ i := by omega
      have hStopI : i < stop := by omega
      have hILeStop : i ≤ stop := by omega
      have hSuccNotStart : ¬i + 1 ≤ start := by omega
      have hSuccLeStop : i + 1 ≤ stop := by omega
      by_cases hEq : i = start
      · subst i
        simp [windowValue, windowSlope, hStopI]
      · have hINotStart : ¬i ≤ start := by omega
        have hSub : i + 1 - start = (i - start) + 1 := by omega
        simp only [windowValue, if_neg hSuccNotStart, if_pos hSuccLeStop,
          if_neg hINotStart, if_pos hILeStop]
        rw [hSub]
        push_cast
        simp [windowSlope, hStart, hStopI]
        ring

/-- The divergence of a window slope is concentrated at its two endpoints.
Coincident endpoints cancel automatically. -/
theorem windowSlope_divergence {length start stop j : ℕ} {slope : ℤ}
    (hOrder : start ≤ stop) (hStop : stop ≤ length) (hj : j ≤ length) :
    (if j < length then windowSlope start stop slope j else 0) -
        (if 0 < j then windowSlope start stop slope (j - 1) else 0) =
      (if j = start then slope else 0) -
        (if j = stop then slope else 0) := by
  simp only [windowSlope]
  split_ifs <;> omega

/-! ## Compatible profiles and their firing scripts -/

/-- One signed slope window on every slot, together with compatible values at
the core vertices.  A zero slope or a degenerate window represents a constant
slot. -/
structure Data {n p : ℕ} (spec : SubdivisionGraph.Spec n p) where
  coreValue : Fin n → ℤ
  start : Fin p → ℕ
  stop : Fin p → ℕ
  slope : Fin p → ℤ
  start_le_stop : ∀ edge, start edge ≤ stop edge
  stop_le_length : ∀ edge, stop edge ≤ spec.length edge
  endpoint_compatible : ∀ edge,
    coreValue (spec.core.head edge) =
      coreValue (spec.core.tail edge) +
        slope edge * (stop edge - start edge : ℕ)

namespace Data

variable {n p : ℕ} {spec : SubdivisionGraph.Spec n p}

/-- Numerical value of the profile along one oriented slot. -/
def pathValue (data : Data spec) (edge : Fin p) (offset : ℕ) : ℤ :=
  data.coreValue (spec.core.tail edge) +
    windowValue (data.start edge) (data.stop edge) (data.slope edge) offset

/-- Extend a compatible profile over every subdivision vertex. -/
def script (data : Data spec) : firingScript spec.graph
  | Sum.inl vertex => data.coreValue vertex
  | Sum.inr interior => data.pathValue interior.1 (interior.2.val + 1)

@[simp] theorem script_core (data : Data spec) (vertex : Fin n) :
    data.script (spec.coreVertex vertex) = data.coreValue vertex := rfl

@[simp] theorem script_interior (data : Data spec) (edge : Fin p)
    (offset : Fin (spec.length edge - 1)) :
    data.script (spec.interiorVertex edge offset) =
      data.pathValue edge (offset.val + 1) := rfl

theorem pathValue_zero (data : Data spec) (edge : Fin p) :
    data.pathValue edge 0 = data.coreValue (spec.core.tail edge) := by
  simp [pathValue]

theorem pathValue_length (data : Data spec) (edge : Fin p) :
    data.pathValue edge (spec.length edge) =
      data.coreValue (spec.core.head edge) := by
  rw [pathValue, windowValue_of_stop_le
    (data.stop_le_length edge) (data.start_le_stop edge)]
  exact (data.endpoint_compatible edge).symm

/-- The profile script agrees with its numerical path value at every named
position, including both core endpoints. -/
theorem script_pathVertex (data : Data spec) (edge : Fin p)
    (position : spec.PathPosition edge) :
    data.script (spec.pathVertex edge position) =
      data.pathValue edge position.val := by
  unfold SubdivisionGraph.Spec.pathVertex
  split_ifs with hZero hLast
  · simpa [hZero] using (data.pathValue_zero edge).symm
  · simpa [hLast] using (data.pathValue_length edge).symm
  · change data.pathValue edge (position.val - 1 + 1) =
      data.pathValue edge position.val
    congr 1
    omega

theorem script_stepLeft (data : Data spec) (edge : Fin p)
    (offset : Fin (spec.length edge)) :
    data.script (spec.stepLeft edge offset) =
      data.pathValue edge offset.val := by
  rw [← spec.pathVertex_stepLeftPosition edge offset,
    data.script_pathVertex]
  rfl

theorem script_stepRight (data : Data spec) (edge : Fin p)
    (offset : Fin (spec.length edge)) :
    data.script (spec.stepRight edge offset) =
      data.pathValue edge (offset.val + 1) := by
  rw [← spec.pathVertex_stepRightPosition edge offset,
    data.script_pathVertex]
  rfl

/-- Every emitted unit step has the profile's advertised slope. -/
theorem script_stepDifference (data : Data spec) (edge : Fin p)
    (offset : Fin (spec.length edge)) :
    data.script (spec.stepRight edge offset) -
        data.script (spec.stepLeft edge offset) =
      windowSlope (data.start edge) (data.stop edge)
        (data.slope edge) offset.val := by
  rw [data.script_stepRight, data.script_stepLeft]
  simp only [pathValue]
  rw [add_sub_add_left_eq_sub]
  exact windowValue_succ_sub_windowValue (data.start_le_stop edge)

/-! ## Exact principal divisor -/

/-- The initial endpoint of a slot's signed slope window. -/
def startPosition (data : Data spec) (edge : Fin p) :
    spec.PathPosition edge :=
  ⟨data.start edge, by
    have hOrder := data.start_le_stop edge
    have hStop := data.stop_le_length edge
    omega⟩

/-- The terminal endpoint of a slot's signed slope window. -/
def stopPosition (data : Data spec) (edge : Fin p) :
    spec.PathPosition edge :=
  ⟨data.stop edge, by
    have hStop := data.stop_le_length edge
    omega⟩

@[simp] theorem startPosition_val (data : Data spec) (edge : Fin p) :
    (data.startPosition edge).val = data.start edge := rfl

@[simp] theorem stopPosition_val (data : Data spec) (edge : Fin p) :
    (data.stopPosition edge).val = data.stop edge := rfl

/-- Contribution of one oriented subdivision slot to a principal-divisor
coefficient, expressed only in terms of the slot's signed step slopes. -/
def edgeDivergence (data : Data spec) (edge : Fin p)
    (vertex : spec.Vertex) : ℤ :=
  ∑ offset : Fin (spec.length edge),
    ((if spec.stepLeft edge offset = vertex then
        windowSlope (data.start edge) (data.stop edge)
          (data.slope edge) offset.val else 0) +
      (if spec.stepRight edge offset = vertex then
        -windowSlope (data.start edge) (data.stop edge)
          (data.slope edge) offset.val else 0))

/-- The global principal divisor is the sum of the independent divergences
of the signed slope windows on its subdivision slots. -/
theorem prin_script_eq_sum_edgeDivergence (data : Data spec)
    (vertex : spec.Vertex) :
    prin spec.graph data.script vertex =
      ∑ edge : Fin p, data.edgeDivergence edge vertex := by
  classical
  rw [spec.prin_eq_sum_step_differences]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro edge _hEdge
  simp only [edgeDivergence]
  apply Finset.sum_congr rfl
  intro offset _hOffset
  rw [data.script_stepDifference]

/-- At a named position of one slot, its edge divergence is the numerical
divergence of the two adjacent window slopes. -/
theorem edgeDivergence_pathVertex (data : Data spec) (edge : Fin p)
    (probe : spec.PathPosition edge) :
    data.edgeDivergence edge (spec.pathVertex edge probe) =
      (if probe.val = data.start edge then data.slope edge else 0) -
        (if probe.val = data.stop edge then data.slope edge else 0) := by
  classical
  have hAt : probe.val ≤ spec.length edge := by
    have := probe.isLt
    omega
  have hLeftIff (offset : Fin (spec.length edge)) :
      spec.stepLeft edge offset = spec.pathVertex edge probe ↔
        offset.val = probe.val := by
    rw [← spec.pathVertex_stepLeftPosition edge offset]
    rw [spec.pathVertex_eq_iff_val_eq]
    rfl
  have hRightIff (offset : Fin (spec.length edge)) :
      spec.stepRight edge offset = spec.pathVertex edge probe ↔
        offset.val + 1 = probe.val := by
    rw [← spec.pathVertex_stepRightPosition edge offset]
    rw [spec.pathVertex_eq_iff_val_eq]
    rfl
  simp only [edgeDivergence]
  simp_rw [hLeftIff, hRightIff]
  rw [Finset.sum_add_distrib]
  have hLeftSum :
      (∑ offset : Fin (spec.length edge),
        if offset.val = probe.val then
          windowSlope (data.start edge) (data.stop edge)
            (data.slope edge) offset.val else 0) =
      if probe.val < spec.length edge then
        windowSlope (data.start edge) (data.stop edge)
          (data.slope edge) probe.val else 0 := by
    by_cases hBefore : probe.val < spec.length edge
    · let selected : Fin (spec.length edge) := ⟨probe.val, hBefore⟩
      calc
        (∑ offset : Fin (spec.length edge),
            if offset.val = probe.val then
              windowSlope (data.start edge) (data.stop edge)
                (data.slope edge) offset.val else 0) =
            (if selected.val = probe.val then
              windowSlope (data.start edge) (data.stop edge)
                (data.slope edge) selected.val else 0) := by
          apply Fintype.sum_eq_single selected
          intro other hOther
          rw [if_neg]
          intro hValue
          apply hOther
          apply Fin.ext
          exact hValue
        _ = _ := by simp [selected, hBefore]
    · have hNever (offset : Fin (spec.length edge)) :
          offset.val ≠ probe.val := by
        intro hValue
        have := offset.isLt
        omega
      simp [hBefore, hNever]
  have hRightSum :
      (∑ offset : Fin (spec.length edge),
        if offset.val + 1 = probe.val then
          -windowSlope (data.start edge) (data.stop edge)
            (data.slope edge) offset.val else 0) =
      if 0 < probe.val then
        -windowSlope (data.start edge) (data.stop edge)
          (data.slope edge) (probe.val - 1) else 0 := by
    by_cases hPositive : 0 < probe.val
    · let selected : Fin (spec.length edge) :=
        ⟨probe.val - 1, by omega⟩
      have hSelected : selected.val + 1 = probe.val := by
        dsimp [selected]
        omega
      calc
        (∑ offset : Fin (spec.length edge),
            if offset.val + 1 = probe.val then
              -windowSlope (data.start edge) (data.stop edge)
                (data.slope edge) offset.val else 0) =
            (if selected.val + 1 = probe.val then
              -windowSlope (data.start edge) (data.stop edge)
                (data.slope edge) selected.val else 0) := by
          apply Fintype.sum_eq_single selected
          intro other hOther
          rw [if_neg]
          intro hValue
          apply hOther
          apply Fin.ext
          dsimp [selected]
          omega
        _ = _ := by simp [hPositive, hSelected, selected]
    · have hNever (offset : Fin (spec.length edge)) :
          offset.val + 1 ≠ probe.val := by omega
      simp [hPositive, hNever]
  rw [hLeftSum, hRightSum]
  have hDivergence := windowSlope_divergence (slope := data.slope edge)
    (data.start_le_stop edge) (data.stop_le_length edge) hAt
  by_cases hPositive : 0 < probe.val
  · simpa [hPositive, sub_eq_add_neg] using hDivergence
  · simpa [hPositive, sub_eq_add_neg] using hDivergence

/-- One slot contributes exactly a positive chip at the start of its signed
window and a negative chip at the stop, both weighted by its integral slope.
The statement also covers degenerate and zero-slope windows. -/
theorem edgeDivergence_eq_endpointDivisor (data : Data spec)
    (edge : Fin p) (vertex : spec.Vertex) :
    data.edgeDivergence edge vertex =
      (data.slope edge •
        (oneChip (G := spec.graph)
            (spec.pathVertex edge (data.startPosition edge)) -
          oneChip (G := spec.graph)
            (spec.pathVertex edge (data.stopPosition edge)))) vertex := by
  classical
  by_cases hOn : ∃ probe : spec.PathPosition edge,
      spec.pathVertex edge probe = vertex
  · obtain ⟨probe, rfl⟩ := hOn
    rw [data.edgeDivergence_pathVertex]
    have hStart :
        spec.pathVertex edge probe =
            spec.pathVertex edge (data.startPosition edge) ↔
          probe.val = data.start edge := by
      rw [spec.pathVertex_eq_iff_val_eq]
      rfl
    have hStop :
        spec.pathVertex edge probe =
            spec.pathVertex edge (data.stopPosition edge) ↔
          probe.val = data.stop edge := by
      rw [spec.pathVertex_eq_iff_val_eq]
      rfl
    simp only [Pi.smul_apply, Pi.sub_apply]
    simp [oneChip, hStart, hStop]
    split_ifs <;> ring
  · have hLeft (offset : Fin (spec.length edge)) :
        spec.stepLeft edge offset ≠ vertex := by
      intro hEqual
      apply hOn
      exact ⟨spec.stepLeftPosition edge offset,
        (spec.pathVertex_stepLeftPosition edge offset).trans hEqual⟩
    have hRight (offset : Fin (spec.length edge)) :
        spec.stepRight edge offset ≠ vertex := by
      intro hEqual
      apply hOn
      exact ⟨spec.stepRightPosition edge offset,
        (spec.pathVertex_stepRightPosition edge offset).trans hEqual⟩
    have hStart :
        spec.pathVertex edge (data.startPosition edge) ≠ vertex := by
      intro hEqual
      exact hOn ⟨data.startPosition edge, hEqual⟩
    have hStop :
        spec.pathVertex edge (data.stopPosition edge) ≠ vertex := by
      intro hEqual
      exact hOn ⟨data.stopPosition edge, hEqual⟩
    have hStart' :
        vertex ≠ spec.pathVertex edge (data.startPosition edge) := hStart.symm
    have hStop' :
        vertex ≠ spec.pathVertex edge (data.stopPosition edge) := hStop.symm
    simp [edgeDivergence, hLeft, hRight, oneChip, hStart', hStop']

/-- Exact signed-endpoint formula for the principal divisor of a compatible
window profile.  This is the compact replay theorem: a checker only needs to
validate the profile bounds and endpoint compatibility, not a full potential
at every subdivision vertex. -/
theorem prin_script_eq_endpointDivisors (data : Data spec) :
    prin spec.graph data.script =
      ∑ edge : Fin p,
        data.slope edge •
          (oneChip (G := spec.graph)
              (spec.pathVertex edge (data.startPosition edge)) -
            oneChip (G := spec.graph)
              (spec.pathVertex edge (data.stopPosition edge))) := by
  classical
  funext vertex
  rw [data.prin_script_eq_sum_edgeDivergence]
  simp_rw [data.edgeDivergence_eq_endpointDivisor]
  simp

end Data

end Utilities.Certificate.WindowProfile
